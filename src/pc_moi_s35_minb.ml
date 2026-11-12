(* ========================================================================= *)
(* pc_moi_s35_minb: Moise GTM 47, Sec 35, Lemma 2 of Theorem 35.1 (p.250),  *)
(* in the tube form of pc_moi_s35_stmt.ml: main theorem DISK_SWAP, the      *)
(* statement MOI_S35_DISK_SWAP.  An innermost inessential circle of an edge *)
(* configuration bounds a disk E in the annulus b; E together with a collar *)
(* is replaced by a planar disk pushed off the level c, and the B-side cell *)
(* is replaced by the ball bounded by the new sphere (PL Schoenflies).      *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt.ml";;
needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_s27.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. General topology: sides of a set, filled spheres (Jordan-Brouwer).    *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_CONNECTED_SIDE = prove
 (`!s t:real^N->bool.
     connected t /\ DISJOINT s t ==> t SUBSET inside s \/ t SUBSET outside s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
    INSIDE_OUTSIDE_INTERSECT_CONNECTED) THEN
  MP_TAC(ISPEC `s:real^N->bool` INSIDE_UNION_OUTSIDE) THEN
  ASM SET_TAC[]);;

let MOI_S5B_CLOPEN_CONNECTED = prove
 (`!c u:real^N->bool.
     connected c /\ open u /\ closure u INTER c SUBSET u /\ ~(u INTER c = {})
     ==> c SUBSET u`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN]) THEN
  DISCH_THEN(MP_TAC o SPEC `u INTER c:real^N->bool`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN
      EXISTS_TAC `closure u:real^N->bool` THEN
      REWRITE_TAC[CLOSED_CLOSURE] THEN
      MP_TAC(ISPEC `u:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]];
    ASM SET_TAC[]]);;

let MOI_S5B_FILL_CHAR = prove
 (`!s x:real^N->bool.
     2 <= dimindex(:N) /\ s homeomorphic sphere(vec 0:real^N,&1) /\
     compact x /\ frontier x = s /\ ~(interior x = {})
     ==> interior x = inside s /\ x = s UNION inside s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `interior x INTER (s:real^N->bool) = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier x = (s:real^N->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(x:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `x = interior x UNION (s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier x = (s:real^N->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `x:real^N->bool` INTERIOR_SUBSET) THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(interior x) INTER ((:real^N) DIFF s) SUBSET interior x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`interior x:real^N->bool`; `x:real^N->bool`]
      CLOSURE_MINIMAL) THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded(interior x:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `x:real^N->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior x INTER outside s:real^N->bool = {}` ASSUME_TAC THENL
   [ASM_CASES_TAC `interior x INTER outside s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`outside s:real^N->bool`; `interior x:real^N->bool`]
      MOI_S5B_CLOPEN_CONNECTED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
      UNDISCH_TAC `closure(interior x) INTER ((:real^N) DIFF s) SUBSET
                   interior x` THEN
      UNDISCH_TAC `inside s UNION outside s = (:real^N) DIFF s` THEN
      SET_TAC[];
      ASM_MESON_TAC[BOUNDED_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior x = inside s:real^N->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [UNDISCH_TAC `interior x INTER outside s:real^N->bool = {}` THEN
      UNDISCH_TAC `interior x INTER (s:real^N->bool) = {}` THEN
      UNDISCH_TAC `inside s UNION outside s = (:real^N) DIFF s` THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S5B_CLOPEN_CONNECTED THEN
      REWRITE_TAC[OPEN_INTERIOR] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `closure(interior x) INTER ((:real^N) DIFF s) SUBSET
                   interior x` THEN
      UNDISCH_TAC `interior x INTER outside s:real^N->bool = {}` THEN
      UNDISCH_TAC `interior x INTER (s:real^N->bool) = {}` THEN
      UNDISCH_TAC `inside s UNION outside s = (:real^N) DIFF s` THEN
      UNDISCH_TAC `~(interior x:real^N->bool = {})` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `x = interior x UNION (s:real^N->bool)` THEN
  UNDISCH_TAC `interior x = inside s:real^N->bool` THEN
  SET_TAC[]);;

let MOI_S5B_PL_BALL_3_FILL = prove
 (`!c:real^3->bool.
     pl_ball 3 c
     ==> pl_sphere 2 (frontier c) /\ compact c /\
         interior c = inside(frontier c) /\
         c = frontier c UNION inside(frontier c)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_sphere 2 (frontier c:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_ball 3 (c:real^3->bool)` THEN
    REWRITE_TAC[pl_ball; pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
    MESON_TAC[MOI_SCD_BALL_BOUNDARY_PLH];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(c:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_BALL_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior c:real^3->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_ball 3 (c:real^3->bool)` THEN
    REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `b:real^3` o MATCH_MP MOI_FN1_SIMPLEX_3_INTERIOR) THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3->bool`; `f:real^3->real^3`;
                   `g:real^3->real^3`] MOI_FN1_HOMEOMORPHISM_INTERIOR) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5B_FILL_CHAR THEN
  ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; DIMINDEX_3; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* 2. The theta configuration: three disks a1, a2, a3 with common boundary   *)
(* k whose pairwise unions are 2-spheres.  If a3 is locally flat, the three *)
(* complementary regions are the free sides of the three spheres, so the    *)
(* filled sphere a1 UNION a3 agrees with the filled sphere a1 UNION a2 off   *)
(* the filled sphere a2 UNION a3 (used for the disk swap of p.250).         *)
(* ------------------------------------------------------------------------- *)

let moi_s5b_flat = new_definition
 `moi_s5b_flat (t:real^N->bool) a3 o3 <=>
    !z. z IN o3
        ==> ?u u1 u2. open u /\ z IN u /\ u INTER t SUBSET a3 /\
                      u DIFF a3 = u1 UNION u2 /\ connected u1 /\ connected u2 /\
                      u INTER a3 SUBSET closure u1 INTER closure u2`;;

let MOI_S5B_COMPONENT_ABSORB = prove
 (`!g u1 w x:real^N.
     connected u1 /\ u1 SUBSET g /\ w IN u1 /\ w IN connected_component g x
     ==> u1 SUBSET connected_component g x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_THETA_ADJ = prove
 (`!t a3 o3 (q:real^N).
     a3 SUBSET t /\ o3 SUBSET a3 /\ connected o3 /\ moi_s5b_flat t a3 o3
     ==> closure(connected_component ((:real^N) DIFF t) q) INTER o3 = {} \/
         o3 SUBSET closure(connected_component ((:real^N) DIFF t) q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5b_flat] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = connected_component ((:real^N) DIFF t) q` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN]) THEN
  DISCH_THEN(MP_TAC o SPEC `o3 INTER closure Q:real^N->bool`) THEN
  ANTS_TAC THENL
   [ALL_TAC; SET_TAC[]] THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_CLOSURE]] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `z:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `u1:real^N->bool`
    (X_CHOOSE_THEN `u2:real^N->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `o3 INTER u:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
  SUBGOAL_THEN `~(u INTER (Q:real^N->bool) = {})` MP_TAC THENL
   [MP_TAC(ISPECL [`u:real^N->bool`; `Q:real^N->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(z:real^N) IN u` THEN
    UNDISCH_TAC `(z:real^N) IN closure Q` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((w:real^N) IN t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N) DIFF t`; `q:real^N`]
      CONNECTED_COMPONENT_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u1:real^N->bool) SUBSET (:real^N) DIFF t /\
                (u2:real^N->bool) SUBSET (:real^N) DIFF t`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN u1 \/ w IN u2` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[];
    MP_TAC(ISPECL [`(:real^N) DIFF t`; `u1:real^N->bool`; `w:real^N`; `q:real^N`]
      MOI_S5B_COMPONENT_ABSORB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SUBSET_CLOSURE) THEN
    ASM SET_TAC[];
    MP_TAC(ISPECL [`(:real^N) DIFF t`; `u2:real^N->bool`; `w:real^N`; `q:real^N`]
      MOI_S5B_COMPONENT_ABSORB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SUBSET_CLOSURE) THEN
    ASM SET_TAC[]]);;

let MOI_S5B_PIGEON3 = prove
 (`!c1 c2 c3 v1 v2:A->bool.
     DISJOINT c1 c2 /\ DISJOINT c1 c3 /\ DISJOINT c2 c3 /\
     (v1 SUBSET c1 /\ ~(v1 = {}) \/ v2 SUBSET c1 /\ ~(v2 = {})) /\
     (v1 SUBSET c2 /\ ~(v1 = {}) \/ v2 SUBSET c2 /\ ~(v2 = {})) /\
     (v1 SUBSET c3 /\ ~(v1 = {}) \/ v2 SUBSET c3 /\ ~(v2 = {}))
     ==> F`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM SET_TAC[]);;

let MOI_S5B_FLAT_COMPONENT = prove
 (`!t a3 u u1 u2 z (x:real^N).
     a3 SUBSET t /\ open u /\ z IN u /\ u INTER t SUBSET a3 /\
     u DIFF a3 = u1 UNION u2 /\
     connected u1 /\ connected u2 /\
     z IN closure(connected_component ((:real^N) DIFF t) x)
     ==> u1 SUBSET connected_component ((:real^N) DIFF t) x /\ ~(u1 = {}) \/
         u2 SUBSET connected_component ((:real^N) DIFF t) x /\ ~(u2 = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Q = connected_component ((:real^N) DIFF t) x` THEN
  SUBGOAL_THEN `~(u INTER (Q:real^N->bool) = {})` MP_TAC THENL
   [MP_TAC(ISPECL [`u:real^N->bool`; `Q:real^N->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(z:real^N) IN u` THEN
    UNDISCH_TAC `(z:real^N) IN closure Q` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Q:real^N->bool) SUBSET (:real^N) DIFF t` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN u1 \/ w IN u2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `u DIFF a3 = (u1 UNION u2):real^N->bool` THEN
    UNDISCH_TAC `u INTER t SUBSET (a3:real^N->bool)` THEN
    UNDISCH_TAC `a3 SUBSET (t:real^N->bool)` THEN
    UNDISCH_TAC `(Q:real^N->bool) SUBSET (:real^N) DIFF t` THEN
    UNDISCH_TAC `(w:real^N) IN Q` THEN UNDISCH_TAC `(w:real^N) IN u` THEN
    SET_TAC[];
    DISJ1_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC MOI_S5B_COMPONENT_ABSORB THEN
      EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `u DIFF a3 = (u1 UNION u2):real^N->bool` THEN
      UNDISCH_TAC `u INTER t SUBSET (a3:real^N->bool)` THEN SET_TAC[];
      UNDISCH_TAC `(w:real^N) IN u1` THEN SET_TAC[]];
    DISJ2_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC MOI_S5B_COMPONENT_ABSORB THEN
      EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `u DIFF a3 = (u1 UNION u2):real^N->bool` THEN
      UNDISCH_TAC `u INTER t SUBSET (a3:real^N->bool)` THEN SET_TAC[];
      UNDISCH_TAC `(w:real^N) IN u2` THEN SET_TAC[]]]);;

let MOI_S5B_THETA_TWO = prove
 (`!t a3 o3 x1 x2 (x3:real^N).
     a3 SUBSET t /\ moi_s5b_flat t a3 o3 /\ ~(o3 = {}) /\
     o3 SUBSET closure(connected_component ((:real^N) DIFF t) x1) /\
     o3 SUBSET closure(connected_component ((:real^N) DIFF t) x2) /\
     o3 SUBSET closure(connected_component ((:real^N) DIFF t) x3) /\
     DISJOINT (connected_component ((:real^N) DIFF t) x1)
              (connected_component ((:real^N) DIFF t) x2) /\
     DISJOINT (connected_component ((:real^N) DIFF t) x1)
              (connected_component ((:real^N) DIFF t) x3) /\
     DISJOINT (connected_component ((:real^N) DIFF t) x2)
              (connected_component ((:real^N) DIFF t) x3)
     ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5b_flat] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z:real^N` o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o check (is_neg o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `u1:real^N->bool`
    (X_CHOOSE_THEN `u2:real^N->bool` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC(ISPECL [`connected_component ((:real^N) DIFF t) x1`;
                       `connected_component ((:real^N) DIFF t) x2`;
                       `connected_component ((:real^N) DIFF t) x3`;
                       `u1:real^N->bool`; `u2:real^N->bool`] MOI_S5B_PIGEON3) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC MOI_S5B_FLAT_COMPONENT THEN
  MAP_EVERY EXISTS_TAC [`a3:real^N->bool`; `u:real^N->bool`; `z:real^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The core of the theta argument: with the side P of a1 UNION a2 that      *)
(* contains the open disk a3 DIFF k and the other side N, the complement of  *)
(* a1 UNION a3 splits into its two components N UNION (a2 DIFF k) UNION I23  *)
(* and P INTER X23 (I23, X23 the inside and outside of a2 UNION a3).  Three  *)
(* complementary regions would touch the flat disk a3 DIFF k, but only two  *)
(* do near each of its points (MOI_S5B_THETA_TWO).                         *)

let MOI_S5B_CONN_SUB = prove
 (`!c e1 e2:real^N->bool.
     connected c /\ c SUBSET e1 UNION e2 /\ open e1 /\ open e2 /\
     e1 INTER e2 = {} /\ ~(c INTER e2 = {})
     ==> c SUBSET e2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e1 UNION e2:real^N->bool`; `c:real^N->bool`;
                 `e1:real^N->bool`; `e2:real^N->bool`]
    MOI_FN1_CONNECTED_SEPARATION) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[]);;

let MOI_S5B_FLAT_ADJ_POINT = prove
 (`!t a3 u u1 u2 z (w:real^N).
     a3 SUBSET t /\ z IN u /\ z IN a3 /\ u INTER t SUBSET a3 /\
     u DIFF a3 = u1 UNION u2 /\ connected u1 /\ connected u2 /\
     u INTER a3 SUBSET closure u1 INTER closure u2 /\ w IN u /\ ~(w IN a3)
     ==> z IN closure(connected_component ((:real^N) DIFF t) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u1:real^N->bool) SUBSET (:real^N) DIFF t /\
                (u2:real^N->bool) SUBSET (:real^N) DIFF t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `u DIFF a3 = (u1 UNION u2):real^N->bool` THEN
    UNDISCH_TAC `u INTER t SUBSET (a3:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN u1 \/ w IN u2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `u DIFF a3 = (u1 UNION u2):real^N->bool` THEN
    UNDISCH_TAC `(w:real^N) IN u` THEN UNDISCH_TAC `~((w:real^N) IN a3)` THEN
    SET_TAC[];
    MP_TAC(ISPECL [`(:real^N) DIFF t`; `u1:real^N->bool`; `w:real^N`]
      CONNECTED_COMPONENT_MAXIMAL);
    MP_TAC(ISPECL [`(:real^N) DIFF t`; `u2:real^N->bool`; `w:real^N`]
      CONNECTED_COMPONENT_MAXIMAL)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SUBSET_CLOSURE) THEN
  UNDISCH_TAC `u INTER a3 SUBSET closure u1 INTER closure (u2:real^N->bool)` THEN
  UNDISCH_TAC `(z:real^N) IN u` THEN UNDISCH_TAC `(z:real^N) IN a3` THEN
  SET_TAC[]);;

let MOI_S5B_THETA_SPLIT = prove
 (`!a1 a2 a3 k P N I23 X23 CX CY:real^N->bool.
     closed a1 /\ closed a2 /\ closed a3 /\
     a1 INTER a2 = k /\ a1 INTER a3 = k /\ a2 INTER a3 = k /\
     connected (a3 DIFF k) /\ ~(a3 DIFF k = {}) /\
     moi_s5b_flat (a1 UNION a2 UNION a3) a3 (a3 DIFF k) /\
     open P /\ open N /\ connected P /\ P INTER N = {} /\
     P UNION N = (:real^N) DIFF (a1 UNION a2) /\
     a3 DIFF k SUBSET P /\
     open I23 /\ open X23 /\ connected I23 /\ ~(I23 = {}) /\
     I23 INTER X23 = {} /\
     I23 UNION X23 = (:real^N) DIFF (a2 UNION a3) /\
     a2 UNION a3 SUBSET closure I23 /\
     I23 SUBSET P /\ DISJOINT I23 (a1 UNION a2) /\
     open CX /\ open CY /\ CX INTER CY = {} /\
     CX UNION CY = (:real^N) DIFF (a1 UNION a3) /\
     a3 SUBSET closure CY /\
     (N UNION (a2 DIFF k) UNION I23) INTER (P INTER X23) = {} /\
     (N UNION (a2 DIFF k) UNION I23) UNION (P INTER X23) =
       (:real^N) DIFF (a1 UNION a3) /\
     N UNION (a2 DIFF k) UNION I23 SUBSET CX
     ==> N UNION (a2 DIFF k) UNION I23 = CX /\ P INTER X23 = CY`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `G = (:real^N) DIFF (a1 UNION a2 UNION a3)` THEN
  SUBGOAL_THEN `open(G:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[GSYM closed] THEN
    ASM_SIMP_TAC[CLOSED_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `CY SUBSET P INTER (X23:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `CX INTER CY:real^N->bool = {}` THEN
    UNDISCH_TAC `CX UNION CY = (:real^N) DIFF (a1 UNION a3)` THEN
    UNDISCH_TAC `(N UNION (a2 DIFF k) UNION I23) UNION (P INTER X23) =
                 (:real^N) DIFF (a1 UNION a3)` THEN
    UNDISCH_TAC `N UNION (a2 DIFF k) UNION I23 SUBSET (CX:real^N->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `P INTER (X23:real^N->bool) SUBSET G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    UNDISCH_TAC `P UNION N = (:real^N) DIFF (a1 UNION a2)` THEN
    UNDISCH_TAC `I23 UNION X23 = (:real^N) DIFF (a2 UNION a3)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `G SUBSET (N UNION I23) UNION P INTER (X23:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    UNDISCH_TAC `P UNION N = (:real^N) DIFF (a1 UNION a2)` THEN
    UNDISCH_TAC `I23 UNION X23 = (:real^N) DIFF (a2 UNION a3)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N UNION I23) INTER P INTER (X23:real^N->bool) = {}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `P INTER N:real^N->bool = {}` THEN
    UNDISCH_TAC `I23 INTER X23:real^N->bool = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `G SUBSET (CX UNION CY:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `CX UNION CY = (:real^N) DIFF (a1 UNION a3)` THEN
    EXPAND_TAC "G" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(I23:real^N->bool) SUBSET G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    UNDISCH_TAC `I23 UNION X23 = (:real^N) DIFF (a2 UNION a3)` THEN
    UNDISCH_TAC `DISJOINT I23 (a1 UNION a2:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CX INTER P INTER (X23:real^N->bool) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
    X_GEN_TAC `y1:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y1:real^N) IN G` ASSUME_TAC THENL
     [UNDISCH_TAC `P INTER (X23:real^N->bool) SUBSET G` THEN
      UNDISCH_TAC `(y1:real^N) IN P` THEN UNDISCH_TAC `(y1:real^N) IN X23` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `Y1 = connected_component G (y1:real^N)` THEN
    SUBGOAL_THEN `(y1:real^N) IN Y1` ASSUME_TAC THENL
     [EXPAND_TAC "Y1" THEN REWRITE_TAC[IN] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `connected (Y1:real^N->bool) /\ open Y1 /\ Y1 SUBSET G`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Y1" THEN
      ASM_SIMP_TAC[CONNECTED_CONNECTED_COMPONENT; OPEN_CONNECTED_COMPONENT;
                   CONNECTED_COMPONENT_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `Y1 SUBSET P INTER (X23:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S5B_CONN_SUB THEN
      EXISTS_TAC `N UNION I23:real^N->bool` THEN
      ASM_SIMP_TAC[OPEN_UNION; OPEN_INTER] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `Y1 SUBSET (CX:real^N->bool)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[UNION_COMM] THEN
      MATCH_MP_TAC MOI_S5B_CONN_SUB THEN
      EXISTS_TAC `CY:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `a3 DIFF k SUBSET closure(Y1:real^N->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`a1 UNION a2 UNION a3:real^N->bool`; `a3:real^N->bool`;
                     `a3 DIFF k:real^N->bool`; `y1:real^N`] MOI_S5B_THETA_ADJ) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`P:real^N->bool`; `Y1:real^N->bool`]
        MOI_S5B_CLOPEN_CONNECTED) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `w:real^N` THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(w:real^N) IN G` ASSUME_TAC THENL
         [EXPAND_TAC "G" THEN
          UNDISCH_TAC `closure Y1 INTER (a3 DIFF k):real^N->bool = {}` THEN
          UNDISCH_TAC `P UNION N = (:real^N) DIFF (a1 UNION a2)` THEN
          UNDISCH_TAC `a1 INTER a3:real^N->bool = k` THEN
          UNDISCH_TAC `(w:real^N) IN P` THEN
          UNDISCH_TAC `(w:real^N) IN closure Y1` THEN SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(w:real^N) IN closure Y1` THEN EXPAND_TAC "Y1" THEN
        ASM_SIMP_TAC[IN_CLOSURE_CONNECTED_COMPONENT];
        DISCH_TAC THEN
        UNDISCH_TAC `~(a3 DIFF k:real^N->bool = {})` THEN
        UNDISCH_TAC `a3 DIFF k SUBSET (P:real^N->bool)` THEN
        UNDISCH_TAC `P SUBSET (Y1:real^N->bool)` THEN
        UNDISCH_TAC `Y1 SUBSET (G:real^N->bool)` THEN EXPAND_TAC "G" THEN
        SET_TAC[]];
      ALL_TAC] THEN
    X_CHOOSE_TAC `i0:real^N` (REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]
      (ASSUME `~(I23:real^N->bool = {})`)) THEN
    SUBGOAL_THEN `connected_component G (i0:real^N) = I23` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5B_CONN_SUB THEN
        EXISTS_TAC `N UNION P INTER X23:real^N->bool` THEN
        ASM_SIMP_TAC[CONNECTED_CONNECTED_COMPONENT; OPEN_UNION; OPEN_INTER] THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`G:real^N->bool`; `i0:real^N`]
            CONNECTED_COMPONENT_SUBSET) THEN ASM SET_TAC[];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `P INTER N:real^N->bool = {}` THEN
          UNDISCH_TAC `I23 INTER X23:real^N->bool = {}` THEN
          UNDISCH_TAC `I23 SUBSET (P:real^N->bool)` THEN SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `i0:real^N` THEN
        ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[IN] THEN
        MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM SET_TAC[];
        MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `a3 DIFF k:real^N->bool` MEMBER_NOT_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
    UNDISCH_TAC `moi_s5b_flat (a1 UNION a2 UNION a3) a3 (a3 DIFF k:real^N->bool)` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      MP_TAC(SPEC `z:real^N` (REWRITE_RULE[moi_s5b_flat] th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `u1:real^N->bool`
      (X_CHOOSE_THEN `u2:real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `?w:real^N. w IN u /\ w IN CY` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IN_INTER; MEMBER_NOT_EMPTY] THEN
      MP_TAC(ISPECL [`u:real^N->bool`; `CY:real^N->bool`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(z:real^N) IN u` THEN UNDISCH_TAC `(z:real^N) IN a3 DIFF k` THEN
      UNDISCH_TAC `a3 SUBSET closure(CY:real^N->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) IN G` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `connected_component G (w:real^N) SUBSET CY` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S5B_CONN_SUB THEN EXISTS_TAC `CX:real^N->bool` THEN
      ASM_REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`G:real^N->bool`; `w:real^N`]
          CONNECTED_COMPONENT_SUBSET) THEN ASM SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `w:real^N` THEN
        ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[IN] THEN
        MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `a3 DIFF k SUBSET closure(connected_component G (w:real^N))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`a1 UNION a2 UNION a3:real^N->bool`; `a3:real^N->bool`;
                     `a3 DIFF k:real^N->bool`; `w:real^N`] MOI_S5B_THETA_ADJ) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^N` THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      MP_TAC(ISPECL [`a1 UNION a2 UNION a3:real^N->bool`; `a3:real^N->bool`;
        `u:real^N->bool`; `u1:real^N->bool`; `u2:real^N->bool`; `z:real^N`;
        `w:real^N`] MOI_S5B_FLAT_ADJ_POINT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^N) IN a3 DIFF k` THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^N) IN CY` THEN
      UNDISCH_TAC `CX UNION CY = (:real^N) DIFF (a1 UNION a3)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL [`a1 UNION a2 UNION a3:real^N->bool`; `a3:real^N->bool`;
                   `a3 DIFF k:real^N->bool`; `y1:real^N`; `w:real^N`;
                   `i0:real^N`] MOI_S5B_THETA_TWO) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `a2 UNION a3 SUBSET closure (I23:real^N->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `Y1 SUBSET (CX:real^N->bool)` THEN
      UNDISCH_TAC `connected_component G (w:real^N) SUBSET CY` THEN
      UNDISCH_TAC `CX INTER CY:real^N->bool = {}` THEN SET_TAC[];
      UNDISCH_TAC `Y1 SUBSET P INTER (X23:real^N->bool)` THEN
      UNDISCH_TAC `I23 INTER X23:real^N->bool = {}` THEN SET_TAC[];
      UNDISCH_TAC `connected_component G (w:real^N) SUBSET CY` THEN
      UNDISCH_TAC `N UNION (a2 DIFF k) UNION I23 SUBSET (CX:real^N->bool)` THEN
      UNDISCH_TAC `CX INTER CY:real^N->bool = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `CX INTER P INTER (X23:real^N->bool) = {}` THEN
  UNDISCH_TAC `CY SUBSET P INTER (X23:real^N->bool)` THEN
  UNDISCH_TAC `CX UNION CY = (:real^N) DIFF (a1 UNION a3)` THEN
  UNDISCH_TAC `(N UNION (a2 DIFF k) UNION I23) UNION (P INTER X23) =
               (:real^N) DIFF (a1 UNION a3)` THEN
  UNDISCH_TAC `N UNION (a2 DIFF k) UNION I23 SUBSET (CX:real^N->bool)` THEN
  UNDISCH_TAC `CX INTER CY:real^N->bool = {}` THEN
  SET_TAC[]);;

(* The theta lemma: the filled spheres of a1 UNION a3 and a1 UNION a2 agree  *)
(* off the filled sphere of a2 UNION a3, when p is inside a1 UNION a2 and    *)
(* outside a2 UNION a3 and a3 is locally flat at its interior points.       *)

let MOI_S5B_COBOUNDED_INTER = prove
 (`!s t:real^N->bool.
     bounded s /\ bounded t ==> ~bounded(outside s INTER outside t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bounded((:real^N))` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[NOT_BOUNDED_UNIV]] THEN
  SUBGOAL_THEN `(:real^N) = ((:real^N) DIFF outside s UNION
                             (:real^N) DIFF outside t) UNION
                            (outside s INTER outside t)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[BOUNDED_UNION; COBOUNDED_OUTSIDE]);;

let MOI_S5B_FRONTIER_CLOSURE = prove
 (`!s t:real^N->bool. frontier s = t ==> t SUBSET closure s`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[frontier] THEN SET_TAC[]);;

let MOI_S5B_THETA_HALF = prove
 (`!a1 a2 a3 k P N I23 X23 I13 X13:real^N->bool.
     closed a1 /\ closed a2 /\ closed a3 /\
     a1 INTER a2 = k /\ a1 INTER a3 = k /\ a2 INTER a3 = k /\
     connected (a2 DIFF k) /\ ~(a2 DIFF k = {}) /\
     connected (a3 DIFF k) /\ ~(a3 DIFF k = {}) /\
     moi_s5b_flat (a1 UNION a2 UNION a3) a3 (a3 DIFF k) /\
     open P /\ open N /\ connected P /\ connected N /\ P INTER N = {} /\
     P UNION N = (:real^N) DIFF (a1 UNION a2) /\ a1 UNION a2 SUBSET closure N /\
     a3 DIFF k SUBSET P /\
     open I23 /\ open X23 /\ connected I23 /\ ~(I23 = {}) /\
     I23 INTER X23 = {} /\ I23 UNION X23 = (:real^N) DIFF (a2 UNION a3) /\
     a2 UNION a3 SUBSET closure I23 /\ DISJOINT I23 (a1 UNION a2) /\
     open I13 /\ open X13 /\ I13 INTER X13 = {} /\
     I13 UNION X13 = (:real^N) DIFF (a1 UNION a3) /\
     a1 UNION a3 SUBSET closure I13 /\ a1 UNION a3 SUBSET closure X13
     ==> (N UNION (a2 DIFF k) UNION I23 = I13 /\ P INTER X23 = X13) \/
         (N UNION (a2 DIFF k) UNION I23 = X13 /\ P INTER X23 = I13)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `I23 SUBSET (P:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`P UNION N:real^N->bool`; `I23:real^N->bool`;
                   `N:real^N->bool`; `P:real^N->bool`]
      MOI_FN1_CONNECTED_SEPARATION) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `DISJOINT I23 (a1 UNION a2:real^N->bool)` THEN
      UNDISCH_TAC `P UNION N = (:real^N) DIFF (a1 UNION a2)` THEN
      UNDISCH_TAC `P INTER N:real^N->bool = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `DISJOINT I23 (a1 UNION a2:real^N->bool)` THEN
      UNDISCH_TAC `P UNION N = (:real^N) DIFF (a1 UNION a2)` THEN
      UNDISCH_TAC `N INTER I23:real^N->bool = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    X_CHOOSE_TAC `z:real^N` (REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]
      (ASSUME `~(a3 DIFF k:real^N->bool = {})`)) THEN
    MP_TAC(ISPECL [`P:real^N->bool`; `I23:real^N->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^N) IN a3 DIFF k` THEN
    UNDISCH_TAC `a3 DIFF k SUBSET (P:real^N->bool)` THEN
    UNDISCH_TAC `a2 UNION a3 SUBSET closure(I23:real^N->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(N UNION (a2 DIFF k) UNION I23) INTER (P INTER X23):real^N->bool = {} /\
    (N UNION (a2 DIFF k) UNION I23) UNION (P INTER X23) =
    (:real^N) DIFF (a1 UNION a3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `I23 SUBSET (P:real^N->bool)` THEN
    UNDISCH_TAC `a3 DIFF k SUBSET (P:real^N->bool)` THEN
    UNDISCH_TAC `DISJOINT I23 (a1 UNION a2:real^N->bool)` THEN
    UNDISCH_TAC `P UNION N = (:real^N) DIFF (a1 UNION a2)` THEN
    UNDISCH_TAC `P INTER N:real^N->bool = {}` THEN
    UNDISCH_TAC `I23 INTER X23:real^N->bool = {}` THEN
    UNDISCH_TAC `I23 UNION X23 = (:real^N) DIFF (a2 UNION a3)` THEN
    UNDISCH_TAC `a1 INTER a2:real^N->bool = k` THEN
    UNDISCH_TAC `a1 INTER a3:real^N->bool = k` THEN
    UNDISCH_TAC `a2 INTER a3:real^N->bool = k` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(N UNION (a2 DIFF k) UNION I23:real^N->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `N UNION (a2 DIFF k) UNION I23:real^N->bool =
                  (N UNION (a2 DIFF k)) UNION (I23 UNION (a2 DIFF k))`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `N:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `N:real^N->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `a1 UNION a2 SUBSET closure(N:real^N->bool)` THEN SET_TAC[];
      MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `I23:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `I23:real^N->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `a2 UNION a3 SUBSET closure(I23:real^N->bool)` THEN SET_TAC[];
      UNDISCH_TAC `~(a2 DIFF k:real^N->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I13 UNION X13:real^N->bool`;
                 `N UNION (a2 DIFF k) UNION I23:real^N->bool`;
                 `X13:real^N->bool`; `I13:real^N->bool`]
    MOI_FN1_CONNECTED_SEPARATION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `(N UNION (a2 DIFF k) UNION I23) UNION (P INTER X23) =
                 (:real^N) DIFF (a1 UNION a3)` THEN
    UNDISCH_TAC `I13 UNION X13 = (:real^N) DIFF (a1 UNION a3)` THEN
    UNDISCH_TAC `I13 INTER X13:real^N->bool = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC MOI_S5B_THETA_SPLIT THEN
    MAP_EVERY EXISTS_TAC [`a1:real^N->bool`; `a3:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `a1 UNION a3 SUBSET closure(X13:real^N->bool)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `X13 INTER (N UNION (a2 DIFF k) UNION I23):real^N->bool = {}` THEN
    UNDISCH_TAC `(N UNION (a2 DIFF k) UNION I23) UNION (P INTER X23) =
                 (:real^N) DIFF (a1 UNION a3)` THEN
    UNDISCH_TAC `I13 UNION X13 = (:real^N) DIFF (a1 UNION a3)` THEN
    SET_TAC[];
    DISJ2_TAC THEN MATCH_MP_TAC MOI_S5B_THETA_SPLIT THEN
    MAP_EVERY EXISTS_TAC [`a1:real^N->bool`; `a3:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `I13 INTER X13:real^N->bool = {}` THEN SET_TAC[];
      UNDISCH_TAC `I13 UNION X13 = (:real^N) DIFF (a1 UNION a3)` THEN
      SET_TAC[];
      UNDISCH_TAC `a1 UNION a3 SUBSET closure(I13:real^N->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `I13 INTER (N UNION (a2 DIFF k) UNION I23):real^N->bool = {}` THEN
      UNDISCH_TAC `(N UNION (a2 DIFF k) UNION I23) UNION (P INTER X23) =
                   (:real^N) DIFF (a1 UNION a3)` THEN
      UNDISCH_TAC `I13 UNION X13 = (:real^N) DIFF (a1 UNION a3)` THEN
      SET_TAC[]]]);;

let MOI_S5B_THETA = prove
 (`!a1 a2 a3 k (p:real^N).
     2 <= dimindex(:N) /\
     closed a1 /\ closed a2 /\ closed a3 /\
     a1 INTER a2 = k /\ a1 INTER a3 = k /\ a2 INTER a3 = k /\
     connected (a1 DIFF k) /\ connected (a2 DIFF k) /\ ~(a2 DIFF k = {}) /\
     connected (a3 DIFF k) /\ ~(a3 DIFF k = {}) /\
     (a1 UNION a2) homeomorphic sphere(vec 0:real^N,&1) /\
     (a1 UNION a3) homeomorphic sphere(vec 0:real^N,&1) /\
     (a2 UNION a3) homeomorphic sphere(vec 0:real^N,&1) /\
     moi_s5b_flat (a1 UNION a2 UNION a3) a3 (a3 DIFF k) /\
     p IN inside(a1 UNION a2) /\ p IN outside(a2 UNION a3)
     ==> ((a1 UNION a3) UNION inside(a1 UNION a3)) DIFF
         ((a2 UNION a3) UNION inside(a2 UNION a3)) =
         ((a1 UNION a2) UNION inside(a1 UNION a2)) DIFF
         ((a2 UNION a3) UNION inside(a2 UNION a3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `a1 UNION a2:real^N->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `a1 UNION a3:real^N->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `a2 UNION a3:real^N->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bounded(a1 UNION a2:real^N->bool) /\
                bounded(a2 UNION a3:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  ABBREV_TAC `I12 = inside(a1 UNION a2:real^N->bool)` THEN
  ABBREV_TAC `X12 = outside(a1 UNION a2:real^N->bool)` THEN
  ABBREV_TAC `I13 = inside(a1 UNION a3:real^N->bool)` THEN
  ABBREV_TAC `X13 = outside(a1 UNION a3:real^N->bool)` THEN
  ABBREV_TAC `I23 = inside(a2 UNION a3:real^N->bool)` THEN
  ABBREV_TAC `X23 = outside(a2 UNION a3:real^N->bool)` THEN
  SUBGOAL_THEN `a1 DIFF k SUBSET (X23:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a2 UNION a3:real^N->bool`; `a1 DIFF k:real^N->bool`]
      MOI_S5B_CONNECTED_SIDE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `a1 INTER a2:real^N->bool = k` THEN
      UNDISCH_TAC `a1 INTER a3:real^N->bool = k` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `X23 SUBSET (X12:real^N->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXPAND_TAC "X12" THEN MATCH_MP_TAC UNBOUNDED_DISJOINT_IN_OUTSIDE THEN
      EXISTS_TAC `X23:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `a1 INTER a2:real^N->bool = k` THEN
      UNDISCH_TAC `a1 DIFF k SUBSET (I23:real^N->bool)` THEN
      UNDISCH_TAC `I23 INTER X23:real^N->bool = {}` THEN
      UNDISCH_TAC `I23 UNION X23 = (:real^N) DIFF (a2 UNION a3)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `X23 SUBSET (X12:real^N->bool)` THEN
    UNDISCH_TAC `(p:real^N) IN I12` THEN UNDISCH_TAC `(p:real^N) IN X23` THEN
    UNDISCH_TAC `I12 INTER X12:real^N->bool = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (I23:real^N->bool) (a1 UNION a2)` ASSUME_TAC THENL
   [UNDISCH_TAC `a1 DIFF k SUBSET (X23:real^N->bool)` THEN
    UNDISCH_TAC `I23 INTER X23:real^N->bool = {}` THEN
    UNDISCH_TAC `I23 UNION X23 = (:real^N) DIFF (a2 UNION a3)` THEN
    UNDISCH_TAC `a1 INTER a2:real^N->bool = k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a1 UNION a2 SUBSET closure(I12:real^N->bool) /\
    a1 UNION a2 SUBSET closure(X12:real^N->bool) /\
    a1 UNION a3 SUBSET closure(I13:real^N->bool) /\
    a1 UNION a3 SUBSET closure(X13:real^N->bool) /\
    a2 UNION a3 SUBSET closure(I23:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S5B_FRONTIER_CLOSURE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a1 UNION a2:real^N->bool`; `a3 DIFF k:real^N->bool`]
    MOI_S5B_CONNECTED_SIDE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `a1 INTER a3:real^N->bool = k` THEN
    UNDISCH_TAC `a2 INTER a3:real^N->bool = k` THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`a1:real^N->bool`; `a2:real^N->bool`; `a3:real^N->bool`;
                   `k:real^N->bool`; `I12:real^N->bool`; `X12:real^N->bool`;
                   `I23:real^N->bool`; `X23:real^N->bool`; `I13:real^N->bool`;
                   `X13:real^N->bool`] MOI_S5B_THETA_HALF) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `bounded (I13:real^N->bool)` THEN
      UNDISCH_TAC `~bounded (X12:real^N->bool)` THEN
      UNDISCH_TAC `X12 UNION (a2 DIFF k) UNION I23 = I13:real^N->bool` THEN
      MESON_TAC[BOUNDED_SUBSET; SUBSET_UNION];
      UNDISCH_TAC `I12 INTER X23 = I13:real^N->bool` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `I23 UNION X23 = (:real^N) DIFF (a2 UNION a3)` THEN
      SET_TAC[]];
    MP_TAC(ISPECL [`a1:real^N->bool`; `a2:real^N->bool`; `a3:real^N->bool`;
                   `k:real^N->bool`; `X12:real^N->bool`; `I12:real^N->bool`;
                   `I23:real^N->bool`; `X23:real^N->bool`; `I13:real^N->bool`;
                   `X13:real^N->bool`] MOI_S5B_THETA_HALF) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `I12 INTER X12:real^N->bool = {}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `I12 UNION (a2 DIFF k) UNION I23 = I13:real^N->bool` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
      MP_TAC(ISPECL [`a1 UNION a2:real^N->bool`; `a2 UNION a3:real^N->bool`]
        MOI_S5B_COBOUNDED_INTER) THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Swapping a PL disk for another with the same boundary (the step       *)
(* "replace E_J by D_J" of p.250), polyhedra cut along disks, and the       *)
(* transfer of insides of spheres through an embedding of an open set.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_DISK_PLH = prove
 (`!e d j:real^N->bool.
     pl_cell_with_boundary 2 e j /\ pl_cell_with_boundary 2 d j
     ==> ?g g'. pl_homeomorphism (e,d) (g,g') /\ !x. x IN j ==> g x = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^N->bool` (X_CHOOSE_THEN `f1:real^N->real^N`
     (X_CHOOSE_THEN `g1:real^N->real^N` STRIP_ASSUME_TAC)))
   (X_CHOOSE_THEN `k2:real^N->bool` (X_CHOOSE_THEN `f2:real^N->real^N`
     (X_CHOOSE_THEN `g2:real^N->real^N` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k1:real^N->bool`; `e:real^N->bool`; `f1:real^N->real^N`;
                 `g1:real^N->real^N`] MOI_S27_PLH_SIMPLEX_RF) THEN
  MP_TAC(ISPECL [`k2:real^N->bool`; `d:real^N->bool`; `f2:real^N->real^N`;
                 `g2:real^N->real^N`] MOI_S27_PLH_SIMPLEX_RF) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `j = IMAGE (f2:real^N->real^N) (relative_frontier k2)`
    (SUBST1_TAC o SYM) THEN
  UNDISCH_THEN `j = IMAGE (f1:real^N->real^N) (relative_frontier k1)`
    (SUBST1_TAC o SYM) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k1:real^N->bool,relative_frontier k2)
                     ((g2:real^N->real^N) o (f1:real^N->real^N),
                      (g1:real^N->real^N) o (f2:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `j:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:real^N->bool`; `k2:real^N->bool`; `2`;
                 `(g2:real^N->real^N) o (f1:real^N->real^N)`;
                 `(g1:real^N->real^N) o (f2:real^N->real^N)`]
    PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` (X_CHOOSE_THEN `r':real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(f2:real^N->real^N) o (r:real^N->real^N) o (g1:real^N->real^N)` THEN
  EXISTS_TAC `((f1:real^N->real^N) o (r':real^N->real^N)) o
              (g2:real^N->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(g1:real^N->real^N) x IN relative_frontier k1` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_IMAGE; IN_IMAGE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM] THEN
  SUBGOAL_THEN `(f1:real^N->real^N)((g1:real^N->real^N) x) = x` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_PL2_PL_HOMEO_RINV THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier k1:real^N->bool`;
                          `j:real^N->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_PL2_PL_HOMEO_RINV THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier k2:real^N->bool`;
                          `j:real^N->bool`] THEN ASM_REWRITE_TAC[]]);;

let MOI_S5B_DISK_REPLACE = prove
 (`!a e d j:real^N->bool.
     pl_cell_with_boundary 2 e j /\ pl_cell_with_boundary 2 d j /\
     a INTER e = j /\ a INTER d = j /\ closed a /\ locally_polyhedral a
     ==> ?h h'. pl_homeomorphism (a UNION e,a UNION d) (h,h') /\
                !y. y IN a ==> h y = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real^N->bool`; `d:real^N->bool`; `j:real^N->bool`]
    MOI_S5B_DISK_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` (X_CHOOSE_THEN `g':real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `compact(e:real^N->bool) /\ compact(d:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 2 (e:real^N->bool) j` THEN
    UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^N->bool) j` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN
    MESON_TAC[MOI_PL2_PL_HOMEO_COMPACT; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `e:real^N->bool`; `a:real^N->bool`;
                 `d:real^N->bool`; `\x:real^N. x`; `\x:real^N. x`;
                 `g:real^N->real^N`; `g':real^N->real^N`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; IMAGE_ID] THEN ANTS_TAC THENL
   [REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
    ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    ASM SET_TAC[];
    DISCH_TAC THEN
    EXISTS_TAC `\x:real^N. if x IN a then x else (g:real^N->real^N) x` THEN
    EXISTS_TAC `\y:real^N. if y IN a then y else (g':real^N->real^N) y` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MOI_S5B_CLOSURE_DIFF_POLYHEDRON = prove
 (`!x e:real^N->bool.
     pl_polyhedron x /\ pl_polyhedron e /\ e SUBSET x
     ==> pl_polyhedron(closure(x DIFF e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(GEN_REWRITE_RULE I [PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX]
    (ASSUME `pl_polyhedron (x:real^N->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?t. simplicial_complex t /\ UNIONS t = (x:real^N->bool) /\
        e = UNIONS {s:real^N->bool | s IN t /\ s SUBSET e}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(GEN_REWRITE_RULE I [pl_polyhedron]
      (ASSUME `pl_polyhedron (e:real^N->bool)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `de:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `de:(real^N->bool)->bool`]
      SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(q:real^N->bool) IN de` THEN
      UNDISCH_TAC `e SUBSET (x:real^N->bool)` THEN
      UNDISCH_TAC `e = UNIONS (de:(real^N->bool)->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?q:real^N->bool. q IN de /\ y IN q` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN e` THEN
      UNDISCH_TAC `e = UNIONS (de:(real^N->bool)->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `!k:real^N->bool. k IN de ==> ?f. f SUBSET t /\ k = UNIONS f` THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?s:real^N->bool. s IN f /\ y IN s` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN q` THEN
      UNDISCH_TAC `q = UNIONS (f:(real^N->bool)->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `f SUBSET (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `e = UNIONS (de:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(q:real^N->bool) IN de` THEN
    UNDISCH_TAC `q = UNIONS (f:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(s:real^N->bool) IN f` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN
   `closure(x DIFF e) = UNIONS {s:real^N->bool | s IN t /\ ~(s SUBSET e)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [UNDISCH_TAC `UNIONS t = (x:real^N->bool)` THEN SET_TAC[];
        MATCH_MP_TAC CLOSED_UNIONS THEN
        ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
        X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC MOI_CON_SC_COMPACT THEN
        EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `relative_interior s SUBSET (x DIFF e:real^N->bool)`
      ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN
        DISCH_TAC THEN CONJ_TAC THENL
         [MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
          UNDISCH_TAC `(y:real^N) IN relative_interior s` THEN
          UNDISCH_TAC `(s:real^N->bool) IN t` THEN
          UNDISCH_TAC `UNIONS t = (x:real^N->bool)` THEN SET_TAC[];
          DISCH_TAC THEN
          MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`;
                         `{s:real^N->bool | s IN t /\ s SUBSET e}`; `y:real^N`]
            MOI_PLT_SIMPLEX_SUBSET_UNIONS) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
            UNDISCH_TAC `(y:real^N) IN e` THEN
            UNDISCH_TAC `e = UNIONS {s:real^N->bool | s IN t /\ s SUBSET e}` THEN
            SET_TAC[];
            UNDISCH_TAC `~((s:real^N->bool) SUBSET e)` THEN
            UNDISCH_TAC `e = UNIONS {s:real^N->bool | s IN t /\ s SUBSET e}` THEN
            SET_TAC[]]];
        ALL_TAC] THEN
      MP_TAC(ISPEC `s:real^N->bool` CONVEX_CLOSURE_RELATIVE_INTERIOR) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
        EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `closure s = s:real^N->bool` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC MOI_CON_SC_COMPACT THEN
        EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{s:real^N->bool | s IN t /\ ~(s SUBSET e)}` THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_CON_SC_POLYTOPE THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_INSIDE_TRANSFER = prove
 (`!(f:real^N->real^N) u s.
     2 <= dimindex(:N) /\ open u /\ f continuous_on u /\
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
     s homeomorphic sphere(vec 0:real^N,&1) /\ s UNION inside s SUBSET u
     ==> IMAGE f s homeomorphic sphere(vec 0:real^N,&1) /\
         inside(IMAGE f s) = IMAGE f (inside s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(s UNION inside s:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; UNION_WITH_INSIDE] THEN
    ASM_SIMP_TAC[GSYM OPEN_CLOSED; OPEN_OUTSIDE; COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[GSYM UNION_WITH_INSIDE; BOUNDED_UNION] THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; BOUNDED_INSIDE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^N) continuous_on (s UNION inside s)`
  ASSUME_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) s homeomorphic sphere(vec 0:real^N,&1)`
  ASSUME_TAC THENL
   [TRANS_TAC HOMEOMORPHIC_TRANS `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
    EXISTS_TAC `f:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION];
                    ASM SET_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPEC `IMAGE (f:real^N->real^N) s` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  MP_TAC(ISPEC `s:real^N->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `V = IMAGE (f:real^N->real^N) (inside s)` THEN
  SUBGOAL_THEN `open(V:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION];
                    ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(V:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (f:real^N->real^N) (s UNION inside s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (s UNION inside s) =
                IMAGE f s UNION V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IMAGE_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded(V:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^N->real^N) (s UNION inside s)` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `V INTER IMAGE (f:real^N->real^N) s = {}` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPEC `s:real^N->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `!x y. x IN u /\ y IN u /\ (f:real^N->real^N) x = f y ==> x = y` THEN
    UNDISCH_TAC `s UNION inside s SUBSET (u:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure V INTER ((:real^N) DIFF IMAGE (f:real^N->real^N) s) SUBSET V`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`;
                   `IMAGE (f:real^N->real^N) (s UNION inside s)`]
      CLOSURE_MINIMAL) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ANTS_TAC THENL
     [SET_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(V:real^N->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `V INTER outside(IMAGE (f:real^N->real^N) s) = {}`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `V INTER outside(IMAGE (f:real^N->real^N) s) = {}` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`outside(IMAGE (f:real^N->real^N) s)`; `V:real^N->bool`]
      MOI_S5B_CLOPEN_CONNECTED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `closure V INTER ((:real^N) DIFF IMAGE (f:real^N->real^N) s) SUBSET V` THEN
      UNDISCH_TAC `inside (IMAGE (f:real^N->real^N) s) UNION
                   outside (IMAGE f s) = (:real^N) DIFF IMAGE f s` THEN
      SET_TAC[];
      ASM_MESON_TAC[BOUNDED_SUBSET]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_CLOPEN_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `closure V INTER ((:real^N) DIFF IMAGE (f:real^N->real^N) s) SUBSET V` THEN
      UNDISCH_TAC `inside (IMAGE (f:real^N->real^N) s) UNION
                   outside (IMAGE f s) = (:real^N) DIFF IMAGE f s` THEN
      SET_TAC[];
      UNDISCH_TAC `V INTER outside(IMAGE (f:real^N->real^N) s) = {}` THEN
      UNDISCH_TAC `V INTER IMAGE (f:real^N->real^N) s = {}` THEN
      UNDISCH_TAC `~(V:real^N->bool = {})` THEN
      UNDISCH_TAC `inside (IMAGE (f:real^N->real^N) s) UNION
                   outside (IMAGE f s) = (:real^N) DIFF IMAGE f s` THEN
      SET_TAC[]];
    UNDISCH_TAC `V INTER outside(IMAGE (f:real^N->real^N) s) = {}` THEN
    UNDISCH_TAC `V INTER IMAGE (f:real^N->real^N) s = {}` THEN
    UNDISCH_TAC `inside (IMAGE (f:real^N->real^N) s) UNION
                 outside (IMAGE f s) = (:real^N) DIFF IMAGE f s` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 4. Disks in topological 2-spheres, by stereographic projection: the open *)
(* disk is open in the sphere and the complement of the closed disk is      *)
(* connected (the 2D facts the swap needs about the sphere frontier xb).    *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_BOUNDED_CLOPEN_INSIDE = prove
 (`!s v:real^N->bool.
     2 <= dimindex(:N) /\ s homeomorphic sphere(vec 0:real^N,&1) /\
     open v /\ bounded v /\ ~(v = {}) /\ v INTER s = {} /\
     closure v INTER ((:real^N) DIFF s) SUBSET v
     ==> v = inside s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `v INTER outside s:real^N->bool = {}` ASSUME_TAC THENL
   [ASM_CASES_TAC `v INTER outside s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`outside s:real^N->bool`; `v:real^N->bool`]
      MOI_S5B_CLOPEN_CONNECTED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `closure v INTER ((:real^N) DIFF s) SUBSET v` THEN
      UNDISCH_TAC `inside s UNION outside s = (:real^N) DIFF s` THEN
      SET_TAC[];
      ASM_MESON_TAC[BOUNDED_SUBSET]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [UNDISCH_TAC `v INTER outside s:real^N->bool = {}` THEN
    UNDISCH_TAC `v INTER s:real^N->bool = {}` THEN
    UNDISCH_TAC `inside s UNION outside s = (:real^N) DIFF s` THEN
    SET_TAC[];
    MATCH_MP_TAC MOI_S5B_CLOPEN_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `closure v INTER ((:real^N) DIFF s) SUBSET v` THEN
      UNDISCH_TAC `inside s UNION outside s = (:real^N) DIFF s` THEN
      SET_TAC[];
      UNDISCH_TAC `v INTER outside s:real^N->bool = {}` THEN
      UNDISCH_TAC `v INTER s:real^N->bool = {}` THEN
      UNDISCH_TAC `~(v:real^N->bool = {})` THEN
      UNDISCH_TAC `inside s UNION outside s = (:real^N) DIFF s` THEN
      SET_TAC[]]]);;

let MOI_S5B_PUNCTURED_SPHERE = prove
 (`!s w:real^3.
     s homeomorphic sphere(vec 0:real^3,&1) /\ w IN s
     ==> ?p p'. homeomorphism (s DELETE w,(:real^2)) (p,p')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `h:real^3->real^3`
    (X_CHOOSE_TAC `h':real^3->real^3`)) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`cball(vec 0:real^3,&1)`; `(:real^2)`; `(h:real^3->real^3) w`]
    HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFFINE_UNIV; AFF_DIM_UNIV;
              AFF_DIM_CBALL; RELATIVE_FRONTIER_CBALL; DIMINDEX_2; DIMINDEX_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
      REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `st:real^3->real^2`
    (X_CHOOSE_TAC `st':real^2->real^3`)) THEN
  MAP_EVERY EXISTS_TAC [`(st:real^3->real^2) o (h:real^3->real^3)`;
                        `(h':real^3->real^3) o (st':real^2->real^3)`] THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `sphere(vec 0:real^3,&1) DELETE (h:real^3->real^3) w` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `sphere(vec 0:real^3,&1)`] THEN
  ASM_REWRITE_TAC[DELETE_SUBSET] THEN
  MP_TAC(REWRITE_RULE[homeomorphism]
    (ASSUME `homeomorphism (s,sphere(vec 0:real^3,&1))
                           ((h:real^3->real^3),h')`)) THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IMAGE_DELETE_INJ o lhand o snd) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5B_SPHERE_DISK_OPEN = prove
 (`!s e (k:real^3->bool) (f:real^3->real^3) g w.
     s homeomorphic sphere(vec 0:real^3,&1) /\ &2 simplex k /\
     homeomorphism (k,e) (f,g) /\ e SUBSET s /\ w IN s /\ ~(w IN e)
     ==> open_in (subtopology euclidean s) (IMAGE f (relative_interior k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `w:real^3`] MOI_S5B_PUNCTURED_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^2` (X_CHOOSE_TAC `p':real^2->real^3`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] (ASSUME
    `homeomorphism (k:real^3->bool,e:real^3->bool)
                   ((f:real^3->real^3),(g:real^3->real^3))`)) THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (relative_interior k) SUBSET s DELETE w`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `s DELETE (w:real^3)` THEN
  SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^3->real^3) (relative_interior k) =
    IMAGE (p':real^2->real^3)
      (IMAGE ((p:real^3->real^2) o f) (relative_interior k))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!x:real^3. x IN relative_interior k
                    ==> (p':real^2->real^3) ((p:real^3->real^2)
                          ((f:real^3->real^3) x)) = f x`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[homeomorphism] o
        check (fun th -> concl th =
        `homeomorphism (s DELETE (w:real^3),(:real^2)) (p,p')`)) THEN
      UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_interior k) SUBSET
                   s DELETE w` THEN
      UNDISCH_TAC `(x:real^3) IN relative_interior k` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o; EXTENSION; IN_IMAGE; o_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->real^2`; `(:real^2)`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  MP_TAC(ISPECL [`(p:real^3->real^2) o (f:real^3->real^3)`;
                 `affine hull (k:real^3->bool)`; `(:real^2)`;
                 `relative_interior (k:real^3->bool)`]
    INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  REWRITE_TAC[AFFINE_AFFINE_HULL; AFFINE_UNIV; AFF_DIM_UNIV;
              AFF_DIM_AFFINE_HULL; SUBSET_UNIV; OPEN_IN_RELATIVE_INTERIOR;
              SUBTOPOLOGY_UNIV; GSYM OPEN_IN; DIMINDEX_2] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o
      check (fun th -> concl th =
      `homeomorphism (s DELETE (w:real^3),(:real^2)) (p,p')`)) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s DELETE (w:real^3)` THEN ASM_REWRITE_TAC[]];
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o
      check (fun th -> concl th =
      `homeomorphism (s DELETE (w:real^3),(:real^2)) (p,p')`)) THEN
    REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN k /\ (y:real^3) IN k` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `k:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^3) IN relative_interior k` THEN
      UNDISCH_TAC `(y:real^3) IN relative_interior k` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN s DELETE w /\ f y IN s DELETE w`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_interior k) SUBSET
                   s DELETE w` THEN
      UNDISCH_TAC `(x:real^3) IN relative_interior k` THEN
      UNDISCH_TAC `(y:real^3) IN relative_interior k` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^3) x = f y` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

let MOI_S5B_SIMPLEX_IMAGE_SPLIT = prove
 (`!n (k:real^M->bool) (f:real^M->real^N) g e.
     n simplex k /\ homeomorphism (k,e) (f,g)
     ==> IMAGE f (relative_interior k) UNION IMAGE f (relative_frontier k) = e /\
         IMAGE f (relative_interior k) INTER IMAGE f (relative_frontier k) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier k = k DIFF relative_interior (k:real^M->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] (ASSUME
    `homeomorphism (k:real^M->bool,e:real^N->bool)
                   ((f:real^M->real^N),(g:real^N->real^M))`)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `k:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `IMAGE (f:real^M->real^N) k = e` THEN
  UNDISCH_TAC `!x. x IN k ==> (g:real^N->real^M) ((f:real^M->real^N) x) = x` THEN
  SET_TAC[]);;

let MOI_S5B_SPHERE_DISK_CONN = prove
 (`!s e (k:real^3->bool) (f:real^3->real^3) g w.
     s homeomorphic sphere(vec 0:real^3,&1) /\ &2 simplex k /\
     homeomorphism (k,e) (f,g) /\ e SUBSET s /\ w IN s /\ ~(w IN e)
     ==> connected (s DIFF e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `e:real^3->bool`; `k:real^3->bool`;
                 `f:real^3->real^3`; `g:real^3->real^3`; `w:real^3`]
    MOI_S5B_SPHERE_DISK_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`&2:int`; `k:real^3->bool`; `f:real^3->real^3`;
                 `g:real^3->real^3`; `e:real^3->bool`]
    MOI_S5B_SIMPLEX_IMAGE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] (ASSUME
    `homeomorphism (k:real^3->bool,e:real^3->bool)
                   ((f:real^3->real^3),(g:real^3->real^3))`)) THEN
  SUBGOAL_THEN `compact(s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(e:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^3->real^3) k = e` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  ABBREV_TAC `w' = (f:real^3->real^3) (simplex_barycentre k)` THEN
  SUBGOAL_THEN `(w':real^3) IN IMAGE (f:real^3->real^3) (relative_interior k)` ASSUME_TAC THENL
   [EXPAND_TAC "w'" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `&2:int` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_PL2_SIMPLEX_2; CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w':real^3) IN s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `w':real^3`] MOI_S5B_PUNCTURED_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^2` (X_CHOOSE_TAC `p':real^2->real^3`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o
    check (fun th -> concl th =
      `homeomorphism (s DELETE (w':real^3),(:real^2)) (p,p')`)) THEN
  ABBREV_TAC `K = s DIFF IMAGE (f:real^3->real^3) (relative_interior k)` THEN
  SUBGOAL_THEN `compact(K:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN
    ASM_REWRITE_TAC[CLOSED_IN_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `K SUBSET s DELETE (w':real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    UNDISCH_TAC `(w':real^3) IN IMAGE (f:real^3->real^3) (relative_interior k)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `K = (s DIFF e) UNION IMAGE (f:real^3->real^3) (relative_frontier k)`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_interior k) UNION
                 IMAGE f (relative_frontier k) = e` THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_interior k) INTER
                 IMAGE f (relative_frontier k) = {}` THEN
    UNDISCH_TAC `e SUBSET (s:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `V = IMAGE (p:real^3->real^2) (s DIFF e)` THEN
  ABBREV_TAC `JJ = IMAGE (p:real^3->real^2)
                         (IMAGE (f:real^3->real^3) (relative_frontier k))` THEN
  SUBGOAL_THEN `compact(IMAGE (p:real^3->real^2) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p:real^3->real^2) K = V UNION JJ` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["V"; "JJ"] THEN ASM_REWRITE_TAC[IMAGE_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] SIMPLEX_IMP_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^3->real^3) (relative_frontier k) SUBSET s DELETE w'`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(w':real^3) IN IMAGE (f:real^3->real^3) (relative_interior k)` THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_interior k) UNION
                 IMAGE f (relative_frontier k) = e` THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_interior k) INTER
                 IMAGE f (relative_frontier k) = {}` THEN
    UNDISCH_TAC `e SUBSET (s:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `V INTER JJ:real^2->bool = {}` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["V"; "JJ"] THEN
    MATCH_MP_TAC(SET_RULE
     `!(p:real^3->real^2) q u a b.
        (!x. x IN u ==> q (p x) = x) /\ a SUBSET u /\ b SUBSET u /\
        a INTER b = {}
        ==> IMAGE p a INTER IMAGE p b = {}`) THEN
    MAP_EVERY EXISTS_TAC [`p':real^2->real^3`; `s DELETE (w':real^3)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(w':real^3) IN IMAGE (f:real^3->real^3) (relative_interior k)` THEN
      UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_interior k) UNION
                   IMAGE f (relative_frontier k) = e` THEN
      SET_TAC[];
      UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_interior k) UNION
                   IMAGE f (relative_frontier k) = e` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(JJ:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [TRANS_TAC HOMEOMORPHIC_TRANS `relative_frontier(k:real^3->bool)` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN EXPAND_TAC "JJ" THEN
      REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
      EXISTS_TAC `(p:real^3->real^2) o (f:real^3->real^3)` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
        MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] SIMPLEX_IMP_COMPACT) THEN
        ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `s DELETE (w':real^3)` THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(f:real^3->real^3) x IN s DELETE w' /\ f y IN s DELETE w'`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_frontier k) SUBSET
                     s DELETE w'` THEN
        UNDISCH_TAC `(x:real^3) IN relative_frontier k` THEN
        UNDISCH_TAC `(y:real^3) IN relative_frontier k` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN k /\ (y:real^3) IN k` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `relative_frontier k SUBSET (k:real^3->bool)` THEN
        UNDISCH_TAC `(x:real^3) IN relative_frontier k` THEN
        UNDISCH_TAC `(y:real^3) IN relative_frontier k` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:real^3->real^3) x = f y` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      MP_TAC(ISPECL [`k:real^3->bool`; `cball(vec 0:real^2,&1)`]
        HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
      REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; RELATIVE_FRONTIER_CBALL;
                  AFF_DIM_CBALL; DIMINDEX_2] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] SIMPLEX_IMP_COMPACT) THEN
      MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] SIMPLEX_IMP_CONVEX) THEN
      MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] AFF_DIM_SIMPLEX) THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `V = inside(JJ:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5B_BOUNDED_CLOPEN_INSIDE THEN
    ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[OPEN_IN] THEN
      ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
      MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`p':real^2->real^3`; `s DELETE (w':real^3)`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
      EXISTS_TAC `s:real^3->bool` THEN
      ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL; CLOSED_SUBSET;
                   COMPACT_IMP_CLOSED; DELETE_SUBSET] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `IMAGE (p:real^3->real^2) K` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN SET_TAC[];
      EXPAND_TAC "V" THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`V:real^2->bool`; `IMAGE (p:real^3->real^2) K`]
        CLOSURE_MINIMAL) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ANTS_TAC THENL
       [SET_TAC[]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s DIFF e = IMAGE (p':real^2->real^3) V` SUBST1_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `!h:real^3->real^3. (!x. x IN t ==> h x = x) ==> t = IMAGE h t`) THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `JJ:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_SIMP_TAC[DIMINDEX_2; LE_REFL] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* 5. Two PL disks glued along their common boundary form a PL 2-sphere     *)
(* (the sphere D_J UNION E_J of p.250).  The model is the boundary of the  *)
(* tetrahedron over the domain triangle of the first disk: the triangle     *)
(* plus the cone over its boundary, which is carried onto the triangle by  *)
(* a conewise map.                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_RAY_OFF_HULL = prove
 (`!s a x y:real^N.
     ~(a IN affine hull s) /\ x IN affine hull s /\ y IN affine hull s /\
     y IN segment[a,x]
     ==> y = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)))) THEN
  ASM_CASES_TAC `u = &1` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN affine hull s` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `a:real^N = inv(&1 - u) % y + (--u / (&1 - u)) % x`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `~(&1 - u = &0)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; real_div] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(a:real^N) = (&1 % a + (b:real) % x) + c % x <=> (b + c) % x = vec 0`] THEN
    SUBGOAL_THEN `inv(&1 - u) * u + --u * inv(&1 - u) = &0` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; REWRITE_TAC[VECTOR_MUL_LZERO]];
    MP_TAC(ISPEC `s:real^N->bool` AFFINE_AFFINE_HULL) THEN
    REWRITE_TAC[affine] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(&1 - u = &0)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&1 - u = &0)` THEN CONV_TAC REAL_FIELD]);;

let MOI_S5B_CONE_SEGMENT = prove
 (`!a b c:real^N.
     UNIONS {segment[a,x] | x IN segment[b,c]} = convex hull {a,b,c}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`{b,c}:real^N->bool`; `a:real^N`] CONVEX_HULL_INSERT_SEGMENTS) THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

let MOI_S5B_TETRA_RF = prove
 (`!a p1 p2 p3:real^N.
     ~collinear{p1,p2,p3} /\ ~(a IN affine hull {p1,p2,p3})
     ==> &3 simplex (convex hull {a,p1,p2,p3}) /\
         relative_frontier (convex hull {a,p1,p2,p3}) =
         convex hull {p1,p2,p3} UNION
         UNIONS {segment[a,x] | x IN relative_frontier(convex hull {p1,p2,p3})} /\
         convex hull {p1,p2,p3} INTER
         UNIONS {segment[a,x] | x IN relative_frontier(convex hull {p1,p2,p3})} =
         relative_frontier(convex hull {p1,p2,p3})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  SUBGOAL_THEN `~(a:real^N = p1) /\ ~(a = p2) /\ ~(a = p3)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~((a:real^N) IN affine hull {p1,p2,p3})` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {p1,p2,p3:real^N}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {a,p1,p2,p3:real^N}` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {segment[a,x] | x IN relative_frontier(convex hull {p1,p2,p3})} =
    convex hull {a,p1,p2} UNION convex hull {a,p2,p3} UNION
    convex hull {a,p3,p1:real^N}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    REWRITE_TAC[SET_RULE
     `UNIONS {(f:real^N->real^N->bool) x | x IN s UNION t UNION u} =
      UNIONS {f x | x IN s} UNION UNIONS {f x | x IN t} UNION
      UNIONS {f x | x IN u}`] THEN
    REWRITE_TAC[MOI_S5B_CONE_SEGMENT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplex] THEN EXISTS_TAC `{a,p1,p2,p3:real^N}` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    MP_TAC(ISPEC `{a,p1,p2,p3:real^N}` RELATIVE_FRONTIER_OF_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0;
                UNION_EMPTY] THEN
    SUBGOAL_THEN
     `{a,p1,p2,p3} DELETE (a:real^N) = {p1,p2,p3} /\
      {a,p1,p2,p3} DELETE p1 = {a,p2,p3} /\
      {a,p1,p2,p3} DELETE p2 = {a,p3,p1} /\
      {a,p1,p2,p3} DELETE p3 = {a,p1,p2}`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC [`~(a:real^N = p1)`; `~(a:real^N = p2)`;
        `~(a:real^N = p3)`; `~(p1:real^N = p2)`; `~(p2:real^N = p3)`;
        `~(p3:real^N = p1)`] THEN SET_TAC[];
      SET_TAC[]];
    SUBGOAL_THEN `relative_frontier(convex hull {p1,p2,p3}) SUBSET
                  convex hull {p1,p2,p3:real^N}` ASSUME_TAC THENL
       [SUBGOAL_THEN `closed(convex hull {p1,p2,p3:real^N})` ASSUME_TAC THENL
         [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
          MATCH_MP_TAC FINITE_IMP_COMPACT THEN
          REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
          ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN SET_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPEC `{p1,p2,p3:real^N}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `y:real^N` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
            (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
        UNDISCH_TAC `(y:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `y:real^N = x` (fun th -> ASM_REWRITE_TAC[th]) THEN
        MATCH_MP_TAC MOI_S5B_RAY_OFF_HULL THEN
        MAP_EVERY EXISTS_TAC [`{p1,p2,p3:real^N}`; `a:real^N`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `convex hull {p1,p2,p3} SUBSET affine hull {p1,p2,p3:real^N}` THEN
        UNDISCH_TAC `relative_frontier(convex hull {p1,p2,p3}) SUBSET
                     convex hull {p1,p2,p3:real^N}` THEN
        UNDISCH_TAC `(x:real^N) IN relative_frontier(convex hull {p1,p2,p3})` THEN
        UNDISCH_TAC `(y:real^N) IN convex hull {p1,p2,p3}` THEN SET_TAC[];
        REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        EXISTS_TAC `segment[a:real^N,x]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]]]);;

let MOI_S5B_DISK_UNION = prove
 (`!d1 d2 j:real^3->bool.
     pl_cell_with_boundary 2 d1 j /\ pl_cell_with_boundary 2 d2 j /\
     d1 INTER d2 = j
     ==> pl_sphere 2 (d1 UNION d2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `d2:real^3->bool`; `j:real^3->bool`]
    MOI_S5B_DISK_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `gg:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(REWRITE_RULE[pl_cell_with_boundary]
    (ASSUME `pl_cell_with_boundary 2 (d1:real^3->bool) j`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` (X_CHOOSE_THEN `f1:real^3->real^3`
    (X_CHOOSE_THEN `g1:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2] o
    check (fun th -> concl th = `&2 simplex (k1:real^3->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^3` (X_CHOOSE_THEN `p2:real^3`
    (X_CHOOSE_THEN `p3:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?a:real^3. ~(a IN affine hull {p1,p2,p3})` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s = (:real^3)) ==> ?a. ~(a IN s)`) THEN
    REWRITE_TAC[GSYM AFF_DIM_LT_FULL] THEN
    MP_TAC(ISPECL [`k1:real^3->bool`; `&2:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL; DIMINDEX_3] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k1 SUBSET affine hull {p1,p2,p3:real^3}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `p1:real^3`; `p2:real^3`; `p3:real^3`]
    MOI_S5B_TETRA_RF) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `k1 = convex hull {p1,p2,p3:real^3}` (SUBST_ALL_TAC o SYM) THEN
  ABBREV_TAC `C = UNIONS {segment[a:real^3,x] | x IN relative_frontier k1}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`k1:real^3->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier k1 SUBSET affine hull {p1,p2,p3:real^3}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `k1:real^3->bool` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[relative_frontier] THEN
      MP_TAC(ISPECL [`k1:real^3->bool`; `&2:int`] SIMPLEX_IMP_CLOSED) THEN
      ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k1:real^3->bool`;
                 `relative_frontier k1:real^3->bool`; `a:real^3`;
                 `simplex_barycentre (k1:real^3->bool)`;
                 `\x:real^3. x`; `\x:real^3. x`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `relative_frontier k1 SUBSET affine hull {p1,p2,p3:real^3}` THEN
      UNDISCH_TAC `~((a:real^3) IN affine hull {p1,p2,p3})` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_S5B_RAY_OFF_HULL THEN
      MAP_EVERY EXISTS_TAC [`{p1,p2,p3:real^3}`; `a:real^3`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `relative_frontier k1 SUBSET affine hull {p1,p2,p3:real^3}` THEN
      UNDISCH_TAC `(x:real^3) IN relative_frontier k1` THEN
      UNDISCH_TAC `(y:real^3) IN relative_frontier k1` THEN SET_TAC[];
      REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
      REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `cm = moi_con_conemap (relative_frontier k1) (a:real^3)
                     (simplex_barycentre k1) (\x:real^3. x)` THEN
  ABBREV_TAC `cm' = moi_con_conemap (relative_frontier k1)
                      (simplex_barycentre (k1:real^3->bool)) (a:real^3)
                      (\x:real^3. x)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (C:real^3->bool,d2)
                  ((g:real^3->real^3) o (f1:real^3->real^3) o (cm:real^3->real^3),
                   ((cm':real^3->real^3) o (g1:real^3->real^3)) o
                   (gg:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `d1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k1:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(C:real^3->bool) /\ compact(d1:real^3->bool) /\
                compact(d2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k1:real^3->bool`; `&2:int`] SIMPLEX_IMP_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `compact(C:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`k1:real^3->bool`; `C:real^3->bool`;
        `cm':real^3->real^3`; `cm:real^3->real^3`] MOI_PL2_PL_HOMEO_COMPACT) THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`k1:real^3->bool`; `d1:real^3->bool`;
        `f1:real^3->real^3`; `g1:real^3->real^3`] MOI_PL2_PL_HOMEO_COMPACT);
      MATCH_MP_TAC(ISPECL [`C:real^3->bool`; `d2:real^3->bool`;
        `(g:real^3->real^3) o (f1:real^3->real^3) o (cm:real^3->real^3)`;
        `((cm':real^3->real^3) o (g1:real^3->real^3)) o (gg:real^3->real^3)`]
        MOI_PL2_PL_HOMEO_COMPACT)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:real^3->bool`; `C:real^3->bool`; `d1:real^3->bool`;
                 `d2:real^3->bool`; `f1:real^3->real^3`; `g1:real^3->real^3`;
                 `(g:real^3->real^3) o (f1:real^3->real^3) o (cm:real^3->real^3)`;
                 `((cm':real^3->real^3) o (g1:real^3->real^3)) o
                  (gg:real^3->real^3)`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`k1:real^3->bool`; `&2:int`] SIMPLEX_IMP_CLOSED) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "x" &&
          rand(lhand(snd(dest_forall(concl th)))) = `j:real^3->bool`
      with Failure _ -> false)) THEN
    UNDISCH_TAC `j = IMAGE (f1:real^3->real^3) (relative_frontier k1)` THEN
    UNDISCH_TAC `(x:real^3) IN relative_frontier k1` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  EXISTS_TAC `convex hull {a,p1,p2,p3:real^3}` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. if x IN k1 then (f1:real^3->real^3) x
               else ((g:real^3->real^3) o f1 o (cm:real^3->real^3)) x`;
    `\y:real^3. if y IN d1 then (g1:real^3->real^3) y
               else (((cm':real^3->real^3) o g1) o (gg:real^3->real^3)) y`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. The model chart.  moi_s5b_u is the open box |x1|,|x2| < 1, |x3| < 1/8, *)
(* inside the domain and the slab and containing the tube S_e; phi is open  *)
(* on it (invariance of domain), xa is the part below the level c there,    *)
(* and the circles lie in the open flat annulus 3/16 < n < 5/16.            *)
(* ------------------------------------------------------------------------- *)

let moi_s5b_u = new_definition
 `moi_s5b_u = interval(--vector[&1;&1;&1 / &8]:real^3,vector[&1;&1;&1 / &8])`;;

let MOI_S5B_IN_U = prove
 (`!x:real^3. x IN moi_s5b_u <=>
              abs(x$1) < &1 /\ abs(x$2) < &1 /\ abs(x$3) < &1 / &8`,
  GEN_TAC THEN REWRITE_TAC[moi_s5b_u; IN_INTERVAL; DIMINDEX_3; FORALL_3;
    VECTOR_NEG_COMPONENT; VECTOR_3] THEN REAL_ARITH_TAC);;

let MOI_S5B_U_FACTS = prove
 (`open moi_s5b_u /\ moi_s5b_u SUBSET moi_s35_dom /\
   moi_s5b_u SUBSET moi_s35_slab /\ moi_s35_stube SUBSET moi_s5b_u /\
   moi_s35_ttube SUBSET moi_s35_stube`,
  CONJ_TAC THENL [REWRITE_TAC[moi_s5b_u; OPEN_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; MOI_S5B_IN_U; moi_s35_dom; moi_s35_slab;
    moi_s35_cube; moi_s35_stube; moi_s35_ttube; moi_s35_n; IN_ELIM_THM;
    IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S5B_PHI_OPEN = prove
 (`!phi:real^3->real^3 u.
     pl_map_on moi_s35_dom phi /\
     (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y) /\
     open u /\ u SUBSET moi_s5b_u
     ==> open(IMAGE phi u)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC MOI_S5B_U_FACTS THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
    ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S5B_XA_LEVEL = prove
 (`!phi:real^3->real^3 xa c.
     pl_map_on moi_s35_dom phi /\
     (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y) /\
     closed xa /\
     xa INTER IMAGE phi moi_s35_slab =
     IMAGE phi {x | x IN moi_s35_slab /\ x$3 <= c}
     ==> !x. x IN moi_s5b_u
             ==> (phi x IN xa <=> x$3 <= c) /\
                 (phi x IN interior xa <=> x$3 < c) /\
                 (phi x IN frontier xa <=> x$3 = c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5B_U_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_slab SUBSET moi_s35_dom` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_slab; moi_s35_dom; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[REAL_ARITH `abs(x:real) <= a ==> x <= a`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s5b_u ==> ((phi:real^3->real^3) x IN xa <=> x$3 <= c)`
  (LABEL_TAC "lev") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s35_slab` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(phi:real^3->real^3) x IN
                    IMAGE phi {x | x IN moi_s35_slab /\ x$3 <= c}` MP_TAC THENL
       [UNDISCH_TAC `xa INTER IMAGE (phi:real^3->real^3) moi_s35_slab =
                     IMAGE phi {x | x IN moi_s35_slab /\ x$3 <= c}` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `y:real^3 = x` (fun th -> ASM_MESON_TAC[th]) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          try fst(dest_var(fst(dest_forall(concl th)))) = "x"
          with Failure _ -> false)) THEN
        ASM SET_TAC[]];
      DISCH_TAC THEN
      UNDISCH_TAC `xa INTER IMAGE (phi:real^3->real^3) moi_s35_slab =
                   IMAGE phi {x | x IN moi_s35_slab /\ x$3 <= c}` THEN
      MATCH_MP_TAC(SET_RULE
       `(y:real^3) IN t ==> s INTER u = t ==> y IN s`) THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s5b_u /\ x$3 < c
                           ==> (phi:real^3->real^3) x IN interior xa`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[interior; IN_ELIM_THM] THEN
    EXISTS_TAC `IMAGE (phi:real^3->real^3)
                      (moi_s5b_u INTER {z:real^3 | z$3 < c})` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5B_PHI_OPEN THEN ASM_REWRITE_TAC[INTER_SUBSET] THEN
      MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s5b_u /\ c <= x$3
                           ==> ~((phi:real^3->real^3) x IN interior xa)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[interior; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(phi:real^3->real^3) continuous at x` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN EXISTS_TAC `moi_s5b_u` THEN
      ASM_SIMP_TAC[INTERIOR_OPEN] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
      ALL_TAC] THEN
    REWRITE_TAC[CONTINUOUS_AT_OPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `moi_s5b_u INTER v:real^3->bool` OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x + (r / &2) % basis 3:real^3) IN ball(x,r)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(x + (r / &2) % basis 3:real^3) IN moi_s5b_u /\
                  x + (r / &2) % basis 3 IN v` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^3->real^3) (x + (r / &2) % basis 3) IN xa`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "lev" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(x + (r / &2) % basis 3:real^3) IN moi_s5b_u`)]) THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; IN_DIFF] THEN
  ASM_MESON_TAC[REAL_LE_LT; REAL_NOT_LT; REAL_LE_REFL]);;

let MOI_S5B_B_SUB = prove
 (`!phi:real^3->real^3 b.
     (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y) /\
     b SUBSET IMAGE phi (interior moi_s35_stube)
     ==> {x | x IN moi_s35_dom /\ phi x IN b} SUBSET interior moi_s35_stube /\
         IMAGE phi {x | x IN moi_s35_dom /\ phi x IN b} = b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5B_U_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPEC `moi_s35_stube` INTERIOR_SUBSET) THEN DISCH_TAC THEN
  SUBGOAL_THEN `interior moi_s35_stube SUBSET moi_s35_dom` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?y:real^3. y IN interior moi_s35_stube /\ (phi:real^3->real^3) x = phi y`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `x:real^3 = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S5B_CIRCLES_FLAT = prove
 (`!phi:real^3->real^3 xa xb b c.
     pl_map_on moi_s35_dom phi /\
     (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y) /\
     abs c <= &1 / &512 /\ closed xa /\ closed xb /\
     xa INTER IMAGE phi moi_s35_slab =
     IMAGE phi {x | x IN moi_s35_slab /\ x$3 <= c} /\
     frontier xa INTER frontier xb SUBSET IMAGE phi (moi_s35_aflat c) /\
     b SUBSET frontier xb /\ b SUBSET IMAGE phi (interior moi_s35_stube) /\
     IMAGE phi (moi_s35_sq (&3 / &16) c) SUBSET interior xb /\
     DISJOINT (IMAGE phi (moi_s35_sq (&5 / &16) c)) xb
     ==> moi_s35_circles phi b c SUBSET
         {x | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5B_U_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `b:real^3->bool`] MOI_S5B_B_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `c:real`]
    MOI_S5B_XA_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_s35_aflat c SUBSET moi_s35_dom /\
                moi_s35_sq (&3 / &16) c SUBSET moi_s35_dom /\
                moi_s35_sq (&5 / &16) c SUBSET moi_s35_dom`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_aflat; moi_s35_sq; moi_s35_dom; moi_s35_cube;
      moi_s35_n; SUBSET; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3;
      VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; moi_s35_circles; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:real^3) IN moi_s5b_u` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_s35_stube` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real^3) x IN frontier xa` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN moi_s35_aflat c` MP_TAC THENL
   [SUBGOAL_THEN `(phi:real^3->real^3) x IN IMAGE phi (moi_s35_aflat c)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^3 = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "x" &&
          is_imp(snd(strip_forall(concl th))) &&
          is_eq(rand(snd(strip_forall(concl th))))
      with Failure _ -> false)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_aflat; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [DISCH_THEN(ASSUME_TAC o SYM) THEN
    SUBGOAL_THEN `(phi:real^3->real^3) x IN interior xb` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (phi:real^3->real^3) (moi_s35_sq (&3 / &16) c) SUBSET
                   interior xb` THEN
      MATCH_MP_TAC(SET_RULE
        `(y:real^3) IN s ==> IMAGE (f:real^3->real^3) s SUBSET t ==> f y IN t`) THEN
      ASM_REWRITE_TAC[moi_s35_sq; IN_ELIM_THM];
      ALL_TAC] THEN
    UNDISCH_TAC `b SUBSET frontier (xb:real^3->bool)` THEN
    UNDISCH_TAC `(phi:real^3->real^3) x IN b` THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    DISCH_TAC THEN
    UNDISCH_TAC `DISJOINT (IMAGE (phi:real^3->real^3) (moi_s35_sq (&5 / &16) c)) xb` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(?y:real^3. y IN s /\ (f:real^3->real^3) y IN t)
                           ==> ~DISJOINT (IMAGE f s) t`) THEN
    EXISTS_TAC `x:real^3` THEN
    ASM_REWRITE_TAC[moi_s35_sq; IN_ELIM_THM] THEN
    UNDISCH_TAC `b SUBSET frontier (xb:real^3->bool)` THEN
    UNDISCH_TAC `(phi:real^3->real^3) x IN b` THEN
    MP_TAC(ISPEC `xb:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. PL disks in the annulus b, read in the square annulus model A0 of     *)
(* pl_annulus_with_ends (the 2D facts of Lemma 2: the open disk is open in   *)
(* b, the disk misses the ends, its boundary is not interior to it in b,    *)
(* circles inside it bound disks in b, and a disk criterion).                *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_PL_SPHERE_HOMEO = prove
 (`!n s:real^N->bool.
     pl_sphere n s /\ n + 1 = dimindex(:N)
     ==> s homeomorphic sphere(vec 0:real^N,&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
     (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `relative_frontier k:real^N->bool` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `f:real^N->real^N`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `cball(vec 0:real^N,&1)`]
    HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; RELATIVE_FRONTIER_CBALL;
              AFF_DIM_CBALL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&(n + 1):int`] SIMPLEX_IMP_COMPACT) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&(n + 1):int`] SIMPLEX_IMP_CONVEX) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&(n + 1):int`] AFF_DIM_SIMPLEX) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]);;

let MOI_S5B_PLANE_FILL = prove
 (`!x j:real^2->bool.
     compact x /\ pl_sphere 1 j /\ frontier x = j /\ ~(interior x = {})
     ==> x = j UNION inside j /\ interior x = inside j /\ pl_ball 2 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `x:real^2->bool`] MOI_S5B_FILL_CHAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
    MATCH_MP_TAC MOI_S5B_PL_SPHERE_HOMEO THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC PL_SCHOENFLIES_2 THEN REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_A0_INTERIOR = prove
 (`interior(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
            interval(--vector[&1;&1]:real^2,vector[&1;&1])) =
   (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
    interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF
   (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) UNION
    relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`,
  SUBGOAL_THEN
   `!a:real^2 b. a = --b /\ b$1 > &0 /\ b$2 > &0
                 ==> ~(interior(interval[a,b]) = {})`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL;
      INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) =
    interval[--vector[&1;&1],vector[&1;&1]] DIFF
    interval(--vector[&1;&1],vector[&1;&1]) /\
    relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) =
    interval[--vector[&2;&2],vector[&2;&2]] DIFF
    interval(--vector[&2;&2],vector[&2;&2])`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN
    W(fun (_,w) -> MP_TAC(PART_MATCH (lhand o rand) RELATIVE_FRONTIER_NONEMPTY_INTERIOR
       (lhand w))) THEN
    (ANTS_TAC THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN
       REWRITE_TAC[VECTOR_2; GT] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[frontier; CLOSURE_INTERVAL; INTERIOR_CLOSED_INTERVAL]]) THEN
    REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
                VECTOR_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(interval(--vector[&1;&1]:real^2,vector[&1;&1])) =
                interval[--vector[&1;&1],vector[&1;&1]]` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^2` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
                VECTOR_2; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INTERIOR_DIFF; INTERIOR_CLOSED_INTERVAL] THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
              VECTOR_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNION; IN_UNIV;
              IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
              VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_S5B_CELL_TO_PLANE = prove
 (`!(a:real^N->bool) (e:real^N->bool) j f g.
     pl_homeomorphism
       (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
        interval(--vector[&1;&1]:real^2,vector[&1;&1]),a) (f,g) /\
     pl_cell_with_boundary 2 e j /\ e SUBSET a
     ==> pl_cell_with_boundary 2 (IMAGE g e) (IMAGE g j) /\
         IMAGE g e SUBSET interval[--vector[&2;&2],vector[&2;&2]] DIFF
                          interval(--vector[&1;&1],vector[&1;&1]) /\
         IMAGE f (IMAGE g e) = e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> try fst(dest_const(rator(rator(concl th)))) =
                         "pl_homeomorphism" with Failure _ -> false)) THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) (IMAGE g e) = e` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^N->real^2) e SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF
    interval(--vector[&1;&1],vector[&1;&1])`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (e:real^N->bool) j` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `F1:real^N->real^N`
    (X_CHOOSE_THEN `G1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S27_SIMPLEX_FROM_PLANE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (e,IMAGE (g:real^N->real^2) e) (g,(f:real^2->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC
     [`a:real^N->bool`;
      `interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])`] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `e = IMAGE (F1:real^N->real^N) k` SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  EXISTS_TAC `k0:real^2->bool` THEN
  EXISTS_TAC `(g:real^N->real^2) o (F1:real^N->real^N) o (h:real^2->real^N)` THEN
  EXISTS_TAC `((h':real^N->real^2) o (G1:real^N->real^N)) o (f:real^2->real^N)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]]);;

let MOI_S5B_PLANE_CELL_FACTS = prove
 (`!d j:real^2->bool.
     pl_cell_with_boundary 2 d j
     ==> compact d /\ frontier d = j /\ interior d = d DIFF j /\ j SUBSET d /\
         ~(d DIFF j = {}) /\ pl_sphere 1 j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `d:real^2->bool`; `f:real^2->real^2`;
                 `g:real^2->real^2`] MOI_PL2_FRONTIER_PL_BALL_2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact(d:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`k:real^2->bool`; `d:real^2->bool`;
      `f:real^2->real^2`; `g:real^2->real^2`] MOI_PL2_PL_HOMEO_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (k,d) ((f:real^2->real^2),(g:real^2->real^2))`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) THEN
  MP_TAC(ISPECL [`&2:int`; `k:real^2->bool`; `f:real^2->real^2`;
                 `g:real^2->real^2`; `d:real^2->bool`] MOI_S5B_SIMPLEX_IMAGE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `interior d = d DIFF IMAGE (f:real^2->real^2) (relative_frontier k)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `frontier d = IMAGE (f:real^2->real^2) (relative_frontier k)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `d:real^2->bool` INTERIOR_SUBSET) THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^2) (relative_interior k) UNION
                 IMAGE f (relative_frontier k) = d` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (f:real^2->real^2) (relative_interior k) UNION
                 IMAGE f (relative_frontier k) = d` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^2) (relative_interior k) INTER
                 IMAGE f (relative_frontier k) = {}` THEN
    MP_TAC(ISPECL [`&2:int`; `k:real^2->bool`]
      SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_PL2_SIMPLEX_2;
        CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      SET_TAC[]];
    REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
    MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `f:real^2->real^2`;
                          `g:real^2->real^2`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S27_PLH_SIMPLEX_RF THEN
    EXISTS_TAC `d:real^2->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S5B_A0_FACTS = prove
 (`relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
   interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
   interval(--vector[&1;&1]:real^2,vector[&1;&1]) /\
   relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
   interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
   interval(--vector[&1;&1]:real^2,vector[&1;&1]) /\
   ~((vec 0:real^2) IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                       interval(--vector[&1;&1],vector[&1;&1])) /\
   compact(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
           interval(--vector[&1;&1]:real^2,vector[&1;&1]))`,
  REWRITE_TAC[MOI_S27_ORIGIN_IN_HOLE] THEN
  SIMP_TAC[COMPACT_DIFF; COMPACT_INTERVAL; OPEN_INTERVAL] THEN
  SUBGOAL_THEN
   `!r. &0 < r
        ==> relative_frontier(interval[--vector[r;r]:real^2,vector[r;r]]) =
            interval[--vector[r;r],vector[r;r]] DIFF
            interval(--vector[r;r],vector[r;r])`
  (fun th -> SIMP_TAC[th; REAL_ARITH `&0 < &1 /\ &0 < &2`]) THENL
   [REPEAT STRIP_TAC THEN
    W(fun (_,w) -> MP_TAC(PART_MATCH (lhand o rand)
       RELATIVE_FRONTIER_NONEMPTY_INTERIOR (lhand w))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `vec 0:real^2` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
                  VECTOR_2; VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[frontier; CLOSURE_INTERVAL; INTERIOR_CLOSED_INTERVAL] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `interval[--vector[r;r]:real^2,vector[r;r]] = {}` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^2` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
                  VECTOR_2; VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_NEG_COMPONENT; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_S5B_IMAGE_DISJ = prove
 (`!(f:A->B) (g:B->A) u s t.
     (!x. x IN u ==> g(f x) = x) /\ s SUBSET u /\ t SUBSET u /\ s INTER t = {}
     ==> IMAGE f s INTER IMAGE f t = {}`,
  SET_TAC[]);;

let MOI_S5B_ANNULUS_CELL = prove
 (`!(a:real^3->bool) a0 a1 f g e j.
     pl_homeomorphism
       (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
        interval(--vector[&1;&1]:real^2,vector[&1;&1]),a) (f,g) /\
     a0 = IMAGE f (relative_frontier
                    (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
     a1 = IMAGE f (relative_frontier
                    (interval[--vector[&2;&2]:real^2,vector[&2;&2]])) /\
     pl_cell_with_boundary 2 e j /\ e SUBSET a /\ DISJOINT j (a0 UNION a1)
     ==> DISJOINT e (a0 UNION a1) /\
         open_in (subtopology euclidean a) (e DIFF j) /\
         (!u. open_in (subtopology euclidean a) u /\ j SUBSET u
              ==> ~(u SUBSET e)) /\
         (!j'. pl_sphere 1 j' /\ j' SUBSET e
               ==> ?d. pl_cell_with_boundary 2 d j' /\ d SUBSET a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_THEN `a0 = IMAGE (f:real^2->real^3) (relative_frontier
                    (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`
    SUBST_ALL_TAC THEN
  UNDISCH_THEN `a1 = IMAGE (f:real^2->real^3) (relative_frontier
                    (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`
    SUBST_ALL_TAC THEN
  ABBREV_TAC `A0 = interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                   interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
  MP_TAC MOI_S5B_A0_FACTS THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_S5B_A0_INTERIOR THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `dA = relative_frontier(interval[--vector[&1;&1]:real^2,
                                              vector[&1;&1]]) UNION
                   relative_frontier(interval[--vector[&2;&2]:real^2,
                                              vector[&2;&2]])` THEN
  SUBGOAL_THEN `dA SUBSET (A0:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "dA" THEN ASM_REWRITE_TAC[UNION_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> try fst(dest_const(rator(rator(concl th)))) =
                         "pl_homeomorphism" with Failure _ -> false)) THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) dA =
                IMAGE f (relative_frontier
                    (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
                IMAGE f (relative_frontier
                    (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`
  ASSUME_TAC THENL
   [EXPAND_TAC "dA" THEN REWRITE_TAC[IMAGE_UNION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `e:real^3->bool`; `j:real^3->bool`;
                 `f:real^2->real^3`; `g:real^3->real^2`] MOI_S5B_CELL_TO_PLANE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^2) e`; `IMAGE (g:real^3->real^2) j`]
    MOI_S5B_PLANE_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `E0 = IMAGE (g:real^3->real^2) e` THEN
  ABBREV_TAC `J0 = IMAGE (g:real^3->real^2) j` THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET e` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 2 (e:real^3->bool) j` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`&2:int`; `k:real^3->bool`; `f':real^3->real^3`;
                   `g':real^3->real^3`; `e:real^3->bool`]
      MOI_S5B_SIMPLEX_IMAGE_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism]; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) J0 = j` ASSUME_TAC THENL
   [EXPAND_TAC "J0" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `J0 INTER dA:real^2->bool = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (j:real^3->bool)
                 (IMAGE (f:real^2->real^3) (relative_frontier
                    (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
                  IMAGE f (relative_frontier
                    (interval[--vector[&2;&2]:real^2,vector[&2;&2]])))` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) dA =
                IMAGE f (relative_frontier
                    (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
                IMAGE f (relative_frontier
                    (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) J0 = j` THEN
    UNDISCH_TAC `dA SUBSET (A0:real^2->bool)` THEN
    UNDISCH_TAC `J0 SUBSET (E0:real^2->bool)` THEN
    UNDISCH_TAC `E0 SUBSET (A0:real^2->bool)` THEN
    UNDISCH_TAC `!x. x IN A0 ==> (g:real^3->real^2) ((f:real^2->real^3) x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `E0 INTER dA:real^2->bool = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`E0:real^2->bool`; `A0:real^2->bool`] SUBSET_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `J0 INTER dA:real^2->bool = {}` THEN
    UNDISCH_TAC `interior A0 = (A0:real^2->bool) DIFF dA` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) dA =
                IMAGE f (relative_frontier
                    (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
                IMAGE f (relative_frontier
                    (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) E0 = e` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S5B_IMAGE_DISJ THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^2`; `A0:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `e DIFF j = IMAGE (f:real^2->real^3) (interior E0)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^3) E0 = e` THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^3) J0 = j` THEN
      UNDISCH_TAC `J0 SUBSET (E0:real^2->bool)` THEN
      UNDISCH_TAC `E0 SUBSET (A0:real^2->bool)` THEN
      UNDISCH_TAC `!x. x IN A0 ==> (g:real^3->real^2) ((f:real^2->real^3) x) = x` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^2`; `A0:real^2->bool`] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[homeomorphism]; ALL_TAC] THEN
    SUBGOAL_THEN `interior E0 = A0 INTER interior (E0:real^2->bool)`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `E0:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `E0 SUBSET (A0:real^2->bool)` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR]];
    X_GEN_TAC `u:real^3->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `open_in (subtopology euclidean A0)
                          (IMAGE (g:real^3->real^2) u)` MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`f:real^2->real^3`; `a:real^3->bool`] THEN
      ASM_REWRITE_TAC[homeomorphism];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?y:real^2. y IN J0` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      ASM_MESON_TAC[MOI_SCD_PL_SPHERE_NONEMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^2) IN interior E0` MP_TAC THENL
     [REWRITE_TAC[interior; IN_ELIM_THM] THEN
      EXISTS_TAC `w INTER interior(A0:real^2->bool)` THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
      UNDISCH_TAC `(y:real^2) IN J0` THEN
      UNDISCH_TAC `J0 INTER dA:real^2->bool = {}` THEN
      UNDISCH_TAC `interior A0 = (A0:real^2->bool) DIFF dA` THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^2) u = A0 INTER w` THEN
      UNDISCH_TAC `J0 SUBSET (E0:real^2->bool)` THEN
      UNDISCH_TAC `E0 SUBSET (A0:real^2->bool)` THEN
      UNDISCH_TAC `(j:real^3->bool) SUBSET u` THEN
      UNDISCH_TAC `(u:real^3->bool) SUBSET e` THEN
      EXPAND_TAC "J0" THEN EXPAND_TAC "E0" THEN SET_TAC[];
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^2) IN J0` THEN SET_TAC[]];
    X_GEN_TAC `j':real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^3->bool`; `j':real^3->bool`; `f:real^2->real^3`;
                   `g:real^3->real^2`] MOI_S27_SPHERE_TO_PLANE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`E0:real^2->bool`; `J0:real^2->bool`] MOI_S5B_PLANE_FILL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (g:real^3->real^2) j' SUBSET E0` ASSUME_TAC THENL
     [EXPAND_TAC "E0" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `inside(IMAGE (g:real^3->real^2) j') SUBSET E0` ASSUME_TAC THENL
     [SUBGOAL_THEN `outside J0 SUBSET outside(IMAGE (g:real^3->real^2) j')`
      MP_TAC THENL
       [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
        MATCH_MP_TAC UNBOUNDED_DISJOINT_IN_OUTSIDE THEN
        EXISTS_TAC `outside J0:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `J0:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
          MATCH_MP_TAC MOI_S5B_PL_SPHERE_HOMEO THEN EXISTS_TAC `1` THEN
          ASM_REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC;
          STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
        MP_TAC(ISPEC `J0:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
        MP_TAC(ISPEC `J0:real^2->bool` INSIDE_NO_OVERLAP) THEN
        UNDISCH_TAC `E0:real^2->bool = J0 UNION inside J0` THEN
        UNDISCH_TAC `IMAGE (g:real^3->real^2) j' SUBSET E0` THEN
        MP_TAC(ISPEC `J0:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
        SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPEC `IMAGE (g:real^3->real^2) j'` INSIDE_OUTSIDE) THEN
      MP_TAC(ISPEC `J0:real^2->bool` INSIDE_OUTSIDE) THEN
      UNDISCH_TAC `E0:real^2->bool = J0 UNION inside J0` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE (g:real^3->real^2) j'` MOI_S27_PLANE_CELL) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    EXISTS_TAC `IMAGE (f:real^2->real^3)
                      (IMAGE (g:real^3->real^2) j' UNION
                       inside (IMAGE (g:real^3->real^2) j'))` THEN
    MATCH_MP_TAC MOI_S27_CELL_FROM_PLANE THEN EXISTS_TAC `g:real^3->real^2` THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM SET_TAC[]]);;

let MOI_S5B_ANNULUS_CRIT = prove
 (`!(a:real^3->bool) f g x jj.
     pl_homeomorphism
       (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
        interval(--vector[&1;&1]:real^2,vector[&1;&1]),a) (f,g) /\
     compact x /\ x SUBSET a /\
     DISJOINT x
       (IMAGE f (relative_frontier
                   (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
        IMAGE f (relative_frontier
                   (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) /\
     pl_sphere 1 jj /\ jj SUBSET x /\
     open_in (subtopology euclidean a) (x DIFF jj) /\
     jj SUBSET closure(a DIFF x) /\ ~(x DIFF jj = {})
     ==> pl_cell_with_boundary 2 x jj`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A0 = interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                   interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
  MP_TAC MOI_S5B_A0_FACTS THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_S5B_A0_INTERIOR THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `dA = relative_frontier(interval[--vector[&1;&1]:real^2,
                                              vector[&1;&1]]) UNION
                   relative_frontier(interval[--vector[&2;&2]:real^2,
                                              vector[&2;&2]])` THEN
  SUBGOAL_THEN `dA SUBSET (A0:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "dA" THEN ASM_REWRITE_TAC[UNION_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> try fst(dest_const(rator(rator(concl th)))) =
                         "pl_homeomorphism" with Failure _ -> false)) THEN
  SUBGOAL_THEN `homeomorphism (a,A0) ((g:real^3->real^2),(f:real^2->real^3))`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[homeomorphism]; ALL_TAC] THEN
  ABBREV_TAC `X0 = IMAGE (g:real^3->real^2) x` THEN
  ABBREV_TAC `J0 = IMAGE (g:real^3->real^2) jj` THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) X0 = x /\ IMAGE f J0 = jj /\
                X0 SUBSET A0 /\ J0 SUBSET X0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X0"; "J0"] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `X0 INTER dA:real^2->bool = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^3) X0 = x` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `DISJOINT (IMAGE (f:real^2->real^3) X0)
       (IMAGE f (relative_frontier
                   (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
        IMAGE f (relative_frontier
                   (interval[--vector[&2;&2]:real^2,vector[&2;&2]])))` THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dA SUBSET (A0:real^2->bool)` THEN
    UNDISCH_TAC `X0 SUBSET (A0:real^2->bool)` THEN
    UNDISCH_TAC `!x. x IN A0 ==> (g:real^3->real^2) ((f:real^2->real^3) x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(X0:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X0" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(X0 DIFF J0:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `open_in (subtopology euclidean A0) (X0 DIFF J0:real^2->bool)`
    MP_TAC THENL
     [SUBGOAL_THEN `X0 DIFF J0 = IMAGE (g:real^3->real^2) (x DIFF jj)`
      SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["X0"; "J0"] THEN
        UNDISCH_TAC `!x. x IN a ==> (f:real^2->real^3) ((g:real^3->real^2) x) = x` THEN
        UNDISCH_TAC `(x:real^3->bool) SUBSET a` THEN
        UNDISCH_TAC `(jj:real^3->bool) SUBSET x` THEN SET_TAC[];
        MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
        MAP_EVERY EXISTS_TAC [`f:real^2->real^3`; `a:real^3->bool`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `X0 DIFF J0 = w INTER interior(A0:real^2->bool)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `X0 DIFF J0 = (A0:real^2->bool) INTER w` THEN
      UNDISCH_TAC `X0 INTER dA:real^2->bool = {}` THEN
      UNDISCH_TAC `X0 SUBSET (A0:real^2->bool)` THEN SET_TAC[];
      ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR]];
    ALL_TAC] THEN
  SUBGOAL_THEN `J0 SUBSET closure((:real^2) DIFF X0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure(IMAGE (g:real^3->real^2) (a DIFF x))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "J0" THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^3->real^2) (closure(a DIFF x))` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[IMAGE_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
      REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `a:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC(ISPECL [`A0:real^2->bool`; `a:real^3->bool`;
        `f:real^2->real^3`; `g:real^3->real^2`] MOI_PL2_PL_HOMEO_COMPACT) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_CLOSURE THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^2) x = X0` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(x:real^3->bool) SUBSET a` THEN
      UNDISCH_TAC `!x. x IN a ==> (f:real^2->real^3) ((g:real^3->real^2) x) = x` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior X0 = X0 DIFF J0:real^2->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `X0:real^2->bool` INTERIOR_SUBSET) THEN
      SUBGOAL_THEN `interior X0 INTER closure((:real^2) DIFF X0) = {}`
      MP_TAC THENL
       [REWRITE_TAC[CLOSURE_COMPLEMENT] THEN SET_TAC[];
        UNDISCH_TAC `J0 SUBSET closure((:real^2) DIFF X0)` THEN SET_TAC[]];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `jj:real^3->bool`; `f:real^2->real^3`;
                 `g:real^3->real^2`] MOI_S27_SPHERE_TO_PLANE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3->bool) SUBSET a` THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET x` THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`X0:real^2->bool`; `J0:real^2->bool`] MOI_S5B_PLANE_FILL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `J0 SUBSET (X0:real^2->bool)` THEN SET_TAC[];
      UNDISCH_TAC `~(x DIFF jj:real^3->bool = {})` THEN
      UNDISCH_TAC `(x:real^3->bool) SUBSET a` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET x` THEN
      UNDISCH_TAC `!x. x IN a ==> (f:real^2->real^3) ((g:real^3->real^2) x) = x` THEN
      MAP_EVERY EXPAND_TAC ["X0"; "J0"] THEN SET_TAC[]];
    DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2)] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^3) X0 = x` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `jj:real^3->bool`; `f:real^2->real^3`;
                 `g:real^3->real^2`; `X0:real^2->bool`] MOI_S27_CELL_FROM_PLANE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `J0 SUBSET (X0:real^2->bool)` THEN SET_TAC[];
      UNDISCH_TAC `(x:real^3->bool) SUBSET a` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET x` THEN SET_TAC[]];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 8. Circles at the level c as planar Jordan curves: the projection to the *)
(* plane, inessential circles bound planar disks in the open flat annulus,  *)
(* nesting of Jordan curves, and the choice of an innermost inessential     *)
(* circle (no other circle over its planar disk, as D_J of p.250).          *)
(* ------------------------------------------------------------------------- *)

let moi_s5b_proj = new_definition
 `moi_s5b_proj (x:real^3) = vector[x$1; x$2]:real^2`;;

let MOI_S5B_PROJ_LIFT = prove
 (`(!c y. moi_s5b_proj (moi_s35_lift c y) = y) /\
   (!c x. x$3 = c ==> moi_s35_lift c (moi_s5b_proj x) = x) /\
   (!c y. (moi_s35_lift c y)$3 = c) /\
   (!c y. moi_s35_n (moi_s35_lift c y) = max (abs(y$1)) (abs(y$2)))`,
  REWRITE_TAC[moi_s5b_proj; moi_s35_lift; moi_s35_n; CART_EQ; DIMINDEX_2;
              DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2; VECTOR_3] THEN
  MESON_TAC[]);;

let MOI_S5B_LIFT_INJ = prove
 (`!c y z. moi_s35_lift c y = moi_s35_lift c z <=> y = z`,
  MESON_TAC[MOI_S5B_PROJ_LIFT]);;

let MOI_S5B_COBOUNDED_COMPL = prove
 (`!s:real^N->bool. bounded s ==> ~bounded((:real^N) DIFF s)`,
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(INST_TYPE [`:N`,`:N`] NOT_BOUNDED_UNIV) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(:real^N) = s UNION ((:real^N) DIFF s)` SUBST1_TAC THENL
   [SET_TAC[]; ASM_REWRITE_TAC[BOUNDED_UNION]]);;

let MOI_S5B_IN_BOX = prove
 (`(!r y:real^2. y IN interval[--vector[r;r],vector[r;r]] <=>
                 max (abs(y$1)) (abs(y$2)) <= r) /\
   (!r y:real^2. y IN interval(--vector[r;r],vector[r;r]) <=>
                 max (abs(y$1)) (abs(y$2)) < r)`,
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
              VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S5B_INESS_PLANAR = prove
 (`!j:real^2->bool.
     pl_sphere 1 j /\
     j SUBSET {y | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
                   max (abs(y$1)) (abs(y$2)) < &5 / &16} /\
     ~(!y. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN inside j)
     ==> (!y. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN outside j) /\
         (!y. &5 / &16 <= max (abs(y$1)) (abs(y$2)) ==> y IN outside j) /\
         j UNION inside j SUBSET
         {y | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
              max (abs(y$1)) (abs(y$2)) < &5 / &16}`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5B_PL_SPHERE_HOMEO THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `j:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^2. y IN j ==> &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
                                      max (abs(y$1)) (abs(y$2)) < &5 / &16`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN outside j`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`j:real^2->bool`;
      `interval[--vector[&3 / &16; &3 / &16]:real^2,
                vector[&3 / &16; &3 / &16]]`] MOI_S5B_CONNECTED_SIDE) THEN
    REWRITE_TAC[CONNECTED_INTERVAL; SUBSET; MOI_S5B_IN_BOX] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                  MOI_S5B_IN_BOX] THEN
      ASM_MESON_TAC[REAL_NOT_LE];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. &5 / &16 <= max (abs(y$1)) (abs(y$2)) ==> y IN outside j`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC UNBOUNDED_DISJOINT_IN_OUTSIDE THEN
    EXISTS_TAC `(:real^2) DIFF
                interval(--vector[&5 / &16; &5 / &16],vector[&5 / &16; &5 / &16])` THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; MOI_S5B_IN_BOX] THEN
    ASM_REWRITE_TAC[REAL_NOT_LT] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
      REWRITE_TAC[DIMINDEX_2; LE_REFL; BOUNDED_INTERVAL; CONVEX_INTERVAL];
      MATCH_MP_TAC MOI_S5B_COBOUNDED_COMPL THEN REWRITE_TAC[BOUNDED_INTERVAL];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF;
                  IN_UNIV; MOI_S5B_IN_BOX] THEN
      ASM_MESON_TAC[REAL_NOT_LT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[];
    MP_TAC(ISPEC `j:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_NOT_LE]]);;

let MOI_S5B_NESTED_INSIDE = prove
 (`!j1 j2:real^2->bool.
     j1 homeomorphic sphere(vec 0:real^2,&1) /\
     j2 homeomorphic sphere(vec 0:real^2,&1) /\ j1 SUBSET inside j2
     ==> inside j1 SUBSET inside j2 /\ outside j2 SUBSET outside j1 /\
         j2 SUBSET outside j1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `j1:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `j2:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected(j1:real^2->bool) /\ connected(j2:real^2->bool) /\
                ~(j1 = {}) /\ ~(j2 = {})` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `connected(sphere(vec 0:real^2,&1)) /\
                  ~(sphere(vec 0:real^2,&1) = {})` STRIP_ASSUME_TAC THENL
     [SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL; SPHERE_EQ_EMPTY] THEN
      REAL_ARITH_TAC;
      ASM_MESON_TAC[HOMEOMORPHIC_CONNECTEDNESS; HOMEOMORPHIC_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `outside j2 SUBSET outside(j1:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC UNBOUNDED_DISJOINT_IN_OUTSIDE THEN
    EXISTS_TAC `outside j2:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j1 SUBSET inside(j2:real^2->bool)` THEN
    UNDISCH_TAC `inside j2 INTER outside j2:real^2->bool = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j2 SUBSET outside(j1:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`j1:real^2->bool`; `j2:real^2->bool`]
      MOI_S5B_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `j2:real^2->bool` INSIDE_NO_OVERLAP) THEN
      UNDISCH_TAC `j1 SUBSET inside(j2:real^2->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `outside j1 SUBSET outside(j2:real^2->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      MATCH_MP_TAC UNBOUNDED_DISJOINT_IN_OUTSIDE THEN
      EXISTS_TAC `outside j1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `j2 SUBSET inside(j1:real^2->bool)` THEN
      UNDISCH_TAC `inside j1 INTER outside j1:real^2->bool = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `j1:real^2->bool = j2` ASSUME_TAC THENL
     [UNDISCH_TAC `frontier(outside j1):real^2->bool = j1` THEN
      UNDISCH_TAC `frontier(outside j2):real^2->bool = j2` THEN
      SUBGOAL_THEN `outside j1:real^2->bool = outside j2` SUBST1_TAC THENL
       [ASM SET_TAC[]; MESON_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `j1 SUBSET inside(j2:real^2->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `j2:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `~(j2:real^2->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`j2:real^2->bool`; `inside j1:real^2->bool`]
    MOI_S5B_CONNECTED_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j2 SUBSET outside(j1:real^2->bool)` THEN
    UNDISCH_TAC `inside j1 INTER outside j1:real^2->bool = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `outside j2 SUBSET outside(j1:real^2->bool)` THEN
  UNDISCH_TAC `inside j1 SUBSET outside(j2:real^2->bool)` THEN
  UNDISCH_TAC `inside j1 INTER outside j1:real^2->bool = {}` THEN
  UNDISCH_TAC `~(inside j1:real^2->bool = {})` THEN SET_TAC[]);;

let MOI_S5B_PROJ_IMAGE_LIFT = prove
 (`!c j. IMAGE moi_s5b_proj (IMAGE (moi_s35_lift c) j) = j`,
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_S5B_PROJ_LIFT; IMAGE_ID]);;

let MOI_S5B_ESS_LIFT = prove
 (`!c k j. k = IMAGE (moi_s35_lift c) j
           ==> (moi_s35_ess c k <=>
                pl_sphere 1 j /\
                !y. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN inside j)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[moi_s35_ess; MOI_S5B_PROJ_LIFT] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `j':real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `j:real^2->bool = j'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `IMAGE moi_s5b_proj`) THEN
    REWRITE_TAC[MOI_S5B_PROJ_IMAGE_LIFT];
    STRIP_TAC THEN EXISTS_TAC `j:real^2->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S5B_INNERMOST = prove
 (`!C0 c (k0:real^3->bool).
     FINITE (components C0) /\
     (!k. k IN components C0
          ==> ?j:real^2->bool. pl_sphere 1 j /\ k = IMAGE (moi_s35_lift c) j) /\
     C0 SUBSET {x | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c} /\
     k0 IN components C0 /\ ~moi_s35_ess c k0
     ==> ?k j. k IN components C0 /\ ~moi_s35_ess c k /\ pl_sphere 1 j /\
               k = IMAGE (moi_s35_lift c) j /\
               (!x. x IN C0 ==> ~(moi_s5b_proj x IN inside j)) /\
               (!y. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN outside j) /\
               (!y. &5 / &16 <= max (abs(y$1)) (abs(y$2)) ==> y IN outside j) /\
               j UNION inside j SUBSET
               {y | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
                    max (abs(y$1)) (abs(y$2)) < &5 / &16}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k j. k IN components C0 /\ k = IMAGE (moi_s35_lift c) j
          ==> j SUBSET {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
                                   max (abs(y$1)) (abs(y$2)) < &5 / &16}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s35_lift c (y:real^2) IN C0` MP_TAC THENL
     [MP_TAC(ISPEC `C0:real^3->bool` IN_COMPONENTS_SUBSET) THEN
      DISCH_THEN(MP_TAC o SPEC `k:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `C0 SUBSET {x | &3 / &16 < moi_s35_n x /\
                                moi_s35_n x < &5 / &16 /\ x$3 = c}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC[MOI_S5B_PROJ_LIFT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `mu = \k:real^3->bool.
     CARD {k' | k' IN components C0 /\
                IMAGE moi_s5b_proj k' SUBSET inside (IMAGE moi_s5b_proj k)}` THEN
  MP_TAC(ISPEC `\n. ?k. k IN components C0 /\ ~moi_s35_ess c k /\
                       (mu:(real^3->bool)->num) k = n` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXISTS_TAC `(mu:(real^3->bool)->num) k0` THEN
    EXISTS_TAC `k0:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:real^3->bool` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "k" &&
        is_exists(rand(snd(dest_forall(concl th))))
    with Failure _ -> false)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^2->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `j:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16
                             ==> y IN inside j)` ASSUME_TAC THENL
   [UNDISCH_TAC `~moi_s35_ess c (k:real^3->bool)` THEN
    MP_TAC(ISPECL [`c:real`; `k:real^3->bool`; `j:real^2->bool`]
      MOI_S5B_ESS_LIFT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `j:real^2->bool` MOI_S5B_INESS_PLANAR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `k1 = connected_component C0 (x:real^3)` THEN
  SUBGOAL_THEN `(k1:real^3->bool) IN components C0` ASSUME_TAC THENL
   [EXPAND_TAC "k1" THEN REWRITE_TAC[IN_COMPONENTS] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k1:real^3->bool` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "k" &&
        is_exists(rand(snd(dest_forall(concl th))))
    with Failure _ -> false)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^3) IN k1` ASSUME_TAC THENL
   [EXPAND_TAC "k1" THEN REWRITE_TAC[IN] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5b_proj x IN (j1:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN k1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MOI_S5B_PROJ_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k1:real^3->bool = k)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `j1:real^2->bool = j` SUBST_ALL_TAC THENL
     [MP_TAC(AP_TERM `IMAGE moi_s5b_proj`
        (ASSUME `k:real^3->bool = IMAGE (moi_s35_lift c) j1`)) THEN
      MP_TAC(AP_TERM `IMAGE moi_s5b_proj`
        (ASSUME `k:real^3->bool = IMAGE (moi_s35_lift c) j`)) THEN
      REWRITE_TAC[MOI_S5B_PROJ_IMAGE_LIFT] THEN MESON_TAC[];
      MP_TAC(ISPEC `j:real^2->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (j:real^2->bool) j1` ASSUME_TAC THENL
   [SUBGOAL_THEN `DISJOINT (k:real^3->bool) k1` MP_TAC THENL
     [ASM_MESON_TAC[COMPONENTS_NONOVERLAP; DISJOINT];
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^2->bool) SUBSET inside j` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`j:real^2->bool`; `j1:real^2->bool`] MOI_S5B_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `connected(k1:real^3->bool)` MP_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o ISPEC `moi_s5b_proj` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] CONNECTED_LINEAR_IMAGE)) THEN
      REWRITE_TAC[MOI_S5B_PROJ_IMAGE_LIFT] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[linear; moi_s5b_proj; CART_EQ; DIMINDEX_2; FORALL_2;
                  VECTOR_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
      MP_TAC(ISPEC `j:real^2->bool` INSIDE_INTER_OUTSIDE) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^2->bool) homeomorphic sphere(vec 0:real^2,&1) /\
                (j1:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5B_PL_SPHERE_HOMEO THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j1:real^2->bool`; `j:real^2->bool`] MOI_S5B_NESTED_INSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~moi_s35_ess c (k1:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real`; `k1:real^3->bool`; `j1:real^2->bool`]
      MOI_S5B_ESS_LIFT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
    REWRITE_TAC[VEC_COMPONENT; REAL_ABS_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN `(vec 0:real^2) IN outside j` MP_TAC THENL
     [MATCH_MP_TAC(ASSUME `!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16
                                     ==> y IN outside j`) THEN
      REWRITE_TAC[VEC_COMPONENT; REAL_ABS_NUM] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC(ISPEC `j1:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
      UNDISCH_TAC `outside j SUBSET outside(j1:real^2->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `!m. m < n ==> ~(?k. k IN components C0 /\ ~moi_s35_ess c k /\
                                  (mu:(real^3->bool)->num) k = m)` THEN
  DISCH_THEN(MP_TAC o SPEC `(mu:(real^3->bool)->num) k1`) THEN
  MATCH_MP_TAC(TAUT `p /\ q ==> (p ==> ~q) ==> r`) THEN CONJ_TAC THENL
   [ALL_TAC; EXISTS_TAC `k1:real^3->bool` THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `(mu:(real^3->bool)->num) k = n` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "mu" THEN
  ASM_REWRITE_TAC[MOI_S5B_PROJ_IMAGE_LIFT] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `k2:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `inside j1 SUBSET inside(j:real^2->bool)` THEN
      UNDISCH_TAC `IMAGE moi_s5b_proj (k2:real^3->bool) SUBSET inside j1` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `k1:real^3->bool`) THEN
    ASM_REWRITE_TAC[MOI_S5B_PROJ_IMAGE_LIFT] THEN
    MP_TAC(ISPEC `j1:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `moi_s5b_proj x IN (j1:real^2->bool)` THEN SET_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `components(C0:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. The collar of the level c in the triangulated surface B (from the slab *)
(* lemma MOI_S35_SLAB_PRODUCT on [c - d0, c + d0]): a height-preserving      *)
(* product Q x t, x on the circles, t in [-1,1], height c + t d0.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_NO_3DIM = prove
 (`!K (G:real^3->real^2) B.
     simplicial_complex K /\ UNIONS K = B /\ G continuous_on B /\
     (!x y. x IN B /\ y IN B /\ G x = G y ==> x = y)
     ==> !s. s IN K ==> aff_dim s <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real^3->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `convex(s:real^3->bool) /\ s SUBSET B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_LE_UNIV) THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  ASM_CASES_TAC `aff_dim(s:real^3->bool) = &3` THENL
   [ALL_TAC; ASM_INT_ARITH_TAC] THEN
  MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_TAC THEN
  SUBGOAL_THEN `dimindex(:3) <= dimindex(:2)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[DIMINDEX_2; DIMINDEX_3] THEN ARITH_TAC] THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION THEN
  MAP_EVERY EXISTS_TAC [`G:real^3->real^2`; `interior s:real^3->bool`] THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let moi_s5b_collar = new_definition
 `moi_s5b_collar (B:real^3->bool) c d0 (Q:real^3->real->real^3) <=>
    &0 < d0 /\
    (!x t. x IN B /\ x$3 = c /\ abs t <= &1
           ==> Q x t IN B /\ (Q x t)$3 = c + t * d0) /\
    (!x. x IN B /\ x$3 = c ==> Q x (&0) = x) /\
    (!x t x' t'. x IN B /\ x$3 = c /\ abs t <= &1 /\
                 x' IN B /\ x'$3 = c /\ abs t' <= &1 /\ Q x t = Q x' t'
                 ==> x = x' /\ t = t') /\
    (!z. z IN B /\ abs(z$3 - c) <= d0
         ==> ?x t. x IN B /\ x$3 = c /\ abs t <= &1 /\ z = Q x t) /\
    (\p. Q (fstcart p) (drop(sndcart p))) continuous_on
    ({x | x IN B /\ x$3 = c} PCROSS interval[--vec 1,vec 1]) /\
    (!t. abs t <= &1 ==> pl_map_on {x | x IN B /\ x$3 = c} (\x. Q x t))`;;

let MOI_S5B_LEVEL_POLYHEDRON = prove
 (`!B c. pl_polyhedron B ==> pl_polyhedron {x:real^3 | x IN B /\ x$3 = c}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PL_POLYHEDRON_IMP_COMPACT) THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_TAC `b:real^3`) o
    MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  SUBGOAL_THEN `{x:real^3 | x IN B /\ x$3 = c} =
                B INTER (interval[a,b] INTER {x | basis 3 dot x = c})`
  SUBST1_TAC THENL
   [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `B SUBSET interval[a:real^3,b]` THEN SET_TAC[];
    MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
    MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; POLYHEDRON_HYPERPLANE]]);;

let MOI_S5B_PL_LINEAR = prove
 (`!s (l:real^M->real^N). locally_polyhedral s /\ linear l ==> pl_map_on s l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^M. (l:real^M->real^N) x + vec 0` THEN
  ASM_SIMP_TAC[PL_MAP_ON_AFFINE; VECTOR_ADD_RID]);;

let MOI_S5B_LIFT_AFFINE = prove
 (`!v:real^1. lift((drop v + &1) / &2) = inv(&2) % v + lift(inv(&2))`,
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

let MOI_S5B_COLLAR_EXISTS = prove
 (`(!(k:(real^3->bool)->bool) c d.
     FINITE k /\ simplicial_complex k /\ (!s. s IN k ==> aff_dim s <= &2) /\
     c < d /\ (!v. {v} IN k ==> v$3 < c \/ d < v$3)
     ==> ?(f:real^(3,1)finite_sum->real^3) g.
           homeomorphism
             ({x | x IN UNIONS k /\ x$3 = c} PCROSS interval[vec 0:real^1,vec 1],
              {x | x IN UNIONS k /\ c <= x$3 /\ x$3 <= d}) (f,g) /\
           pl_map_on ({x | x IN UNIONS k /\ x$3 = c} PCROSS
                      interval[vec 0:real^1,vec 1]) f /\
           (!x s. x IN UNIONS k /\ x$3 = c /\ s IN interval[vec 0:real^1,vec 1]
                  ==> (f(pastecart x s))$3 = c + drop s * (d - c)) /\
           (!x. x IN UNIONS k /\ x$3 = c ==> f(pastecart x (vec 0)) = x))
   ==> !K B c d0.
         FINITE K /\ simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &2) /\
         UNIONS K = B /\ &0 < d0 /\ (!v. {v} IN K ==> d0 < abs(v$3 - c))
         ==> ?Q. moi_s5b_collar B c d0 Q`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`K:(real^3->bool)->bool`; `c - d0:real`;
                                `c + d0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(c + d0) - (c - d0) = &2 * d0`] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(3,1)finite_sum->real^3`
   (X_CHOOSE_THEN `g:real^3->real^(3,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
    try fst(dest_const(rator(rator(concl th)))) = "homeomorphism"
    with Failure _ -> false)) THEN
  SUBGOAL_THEN `!x:real^3. x IN B /\ x$3 = c
                ==> fstcart((g:real^3->real^(3,1)finite_sum) x) IN
                      {x | x IN B /\ x$3 = c - d0} /\
                    g x = pastecart (fstcart(g x)) (lift(&1 / &2))`
  (LABEL_TAC "gx") THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0}` ASSUME_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum) x IN
                  {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_INJ] THEN
    SUBGOAL_THEN `((f:real^(3,1)finite_sum->real^3)
                    (pastecart (fstcart ((g:real^3->real^(3,1)finite_sum) x))
                               (sndcart (g x))))$3 =
                  (c - d0) + drop(sndcart(g x)) * (&2 * d0)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `fstcart
        ((g:real^3->real^(3,1)finite_sum) x) IN {x | x IN B /\ x$3 = c - d0}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[PASTECART_FST_SND] THEN
    SUBGOAL_THEN `(f:real^(3,1)finite_sum->real^3) (g x) = x` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
    UNDISCH_TAC `&0 < d0` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  EXISTS_TAC `\x t. (f:real^(3,1)finite_sum->real^3)
                      (pastecart (fstcart((g:real^3->real^(3,1)finite_sum) x))
                                 (lift((t + &1) / &2)))` THEN
  REWRITE_TAC[moi_s5b_collar] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x t. x IN B /\ x$3 = c /\ abs t <= &1
                ==> pastecart (fstcart((g:real^3->real^(3,1)finite_sum) x))
                              (lift((t + &1) / &2)) IN
                    {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]`
  (LABEL_TAC "pin") THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    UNDISCH_TAC `abs t <= &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^(3,1)finite_sum.
                  z IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS
                       interval[vec 0:real^1,vec 1]
                  ==> (f:real^(3,1)finite_sum->real^3) z IN B`
  (LABEL_TAC "fB") THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^(3,1)finite_sum->real^3) z IN
                  {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0}`
    MP_TAC THENL [ASM SET_TAC[]; SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "gx" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM]] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`fstcart((g:real^3->real^(3,1)finite_sum) x)`;
                  `lift((t + &1) / &2)`]
      (ASSUME `!x s. x IN B /\ x$3 = c - d0 /\ s IN interval[vec 0:real^1,vec 1]
                     ==> ((f:real^(3,1)finite_sum->real^3) (pastecart x s))$3 =
                         c - d0 + drop s * &2 * d0`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      UNDISCH_TAC `abs t <= &1` THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP] THEN CONV_TAC REAL_RING];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_ARITH `&1 / &2 = &1 / &2`] THEN
    USE_THEN "gx" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "y"
      with Failure _ -> false)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "gx" (fun th -> MP_TAC(SPEC `x:real^3` th) THEN
                             MP_TAC(SPEC `x':real^3` th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "pin" (fun th -> MP_TAC(SPECL [`x:real^3`; `t:real`] th) THEN
                              MP_TAC(SPECL [`x':real^3`; `t':real`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `pastecart (fstcart((g:real^3->real^(3,1)finite_sum) x))
                (lift((t + &1) / &2)) =
      pastecart (fstcart(g x')) (lift((t' + &1) / &2))`
    MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `g:real^3->real^(3,1)finite_sum` o
        check (fun th -> try is_eq(concl th) &&
               fst(dest_var(rator(lhs(concl th)))) = "f" with Failure _ -> false)) THEN
      REWRITE_TAC[MATCH_MP (ASSUME `!z. z IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1] ==> (g:real^3->real^(3,1)finite_sum) ((f:real^(3,1)finite_sum->real^3) z) = z`) (ASSUME
        `pastecart (fstcart((g:real^3->real^(3,1)finite_sum) x))
                   (lift((t + &1) / &2)) IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]`);
                  MATCH_MP (ASSUME `!z. z IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1] ==> (g:real^3->real^(3,1)finite_sum) ((f:real^(3,1)finite_sum->real^3) z) = z`) (ASSUME
        `pastecart (fstcart((g:real^3->real^(3,1)finite_sum) x'))
                   (lift((t' + &1) / &2)) IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]`)];
      ALL_TAC] THEN
    REWRITE_TAC[PASTECART_INJ; LIFT_EQ] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `(t + &1) / &2 = (t' + &1) / &2` THEN
                    REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0} /\ (x':real^3) IN {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0}` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum) x = g x'` MP_TAC THENL
     [ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `f:real^(3,1)finite_sum->real^3`) THEN
    REWRITE_TAC[MATCH_MP (ASSUME `!y. y IN {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0} ==> (f:real^(3,1)finite_sum->real^3) ((g:real^3->real^(3,1)finite_sum) y) = y`) (ASSUME `(x:real^3) IN {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0}`);
                MATCH_MP (ASSUME `!y. y IN {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0} ==> (f:real^(3,1)finite_sum->real^3) ((g:real^3->real^(3,1)finite_sum) y) = y`) (ASSUME `(x':real^3) IN {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0}`)];
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0}` ASSUME_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs((z:real^3)$3 - c) <= d0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^3->real^(3,1)finite_sum) z IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN
    ABBREV_TAC `y = fstcart((g:real^3->real^(3,1)finite_sum) z)` THEN
    ABBREV_TAC `sz = sndcart((g:real^3->real^(3,1)finite_sum) z)` THEN
    SUBGOAL_THEN `pastecart (y:real^3) (lift(&1 / &2)) IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]` ASSUME_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC;
                  LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `(f:real^(3,1)finite_sum->real^3) (pastecart y (lift(&1 / &2)))` THEN
    EXISTS_TAC `&2 * drop sz - &1` THEN
    USE_THEN "fB" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `pastecart (y:real^3) (lift(&1 / &2)) IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]`)]) THEN
    MP_TAC(SPECL [`y:real^3`; `lift(&1 / &2)`] (ASSUME `!x s. x IN B /\ x$3 = c - d0 /\ s IN interval[vec 0:real^1,vec 1] ==> ((f:real^(3,1)finite_sum->real^3) (pastecart x s))$3 = c - d0 + drop s * &2 * d0`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&0 <= drop sz` THEN UNDISCH_TAC `drop sz <= &1` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP (ASSUME `!z. z IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1] ==> (g:real^3->real^(3,1)finite_sum) ((f:real^(3,1)finite_sum->real^3) z) = z`) (ASSUME
      `pastecart (y:real^3) (lift(&1 / &2)) IN {x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]`)] THEN
    REWRITE_TAC[FSTCART_PASTECART;
                REAL_ARITH `((&2 * x - &1) + &1) / &2 = x`; LIFT_DROP] THEN
    EXPAND_TAC "y" THEN EXPAND_TAC "sz" THEN REWRITE_TAC[PASTECART_FST_SND] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ASSUME `!y. y IN {x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0} ==> (f:real^(3,1)finite_sum->real^3) ((g:real^3->real^(3,1)finite_sum) y) = y`) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `(\p. (f:real^(3,1)finite_sum->real^3)
             (pastecart (fstcart((g:real^3->real^(3,1)finite_sum) (fstcart p)))
                        (lift((drop(sndcart p) + &1) / &2)))) =
      f o (\p. pastecart (fstcart(g (fstcart p)))
                         (lift((drop(sndcart (p:real^(3,1)finite_sum)) + &1) / &2)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_FSTCART THEN
        SUBGOAL_THEN `(\p. (g:real^3->real^(3,1)finite_sum)
                             (fstcart(p:real^(3,1)finite_sum))) =
                      g o fstcart` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0}` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS;
                    FSTCART_PASTECART; IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC;
        REWRITE_TAC[MOI_S5B_LIFT_AFFINE] THEN
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^3`; `v:real^1`] THEN STRIP_TAC THEN
      USE_THEN "pin" (MP_TAC o SPECL [`x:real^3`; `drop v`]) THEN
      ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(v:real^1) IN interval[--vec 1,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\x. (f:real^(3,1)finite_sum->real^3)
             (pastecart (fstcart((g:real^3->real^(3,1)finite_sum) x))
                        (lift((t + &1) / &2)))) =
      f o (\x. pastecart (fstcart(g x)) (lift((t + &1) / &2)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `locally_polyhedral {x:real^3 | x IN B /\ x$3 = c}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_S5B_LEVEL_POLYHEDRON THEN
      REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
      EXISTS_TAC `K:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `{x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_PASTECART THEN
      ASM_SIMP_TAC[PL_MAP_ON_CONST] THEN
      SUBGOAL_THEN `(\x. fstcart((g:real^3->real^(3,1)finite_sum) x)) =
                    fstcart o g` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
      EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
      SIMP_TAC[MOI_S5B_PL_LINEAR; LINEAR_FSTCART; LOCALLY_POLYHEDRAL_OPEN;
               OPEN_UNIV; SUBSET_UNIV] THEN
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | x IN B /\ c - d0 <= x$3 /\ x$3 <= c + d0}` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
        EXISTS_TAC `{x:real^3 | x IN B /\ x$3 = c - d0} PCROSS interval[vec 0:real^1,vec 1]` THEN
        EXISTS_TAC `f:real^(3,1)finite_sum->real^3` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      USE_THEN "pin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Pointed relative subdivision: the extension of SIMPLICIAL_SUBDIVISION_   *)
(* EXTEND (unit pc_moi_cone) with chosen cone points zf t in the relative   *)
(* interiors and an invariant P of the new simplices.  The base and cone    *)
(* steps are copies of MOI_CON_EXTEND_BASE and MOI_CON_EXTEND_STEP_CONE     *)
(* (pc_moi_cone.ml) with the complex made explicit.                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_EXT_BASE = prove
 (`!l f d:(real^N->bool)->bool.
        moi_con_relhyp l f d /\ l DIFF f = {}
        ==> moi_con_relsub l f d (d UNION {s:real^N->bool | s IN f /\ s = {}})`,
  REWRITE_TAC[moi_con_relhyp; moi_con_relsub] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `l:(real^N->bool)->bool = f` SUBST_ALL_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {s:real^N->bool | s IN f /\ s = {}} = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_SIMPLICIAL_COMPLEX_UNION THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
        MESON_TAC[SIMPLEX_EMPTY];
        REPEAT GEN_TAC THEN STRIP_TAC THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o check
          (fun th -> rhs(concl th) = `{}:real^N->bool`)) THEN
        ASM_MESON_TAC[FACE_OF_EMPTY];
        REPEAT GEN_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[INTER_EMPTY; EMPTY_FACE_OF]];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[INTER_EMPTY; EMPTY_FACE_OF]];
    ASM_REWRITE_TAC[UNIONS_UNION; UNION_EMPTY];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET_REFL];
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    SIMP_TAC[IN_UNION];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t:real^N->bool) SUBSET UNIONS f` MP_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]]]);;

let MOI_S5B_EXT_CONE = prove
 (`!(l:(real^N->bool)->bool) f d (t:real^N->bool) l0 (b:real^N).
        moi_con_relhyp l f d /\ t IN l /\ ~(t IN f) /\
        ~DISJOINT t (UNIONS f) /\
        (!u. u IN l /\ t SUBSET u ==> u = t) /\
        moi_con_relsub (l DELETE t) f d l0 /\ b IN relative_interior t
        ==> moi_con_relsub l f d
             (l0 UNION {convex hull (b INSERT s) |
                        s IN {s | s IN l0 /\ s SUBSET relative_frontier t}})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_con_relhyp] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_con_relsub]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  SUBGOAL_THEN `convex (t:real^N->bool) /\ closed t /\ compact t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~DISJOINT (t:real^N->bool) (UNIONS f)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_frontier t:real^N->bool = {})` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CON_ACTIVE_RF_NONEMPTY THEN
    MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `f:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((b:real^N) IN UNIONS f)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CON_RI_NOT_IN_F THEN
    MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l0:(real^N->bool)->bool`; `t:real^N->bool`; `n:int`]
    MOI_CON_RF_SUBCOMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!t':real^N->bool. t' IN l DELETE t ==> ?e. e SUBSET l0 /\ t' = UNIONS e`
    THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`{s:real^N->bool | s IN l0 /\ s SUBSET relative_frontier t}`;
    `t:real^N->bool`; `n:int`; `b:real^N`] MOI_CON_CONE_OVER_RF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u:real^N->bool. u IN l0 ==> u INTER t SUBSET relative_frontier t`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!s:real^N->bool. s IN l0 ==> ?t'. t' IN l DELETE t /\ s SUBSET t'` THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`;
                   `w:real^N->bool`] MOI_CON_INTER_MAXIMAL_RF) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(u:real^N->bool) SUBSET w` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s u:real^N->bool.
        s IN {s | s IN l0 /\ s SUBSET relative_frontier t} /\ u IN l0
        ==> convex hull (b INSERT s) INTER u = s INTER u`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_CON_CONE_INTER_OUTSIDE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
      EXISTS_TAC `l0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_con_relsub] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_GLUE_CONE THEN ASM_REWRITE_TAC[SUBSET_RESTRICT];
    SUBGOAL_THEN `UNIONS l = t UNION UNIONS (l DELETE (t:real^N->bool))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(t:real^N->bool) IN l` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`{s:real^N->bool | s IN l0 /\ s SUBSET relative_frontier t}`;
      `l0:(real^N->bool)->bool`] SUBSET_UNIONS) THEN
    REWRITE_TAC[SUBSET_RESTRICT] THEN
    UNDISCH_TAC `UNIONS l0 = UNIONS (l DELETE (t:real^N->bool))` THEN
    UNDISCH_TAC
     `UNIONS ({s | s IN l0 /\ s SUBSET relative_frontier t} UNION
       {convex hull ((b:real^N) INSERT s) |
        s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}) = t` THEN
    REWRITE_TAC[UNIONS_UNION] THEN
    SPEC_TAC(`UNIONS {convex hull ((b:real^N) INSERT s) |
                      s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}`,
             `C:real^N->bool`) THEN
    SPEC_TAC(`UNIONS {s:real^N->bool | s IN l0 /\
                                      s SUBSET relative_frontier t}`,
             `Ks:real^N->bool`) THEN
    SPEC_TAC(`UNIONS (l DELETE (t:real^N->bool))`, `X:real^N->bool`) THEN
    SPEC_TAC(`UNIONS l0:real^N->bool`, `A:real^N->bool`) THEN SET_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [UNDISCH_TAC
       `!s:real^N->bool. s IN l0 ==> ?t'. t' IN l DELETE t /\ s SUBSET t'` THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MESON_TAC[];
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `UNIONS ({s | s IN l0 /\ s SUBSET relative_frontier t} UNION
         {convex hull ((b:real^N) INSERT s) |
          s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}) = t` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
      ASM_REWRITE_TAC[IN_UNION]];
    X_GEN_TAC `t':real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t':real^N->bool = t` THENL
     [EXISTS_TAC
       `{s:real^N->bool | s IN l0 /\ s SUBSET relative_frontier t} UNION
        {convex hull ((b:real^N) INSERT s) |
         s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      UNDISCH_TAC
       `!t':real^N->bool. t' IN l DELETE t ==> ?e. e SUBSET l0 /\ t' = UNIONS e`
      THEN DISCH_THEN(MP_TAC o SPEC `t':real^N->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SET_TAC[]];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    UNDISCH_TAC `!s:real^N->bool. s IN d /\ ~(s = {}) ==> s IN l0` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC
       `!s:real^N->bool. s IN l0 /\ ~(s = {}) /\ s SUBSET UNIONS f ==> s IN d`
      THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(b:real^N) IN s` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
        REWRITE_TAC[IN_INSERT];
        UNDISCH_TAC `~((b:real^N) IN UNIONS f)` THEN
        UNDISCH_TAC `(s:real^N->bool) SUBSET UNIONS f` THEN
        UNDISCH_TAC `(b:real^N) IN s` THEN SET_TAC[]]];
    X_GEN_TAC `t':real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    UNDISCH_TAC
     `!t':real^N->bool.
        t' IN l DELETE t /\ DISJOINT t' (UNIONS f) ==> t' IN l0` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]]);;

let MOI_S5B_EXT_INDUCT = prove
 (`!(f:(real^N->bool)->bool) d (zf:(real^N->bool)->real^N)
    (P:(real^N->bool)->bool) n l.
        moi_con_relhyp l f d /\ CARD (l DIFF f) = n /\
        (!t. t IN l /\ ~(t IN f) /\ ~DISJOINT t (UNIONS f)
             ==> zf t IN relative_interior t) /\
        (!s. s IN d ==> P s) /\
        (!t. t IN l /\ DISJOINT t (UNIONS f) ==> P t) /\
        (!t s. t IN l /\ ~(t IN f) /\ ~DISJOINT t (UNIONS f) /\
               s SUBSET relative_frontier t /\ P s
               ==> P (convex hull (zf t INSERT s)))
        ==> ?l'. moi_con_relsub l f d l' /\ !s. s IN l' ==> P s`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `l:(real^N->bool)->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `l DIFF f:(real^N->bool)->bool = {}` THENL
   [EXISTS_TAC `d UNION {s:real^N->bool | s IN f /\ s = {}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5B_EXT_BASE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
      STRIP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(s:real^N->bool) IN l /\ DISJOINT s (UNIONS f)` MP_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `moi_con_relhyp (l:(real^N->bool)->bool) f d` THEN
          REWRITE_TAC[moi_con_relhyp] THEN STRIP_TAC THEN
          UNDISCH_TAC `(f:(real^N->bool)->bool) SUBSET l` THEN
          UNDISCH_TAC `(s:real^N->bool) IN f` THEN SET_TAC[];
          ASM_REWRITE_TAC[DISJOINT_EMPTY]];
        FIRST_ASSUM MATCH_ACCEPT_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_con_relhyp]) THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [simplicial_complex]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t:real^N->bool. t IN l /\ ~(t IN f) /\
                     !u. u IN l /\ ~(u IN f) ==> ~(t PSUBSET u)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(PSUBSET):(real^N->bool)->(real^N->bool)->bool`;
                   `l DIFF f:(real^N->bool)->bool`]
      FINITE_TRANSITIVITY_CHAIN) THEN
    ASM_SIMP_TAC[FINITE_DIFF; PSUBSET_IRREFL] THEN
    REWRITE_TAC[IN_DIFF] THEN MESON_TAC[PSUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN l /\ t SUBSET u ==> u = t`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(u:real^N->bool) IN f` THENL
     [MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`;
                     `u:real^N->bool`] MOI_CON_SC_INTER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `t INTER u:real^N->bool = t` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[GSYM SUBSET_INTER_ABSORPTION]; ALL_TAC] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) IN f` MP_TAC THENL
       [MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `u:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      UNDISCH_TAC
       `!u:real^N->bool. u IN l /\ ~(u IN f) ==> ~(t PSUBSET u)` THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
      ASM_REWRITE_TAC[PSUBSET] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL
   [SUBGOAL_THEN `~(n = 0)` MP_TAC THENL
     [EXPAND_TAC "n" THEN ASM_SIMP_TAC[CARD_EQ_0; FINITE_DIFF]; ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l DELETE (t:real^N->bool)`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[moi_con_relhyp] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_CON_SC_DELETE_MAXIMAL THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(l DELETE t) DIFF f = (l DIFF f) DELETE (t:real^N->bool)`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_DELETE; FINITE_DIFF; IN_DIFF];
      ALL_TAC] THEN
    REWRITE_TAC[IN_DELETE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `DISJOINT (t:real^N->bool) (UNIONS f)` THENL
   [EXISTS_TAC `(t:real^N->bool) INSERT l0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_EXTEND_STEP_DISJ THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `s:real^N->bool` THEN
      STRIP_TAC THEN ASM_SIMP_TAC[]];
    EXISTS_TAC
     `l0 UNION {convex hull ((zf:(real^N->bool)->real^N) t INSERT s) | s |
                s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5B_EXT_CONE THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
      STRIP_TAC THEN ASM_SIMP_TAC[]]]);;

let MOI_S5B_EXTEND_POINTED = prove
 (`!(l:(real^N->bool)->bool) f d (zf:(real^N->bool)->real^N)
    (P:(real^N->bool)->bool).
     simplicial_complex l /\ simplicial_complex f /\ f SUBSET l /\
     simplicial_complex d /\ UNIONS d = UNIONS f /\
     (!s. s IN d ==> ?t. t IN f /\ s SUBSET t) /\
     (!t. t IN f ==> ?e. e SUBSET d /\ t = UNIONS e) /\
     (!t. t IN l /\ ~(t IN f) /\ ~DISJOINT t (UNIONS f)
          ==> zf t IN relative_interior t) /\
     (!s. s IN d ==> P s) /\
     (!t. t IN l /\ DISJOINT t (UNIONS f) ==> P t) /\
     (!t s. t IN l /\ ~(t IN f) /\ ~DISJOINT t (UNIONS f) /\
            s SUBSET relative_frontier t /\ P s
            ==> P (convex hull (zf t INSERT s)))
     ==> ?l'. simplicial_complex l' /\ UNIONS l' = UNIONS l /\
              (!s. s IN l' ==> ?t. t IN l /\ s SUBSET t) /\
              (!t. t IN l ==> ?e. e SUBSET l' /\ t = UNIONS e) /\
              (!s. s IN d /\ ~(s = {}) ==> s IN l') /\
              (!s. s IN l' /\ ~(s = {}) /\ s SUBSET UNIONS f ==> s IN d) /\
              (!t. t IN l /\ DISJOINT t (UNIONS f) ==> t IN l') /\
              (!s. s IN l' ==> P s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(real^N->bool)->bool`; `d:(real^N->bool)->bool`;
                 `zf:(real^N->bool)->real^N`; `P:(real^N->bool)->bool`;
                 `CARD (l DIFF f:(real^N->bool)->bool)`;
                 `l:(real^N->bool)->bool`] MOI_S5B_EXT_INDUCT) THEN
  ASM_REWRITE_TAC[moi_con_relhyp] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':(real^N->bool)->bool` MP_TAC) THEN
  REWRITE_TAC[moi_con_relsub] THEN STRIP_TAC THEN
  EXISTS_TAC `l':(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cutting a simplicial complex of real^3 at a level c' (no vertex at the   *)
(* levels c and c'): a subdivision whose simplices lie on one side of c'   *)
(* and whose vertices avoid the level c (pointed relative subdivision over  *)
(* the vertex complex, cone points at the level c' for crossing simplices). *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_RI_SEGMENT = prove
 (`!(t:real^N->bool) z0 b u.
     convex t /\ z0 IN relative_interior t /\ b IN t /\ &0 <= u /\ u < &1
     ==> (&1 - u) % z0 + u % b IN relative_interior t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `u = &0` THENL
   [ASM_REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                    VECTOR_ADD_RID];
    ALL_TAC] THEN
  ASM_CASES_TAC `b:real^N = z0` THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `(&1 - u) % z + u % z = z:real^N`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `z0:real^N`; `b:real^N`]
    IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5B_CUT_POINT = prove
 (`!(t:real^3->bool) c c'.
     convex t /\ (?v. v IN t /\ ~(v$3 = c))
     ==> ?z. z IN relative_interior t /\
             (if ?x y. x IN t /\ y IN t /\ x$3 < c' /\ c' < y$3
              then z$3 = c' else ~(z$3 = c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?z0:real^3. z0 IN relative_interior t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `!b:real^3 u. b IN t /\ &0 <= u /\ u < &1
                ==> (&1 - u) % z0 + u % b IN relative_interior t /\
                    ((&1 - u) % z0 + u % b)$3 = (&1 - u) * z0$3 + u * b$3`
  (LABEL_TAC "seg") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5B_RI_SEGMENT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?x y:real^3. x IN t /\ y IN t /\ x$3 < c' /\ c' < y$3` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `(z0:real^3)$3 = c'` THENL
     [EXISTS_TAC `z0:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
      `~(a = b:real) ==> b < a \/ a < b`)) THENL
     [SUBGOAL_THEN `&0 < (z0:real^3)$3 - (x:real^3)$3` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "seg" (MP_TAC o SPECL
        [`x:real^3`; `((z0:real^3)$3 - c') / (z0$3 - (x:real^3)$3)`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      STRIP_TAC THEN
      EXISTS_TAC `(&1 - ((z0:real^3)$3 - c') / (z0$3 - (x:real^3)$3)) % z0 +
                  ((z0$3 - c') / (z0$3 - x$3)) % x` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < (z0:real^3)$3 - (x:real^3)$3` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `&0 < (y:real^3)$3 - (z0:real^3)$3` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "seg" (MP_TAC o SPECL
        [`y:real^3`; `(c' - (z0:real^3)$3) / ((y:real^3)$3 - z0$3)`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      STRIP_TAC THEN
      EXISTS_TAC `(&1 - (c' - (z0:real^3)$3) / ((y:real^3)$3 - z0$3)) % z0 +
                  ((c' - z0$3) / (y$3 - z0$3)) % y` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < (y:real^3)$3 - (z0:real^3)$3` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_CASES_TAC `~((z0:real^3)$3 = c)` THENL
   [EXISTS_TAC `z0:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPECL [`v:real^3`; `&1 / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `(&1 - &1 / &2) % z0 + (&1 / &2) % (v:real^3)` THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((v:real^3)$3 = c)` THEN
  UNDISCH_TAC `~ ~((z0:real^3)$3 = c)` THEN REAL_ARITH_TAC);;

let MOI_S5B_AFF_DIM_LE0 = prove
 (`!s:real^N->bool. aff_dim s <= &0 <=> s = {} \/ ?a. s = {a}`,
  GEN_TAC THEN REWRITE_TAC[GSYM AFF_DIM_EQ_0; GSYM AFF_DIM_EQ_MINUS1] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN INT_ARITH_TAC);;

let MOI_S5B_SKELETON = prove
 (`!(K:(real^N->bool)->bool) d.
     simplicial_complex K ==> simplicial_complex {s | s IN K /\ aff_dim s <= d}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      TRANS_TAC INT_LE_TRANS `aff_dim(s:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    ASM_MESON_TAC[]]);;

let MOI_S5B_SC_VERTEX = prove
 (`!(K:(real^N->bool)->bool) s.
     simplicial_complex K /\ s IN K /\ ~(s = {}) ==> ?v. v IN s /\ {v} IN K`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN EXISTS_TAC `v:real^N` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
  ASM_MESON_TAC[FACE_OF_SING]);;

let MOI_S5B_HULL_SIDE = prove
 (`!(z:real^N) s k c'.
     ((!x. x IN s ==> x$k <= c') /\ z$k <= c'
      ==> !x. x IN convex hull (z INSERT s) ==> x$k <= c') /\
     ((!x. x IN s ==> c' <= x$k) /\ c' <= z$k
      ==> !x. x IN convex hull (z INSERT s) ==> c' <= x$k)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `convex hull ((z:real^N) INSERT s) SUBSET {x:real^N | x$k <= c'}`
    MP_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE] THEN
      REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SET_TAC[]];
    SUBGOAL_THEN `convex hull ((z:real^N) INSERT s) SUBSET {x:real^N | x$k >= c'}`
    MP_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE] THEN
      REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM; real_ge] THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN MESON_TAC[]]]);;

let MOI_S5B_CUT = prove
 (`!(K:(real^3->bool)->bool) c c'.
     simplicial_complex K /\ ~(c' = c) /\
     (!v. {v} IN K ==> ~(v$3 = c) /\ ~(v$3 = c'))
     ==> ?L. simplicial_complex L /\ UNIONS L = UNIONS K /\
             (!s. s IN L ==> ?t. t IN K /\ s SUBSET t) /\
             (!s. s IN L ==> (!x. x IN s ==> x$3 <= c') \/
                             (!x. x IN s ==> c' <= x$3)) /\
             (!v. {v} IN L ==> ~(v$3 = c))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f = {s:real^3->bool | s IN K /\ aff_dim s <= &0}` THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN f <=> s IN K /\ (s = {} \/ ?a. s = {a})`
  (LABEL_TAC "inf") THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[IN_ELIM_THM; MOI_S5B_AFF_DIM_LE0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN UNIONS f <=> {x} IN K` (LABEL_TAC "uf") THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNIONS] THEN
    USE_THEN "inf" (fun th -> REWRITE_TAC[th]) THEN
    EQ_TAC THENL [ALL_TAC; MESON_TAC[IN_SING]] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `s:real^3->bool` THEN
    STRIP_TAC THEN ASM_MESON_TAC[NOT_IN_EMPTY; IN_SING];
    ALL_TAC] THEN
  ABBREV_TAC
   `zf = \t:real^3->bool. @z:real^3. z IN relative_interior t /\
          (if ?x y:real^3. x IN t /\ y IN t /\ x$3 < c' /\ c' < y$3
           then z$3 = c' else ~(z$3 = c))` THEN
  SUBGOAL_THEN
   `!t:real^3->bool. t IN K /\ ~(t IN f) /\ ~DISJOINT t (UNIONS f)
       ==> zf t IN relative_interior t /\
           (if ?x y:real^3. x IN t /\ y IN t /\ x$3 < c' /\ c' < y$3
            then (zf t)$3 = c' else ~((zf t)$3 = c))`
  (LABEL_TAC "zf") THENL
   [X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN EXPAND_TAC "zf" THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC SELECT_CONV THEN
    MATCH_MP_TAC MOI_S5B_CUT_POINT THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    UNDISCH_TAC `~DISJOINT (t:real^3->bool) (UNIONS f)` THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    USE_THEN "uf" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`K:(real^3->bool)->bool`; `f:(real^3->bool)->bool`;
    `f:(real^3->bool)->bool`; `zf:(real^3->bool)->real^3`;
    `\s:real^3->bool. ((!x:real^3. x IN s ==> x$3 <= c') \/
                       (!x:real^3. x IN s ==> c' <= x$3)) /\
                      (!v:real^3. s = {v} ==> ~(v$3 = c))`]
   MOI_S5B_EXTEND_POINTED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `simplicial_complex (f:(real^3->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN MATCH_MP_TAC MOI_S5B_SKELETON THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `simplicial_complex (K:(real^3->bool)->bool)`;
                ASSUME `simplicial_complex (f:(real^3->bool)->bool)`] THEN
    SUBGOAL_THEN `!s:real^3->bool.
                    (s = {} \/ ?a. s = {a} /\ {a} IN K)
                    ==> ((!x. x IN s ==> x$3 <= c') \/
                         (!x. x IN s ==> c' <= x$3)) /\
                        (!v. s = {v} ==> ~(v$3 = c))`
    (LABEL_TAC "small") THENL
     [X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY; IN_SING] THENL
       [MESON_TAC[NOT_INSERT_EMPTY];
        CONJ_TAC THENL [MESON_TAC[REAL_LE_TOTAL]; ALL_TAC] THEN
        REWRITE_TAC[SET_RULE `{a:real^3} = {v} <=> v = a`] THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "f" THEN SET_TAC[];
      MESON_TAC[SUBSET_REFL];
      X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
      EXISTS_TAC `{t:real^3->bool}` THEN REWRITE_TAC[UNIONS_1] THEN
      ASM SET_TAC[];
      X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
      USE_THEN "zf" (MP_TAC o SPEC `t:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `s:real^3->bool` THEN USE_THEN "inf" (fun th -> REWRITE_TAC[th]) THEN
      STRIP_TAC THEN USE_THEN "small" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
      USE_THEN "small" MATCH_MP_TAC THEN DISJ1_TAC THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `t:real^3->bool`]
        MOI_S5B_SC_VERTEX) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `DISJOINT (t:real^3->bool) (UNIONS f)` THEN
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "uf" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real^3->bool`; `s:real^3->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "side") ASSUME_TAC))))) THEN
      USE_THEN "zf" (MP_TAC o SPEC `t:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SPEC_TAC(`(zf:(real^3->bool)->real^3) t`,`z:real^3`) THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `convex(t:real^3->bool) /\ (z:real^3) IN t /\
                    (s:real^3->bool) SUBSET t`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `?n. n simplex (t:real^3->bool)` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `simplicial_complex (K:(real^3->bool)->bool)` THEN
          REWRITE_TAC[simplicial_complex] THEN
          DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `convex(t:real^3->bool) /\ closed t` STRIP_ASSUME_TAC THENL
         [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SIMPLEX_IMP_CONVEX th;
                                            MATCH_MP SIMPLEX_IMP_CLOSED th]);
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `(s:real^3->bool) SUBSET relative_frontier t` THEN
        ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN SET_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC `?x y:real^3. x IN t /\ y IN t /\ x$3 < c' /\ c' < y$3` THENL
         [UNDISCH_TAC `if ?x y:real^3. x IN t /\ y IN t /\ x$3 < c' /\ c' < y$3
                       then (z:real^3)$3 = c' else ~(z$3 = c)` THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          REMOVE_THEN "side" DISJ_CASES_TAC THENL
           [DISJ1_TAC; DISJ2_TAC] THEN
          MP_TAC(ISPECL [`z:real^3`; `s:real^3->bool`; `3`; `c':real`]
            MOI_S5B_HULL_SIDE) THEN
          ASM_SIMP_TAC[REAL_LE_REFL];
          SUBGOAL_THEN `(!x:real^3. x IN t ==> x$3 <= c') \/
                        (!x:real^3. x IN t ==> c' <= x$3)` MP_TAC THENL
           [ASM_MESON_TAC[REAL_NOT_LT]; ALL_TAC] THEN
          SUBGOAL_THEN `convex hull ((z:real^3) INSERT s) SUBSET t` MP_TAC THENL
           [MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[]; SET_TAC[]]];
        X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `v:real^3 = z` SUBST1_TAC THENL
         [SUBGOAL_THEN `(z:real^3) IN convex hull (z INSERT s)` MP_TAC THENL
           [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
            ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]];
          ALL_TAC] THEN
        UNDISCH_TAC `if ?x y:real^3. x IN t /\ y IN t /\ x$3 < c' /\ c' < y$3
                     then (z:real^3)$3 = c' else ~(z$3 = c)` THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(c':real = c)` THEN REAL_ARITH_TAC]];
    DISCH_THEN(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `L:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Images of simplicial complexes under maps that are injective and affine  *)
(* on every simplex (the affine left inverse MOI_PLM_AFFINE_INJECTIVE_LEFT_ *)
(* INVERSE of unit pc_moi_plmap keeps the vertex sets affinely independent). *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_AFFINE_INDEP_IMAGE = prove
 (`!(h:real^M->real^N) (l:real^M->real^N) y v.
     ~affine_dependent v /\ linear l /\
     (!x. x IN convex hull v ==> h x = l x + y) /\
     (!x x'. x IN convex hull v /\ x' IN convex hull v /\ h x = h x' ==> x = x')
     ==> ~affine_dependent (IMAGE h v) /\
         (!w. w SUBSET v ==> IMAGE h (convex hull w) = convex hull (IMAGE h w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "hl") (LABEL_TAC "inj")))) THEN
  SUBGOAL_THEN `!w:real^M->bool. w SUBSET convex hull v
                ==> IMAGE (h:real^M->real^N) w = IMAGE (\x. l x + y) w`
  (LABEL_TAC "im") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN
    USE_THEN "hl" MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^M->bool) SUBSET convex hull v` ASSUME_TAC THENL
   [REWRITE_TAC[HULL_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `w:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull w SUBSET convex hull (v:real^M->bool)`
    ASSUME_TAC THENL [MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^M->bool) SUBSET convex hull v` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`convex:(real^M->bool)->bool`; `w:real^M->bool`]
        HULL_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "im" (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_SIMP_TAC[MOI_REAL_AFFINE_IMAGE_CONVEX_HULL]] THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `convex hull v:real^M->bool`]
    MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN REPEAT STRIP_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `y':real^M`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "im" (fun th -> ASM_SIMP_TAC[th]) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `affine_dependent (IMAGE (\z. y' + z)
      (IMAGE (l':real^N->real^M) (IMAGE (\x. (l:real^M->real^N) x + y) v)))`
  MP_TAC THENL
   [MATCH_MP_TAC AFFINE_DEPENDENT_TRANSLATION THEN
    MATCH_MP_TAC AFFINE_DEPENDENT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `a:real^M` THEN DISCH_TAC THEN
    X_GEN_TAC `b:real^M` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `a:real^M = b` (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(l':real^N->real^M) ((l:real^M->real^N) a + y) + y' =
                  l' (l b + y) + y'` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET]
      (ASSUME `(v:real^M->bool) SUBSET convex hull v`)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\z. y' + z)
      (IMAGE (l':real^N->real^M) (IMAGE (\x. (l:real^M->real^N) x + y) v)) = v`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^M. x) v` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]] THEN
  MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC(VECTOR_ARITH `a + y' = x ==> y' + a = x:real^M`) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `y':real^M`)) (concl th))) THEN
  ASM SET_TAC[]);;

let MOI_S5B_AFFINE_SIMPLEX_FACES = prove
 (`!(h:real^M->real^N) s.
     (?n. n simplex s) /\
     (?l y. linear l /\ !x. x IN s ==> h x = l x + y) /\
     (!x x'. x IN s /\ x' IN s /\ h x = h x' ==> x = x')
     ==> (?n. n simplex (IMAGE h s)) /\
         (!t. t face_of (IMAGE h s) <=> ?t0. t0 face_of s /\ t = IMAGE h t0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:int`)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC)) ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [simplex]) THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `l:real^M->real^N`; `y:real^N`;
                 `v:real^M->bool`] MOI_S5B_AFFINE_INDEP_IMAGE) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `s:real^M->bool = convex hull v` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^M->real^N) s = convex hull (IMAGE h v)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^M->bool) SUBSET s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HULL_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `n:int` THEN REWRITE_TAC[simplex] THEN
    EXISTS_TAC `IMAGE (h:real^M->real^N) v` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try rhs(concl th) = `n + &1:int` with Failure _ -> false)) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[SUBSET_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `convex hull w:real^M->bool` THEN
    CONJ_TAC THENL [EXISTS_TAC `w:real^M->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t0:real^M->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `IMAGE (h:real^M->real^N) w` THEN
    CONJ_TAC THENL [EXISTS_TAC `w:real^M->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

let MOI_S5B_IMAGE_COMPLEX = prove
 (`!c (h:real^M->real^N).
     simplicial_complex c /\
     (!x y. x IN UNIONS c /\ y IN UNIONS c /\ h x = h y ==> x = y) /\
     (!s. s IN c ==> ?l y. linear l /\ !x. x IN s ==> h x = l x + y)
     ==> simplicial_complex (IMAGE (IMAGE h) c) /\
         UNIONS (IMAGE (IMAGE h) c) = IMAGE h (UNIONS c) /\
         (!w. {w} IN IMAGE (IMAGE h) c ==> ?v. {v} IN c /\ w = h v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (LABEL_TAC "aff"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN
   `!s:real^M->bool. s IN c
      ==> (?n. n simplex (IMAGE (h:real^M->real^N) s)) /\
          (!t. t face_of (IMAGE h s) <=> ?t0. t0 face_of s /\ t = IMAGE h t0)`
  (LABEL_TAC "fac") THENL
   [X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5B_AFFINE_SIMPLEX_FACES THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplicial_complex] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `f:real^N->bool` THEN X_GEN_TAC `s:real^M->bool` THEN
      DISCH_TAC THEN USE_THEN "fac" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(s:real^M->bool) IN c`))) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:real^M->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[];
      X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
      X_GEN_TAC `s':real^M->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `IMAGE (h:real^M->real^N) s INTER IMAGE h s' = IMAGE h (s INTER s')`
      SUBST1_TAC THENL
       [USE_THEN "inj" MP_TAC THEN
        SUBGOAL_THEN `(s:real^M->bool) SUBSET UNIONS c /\ s' SUBSET UNIONS c`
        MP_TAC THENL [ASM SET_TAC[]; SET_TAC[]];
        ALL_TAC] THEN
      USE_THEN "fac" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(s:real^M->bool) IN c`))) THEN
      USE_THEN "fac" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(s':real^M->bool) IN c`))) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
      CONJ_TAC THENL
       [EXISTS_TAC `s INTER s':real^M->bool` THEN ASM_MESON_TAC[];
        EXISTS_TAC `s INTER s':real^M->bool` THEN ASM_MESON_TAC[]]];
    REWRITE_TAC[IMAGE_UNIONS];
    X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?v:real^M. v IN s /\ (h:real^M->real^N) v = w`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{w:real^N} = IMAGE (h:real^M->real^N) s` THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `v:real^M` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s = {v:real^M}` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_SING] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `{w:real^N} = IMAGE (h:real^M->real^N) s` THEN
    UNDISCH_TAC `(h:real^M->real^N) v = w` THEN
    UNDISCH_TAC `(x:real^M) IN s` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Triangulation of a swapped surface: K cut at the level c' along k',      *)
(* split into the parts E and a, subdivided so that the swap map h is       *)
(* affine on simplices, extended with cone points off the level c, and      *)
(* mapped by h (no vertex at the level c).                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_CONN_TWO_CLOSED = prove
 (`!s e1 e2:real^N->bool.
     connected s /\ closed e1 /\ closed e2 /\ s SUBSET e1 UNION e2 /\
     e1 INTER e2 INTER s = {}
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S5B_SUBDIV_COVER = prove
 (`!(t:(real^N->bool)->bool) c.
     simplicial_complex t /\ simplicial_complex c /\ UNIONS t = UNIONS c /\
     (!s. s IN t ==> ?u. u IN c /\ s SUBSET u)
     ==> !u. u IN c ==> ?e. e SUBSET t /\ u = UNIONS e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:real^N->bool` THEN
  DISCH_TAC THEN EXISTS_TAC `{s:real^N->bool | s IN t /\ s SUBSET u}` THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?s0:real^N->bool. s0 IN t /\ x IN s0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS t:real^N->bool = UNIONS c` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `x:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(r:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]] THEN
  MP_TAC(ISPECL [`u':real^N->bool`; `u INTER u':real^N->bool`;
                 `r:real^N->bool`] SUBSET_OF_FACE_OF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    SET_TAC[]]);;

let MOI_S5B_SUBCOMPLEX_SUBSET = prove
 (`!(L:(real^N->bool)->bool) X.
     simplicial_complex L ==> simplicial_complex {s | s IN L /\ s SUBSET X}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ASM_MESON_TAC[]]);;

let MOI_S5B_CUT_LEVEL = prove
 (`!(L:(real^3->bool)->bool) c'.
     simplicial_complex L /\
     (!s. s IN L ==> (!x. x IN s ==> x$3 <= c') \/ (!x. x IN s ==> c' <= x$3))
     ==> !x. x IN UNIONS L /\ x$3 = c'
             ==> ?s. s IN L /\ x IN s /\ (!y. y IN s ==> y$3 = c')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  EXISTS_TAC `s INTER {y:real^3 | basis 3 dot y = c'}` THEN
  SIMP_TAC[IN_INTER; IN_ELIM_THM; DOT_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex(s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(s INTER {y:real^3 | y$3 = c'}) face_of s`
  (fun th -> ASM_MESON_TAC[th]) THEN
  SUBGOAL_THEN `{y:real^3 | y$3 = c'} = {y | basis 3 dot y = c'}` SUBST1_TAC THENL
   [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  UNDISCH_TAC `!s:real^3->bool. s IN L
      ==> (!x. x IN s ==> x$3 <= c') \/ (!x. x IN s ==> c' <= x$3)` THEN
  DISCH_THEN(DISJ_CASES_TAC o C MATCH_MP (ASSUME `(s:real^3->bool) IN L`)) THENL
   [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE;
    MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE] THEN
  ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; real_ge]);;

let MOI_S5B_UNIONS_PART = prove
 (`!(L:(real^N->bool)->bool) E a k'.
     UNIONS L = E UNION a /\ E INTER a = k' /\
     (!s. s IN L ==> s SUBSET E \/ s SUBSET a) /\
     (!x. x IN k' ==> ?s. s IN L /\ x IN s /\ s SUBSET k')
     ==> UNIONS {s | s IN L /\ s SUBSET E} = E`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "or") (LABEL_TAC "kk")))) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN L /\ x IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS L:real^N->bool = E UNION a` THEN
    UNDISCH_TAC `(x:real^N) IN E` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "or" (DISJ_CASES_TAC o C MATCH_MP (ASSUME `(s:real^N->bool) IN L`)) THENL
   [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "kk" (MP_TAC o SPEC `x:real^N`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `E INTER a:real^N->bool = k'` THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET a` THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN UNDISCH_TAC `(x:real^N) IN E` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(r:real^N->bool) SUBSET k'` THEN
  UNDISCH_TAC `E INTER a:real^N->bool = k'` THEN SET_TAC[]);;

let MOI_S5B_SPLIT_COMPLEX = prove
 (`!(L:(real^3->bool)->bool) E a k' c'.
     simplicial_complex L /\ UNIONS L = E UNION a /\ closed E /\ closed a /\
     E INTER a = k' /\ (!x. x IN k' ==> x$3 = c') /\
     open_in (subtopology euclidean {x | x IN E UNION a /\ x$3 = c'}) k' /\
     (!s. s IN L ==> (!x. x IN s ==> x$3 <= c') \/ (!x. x IN s ==> c' <= x$3))
     ==> (!s. s IN L ==> s SUBSET E \/ s SUBSET a) /\
         UNIONS {s | s IN L /\ s SUBSET E} = E /\
         UNIONS {s | s IN L /\ s SUBSET a} = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s:real^3->bool. connected s /\ s SUBSET {x | x IN E UNION a /\ x$3 = c'} /\
                     ~(s INTER k' = {}) ==> s SUBSET k'`
  (LABEL_TAC "lev") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ow:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `E INTER a:real^3->bool`;
       `{x:real^3 | x IN E UNION a /\ x$3 = c'} DIFF ow`] MOI_S5B_CONN_TWO_CLOSED) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CLOSED_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_DIFF THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `{x:real^3 | x IN E UNION a /\ x$3 = c'} =
                      (E UNION a) INTER {x | x$3 = c'}` SUBST1_TAC THENL
         [SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC CLOSED_INTER THEN
        ASM_SIMP_TAC[CLOSED_UNION; CLOSED_STANDARD_HYPERPLANE];
        ALL_TAC] THEN
      UNDISCH_TAC `E INTER a:real^3->bool = k'` THEN
      UNDISCH_TAC `k':real^3->bool = {x | x IN E UNION a /\ x$3 = c'} INTER ow` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET {x | x IN E UNION a /\ x$3 = c'}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `E INTER a:real^3->bool = k'` THEN
    UNDISCH_TAC `k':real^3->bool = {x | x IN E UNION a /\ x$3 = c'} INTER ow` THEN
    UNDISCH_TAC `~(s INTER k':real^3->bool = {})` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN L ==> s SUBSET E \/ s SUBSET a`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex(s:real^3->bool) /\ closed s /\ s SUBSET E UNION a`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `!x:real^3. x IN s ==> x$3 = c'` THENL
     [ASM_CASES_TAC `s INTER k':real^3->bool = {}` THENL
       [MATCH_MP_TAC MOI_S5B_CONN_TWO_CLOSED THEN
        ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
        UNDISCH_TAC `E INTER a:real^3->bool = k'` THEN
        UNDISCH_TAC `s INTER k':real^3->bool = {}` THEN SET_TAC[];
        DISJ1_TAC THEN
        SUBGOAL_THEN `(s:real^3->bool) SUBSET k'` MP_TAC THENL
         [USE_THEN "lev" MATCH_MP_TAC THEN ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
          UNDISCH_TAC `(s:real^3->bool) SUBSET E UNION a` THEN
          UNDISCH_TAC `!x:real^3. x IN s ==> x$3 = c'` THEN SET_TAC[];
          UNDISCH_TAC `E INTER a:real^3->bool = k'` THEN SET_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_interior s INTER {x:real^3 | x$3 = c'} = {}`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s INTER {y:real^3 | basis 3 dot y = c'}`; `s:real^3->bool`]
        FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `!s:real^3->bool. s IN L
            ==> (!x. x IN s ==> x$3 <= c') \/ (!x. x IN s ==> c' <= x$3)` THEN
          DISCH_THEN(DISJ_CASES_TAC o C MATCH_MP (ASSUME `(s:real^3->bool) IN L`)) THENL
           [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE;
            MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE] THEN
          ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; real_ge];
          UNDISCH_TAC `~(!x:real^3. x IN s ==> x$3 = c')` THEN
          SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN SET_TAC[]];
        MP_TAC(ISPEC `s:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
        SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`relative_interior s:real^3->bool`; `E:real^3->bool`;
                   `a:real^3->bool`] MOI_S5B_CONN_TWO_CLOSED) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR] THEN
      MP_TAC(ISPEC `s:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `relative_interior s INTER {x:real^3 | x$3 = c'} = {}` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET E UNION a` THEN
      UNDISCH_TAC `E INTER a:real^3->bool = k'` THEN
      UNDISCH_TAC `!x:real^3. x IN k' ==> x$3 = c'` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `closure(relative_interior s) = s:real^3->bool` MP_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure(relative_interior s):real^3->bool` THEN
    (CONJ_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL];
                     MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN k' ==> ?s. s IN L /\ x IN s /\ s SUBSET k'`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `c':real`] MOI_S5B_CUT_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
      UNDISCH_TAC `(x:real^3) IN k'` THEN
      UNDISCH_TAC `E INTER a:real^3->bool = k'` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "lev" MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `(x:real^3) IN k'` THEN UNDISCH_TAC `(x:real^3) IN s` THEN
      SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `UNIONS L:real^3->bool = E UNION a` THEN
    UNDISCH_TAC `(y:real^3) IN s` THEN UNDISCH_TAC `(s:real^3->bool) IN L` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_UNIONS_PART THEN
    MAP_EVERY EXISTS_TAC [`a:real^3->bool`; `k':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5B_UNIONS_PART THEN
    MAP_EVERY EXISTS_TAC [`E:real^3->bool`; `k':real^3->bool`] THEN
    ONCE_REWRITE_TAC[UNION_COMM; INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

let MOI_S5B_RI_OFF_LEVEL = prove
 (`!(t:real^3->bool) c.
     convex t /\ (?v. v IN t /\ ~(v$3 = c))
     ==> ?z. z IN relative_interior t /\ ~(z$3 = c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?z0:real^3. z0 IN relative_interior t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  ASM_CASES_TAC `(z0:real^3)$3 = c` THENL
   [ALL_TAC; EXISTS_TAC `z0:real^3` THEN ASM_REWRITE_TAC[]] THEN
  EXISTS_TAC `(&1 - &1 / &2) % z0 + (&1 / &2) % (v:real^3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_RI_SEGMENT THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    UNDISCH_TAC `~((v:real^3)$3 = c)` THEN UNDISCH_TAC `(z0:real^3)$3 = c` THEN
    REAL_ARITH_TAC]);;

let MOI_S5B_TRIANG_EXT = prove
 (`!(L:(real^3->bool)->bool) Kin tin E a (h:real^3->real^3) c.
     simplicial_complex L /\ simplicial_complex Kin /\ simplicial_complex tin /\
     (!t. t IN Kin <=> t IN L /\ t SUBSET E) /\ UNIONS Kin = E /\ UNIONS tin = E /\
     (!s. s IN tin ==> ?u. u IN Kin /\ s SUBSET u) /\
     (!u. u IN Kin ==> ?e. e SUBSET tin /\ u = UNIONS e) /\
     (!s. s IN tin ==> ?l y. linear l /\ !x. x IN s ==> h x = l x + y) /\
     (!s. s IN L ==> s SUBSET E \/ s SUBSET a) /\
     (!v. {v} IN L ==> ~(v$3 = c)) /\
     (!x. x IN a ==> h x = x) /\ (!x. x IN E ==> ~((h x)$3 = c))
     ==> ?L2. simplicial_complex L2 /\ UNIONS L2 = UNIONS L /\
              (!s. s IN L2 ==> ?l y. linear l /\ !x. x IN s ==> h x = l x + y) /\
              (!v. {v} IN L2 ==> ~((h v)$3 = c))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "kin")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "aff") (CONJUNCTS_THEN2 (LABEL_TAC "or")
   (CONJUNCTS_THEN2 (LABEL_TAC "vL") (CONJUNCTS_THEN2 (LABEL_TAC "ida0")
     (LABEL_TAC "hE"))))))))))))) THEN
  SUBGOAL_THEN `!t:real^3->bool. t IN L ==> convex t /\ closed t`
  (LABEL_TAC "cvx") THENL
   [X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n. n simplex (t:real^3->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (L:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^3->bool. t SUBSET a
      ==> (?l y. linear l /\ !x. x IN t ==> (h:real^3->real^3) x = l x + y) /\
          (!v. t = {v} ==> (h v)$3 = v$3)`
  (LABEL_TAC "ida") THENL
   [X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `vec 0:real^3`] THEN
      REWRITE_TAC[LINEAR_ID; VECTOR_ADD_RID] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "ida0" MATCH_MP_TAC THEN
      UNDISCH_TAC `(t:real^3->bool) SUBSET a` THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN SET_TAC[];
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(h:real^3->real^3) v = v` (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "ida0" MATCH_MP_TAC THEN
      UNDISCH_TAC `(t:real^3->bool) SUBSET a` THEN
      UNDISCH_TAC `t = {v:real^3}` THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `zf = \t:real^3->bool. @z:real^3. z IN relative_interior t /\ ~(z$3 = c)` THEN
  SUBGOAL_THEN
   `!t:real^3->bool. t IN L /\ ~(t IN Kin) /\ ~DISJOINT t (UNIONS Kin)
       ==> t SUBSET a /\ zf t IN relative_interior t /\ ~((zf t)$3 = c)`
  (LABEL_TAC "zf") THENL
   [X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:real^3->bool) SUBSET a` ASSUME_TAC THENL
     [UNDISCH_TAC `~((t:real^3->bool) IN Kin)` THEN
      USE_THEN "kin" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "or" (MP_TAC o SPEC `t:real^3->bool`) THEN
      REWRITE_TAC[ASSUME `(t:real^3->bool) IN L`] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "zf" THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC SELECT_CONV THEN
    MATCH_MP_TAC MOI_S5B_RI_OFF_LEVEL THEN
    CONJ_TAC THENL
     [USE_THEN "cvx" (MP_TAC o SPEC `t:real^3->bool`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `t:real^3->bool`]
      MOI_S5B_SC_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~DISJOINT (t:real^3->bool) (UNIONS Kin)` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "vL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`L:(real^3->bool)->bool`; `Kin:(real^3->bool)->bool`;
    `tin:(real^3->bool)->bool`; `zf:(real^3->bool)->real^3`;
    `\s:real^3->bool.
       (?l y. linear l /\ !x. x IN s ==> (h:real^3->real^3) x = l x + y) /\
       (!v. s = {v} ==> ~((h v)$3 = c))`] MOI_S5B_EXTEND_POINTED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "kin" (fun th -> REWRITE_TAC[SUBSET; th]) THEN MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      USE_THEN "zf" (fun th -> MESON_TAC[th]);
      X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "aff" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN USE_THEN "hE" MATCH_MP_TAC THEN
      UNDISCH_TAC `UNIONS tin:real^3->bool = E` THEN
      UNDISCH_TAC `(s:real^3->bool) IN tin` THEN
      UNDISCH_TAC `s = {v:real^3}` THEN SET_TAC[];
      X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(t:real^3->bool) SUBSET a` ASSUME_TAC THENL
       [USE_THEN "or" (MP_TAC o SPEC `t:real^3->bool`) THEN
        UNDISCH_TAC `DISJOINT (t:real^3->bool) (UNIONS Kin)` THEN
        REWRITE_TAC[ASSUME `(t:real^3->bool) IN L`;
                    ASSUME `UNIONS Kin:real^3->bool = E`] THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "ida" (MP_TAC o SPEC `t:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) ASSUME_TAC) THEN
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `t = {v:real^3}`)]) THEN
      USE_THEN "vL" MATCH_MP_TAC THEN
      UNDISCH_TAC `(t:real^3->bool) IN L` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real^3->bool`; `s:real^3->bool`] THEN STRIP_TAC THEN
      USE_THEN "zf" (MP_TAC o SPEC `t:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      SUBGOAL_THEN `convex hull ((zf:(real^3->bool)->real^3) t INSERT s) SUBSET a`
      ASSUME_TAC THENL
       [TRANS_TAC SUBSET_TRANS `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN
        USE_THEN "cvx" (MP_TAC o SPEC `t:real^3->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        ASM_REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
         [MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
          UNDISCH_TAC `(zf:(real^3->bool)->real^3) t IN relative_interior t` THEN
          SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(s:real^3->bool) SUBSET relative_frontier t` THEN
        ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "ida" (MP_TAC o SPEC
        `convex hull ((zf:(real^3->bool)->real^3) t INSERT s)`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) ASSUME_TAC) THEN
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `v = (zf:(real^3->bool)->real^3) t` SUBST_ALL_TAC THENL
       [SUBGOAL_THEN `(zf:(real^3->bool)->real^3) t IN
                      convex hull (zf t INSERT s)` MP_TAC THENL
         [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
          ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `convex hull ((zf:(real^3->bool)->real^3) t INSERT s) = {zf t}`)]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `L2:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{v:real^3}` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "s" &&
        can (find_term (fun t -> t = `c:real`)) (concl th)
    with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S5B_TRIANG_SWAP = prove
 (`!(K:(real^3->bool)->bool) E a k' (h:real^3->real^3) h' B' c c'.
     simplicial_complex K /\ UNIONS K = E UNION a /\ ~(c' = c) /\
     (!v. {v} IN K ==> ~(v$3 = c) /\ ~(v$3 = c')) /\
     closed E /\ closed a /\ E INTER a = k' /\ (!x. x IN k' ==> x$3 = c') /\
     open_in (subtopology euclidean {x | x IN E UNION a /\ x$3 = c'}) k' /\
     pl_homeomorphism (E UNION a,B') (h,h') /\
     (!x. x IN a ==> h x = x) /\ (!x. x IN E ==> ~((h x)$3 = c))
     ==> ?L'. simplicial_complex L' /\ UNIONS L' = B' /\
              !v. {v} IN L' ==> ~(v$3 = c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `c:real`; `c':real`] MOI_S5B_CUT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `E:real^3->bool`; `a:real^3->bool`;
                 `k':real^3->bool`; `c':real`] MOI_S5B_SPLIT_COMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  ABBREV_TAC `Kin = {s:real^3->bool | s IN L /\ s SUBSET E}` THEN
  SUBGOAL_THEN `simplicial_complex (Kin:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kin" THEN MATCH_MP_TAC MOI_S5B_SUBCOMPLEX_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `pl_map_on (UNIONS Kin) (h:real^3->real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `E UNION a:real^3->bool` THEN ASM_REWRITE_TAC[SUBSET_UNION] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
    EXISTS_TAC `Kin:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Kin:(real^3->bool)->bool`; `h:real^3->real^3`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tin:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!u:real^3->bool. u IN Kin ==> ?e. e SUBSET tin /\ u = UNIONS e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5B_SUBDIV_COVER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `Kin:(real^3->bool)->bool`;
                 `tin:(real^3->bool)->bool`; `E:real^3->bool`; `a:real^3->bool`;
                 `h:real^3->real^3`; `c:real`] MOI_S5B_TRIANG_EXT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kin" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L2:(real^3->bool)->bool`; `h:real^3->real^3`]
    MOI_S5B_IMAGE_COMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(h':real^3->real^3) ((h:real^3->real^3) x) = h' (h y)`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `IMAGE (IMAGE (h:real^3->real^3)) L2` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "w" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transport of PL cells and spheres: PL embeddings of compact sets,        *)
(* PL homeomorphisms in one space, injective affine maps between spaces,    *)
(* PL circles to the plane, and the planar disk bounded by a PL circle.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_PL_EMBED = prove
 (`!(X:real^M->bool) (f:real^M->real^N).
     compact X /\ pl_map_on X f /\
     (!x y. x IN X /\ y IN X /\ f x = f y ==> x = y)
     ==> ?g. pl_homeomorphism (X,IMAGE f X) (f,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^M->bool`; `f:real^M->real^N`; `IMAGE (f:real^M->real^N) X`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_CELL_TRANSPORT = prove
 (`!(s:real^N->bool) (t:real^N->bool) (f:real^N->real^N) (g:real^N->real^N) n e j.
     pl_homeomorphism (s,t) (f,g) /\ pl_cell_with_boundary n e j /\ e SUBSET s
     ==> pl_cell_with_boundary n (IMAGE f e) (IMAGE f j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `F1:real^N->real^N`
      (X_CHOOSE_THEN `G1:real^N->real^N` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism (e,IMAGE (f:real^N->real^N) e) (f,g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `e = IMAGE (F1:real^N->real^N) k` SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `(f:real^N->real^N) o (F1:real^N->real^N)`;
                        `(G1:real^N->real^N) o (g:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_SPHERE_TRANSPORT = prove
 (`!(s:real^N->bool) (t:real^N->bool) (f:real^N->real^N) (g:real^N->real^N) n S.
     pl_homeomorphism (s,t) (f,g) /\ pl_sphere n S /\ S SUBSET s
     ==> pl_sphere n (IMAGE f S)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
  MAP_EVERY EXISTS_TAC [`S:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
  ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON]);;

let MOI_S5B_FILL_FRONTIER = prove
 (`!s:real^N->bool.
     2 <= dimindex(:N) /\ s homeomorphic sphere(vec 0:real^N,&1)
     ==> frontier(s UNION inside s) = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s UNION inside s = (:real^N) DIFF outside s` SUBST1_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` INSIDE_OUTSIDE) THEN
    MP_TAC(ISPEC `s:real^N->bool` OUTSIDE_NO_OVERLAP) THEN SET_TAC[];
    ASM_REWRITE_TAC[FRONTIER_COMPLEMENT]]);;

let MOI_S5B_CELL_AFFINE = prove
 (`!(l:real^M->real^N) y n (e:real^M->bool) j.
     linear l /\ (!x x'. l x = l x' ==> x = x') /\ pl_cell_with_boundary n e j
     ==> pl_cell_with_boundary n (IMAGE (\x. l x + y) e) (IMAGE (\x. l x + y) j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `F1:real^M->real^M`
      (X_CHOOSE_THEN `G1:real^M->real^M` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `&n:int`; `k:real^M->bool`]
    MOI_S27_INJ_AFFINE_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `h':real^N->real^M`))) THEN
  SUBGOAL_THEN `pl_polyhedron (e:real^M->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `e = IMAGE (F1:real^M->real^M) k` SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real^M->bool`; `\x:real^M. (l:real^M->real^N) x + y`]
    MOI_S5B_PL_EMBED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
      REWRITE_TAC[VECTOR_ARITH `a + y:real^N = b + y <=> a = b`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^M`) THEN
  EXISTS_TAC `IMAGE (\x:real^M. (l:real^M->real^N) x + y) k` THEN
  EXISTS_TAC `(\x:real^M. (l:real^M->real^N) x + y) o
              ((F1:real^M->real^M) o (h':real^N->real^M))` THEN
  EXISTS_TAC `((\x:real^M. (l:real^M->real^N) x + y) o (G1:real^M->real^M)) o
              (g:real^N->real^M)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `e:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^M->bool)` MP_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism (k,IMAGE (\x:real^M. (l:real^M->real^N) x + y) k)
                ((\x. l x + y),(h':real^N->real^M))` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SET_TAC[]);;

let MOI_S5B_SPHERE_AFFINE = prove
 (`!(l:real^M->real^N) y n (S:real^M->bool).
     linear l /\ (!x x'. l x = l x' ==> x = x') /\ pl_sphere n S
     ==> pl_sphere n (IMAGE (\x. l x + y) S)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[pl_sphere] th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `F1:real^M->real^M`
      (X_CHOOSE_THEN `G1:real^M->real^M` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `&(n + 1):int`; `k:real^M->bool`]
    MOI_S27_INJ_AFFINE_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `h':real^N->real^M`))) THEN
  SUBGOAL_THEN `pl_polyhedron (S:real^M->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^M->bool`; `\x:real^M. (l:real^M->real^N) x + y`]
    MOI_S5B_PL_EMBED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
      REWRITE_TAC[VECTOR_ARITH `a + y:real^N = b + y <=> a = b`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^M`) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k,
                      IMAGE (\x:real^M. (l:real^M->real^N) x + y) (relative_frontier k))
                     ((\x. l x + y),(h':real^N->real^M))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`k:real^M->bool`;
                          `IMAGE (\x:real^M. (l:real^M->real^N) x + y) k`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `n:num` THEN
      MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[pl_sphere] THEN
  EXISTS_TAC `IMAGE (\x:real^M. (l:real^M->real^N) x + y) k` THEN
  EXISTS_TAC `(\x:real^M. (l:real^M->real^N) x + y) o
              ((F1:real^M->real^M) o (h':real^N->real^M))` THEN
  EXISTS_TAC `((\x:real^M. (l:real^M->real^N) x + y) o (G1:real^M->real^M)) o
              (g:real^N->real^M)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `S:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_SPHERE1_TO_PLANE = prove
 (`!(S:real^N->bool) (T2:real^2->bool) f g.
     pl_sphere 1 S /\ pl_homeomorphism (S,T2) (f,g) ==> pl_sphere 1 T2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[pl_sphere; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `F1:real^N->real^N`
      (X_CHOOSE_THEN `G1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S27_SIMPLEX_FROM_PLANE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k0:real^2->bool`; `k:real^N->bool`; `h:real^2->real^N`;
                 `h':real^N->real^2`] MOI_S27_PLH_SIMPLEX_RF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `k0:real^2->bool` THEN
  EXISTS_TAC `(f:real^N->real^2) o (F1:real^N->real^N) o (h:real^2->real^N)` THEN
  EXISTS_TAC `((h':real^N->real^2) o (G1:real^N->real^N)) o (g:real^2->real^N)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `S:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier k:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_PLANE_DISK = prove
 (`!j:real^2->bool. pl_sphere 1 j ==> pl_cell_with_boundary 2 (j UNION inside j) j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[PL_SCHOENFLIES_2_STATEMENT] PL_SCHOENFLIES_2) THEN
  DISCH_THEN(MP_TAC o SPEC `j:real^2->bool`) THEN ASM_REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^2->bool` (X_CHOOSE_THEN `f1:real^2->real^2`
    (X_CHOOSE_THEN `g1:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`k1:real^2->bool`; `f1:real^2->real^2`; `g1:real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k1:real^2->bool`; `j UNION inside j:real^2->bool`;
                 `f1:real^2->real^2`; `g1:real^2->real^2`] MOI_PL2_FRONTIER_PL_BALL_2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S5B_FILL_FRONTIER THEN
  REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
  MATCH_MP_TAC MOI_S5B_PL_SPHERE_HOMEO THEN EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Pushing a point and a planar Jordan curve together: if the curves        *)
(* x |-> h(t,x) never hit the moving point p(t), the point stays outside    *)
(* (Borsuk maps, BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT).                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_SLICE_CONTINUOUS = prove
 (`!(h:real^(1,M)finite_sum->real^N) k t.
     h continuous_on (interval[vec 0,vec 1] PCROSS k) /\
     t IN interval[vec 0,vec 1]
     ==> (\x. h(pastecart t x)) continuous_on k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (h:real^(1,M)finite_sum->real^N) (pastecart t x)) =
                h o (\x:real^M. pastecart t x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS (k:real^M->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS]]);;

let MOI_S5B_PUSH_OUTSIDE = prove
 (`!(k:real^M->bool) (h:real^(1,M)finite_sum->real^2) (p:real^1->real^2).
     compact k /\
     h continuous_on (interval[vec 0,vec 1] PCROSS k) /\
     p continuous_on interval[vec 0,vec 1] /\
     (!t x. t IN interval[vec 0,vec 1] /\ x IN k ==> ~(h(pastecart t x) = p t)) /\
     (!x y. x IN k /\ y IN k /\ h(pastecart (vec 1) x) = h(pastecart (vec 1) y)
            ==> x = y) /\
     p(vec 0) IN outside (IMAGE (\x. h(pastecart (vec 0) x)) k)
     ==> p(vec 1) IN outside (IMAGE (\x. h(pastecart (vec 1) x)) k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "miss")
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,vec 1] /\
                (vec 1:real^1) IN interval[vec 0,vec 1]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (h:real^(1,M)finite_sum->real^2) (pastecart (vec 0) x)) continuous_on k /\
    (\x. h (pastecart (vec 1) x)) continuous_on k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5B_SLICE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `h0 = \x. (h:real^(1,M)finite_sum->real^2) (pastecart (vec 0) x)` THEN
  ABBREV_TAC `h1 = \x. (h:real^(1,M)finite_sum->real^2) (pastecart (vec 1) x)` THEN
  ABBREV_TAC `s0 = IMAGE (h0:real^M->real^2) k` THEN
  ABBREV_TAC `s1 = IMAGE (h1:real^M->real^2) k` THEN
  SUBGOAL_THEN `compact(s0:real^2->bool) /\ compact(s1:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN EXPAND_TAC "s1" THEN CONJ_TAC THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real^1->real^2) (vec 0) IN s0)` ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN EXPAND_TAC "h0" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
    USE_THEN "miss" (MP_TAC o SPECL [`vec 0:real^1`; `x:real^M`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real^1->real^2) (vec 1) IN s1)` ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN EXPAND_TAC "h1" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
    USE_THEN "miss" (MP_TAC o SPECL [`vec 1:real^1`; `x:real^M`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(p:real^1->real^2) (vec 0) IN outside s0` THEN
  REWRITE_TAC[outside; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s0:real^2->bool`; `(p:real^1->real^2) (vec 0)`]
    BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s1:real^2->bool`; `(p:real^1->real^2) (vec 1)`]
    BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `c:real^2`) THEN
  EXISTS_TAC `c:real^2` THEN
  MP_TAC(ISPECL
   [`\x:real^2. inv(norm(x - (p:real^1->real^2) (vec 0))) % (x - p (vec 0))`;
    `\x:real^2. (c:real^2)`; `h0:real^M->real^2`;
    `k:real^M->bool`; `s0:real^2->bool`; `sphere(vec 0:real^2,&1)`]
    HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "s0" THEN REWRITE_TAC[SUBSET_REFL];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `homotopic_with (\x. T)
      (subtopology euclidean k,subtopology euclidean (sphere(vec 0:real^2,&1)))
      ((\x. inv(norm(x - (p:real^1->real^2) (vec 0))) % (x - p (vec 0))) o
       (h0:real^M->real^2))
      ((\x. inv(norm(x - p (vec 1))) % (x - p (vec 1))) o (h1:real^M->real^2))`
  ASSUME_TAC THENL
   [SIMP_TAC[HOMOTOPIC_WITH_EUCLIDEAN_ALT] THEN
    EXISTS_TAC `\z:real^(1,M)finite_sum.
       inv(norm((h:real^(1,M)finite_sum->real^2) z - (p:real^1->real^2)(fstcart z))) %
       (h z - p(fstcart z))` THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART] THEN
    EXPAND_TAC "h0" THEN EXPAND_TAC "h1" THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
        REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; NORM_EQ_0;
                    VECTOR_SUB_EQ] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE; ASM_MESON_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      REWRITE_TAC[IMAGE_FSTCART_PCROSS] THEN ASM_MESON_TAC[CONTINUOUS_ON_EMPTY];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; IN_SPHERE_0;
                  FSTCART_PASTECART] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN
      USE_THEN "miss" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_with (\x. T)
      (subtopology euclidean k,subtopology euclidean (sphere(vec 0:real^2,&1)))
      ((\x. inv(norm(x - (p:real^1->real^2) (vec 1))) % (x - p (vec 1))) o
       (h1:real^M->real^2))
      ((\x:real^2. (c:real^2)) o (h0:real^M->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
    EXISTS_TAC `(\x. inv(norm(x - (p:real^1->real^2) (vec 0))) % (x - p (vec 0))) o
                (h0:real^M->real^2)` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^M->bool`; `h1:real^M->real^2`; `s1:real^2->bool`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "h1" THEN REWRITE_TAC[] THEN
    USE_THEN "inj" (fun th -> REWRITE_TAC[th]);
    DISCH_THEN(X_CHOOSE_THEN `g1:real^2->real^M` (STRIP_ASSUME_TAC o
      REWRITE_RULE[homeomorphism]))] THEN
  MP_TAC(ISPECL
   [`(\x. inv(norm(x - (p:real^1->real^2) (vec 1))) % (x - p (vec 1))) o
     (h1:real^M->real^2)`;
    `(\x:real^2. (c:real^2)) o (h0:real^M->real^2)`; `g1:real^2->real^M`;
    `s1:real^2->bool`; `k:real^M->bool`; `sphere(vec 0:real^2,&1)`]
    HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`((\x. inv(norm(x - (p:real^1->real^2) (vec 1))) % (x - p (vec 1))) o
      (h1:real^M->real^2)) o (g1:real^2->real^M)`;
    `((\x:real^2. (c:real^2)) o (h0:real^M->real^2)) o (g1:real^2->real^M)`] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Consequences of a collar Q of the level c of a compact set B.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_COLLAR_IMAGE = prove
 (`!(B:real^3->bool) c d0 Q.
     moi_s5b_collar B c d0 Q
     ==> IMAGE (\p. Q (fstcart p) (drop(sndcart p)))
               ({x | x IN B /\ x$3 = c} PCROSS interval[--vec 1,vec 1]) =
         {z | z IN B /\ abs(z$3 - c) <= d0}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5b_collar] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM;
              IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `v:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `drop v`] o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "x" &&
          is_conj(rand(snd(strip_forall(concl th)))) &&
          length(conjuncts(lhand(snd(strip_forall(concl th))))) = 3
      with Failure _ -> false)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `(c + t * d) - c = t * d`; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs d0 = d0` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "z" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `t:real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`x:real^3`; `lift t`] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S5B_COLLAR_HOMEO = prove
 (`!(B:real^3->bool) c d0 Q.
     compact B /\ moi_s5b_collar B c d0 Q
     ==> ?P'. homeomorphism
                ({x | x IN B /\ x$3 = c} PCROSS interval[--vec 1,vec 1],
                 {z | z IN B /\ abs(z$3 - c) <= d0})
                ((\p. Q (fstcart p) (drop(sndcart p))),P')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  ASM_SIMP_TAC[MOI_S5B_COLLAR_IMAGE] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_collar]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    SUBGOAL_THEN `{x:real^3 | x IN B /\ x$3 = c} = B INTER {x | x$3 = c}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    ASM_REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `v:real^1`; `x':real^3`; `v':real^1`] THEN
  STRIP_TAC THEN REWRITE_TAC[PASTECART_INJ; GSYM DROP_EQ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5B_COLLAR_OPEN = prove
 (`!(B:real^3->bool) c d0 Q k a b.
     compact B /\ moi_s5b_collar B c d0 Q /\
     open_in (subtopology euclidean {x | x IN B /\ x$3 = c}) k /\
     -- &1 <= a /\ a < b /\ b <= &1
     ==> open_in (subtopology euclidean B) {Q x t | x IN k /\ a < t /\ t < b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `c:real`; `d0:real`; `Q:real^3->real->real^3`]
    MOI_S5B_COLLAR_HOMEO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `P':real^3->real^(3,1)finite_sum`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_collar]) THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean {z:real^3 | z IN B /\ abs(z$3 - c) <= d0})
      (IMAGE (\p. (Q:real^3->real->real^3) (fstcart p) (drop(sndcart p)))
             (k PCROSS interval[--vec 1,vec 1]))`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`P':real^3->real^(3,1)finite_sum`;
      `{x:real^3 | x IN B /\ x$3 = c} PCROSS interval[--vec 1:real^1,vec 1]`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_PCROSS THEN
    ASM_REWRITE_TAC[OPEN_IN_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `ow:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ow INTER {z:real^3 | c + a * d0 < z$3} INTER {z | z$3 < c + b * d0}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_INTER THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN
    REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN IMAGE (\p. (Q:real^3->real->real^3) (fstcart p) (drop(sndcart p)))
                         (k PCROSS interval[--vec 1,vec 1]) <=>
               ?x t. x IN k /\ abs t <= &1 /\ z = Q x t`
  (LABEL_TAC "img") THENL
   [GEN_TAC THEN REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
       FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`x:real^3`; `drop y`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`x:real^3`; `lift t`] THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t. x IN k /\ abs t <= &1
          ==> (Q:real^3->real->real^3) x t IN B /\ (Q x t)$3 = c + t * d0`
  (LABEL_TAC "qh") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "x" &&
          is_conj(rand(snd(strip_forall(concl th)))) &&
          length(conjuncts(lhand(snd(strip_forall(concl th))))) = 3
      with Failure _ -> false)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `t:real`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "qh" (MP_TAC o SPECL [`x:real^3`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN {z:real^3 | z IN B /\ abs(z$3 - c) <= d0} INTER ow`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "IMAGE"
        with Failure _ -> false)) THEN
      USE_THEN "img" (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY EXISTS_TAC [`x:real^3`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x < y ==> c + x < c + y`) THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `-- d0 <= a * d0 /\ b * d0 <= d0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPECL [`-- &1`; `a:real`; `d0:real`] REAL_LE_RMUL);
        MP_TAC(SPECL [`b:real`; `&1`; `d0:real`] REAL_LE_RMUL)] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN {z:real^3 | z IN B /\ abs(z$3 - c) <= d0} INTER ow`
    MP_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "IMAGE"
      with Failure _ -> false)) THEN
    USE_THEN "img" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `t:real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`x:real^3`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "qh" (MP_TAC o SPECL [`x:real^3`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `c + a * d0 < (z:real^3)$3` THEN
    UNDISCH_TAC `(z:real^3)$3 < c + b * d0` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `c + x < c + y <=> x < y`] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN REAL_ARITH_TAC]);;

let MOI_S5B_COLLAR_PIECE = prove
 (`!(B:real^3->bool) c d0 Q k (ivl:real^1->bool).
     moi_s5b_collar B c d0 Q /\ k SUBSET {x | x IN B /\ x$3 = c} /\
     ivl SUBSET interval[--vec 1,vec 1]
     ==> {Q x (drop v) | x IN k /\ v IN ivl} =
         IMAGE (\p. Q (fstcart p) (drop(sndcart p))) (k PCROSS ivl) /\
         (\p. Q (fstcart p) (drop(sndcart p))) continuous_on (k PCROSS ivl)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM] THEN
    MESON_TAC[];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_collar]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | x IN B /\ x$3 = c} PCROSS interval[--vec 1:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[]]);;

let MOI_S5B_COLLAR_CONN0 = prove
 (`!(B:real^3->bool) c d0 Q k (ivl:real^1->bool).
     moi_s5b_collar B c d0 Q /\ k SUBSET {x | x IN B /\ x$3 = c} /\
     ivl SUBSET interval[--vec 1,vec 1] /\ connected k /\ connected ivl
     ==> connected {Q x (drop v) | x IN k /\ v IN ivl}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `c:real`; `d0:real`; `Q:real^3->real->real^3`;
                 `k:real^3->bool`; `ivl:real^1->bool`] MOI_S5B_COLLAR_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONNECTED_PCROSS THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_COLLAR_COMPACT0 = prove
 (`!(B:real^3->bool) c d0 Q k (ivl:real^1->bool).
     moi_s5b_collar B c d0 Q /\ k SUBSET {x | x IN B /\ x$3 = c} /\
     ivl SUBSET interval[--vec 1,vec 1] /\ compact k /\ compact ivl
     ==> compact {Q x (drop v) | x IN k /\ v IN ivl}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `c:real`; `d0:real`; `Q:real^3->real->real^3`;
                 `k:real^3->bool`; `ivl:real^1->bool`] MOI_S5B_COLLAR_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_REAL_INTERVALS = prove
 (`!(Q:real^3->real->real^3) k a b.
     {Q x t | x IN k /\ a < t /\ t < b} =
     {Q x (drop v) | x IN k /\ v IN interval(lift a,lift b)} /\
     {Q x t | x IN k /\ a <= t /\ t <= b} =
     {Q x (drop v) | x IN k /\ v IN interval[lift a,lift b]}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
  MESON_TAC[LIFT_DROP]);;

let MOI_S5B_COLLAR_LEVEL = prove
 (`!(B:real^3->bool) c d0 Q t.
     moi_s5b_collar B c d0 Q /\ abs t <= &1
     ==> {x | x IN B /\ x$3 = c + t * d0} =
         IMAGE (\x. Q x t) {x | x IN B /\ x$3 = c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5b_collar] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "z" with Failure _ -> false)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `(c + t * d) - c = t * d`; REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs d0 = d0` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `t':real`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t':real = t` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `t':real`] o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "x" &&
          is_conj(rand(snd(strip_forall(concl th)))) &&
          length(conjuncts(lhand(snd(strip_forall(concl th))))) = 3
      with Failure _ -> false)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `(z:real^3) = Q (x:real^3) (t':real)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_EQ_ADD_LCANCEL; REAL_EQ_MUL_RCANCEL] THEN
    UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "x" &&
          is_conj(rand(snd(strip_forall(concl th)))) &&
          length(conjuncts(lhand(snd(strip_forall(concl th))))) = 3
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S5B_COLLAR_TCONT = prove
 (`!(B:real^3->bool) c d0 Q x.
     moi_s5b_collar B c d0 Q /\ x IN B /\ x$3 = c
     ==> (\v. Q x (drop v)) continuous_on interval[--vec 1,vec 1]`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_collar]) THEN
  SUBGOAL_THEN `(\v. (Q:real^3->real->real^3) x (drop v)) =
                (\p. Q (fstcart p) (drop(sndcart p))) o (\v:real^1. pastecart x v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | x IN B /\ x$3 = c} PCROSS interval[--vec 1:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* The side of a disk E in B at its boundary curve k: of the two halves of   *)
(* a collar of k exactly one lies in E.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_CONN_TWO_OPEN_IN = prove
 (`!(B:real^N->bool) s e1 e2.
     connected s /\ s SUBSET B /\
     open_in (subtopology euclidean B) e1 /\ open_in (subtopology euclidean B) e2 /\
     s SUBSET e1 UNION e2 /\ e1 INTER e2 INTER s = {}
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_OPEN_IN] o check
    (fun th -> try fst(dest_const(rator(concl th))) = "connected"
               with Failure _ -> false)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`s INTER e1:real^N->bool`; `s INTER e2:real^N->bool`]) THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ (~c ==> d) ==> ~(a /\ b /\ c) ==> d`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC `B:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SET_RULE `(e:real^N->bool) SUBSET B ==> B INTER e = e`];
    ASM SET_TAC[]]);;

let MOI_S5B_SIDE_GEN = prove
 (`!(B:real^3->bool) E k A1 A2.
     k SUBSET closure (E DIFF k) /\ closed B /\ closed E /\ E SUBSET B /\
     k SUBSET E /\ ~(k = {}) /\
     open_in (subtopology euclidean B) (E DIFF k) /\ ~(E DIFF k = {}) /\
     (!u. open_in (subtopology euclidean B) u /\ k SUBSET u ==> ~(u SUBSET E)) /\
     connected A1 /\ connected A2 /\ A1 SUBSET B DIFF k /\ A2 SUBSET B DIFF k /\
     open_in (subtopology euclidean B) (A1 UNION A2 UNION k)
     ==> (A1 SUBSET E /\ DISJOINT A2 E) \/ (A2 SUBSET E /\ DISJOINT A1 E)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "nou") STRIP_ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean B) (B DIFF E:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_SIMP_TAC[OPEN_IN_REFL; CLOSED_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!A:real^3->bool. connected A /\ A SUBSET B DIFF k
                 ==> A SUBSET E \/ DISJOINT A E`
  (LABEL_TAC "dich") THENL
   [X_GEN_TAC `A:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`B:real^3->bool`; `A:real^3->bool`; `E DIFF k:real^3->bool`;
                   `B DIFF E:real^3->bool`] MOI_S5B_CONN_TWO_OPEN_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(A:real^3->bool) SUBSET B DIFF k` THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A1:real^3->bool) SUBSET E \/ DISJOINT A1 E` ASSUME_TAC THENL
   [USE_THEN "dich" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(A2:real^3->bool) SUBSET E \/ DISJOINT A2 E` ASSUME_TAC THENL
   [USE_THEN "dich" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(A1:real^3->bool) SUBSET E /\ A2 SUBSET E` THENL
   [USE_THEN "nou" (MP_TAC o SPEC `A1 UNION A2 UNION k:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_SUBSET];
    ALL_TAC] THEN
  ASM_CASES_TAC `DISJOINT (A1:real^3->bool) E /\ DISJOINT A2 E` THENL
   [ALL_TAC;
    UNDISCH_TAC `(A1:real^3->bool) SUBSET E \/ DISJOINT A1 E` THEN
    UNDISCH_TAC `(A2:real^3->bool) SUBSET E \/ DISJOINT A2 E` THEN
    UNDISCH_TAC `~((A1:real^3->bool) SUBSET E /\ A2 SUBSET E)` THEN
    UNDISCH_TAC `~(DISJOINT (A1:real^3->bool) E /\ DISJOINT A2 E)` THEN
    MESON_TAC[]] THEN
  SUBGOAL_THEN `closed(E DIFF k:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN EXISTS_TAC `B:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `E DIFF k:real^3->bool = E INTER (B DIFF (A1 UNION A2 UNION k))`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_INTER THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CLOSED_SUBSET];
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL]];
    ALL_TAC] THEN
  UNDISCH_TAC `(k:real^3->bool) SUBSET closure (E DIFF k)` THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  UNDISCH_TAC `~(k:real^3->bool = {})` THEN SET_TAC[]);;

let MOI_S5B_COMPONENT_OPEN_IN = prove
 (`!(s:real^N->bool) c.
     FINITE (components s) /\ c IN components s
     ==> open_in (subtopology euclidean s) c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c = s DIFF (s DIFF c:real^N->bool)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `c:real^N->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
  ASM_SIMP_TAC[IN_COMPONENTS_UNIONS_COMPLEMENT] THEN
  MATCH_MP_TAC CLOSED_IN_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
  ASM_MESON_TAC[CLOSED_IN_COMPONENT]);;

let MOI_S5B_COMPONENTS_SUBUNION = prove
 (`!(s:real^N->bool) f.
     f SUBSET components s ==> components (UNIONS f) = f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_UNIQUE THEN
  REWRITE_TAC[] THEN X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c:real^N->bool) IN components s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_COMPONENTS_MAXIMAL] o
      check (fun th -> concl th = `(c:real^N->bool) IN components s`)) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS `UNIONS f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]]);;

let MOI_S5B_CELL_INTERIOR_NONEMPTY = prove
 (`!n (e:real^N->bool) j.
     pl_cell_with_boundary n e j /\ 1 <= n ==> ~(e DIFF j = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool`
    (X_CHOOSE_THEN `f:real^N->real^N` (X_CHOOSE_THEN `g:real^N->real^N`
      STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `?z:real^N. z IN relative_interior k` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(relative_interior k:real^N->bool = {})` MP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; SIMPLEX_IMP_CONVEX;
                    SIMPLEX_EMPTY; INT_OF_NUM_EQ; ARITH_RULE `1 <= n ==> ~(n = 0)`;
                    INT_ARITH `~(&n:int = -- &1)`];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN k /\ ~(z IN relative_frontier k)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier; IN_DIFF] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
  EXISTS_TAC `(f:real^N->real^N) z` THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `w:real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SIMPLEX_IMP_CLOSED; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) = z` (fun th -> ASM_MESON_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let MOI_S5B_CELL_BOUNDARY_CLOSURE = prove
 (`!n (e:real^N->bool) j.
     pl_cell_with_boundary n e j ==> j SUBSET closure (e DIFF j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool`
    (X_CHOOSE_THEN `f:real^N->real^N` (X_CHOOSE_THEN `g:real^N->real^N`
      STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `convex(k:real^N->bool) /\ closed k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (closure(relative_interior k)) SUBSET
                closure (e DIFF j)` MP_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    TRANS_TAC SUBSET_TRANS
      `e DIFF IMAGE (f:real^N->real^N) (relative_frontier k)` THEN
    REWRITE_TAC[CLOSURE_SUBSET] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_IMAGE] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN k /\ ~(z IN relative_frontier k)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[relative_frontier; IN_DIFF] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) = z` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[];
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    MATCH_MP_TAC(SET_RULE `(t:real^N->bool) SUBSET e ==> e SUBSET s ==> t SUBSET s`) THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = e` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The model setting: B = phi^-1 b with annulus chart (FF,GG), triangulation *)
(* K with no vertex near the level c, collar Q of width d0, the circles C0;  *)
(* and an innermost inessential circle k = lift c j bounding a disk E in B.  *)
(* ------------------------------------------------------------------------- *)

let moi_s5b_otube = new_definition
 `moi_s5b_otube =
    {x:real^3 | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\
                abs(x$3) < &1 / &32}`;;

let MOI_S5B_OTUBE = prove
 (`open moi_s5b_otube /\ moi_s5b_otube SUBSET moi_s35_ttube /\
   moi_s5b_otube SUBSET interior moi_s35_ttube`,
  SUBGOAL_THEN `open moi_s5b_otube` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `moi_s5b_otube =
      (({x:real^3 | x$1 > &3 / &16} UNION {x | x$1 < --(&3 / &16)}) UNION
       ({x | x$2 > &3 / &16} UNION {x | x$2 < --(&3 / &16)})) INTER
      (({x | x$1 > --(&5 / &16)} INTER {x | x$1 < &5 / &16}) INTER
       ({x | x$2 > --(&5 / &16)} INTER {x | x$2 < &5 / &16}) INTER
       ({x | x$3 > --(&1 / &32)} INTER {x | x$3 < &1 / &32}))`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_s5b_otube; moi_s35_n; EXTENSION; IN_UNION; IN_INTER;
                  IN_ELIM_THM; real_gt] THEN
      GEN_TAC THEN REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC OPEN_INTER ORELSE MATCH_MP_TAC OPEN_UNION THEN
             CONJ_TAC) THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5b_otube SUBSET moi_s35_ttube` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5b_otube; moi_s35_ttube; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[]);;

let moi_s5b_mset = new_definition
 `moi_s5b_mset (B:real^3->bool) (K:(real^3->bool)->bool) (FF:real^2->real^3)
               (GG:real^3->real^2) (Q:real^3->real->real^3) c d0 <=>
    pl_homeomorphism
      (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1]),B) (FF,GG) /\
    FINITE K /\ simplicial_complex K /\ UNIONS K = B /\
    (!s. s IN K ==> aff_dim s <= &2) /\
    (!v. {v} IN K ==> d0 < abs(v$3 - c)) /\
    moi_s5b_collar B c d0 Q /\
    {x | x IN B /\ abs(x$3 - c) <= d0} SUBSET moi_s5b_otube /\
    DISJOINT
      (IMAGE FF (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
       IMAGE FF (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])))
      moi_s35_ttube /\
    abs c <= &1 / &512 /\ d0 <= &1 / &64 /\
    B SUBSET interior moi_s35_stube /\
    FINITE (components {x | x IN B /\ x$3 = c}) /\
    (!k. k IN components {x | x IN B /\ x$3 = c}
         ==> ?j:real^2->bool. pl_sphere 1 j /\ k = IMAGE (moi_s35_lift c) j) /\
    {x | x IN B /\ x$3 = c} SUBSET
    {x | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}`;;

let moi_s5b_kset = new_definition
 `moi_s5b_kset (B:real^3->bool) c (k:real^3->bool) (j:real^2->bool)
               (E:real^3->bool) <=>
    k IN components {x | x IN B /\ x$3 = c} /\ pl_sphere 1 j /\
    k = IMAGE (moi_s35_lift c) j /\
    (!x. x IN B /\ x$3 = c ==> ~(moi_s5b_proj x IN inside j)) /\
    (!y. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN outside j) /\
    (!y. &5 / &16 <= max (abs(y$1)) (abs(y$2)) ==> y IN outside j) /\
    pl_cell_with_boundary 2 E k /\ E SUBSET B`;;

let MOI_S5B_MSET_BASIC = prove
 (`!B K FF GG Q c d0.
     moi_s5b_mset B K FF GG Q c d0
     ==> compact B /\ &0 < d0 /\ compact {x:real^3 | x IN B /\ x$3 = c} /\
         {x:real^3 | x IN B /\ x$3 = c} SUBSET moi_s5b_otube /\
         pl_polyhedron B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5b_mset] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(B:real^3->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
        try fst(dest_const(rator(rator(concl th)))) = "pl_homeomorphism"
        with Failure _ -> false)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try rhs(concl th) = `B:real^3->bool` &&
          fst(dest_const(fst(strip_comb(lhs(concl th))))) = "IMAGE"
      with Failure _ -> false)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOI_S5B_A0_FACTS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s5b_collar]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `{x:real^3 | x IN B /\ x$3 = c} = B INTER {x | x$3 = c}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    ASM_REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [TRANS_TAC SUBSET_TRANS `{x:real^3 | x IN B /\ abs(x$3 - c) <= d0}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s5b_collar]) THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN ASM_MESON_TAC[]]);;

let MOI_S5B_CELL_COMPACT = prove
 (`!n (e:real^N->bool) j.
     pl_cell_with_boundary n e j ==> compact e /\ j SUBSET e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool`
    (X_CHOOSE_THEN `f:real^N->real^N` (X_CHOOSE_THEN `g:real^N->real^N`
      STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try rhs(concl th) = `e:real^N->bool` with Failure _ -> false)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try rhs(concl th) = `e:real^N->bool` with Failure _ -> false)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]]);;

let MOI_S5B_KSET_BASIC = prove
 (`!B K FF GG Q c d0 k j E.
     moi_s5b_mset B K FF GG Q c d0 /\ moi_s5b_kset B c k j E
     ==> k SUBSET {x:real^3 | x IN B /\ x$3 = c} /\ connected k /\ ~(k = {}) /\
         compact k /\
         open_in (subtopology euclidean {x | x IN B /\ x$3 = c}) k /\
         compact E /\ k SUBSET E /\ ~(E DIFF k = {}) /\
         k SUBSET closure (E DIFF k) /\
         open_in (subtopology euclidean B) (E DIFF k) /\
         (!u. open_in (subtopology euclidean B) u /\ k SUBSET u ==> ~(u SUBSET E)) /\
         DISJOINT E
          (IMAGE FF (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
           IMAGE FF (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) /\
         (!j'. pl_sphere 1 j' /\ j' SUBSET E
               ==> ?d. pl_cell_with_boundary 2 d j' /\ d SUBSET B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_MSET_BASIC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_kset]) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try lhs(concl th) = `k:real^3->bool` with Failure _ -> false)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_mset]) THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c} /\
                connected k /\ ~(k = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED;
                  IN_COMPONENTS_NONEMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2`; `E:real^3->bool`; `k:real^3->bool`] MOI_S5B_CELL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT THEN
    EXISTS_TAC `{x:real^3 | x IN B /\ x$3 = c}` THEN
    ASM_SIMP_TAC[CLOSED_IN_COMPONENT];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_COMPONENT_OPEN_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_CELL_INTERIOR_NONEMPTY THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_CELL_BOUNDARY_CLOSURE THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`B:real^3->bool`;
    `IMAGE (FF:real^2->real^3)
       (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`;
    `IMAGE (FF:real^2->real^3)
       (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`;
    `FF:real^2->real^3`; `GG:real^3->real^2`; `E:real^3->bool`; `k:real^3->bool`]
   MOI_S5B_ANNULUS_CELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!t:real^3->bool. k SUBSET t /\ DISJOINT a t ==> DISJOINT k a`) THEN
    EXISTS_TAC `moi_s35_ttube` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC SUBSET_TRANS `{x:real^3 | x IN B /\ x$3 = c}` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC SUBSET_TRANS `moi_s5b_otube` THEN
    ASM_REWRITE_TAC[MOI_S5B_OTUBE];
    SIMP_TAC[]]);;

let MOI_S5B_COLLAR_CONN_OPEN = prove
 (`!(B:real^3->bool) c d0 Q k a b.
     moi_s5b_collar B c d0 Q /\ k SUBSET {x | x IN B /\ x$3 = c} /\
     connected k /\ -- &1 <= a /\ b <= &1
     ==> connected {Q x t | x IN k /\ a < t /\ t < b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_S5B_REAL_INTERVALS] THEN
  MATCH_MP_TAC MOI_S5B_COLLAR_CONN0 THEN
  MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `c:real`; `d0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL] THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
  UNDISCH_TAC `-- &1 <= a` THEN UNDISCH_TAC `b <= &1` THEN REAL_ARITH_TAC);;

let MOI_S5B_COLLAR_OFF = prove
 (`!(B:real^3->bool) c d0 Q x t.
     moi_s5b_collar B c d0 Q /\ x IN B /\ x$3 = c /\ abs t <= &1 /\ ~(t = &0)
     ==> Q x t IN B /\ ~((Q x t)$3 = c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5b_collar] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `t:real`] o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "x" &&
          is_conj(rand(snd(strip_forall(concl th)))) &&
          length(conjuncts(lhand(snd(strip_forall(concl th))))) = 3
      with Failure _ -> false)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ARITH `c + x = c <=> x = &0`; REAL_ENTIRE] THEN
  UNDISCH_TAC `&0 < d0` THEN UNDISCH_TAC `~(t = &0)` THEN REAL_ARITH_TAC);;

let MOI_S5B_SIDE_MODEL = prove
 (`!B K FF GG Q c d0 k j E.
     moi_s5b_mset B K FF GG Q c d0 /\ moi_s5b_kset B c k j E
     ==> ?s. (s = &1 \/ s = -- &1) /\
             (!x u. x IN k /\ &0 < u /\ u < &1 ==> Q x (s * u) IN E) /\
             (!x u. x IN k /\ -- &1 < u /\ u < &0 ==> ~(Q x (s * u) IN E))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
                 `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
                 `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`]
    MOI_S5B_KSET_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_MSET_BASIC) THEN
  SUBGOAL_THEN `moi_s5b_collar B c d0 (Q:real^3->real->real^3) /\ E SUBSET B`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_s5b_mset; moi_s5b_kset]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t. x IN k /\ abs t <= &1 /\ ~(t = &0)
          ==> (Q:real^3->real->real^3) x t IN B DIFF k`
  (LABEL_TAC "off") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`B:real^3->bool`; `c:real`; `d0:real`; `Q:real^3->real->real^3`;
                   `x:real^3`; `t:real`] MOI_S5B_COLLAR_OFF) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `E:real^3->bool`; `k:real^3->bool`;
                 `{(Q:real^3->real->real^3) x t | x IN k /\ &0 < t /\ t < &1}`;
                 `{(Q:real^3->real->real^3) x t | x IN k /\ -- &1 < t /\ t < &0}`]
    MOI_S5B_SIDE_GEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5B_COLLAR_CONN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `c:real`; `d0:real`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_S5B_COLLAR_CONN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `c:real`; `d0:real`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `t < &1` THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `-- &1 < t` THEN UNDISCH_TAC `t < &0` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN
       `{(Q:real^3->real->real^3) x t | x IN k /\ &0 < t /\ t < &1} UNION
        {Q x t | x IN k /\ -- &1 < t /\ t < &0} UNION k =
        {Q x t | x IN k /\ -- &1 < t /\ t < &1}`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `!x. x IN k ==> (Q:real^3->real->real^3) x (&0) = x`
        ASSUME_TAC THENL
         [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
          UNDISCH_TAC `moi_s5b_collar B c d0 (Q:real^3->real->real^3)` THEN
          REWRITE_TAC[moi_s5b_collar] THEN
          DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
        EQ_TAC THENL
         [MESON_TAC[REAL_ARITH `&0 < t /\ t < &1 ==> -- &1 < t /\ t < &1`;
                    REAL_ARITH `-- &1 < t /\ t < &0 ==> -- &1 < t /\ t < &1`;
                    REAL_ARITH `-- &1 < &0 /\ &0 < &1`;
                    ASSUME `!x. x IN k ==> (Q:real^3->real->real^3) x (&0) = x`];
          MESON_TAC[REAL_ARITH `-- &1 < t /\ t < &1
                       ==> (&0 < t /\ t < &1) \/ (-- &1 < t /\ t < &0) \/ t = &0`;
                    ASSUME `!x. x IN k ==> (Q:real^3->real->real^3) x (&0) = x`]];
        MATCH_MP_TAC MOI_S5B_COLLAR_OPEN THEN
        MAP_EVERY EXISTS_TAC [`c:real`; `d0:real`] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; SET_RULE
    `DISJOINT (s:real^3->bool) t <=> !x. x IN s ==> ~(x IN t)`] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_MUL_LID] THEN CONJ_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `-- &1` THEN
    REWRITE_TAC[REAL_ARITH `-- &1 * u = --u`] THEN CONJ_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      free_in `u:real` (concl th) && not(is_forall(concl th))))) THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The enlarged disk E' = E plus the collar strip of k on the side away     *)
(* from E, down to the pushed curve k' = Q(k, -s/2).                        *)
(* ------------------------------------------------------------------------- *)

let moi_s5b_ep = new_definition
 `moi_s5b_ep (Q:real^3->real->real^3) s k E =
    E UNION {Q x (s * u) | x IN k /\ -- (&1 / &2) <= u /\ u <= &0}`;;

let moi_s5b_kp = new_definition
 `moi_s5b_kp (Q:real^3->real->real^3) s k = IMAGE (\x. Q x (s * --(&1 / &2))) k`;;

let MOI_S5B_SIDE_FLIP = prove
 (`!(Q:real^3->real->real^3) k a b.
     {Q x (-- &1 * u) | x IN k /\ a < u /\ u < b} =
     {Q x t | x IN k /\ --b < t /\ t < --a} /\
     {Q x (-- &1 * u) | x IN k /\ a <= u /\ u <= b} =
     {Q x t | x IN k /\ --b <= t /\ t <= --a} /\
     {Q x (&1 * u) | x IN k /\ a < u /\ u < b} =
     {Q x t | x IN k /\ a < t /\ t < b} /\
     {Q x (&1 * u) | x IN k /\ a <= u /\ u <= b} =
     {Q x t | x IN k /\ a <= t /\ t <= b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `u0:real` STRIP_ASSUME_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`x0:real^3`; `--u0:real`];
    MAP_EVERY EXISTS_TAC [`x0:real^3`; `--u0:real`];
    MAP_EVERY EXISTS_TAC [`x0:real^3`; `--u0:real`];
    MAP_EVERY EXISTS_TAC [`x0:real^3`; `--u0:real`]] THEN
  ASM_REWRITE_TAC[REAL_ARITH `-- &1 * u = --u`; REAL_NEG_NEG] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

let MOI_S5B_SIDE_OPEN = prove
 (`!(B:real^3->bool) c d0 Q k s a b.
     compact B /\ moi_s5b_collar B c d0 Q /\
     open_in (subtopology euclidean {x | x IN B /\ x$3 = c}) k /\
     (s = &1 \/ s = -- &1) /\ -- &1 <= a /\ a < b /\ b <= &1
     ==> open_in (subtopology euclidean B) {Q x (s * u) | x IN k /\ a < u /\ u < b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[MOI_S5B_SIDE_FLIP] THEN MATCH_MP_TAC MOI_S5B_COLLAR_OPEN THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `d0:real`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S5B_SIDE_CONN = prove
 (`!(B:real^3->bool) c d0 Q k s a b.
     moi_s5b_collar B c d0 Q /\ k SUBSET {x | x IN B /\ x$3 = c} /\
     connected k /\ (s = &1 \/ s = -- &1) /\ -- &1 <= a /\ b <= &1
     ==> connected {Q x (s * u) | x IN k /\ a < u /\ u < b} /\
         connected {Q x (s * u) | x IN k /\ a <= u /\ u <= b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[MOI_S5B_SIDE_FLIP; REAL_MUL_LID] THEN REWRITE_TAC[MOI_S5B_REAL_INTERVALS] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_S5B_COLLAR_CONN0 THEN
  MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `c:real`; `d0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL] THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
  UNDISCH_TAC `-- &1 <= a` THEN UNDISCH_TAC `b <= &1` THEN REAL_ARITH_TAC);;

let MOI_S5B_SIDE_COMPACT = prove
 (`!(B:real^3->bool) c d0 Q k s a b.
     moi_s5b_collar B c d0 Q /\ k SUBSET {x | x IN B /\ x$3 = c} /\
     compact k /\ (s = &1 \/ s = -- &1) /\ -- &1 <= a /\ b <= &1
     ==> compact {Q x (s * u) | x IN k /\ a <= u /\ u <= b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[MOI_S5B_SIDE_FLIP; REAL_MUL_LID] THEN REWRITE_TAC[MOI_S5B_REAL_INTERVALS] THEN
  MATCH_MP_TAC MOI_S5B_COLLAR_COMPACT0 THEN
  MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `c:real`; `d0:real`] THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
  UNDISCH_TAC `-- &1 <= a` THEN UNDISCH_TAC `b <= &1` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The setting with the side s chosen; facts about the side collar          *)
(* Q x (s * u) and about E' = moi_s5b_ep Q s k E, k' = moi_s5b_kp Q s k.     *)
(* ------------------------------------------------------------------------- *)

let moi_s5b_setting = new_definition
 `moi_s5b_setting B K FF GG (Q:real^3->real->real^3) c d0 k j E s <=>
    moi_s5b_mset B K FF GG Q c d0 /\ moi_s5b_kset B c k j E /\
    (s = &1 \/ s = -- &1) /\
    (!x u. x IN k /\ &0 < u /\ u < &1 ==> Q x (s * u) IN E) /\
    (!x u. x IN k /\ -- &1 < u /\ u < &0 ==> ~(Q x (s * u) IN E))`;;

let MOI_S5B_SETTING_EXISTS = prove
 (`!B K FF GG Q c d0 k j E.
     moi_s5b_mset B K FF GG Q c d0 /\ moi_s5b_kset B c k j E
     ==> ?s. moi_s5b_setting B K FF GG Q c d0 k j E s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5B_SIDE_MODEL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[moi_s5b_setting]);;

let MOI_S5B_UNIT_S = prove
 (`!s. s = &1 \/ s = -- &1 ==> abs s = &1 /\ ~(s = &0) /\ s * s = &1`,
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC);;

let MOI_S5B_SETTING_BASIC = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> compact B /\ &0 < d0 /\ moi_s5b_collar B c d0 Q /\ E SUBSET B /\
         compact {x:real^3 | x IN B /\ x$3 = c} /\
         k SUBSET {x:real^3 | x IN B /\ x$3 = c} /\ connected k /\ ~(k = {}) /\
         compact k /\ open_in (subtopology euclidean {x | x IN B /\ x$3 = c}) k /\
         compact E /\ k SUBSET E /\ ~(E DIFF k = {}) /\
         open_in (subtopology euclidean B) (E DIFF k) /\
         abs s = &1 /\ ~(s = &0) /\
         (!x u. x IN B /\ x$3 = c /\ abs u <= &1
                ==> Q x (s * u) IN B /\ (Q x (s * u))$3 = c + s * u * d0 /\
                    abs((Q x (s * u))$3 - c) <= d0) /\
         (!x u x' u'. x IN B /\ x$3 = c /\ abs u <= &1 /\
                      x' IN B /\ x'$3 = c /\ abs u' <= &1 /\
                      Q x (s * u) = Q x' (s * u') ==> x = x' /\ u = u') /\
         (!x. x IN B /\ x$3 = c ==> Q x (s * &0) = x) /\
         (!x u. x IN k /\ &0 < u /\ u < &1 ==> Q x (s * u) IN E) /\
         (!x u. x IN k /\ -- &1 < u /\ u < &0 ==> ~(Q x (s * u) IN E))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5b_setting] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
                 `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
                 `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`]
    MOI_S5B_KSET_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_MSET_BASIC) THEN
  SUBGOAL_THEN `moi_s5b_collar B c d0 (Q:real^3->real->real^3) /\ E SUBSET B`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_s5b_mset; moi_s5b_kset]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs s = &1 /\ ~(s = &0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S5B_UNIT_S]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_collar] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "moi_s5b_collar"
                     with Failure _ -> false)) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(s * u) <= &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_LID]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `s * u:real`] o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "x" &&
          is_conj(rand(snd(strip_forall(concl th)))) &&
          length(conjuncts(lhand(snd(strip_forall(concl th))))) = 3
      with Failure _ -> false)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_ARITH `(c + x) - c = x`; REAL_ABS_MUL] THEN
    UNDISCH_TAC `abs s = &1` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    SUBGOAL_THEN `abs d0 = d0` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `s * u:real`; `x':real^3`; `s * u':real`] o
      check (fun th -> try length(fst(strip_forall(concl th))) = 4
                       with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_LID; REAL_EQ_MUL_LCANCEL];
    REWRITE_TAC[REAL_MUL_RZERO] THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S5B_EP_SETS = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> moi_s5b_kp Q s k SUBSET moi_s5b_ep Q s k E /\
         DISJOINT E (moi_s5b_kp Q s k) /\
         moi_s5b_ep Q s k E SUBSET B /\
         compact (moi_s5b_ep Q s k E) /\
         moi_s5b_ep Q s k E DIFF moi_s5b_kp Q s k =
         (E DIFF k) UNION {Q x (s * u) | x IN k /\ --(&1 / &2) < u /\ u < &1}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  SUBGOAL_THEN `!x:real^3. x IN k ==> x IN B /\ x$3 = c` (LABEL_TAC "k0") THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN k ==> ~((Q:real^3->real->real^3) x (s * --(&1 / &2)) IN E)`
  (LABEL_TAC "kpE") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!x u. x IN k /\ -- &1 < u /\ u < &0 ==> ~((Q:real^3->real->real^3) x (s * u) IN E)` THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `--(&1 / &2)`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_s5b_ep; moi_s5b_kp] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^3`; `--(&1 / &2)`] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
    USE_THEN "kpE" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> try lhs(concl th) = `z:real^3`
                                                 with Failure _ -> false)) THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    USE_THEN "k0" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `u:real`] o check (fun th ->
      try length(fst(strip_forall(concl th))) = 2 &&
          length(conjuncts(lhand(snd(strip_forall(concl th))))) = 3 &&
          length(conjuncts(rand(snd(strip_forall(concl th))))) = 3
      with Failure _ -> false)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `--(&1 / &2) <= u` THEN UNDISCH_TAC `u <= &0` THEN
      REAL_ARITH_TAC;
      SIMP_TAC[]];
    MATCH_MP_TAC COMPACT_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S5B_SIDE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `c:real`; `d0:real`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [UNDISCH_TAC `abs s = &1` THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THENL
     [ASM_CASES_TAC `(z:real^3) IN k` THENL
       [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`z:real^3`; `&0`] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "k0" (MP_TAC o SPEC `z:real^3`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        UNDISCH_TAC `!x. x IN B /\ x$3 = c ==> (Q:real^3->real->real^3) x (s * &0) = x` THEN
        DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[];
        DISJ1_TAC THEN ASM_REWRITE_TAC[]];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^3`; `u:real`] THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `u <= &0` THEN REAL_ARITH_TAC] THEN
      ASM_CASES_TAC `u = --(&1 / &2)` THENL
       [UNDISCH_TAC `~(?x':real^3. (z:real^3) =
            (Q:real^3->real->real^3) x' (s * --(&1 / &2)) /\ x' IN k)` THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^3` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `--(&1 / &2) <= u` THEN UNDISCH_TAC `~(u = --(&1 / &2))` THEN
        REAL_ARITH_TAC]];
    DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THENL
     [ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      USE_THEN "kpE" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^3) IN E` THEN ASM_REWRITE_TAC[];
      CONJ_TAC THENL
       [ASM_CASES_TAC `&0 < u` THENL
         [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `!x u. x IN k /\ &0 < u /\ u < &1
                         ==> (Q:real^3->real->real^3) x (s * u) IN E` THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^3`; `u:real`] THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `--(&1 / &2) < u` THEN UNDISCH_TAC `~(&0 < u)` THEN
          REAL_ARITH_TAC];
        REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
        USE_THEN "k0" (MP_TAC o SPEC `x:real^3`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        USE_THEN "k0" (MP_TAC o SPEC `y:real^3`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        UNDISCH_TAC `!x u x' u'. x IN B /\ x$3 = c /\ abs u <= &1 /\
                      x' IN B /\ x'$3 = c /\ abs u' <= &1 /\
                      (Q:real^3->real->real^3) x (s * u) = Q x' (s * u')
                      ==> x = x' /\ u = u'` THEN
        DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`; `y:real^3`; `--(&1 / &2)`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [REAL_ARITH_TAC; ASM_MESON_TAC[]]] THEN
          UNDISCH_TAC `--(&1 / &2) < u` THEN UNDISCH_TAC `u < &1` THEN REAL_ARITH_TAC;
          UNDISCH_TAC `--(&1 / &2) < u` THEN REAL_ARITH_TAC]]]]);;

(* ------------------------------------------------------------------------- *)
(* E' is a PL disk with boundary k' (ANNULUS_CRIT in the model annulus).    *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_EP_OPEN = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> open_in (subtopology euclidean B)
                 (moi_s5b_ep Q s k E DIFF moi_s5b_kp Q s k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_EP_SETS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S5B_SIDE_OPEN THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `d0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [UNDISCH_TAC `abs s = &1` THEN REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let MOI_S5B_EP_ENDS = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> DISJOINT (moi_s5b_ep Q s k E)
          (IMAGE FF (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
           IMAGE FF (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
                 `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
                 `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`]
    MOI_S5B_KSET_BASIC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_s5b_setting]; STRIP_TAC] THEN
  SUBGOAL_THEN `{x:real^3 | x IN B /\ abs(x$3 - c) <= d0} SUBSET moi_s5b_otube /\
     DISJOINT
      (IMAGE FF (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
       IMAGE FF (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])))
      moi_s35_ttube` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s5b_setting; moi_s5b_mset]; ALL_TAC] THEN
  REWRITE_TAC[moi_s5b_ep; DISJOINT_UNION] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!t. s SUBSET t /\ DISJOINT a t ==> DISJOINT (s:real^3->bool) a`) THEN
  EXISTS_TAC `moi_s35_ttube` THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC SUBSET_TRANS `moi_s5b_otube` THEN REWRITE_TAC[MOI_S5B_OTUBE] THEN
  TRANS_TAC SUBSET_TRANS `{x:real^3 | x IN B /\ abs(x$3 - c) <= d0}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `u:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN B /\ x$3 = c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
    UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                ==> (Q:real^3->real->real^3) x (s * u) IN B /\
                    (Q x (s * u))$3 = c + s * u * d0 /\
                    abs((Q x (s * u))$3 - c) <= d0` THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `--(&1 / &2) <= u` THEN
    UNDISCH_TAC `u <= &0` THEN REAL_ARITH_TAC;
    SIMP_TAC[]]);;

let MOI_S5B_EP_CLOSURE = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> moi_s5b_kp Q s k SUBSET closure (B DIFF moi_s5b_ep Q s k E)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  REWRITE_TAC[moi_s5b_kp; SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN B /\ x$3 = c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
    UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s = &1 \/ s = -- &1` ASSUME_TAC THENL
   [UNDISCH_TAC `abs s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v:real^1. (Q:real^3->real->real^3) x (s * drop v)) continuous_on
    interval[--vec 1:real^1,vec 1]`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\v:real^1. (Q:real^3->real->real^3) x (s * drop v)) =
                  (\w. Q x (drop w)) o (\v. s % v)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
      REWRITE_TAC[LINEAR_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[--vec 1:real^1,vec 1]` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5B_COLLAR_TCONT THEN
        MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `c:real`; `d0:real`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_CMUL; DROP_NEG;
                    DROP_VEC] THEN
        X_GEN_TAC `v:real^1` THEN
        UNDISCH_TAC `s = &1 \/ s = -- &1` THEN
        DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\v:real^1. (Q:real^3->real->real^3) x (s * drop v))
          (closure (interval(lift(-- &1),lift(--(&1 / &2))))) SUBSET
    closure (B DIFF moi_s5b_ep Q s k E)`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[--vec 1:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[CLOSURE_OPEN_INTERVAL; INTERVAL_NE_EMPTY_1; LIFT_DROP;
               REAL_ARITH `-- &1 < --(&1 / &2)`] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP; DROP_NEG; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS `B DIFF moi_s5b_ep Q s k E:real^3->bool` THEN
    REWRITE_TAC[CLOSURE_SUBSET] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP; IN_DIFF;
                moi_s5b_ep; IN_UNION; IN_ELIM_THM;
                TAUT `~(a \/ b) <=> ~a /\ ~b`; NOT_EXISTS_THM] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                  ==> (Q:real^3->real->real^3) x (s * u) IN B /\
                      (Q x (s * u))$3 = c + s * u * d0 /\
                      abs((Q x (s * u))$3 - c) <= d0` THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `drop v`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `-- &1 < drop v` THEN
      UNDISCH_TAC `drop v < --(&1 / &2)` THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `!x u. x IN k /\ -- &1 < u /\ u < &0
                    ==> ~((Q:real^3->real->real^3) x (s * u) IN E)` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `drop v < --(&1 / &2)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN B /\ y$3 = c` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
      UNDISCH_TAC `(y:real^3) IN k` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!x u x' u'. x IN B /\ x$3 = c /\ abs u <= &1 /\
                      x' IN B /\ x'$3 = c /\ abs u' <= &1 /\
                      (Q:real^3->real->real^3) x (s * u) = Q x' (s * u')
                      ==> x = x' /\ u = u'` THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `drop v`; `y:real^3`; `w:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [UNDISCH_TAC `-- &1 < drop v` THEN UNDISCH_TAC `drop v < --(&1 / &2)` THEN
      UNDISCH_TAC `--(&1 / &2) <= w` THEN UNDISCH_TAC `w <= &0` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `drop v < --(&1 / &2)` THEN UNDISCH_TAC `--(&1 / &2) <= w` THEN
      REAL_ARITH_TAC];
    SIMP_TAC[CLOSURE_OPEN_INTERVAL; INTERVAL_NE_EMPTY_1; LIFT_DROP;
             REAL_ARITH `-- &1 < --(&1 / &2)`] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `lift(--(&1 / &2))`) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]]);;

let MOI_S5B_LIFT_LINEAR = prove
 (`!c. moi_s35_lift c =
       (\y. (\y:real^2. vector[y$1; y$2; &0]:real^3) y + vector[&0; &0; c]) /\
       linear (\y:real^2. vector[y$1; y$2; &0]:real^3) /\
       (!y z. (\y:real^2. vector[y$1; y$2; &0]:real^3) y =
              (\y:real^2. vector[y$1; y$2; &0]:real^3) z ==> y = z)`,
  GEN_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_s35_lift] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    SIMP_TAC[CART_EQ; DIMINDEX_3; DIMINDEX_2; FORALL_3; FORALL_2; VECTOR_3]]);;

let MOI_S5B_LIFT_SPHERE = prove
 (`!c j. pl_sphere 1 j ==> pl_sphere 1 (IMAGE (moi_s35_lift c) j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `c:real` MOI_S5B_LIFT_LINEAR) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S5B_SPHERE_AFFINE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_S5B_LIFT_CELL = prove
 (`!c e j. pl_cell_with_boundary 2 e j
           ==> pl_cell_with_boundary 2 (IMAGE (moi_s35_lift c) e)
                                       (IMAGE (moi_s35_lift c) j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `c:real` MOI_S5B_LIFT_LINEAR) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S5B_CELL_AFFINE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_S5B_KP_SPHERE = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> pl_sphere 1 (moi_s5b_kp Q s k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  SUBGOAL_THEN `pl_sphere 1 (k:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `pl_sphere 1 (j:real^2->bool) /\ k = IMAGE (moi_s35_lift c) j`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_s5b_setting; moi_s5b_kset]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S5B_LIFT_SPHERE];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_collar] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "moi_s5b_collar"
                     with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`{x:real^3 | x IN B /\ x$3 = c}`;
                 `\x. (Q:real^3->real->real^3) x (s * --(&1 / &2))`] MOI_S5B_PL_EMBED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `abs s = &1` THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      UNDISCH_TAC `!x u x' u'. x IN B /\ x$3 = c /\ abs u <= &1 /\
                      x' IN B /\ x'$3 = c /\ abs u' <= &1 /\
                      (Q:real^3->real->real^3) x (s * u) = Q x' (s * u')
                      ==> x = x' /\ u = u'` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `--(&1 / &2)`; `y:real^3`; `--(&1 / &2)`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^3`) THEN
  REWRITE_TAC[moi_s5b_kp] THEN MATCH_MP_TAC MOI_S5B_SPHERE_TRANSPORT THEN
  MAP_EVERY EXISTS_TAC
   [`{x:real^3 | x IN B /\ x$3 = c}`;
    `IMAGE (\x. (Q:real^3->real->real^3) x (s * --(&1 / &2))) {x | x IN B /\ x$3 = c}`;
    `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5B_EP_CELL = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> pl_cell_with_boundary 2 (moi_s5b_ep Q s k E) (moi_s5b_kp Q s k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_EP_SETS) THEN
  MATCH_MP_TAC MOI_S5B_ANNULUS_CRIT THEN
  MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `FF:real^2->real^3`; `GG:real^3->real^2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[moi_s5b_setting; moi_s5b_mset];
    MATCH_MP_TAC MOI_S5B_EP_ENDS THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_S5B_KP_SPHERE THEN ASM_MESON_TAC[];
    MP_TAC(SPEC_ALL MOI_S5B_EP_OPEN) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPEC_ALL MOI_S5B_EP_CLOSURE) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(E DIFF k:real^3->bool = {})` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The cap: the planar projection j'' of k' and the planar disk D' at the   *)
(* level c' = c + (s * -1/2) * d0; the Borsuk push keeps the other circles  *)
(* and the inner and outer planar regions outside j''.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_PROJ_FACTS = prove
 (`linear moi_s5b_proj /\
   (!x y:real^3. x$3 = y$3 /\ moi_s5b_proj x = moi_s5b_proj y ==> x = y) /\
   (!x:real^3. max (abs((moi_s5b_proj x)$1)) (abs((moi_s5b_proj x)$2)) =
               moi_s35_n x)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; moi_s5b_proj] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT];
    REWRITE_TAC[moi_s5b_proj] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2] THEN
    MESON_TAC[];
    REWRITE_TAC[moi_s5b_proj; moi_s35_n] THEN SIMP_TAC[VECTOR_2]]);;

let MOI_S5B_PUSH_COLLAR = prove
 (`!B K FF GG Q c d0 k j E s (p:real^1->real^2).
     moi_s5b_setting B K FF GG Q c d0 k j E s /\
     p continuous_on interval[vec 0,vec 1] /\
     (!v z. v IN interval[vec 0,vec 1] /\ z IN k
            ==> ~(moi_s5b_proj (Q z (s * --(&1 / &2) * drop v)) = p v)) /\
     p(vec 0) IN outside j
     ==> p(vec 1) IN outside (IMAGE moi_s5b_proj (moi_s5b_kp Q s k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "miss") ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  SUBGOAL_THEN `IMAGE moi_s5b_proj k = (j:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `k = IMAGE (moi_s35_lift c) j` SUBST1_TAC THENL
     [ASM_MESON_TAC[moi_s5b_setting; moi_s5b_kset];
      REWRITE_TAC[MOI_S5B_PROJ_IMAGE_LIFT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN k ==> x IN B /\ x$3 = c` (LABEL_TAC "k0") THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_collar] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "moi_s5b_collar"
                     with Failure _ -> false)) THEN
  MP_TAC(ISPECL
   [`k:real^3->bool`;
    `\q:real^(1,3)finite_sum. moi_s5b_proj ((Q:real^3->real->real^3) (sndcart q)
                                (s * --(&1 / &2) * drop(fstcart q)))`;
    `p:real^1->real^2`] MOI_S5B_PUSH_OUTSIDE) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; REAL_MUL_RZERO;
              REAL_MUL_RID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\q:real^(1,3)finite_sum. moi_s5b_proj ((Q:real^3->real->real^3) (sndcart q)
                                (s * --(&1 / &2) * drop(fstcart q)))) =
        moi_s5b_proj o (\p. Q (fstcart p) (drop(sndcart p))) o
        (\q. pastecart (sndcart q) ((s * --(&1 / &2)) % fstcart q))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                    DROP_CMUL; REAL_MUL_ASSOC];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
           [SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
            MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
            MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_FSTCART]];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{x:real^3 | x IN B /\ x$3 = c} PCROSS interval[--vec 1:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM] THEN
        MAP_EVERY X_GEN_TAC [`v:real^1`; `z:real^3`] THEN STRIP_TAC THEN
        USE_THEN "k0" (MP_TAC o SPEC `z:real^3`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]] THEN
        DISCH_THEN(K ALL_TAC) THEN
        UNDISCH_TAC `(v:real^1) IN interval[vec 0,vec 1]` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_NEG; DROP_VEC] THEN
        UNDISCH_TAC `abs s = &1` THEN
        DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH
          `abs s = &1 ==> s = &1 \/ s = -- &1`)) THEN REAL_ARITH_TAC];
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MOI_S5B_PROJ_FACTS]];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      USE_THEN "k0" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      USE_THEN "k0" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      UNDISCH_TAC `!x u x' u'. x IN B /\ x$3 = c /\ abs u <= &1 /\
                      x' IN B /\ x'$3 = c /\ abs u' <= &1 /\
                      (Q:real^3->real->real^3) x (s * u) = Q x' (s * u')
                      ==> x = x' /\ u = u'` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `--(&1 / &2)`; `y:real^3`; `--(&1 / &2)`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 MOI_S5B_PROJ_FACTS)) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                  ==> (Q:real^3->real->real^3) x (s * u) IN B /\
                      (Q x (s * u))$3 = c + s * u * d0 /\
                      abs((Q x (s * u))$3 - c) <= d0` THEN
      DISCH_THEN(fun th -> MP_TAC(SPECL [`x:real^3`; `--(&1 / &2)`] th) THEN
                           MP_TAC(SPECL [`y:real^3`; `--(&1 / &2)`] th)) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `abs(--(&1 / &2)) <= &1`] THEN SIMP_TAC[];
      SUBGOAL_THEN `IMAGE (\x. moi_s5b_proj ((Q:real^3->real->real^3) x (&0))) k = j`
        (fun th -> ASM_REWRITE_TAC[th]) THEN
      TRANS_TAC EQ_TRANS `IMAGE moi_s5b_proj k` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        REWRITE_TAC[] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `!x. x IN B /\ x$3 = c ==> (Q:real^3->real->real^3) x (&0) = x` THEN
        DISCH_THEN MATCH_MP_TAC THEN USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM ACCEPT_TAC]];
    REWRITE_TAC[moi_s5b_kp; GSYM IMAGE_o; o_DEF]]);;

let moi_s5b_jpp = new_definition
 `moi_s5b_jpp (Q:real^3->real->real^3) s k = IMAGE moi_s5b_proj (moi_s5b_kp Q s k)`;;

let moi_s5b_cp = new_definition
 `moi_s5b_cp c d0 s = c + (s * --(&1 / &2)) * d0`;;

let moi_s5b_dp = new_definition
 `moi_s5b_dp (Q:real^3->real->real^3) c d0 s k =
    IMAGE (moi_s35_lift (moi_s5b_cp c d0 s))
          (moi_s5b_jpp Q s k UNION inside (moi_s5b_jpp Q s k))`;;

let MOI_S5B_KP_LEVEL = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> !z. z IN moi_s5b_kp Q s k
             ==> z IN B /\ z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  SUBGOAL_THEN `{x:real^3 | x IN B /\ abs(x$3 - c) <= d0} SUBSET moi_s5b_otube`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_s5b_setting; moi_s5b_mset]; ALL_TAC] THEN
  REWRITE_TAC[moi_s5b_kp; FORALL_IN_IMAGE; moi_s5b_cp] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN B /\ x$3 = c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
    UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                  ==> (Q:real^3->real->real^3) x (s * u) IN B /\
                      (Q x (s * u))$3 = c + s * u * d0 /\
                      abs((Q x (s * u))$3 - c) <= d0` THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `--(&1 / &2)`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN
  UNDISCH_TAC `{x:real^3 | x IN B /\ abs(x$3 - c) <= d0} SUBSET moi_s5b_otube` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5B_JPP_SPHERE = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> pl_sphere 1 (moi_s5b_jpp Q s k) /\
         IMAGE (moi_s35_lift (moi_s5b_cp c d0 s)) (moi_s5b_jpp Q s k) =
         moi_s5b_kp Q s k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_KP_SPHERE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_KP_LEVEL) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[moi_s5b_jpp; GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x) (moi_s5b_kp Q s k)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]] THEN
    MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 MOI_S5B_PROJ_LIFT)) THEN
    ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `compact (moi_s5b_kp (Q:real^3->real->real^3) s k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON; PL_POLYHEDRON_IMP_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s5b_kp (Q:real^3->real->real^3) s k`; `moi_s5b_proj`]
    MOI_S5B_PL_EMBED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5B_PL_LINEAR THEN REWRITE_TAC[MOI_S5B_PROJ_FACTS] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 MOI_S5B_PROJ_FACTS)) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^2->real^3`) THEN
  REWRITE_TAC[moi_s5b_jpp] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MOI_S5B_SPHERE1_TO_PLANE) THEN
  MAP_EVERY EXISTS_TAC [`moi_s5b_kp (Q:real^3->real->real^3) s k`;
                        `moi_s5b_proj`; `g:real^2->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5B_JPP_OUTSIDE = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> (!x. x IN B /\ x$3 = c /\ ~(x IN k)
              ==> moi_s5b_proj (Q x (s * --(&1 / &2))) IN
                  outside (moi_s5b_jpp Q s k)) /\
         (!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16 \/
                     &5 / &16 <= max (abs(y$1)) (abs(y$2))
                     ==> y IN outside (moi_s5b_jpp Q s k))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  SUBGOAL_THEN
   `(!x:real^3. x IN B /\ x$3 = c ==> ~(moi_s5b_proj x IN inside j)) /\
    (!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN outside j) /\
    (!y:real^2. &5 / &16 <= max (abs(y$1)) (abs(y$2)) ==> y IN outside j) /\
    (!x:real^3. x$3 = c /\ moi_s5b_proj x IN j ==> x IN k)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s5b_setting]) THEN
    REWRITE_TAC[moi_s5b_kset] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `moi_s5b_proj x` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 MOI_S5B_PROJ_LIFT)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^3 | x IN B /\ abs(x$3 - c) <= d0} SUBSET moi_s5b_otube`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s5b_setting]) THEN
    REWRITE_TAC[moi_s5b_mset] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
                   `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
                   `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`; `s:real`;
                   `\v:real^1. moi_s5b_proj ((Q:real^3->real->real^3) x
                                 (s * --(&1 / &2) * drop v))`]
      MOI_S5B_PUSH_COLLAR) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_MUL_RID; GSYM moi_s5b_jpp] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\v:real^1. moi_s5b_proj ((Q:real^3->real->real^3) x (s * --(&1 / &2) * drop v))) =
        moi_s5b_proj o (\w. Q x (drop w)) o (\v. (s * --(&1 / &2)) % v)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_CMUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
          REWRITE_TAC[LINEAR_ID];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[--vec 1:real^1,vec 1]` THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S5B_COLLAR_TCONT THEN
          MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `c:real`; `d0:real`] THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_CMUL; DROP_NEG;
                      DROP_VEC] THEN
          X_GEN_TAC `v:real^1` THEN
          UNDISCH_TAC `abs s = &1` THEN
          DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH
            `abs s = &1 ==> s = &1 \/ s = -- &1`)) THEN REAL_ARITH_TAC];
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MOI_S5B_PROJ_FACTS]];
      MAP_EVERY X_GEN_TAC [`v:real^1`; `z:real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN B /\ z$3 = c` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
        UNDISCH_TAC `(z:real^3) IN k` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `abs(--(&1 / &2) * drop v) <= &1` ASSUME_TAC THENL
       [UNDISCH_TAC `(v:real^1) IN interval[vec 0,vec 1]` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `~((x:real^3) IN k)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `x:real^3 = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `!x u x' u'. x IN B /\ x$3 = c /\ abs u <= &1 /\
                      x' IN B /\ x'$3 = c /\ abs u' <= &1 /\
                      (Q:real^3->real->real^3) x (s * u) = Q x' (s * u')
                      ==> x = x' /\ u = u'` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `--(&1 / &2) * drop v`; `z:real^3`;
                                 `--(&1 / &2) * drop v`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 MOI_S5B_PROJ_FACTS)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                  ==> (Q:real^3->real->real^3) x (s * u) IN B /\
                      (Q x (s * u))$3 = c + s * u * d0 /\
                      abs((Q x (s * u))$3 - c) <= d0` THEN
      DISCH_THEN(fun th -> MP_TAC(SPECL [`x:real^3`; `--(&1 / &2) * drop v`] th) THEN
                           MP_TAC(SPECL [`z:real^3`; `--(&1 / &2) * drop v`] th)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      UNDISCH_TAC `!x. x IN B /\ x$3 = c ==> (Q:real^3->real->real^3) x (s * &0) = x` THEN
      REWRITE_TAC[REAL_MUL_RZERO] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPEC `j:real^2->bool` INSIDE_OUTSIDE) THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_UNIV] THEN
      DISCH_THEN(MP_TAC o SPEC `moi_s5b_proj x`) THEN
      SUBGOAL_THEN `~(moi_s5b_proj (x:real^3) IN inside j)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `!x:real^3. x IN B /\ x$3 = c ==> ~(moi_s5b_proj x IN inside j)` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^3) IN k` MP_TAC THENL
       [UNDISCH_TAC `!x:real^3. x$3 = c /\ moi_s5b_proj x IN j ==> x IN k` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
                 `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
                 `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`; `s:real`;
                 `\v:real^1. (y:real^2)`] MOI_S5B_PUSH_COLLAR) THEN
  REWRITE_TAC[GSYM moi_s5b_jpp] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`v:real^1`; `z:real^3`] THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN B /\ z$3 = c` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
      UNDISCH_TAC `(z:real^3) IN k` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                  ==> (Q:real^3->real->real^3) x (s * u) IN B /\
                      (Q x (s * u))$3 = c + s * u * d0 /\
                      abs((Q x (s * u))$3 - c) <= d0` THEN
    DISCH_THEN(MP_TAC o SPECL [`z:real^3`; `--(&1 / &2) * drop v`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    SUBGOAL_THEN `(Q:real^3->real->real^3) z (s * --(&1 / &2) * drop v) IN moi_s5b_otube`
    MP_TAC THENL
     [UNDISCH_TAC `{x:real^3 | x IN B /\ abs(x$3 - c) <= d0} SUBSET moi_s5b_otube` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s5b_otube; IN_ELIM_THM] THEN
    SUBGOAL_THEN `moi_s35_n ((Q:real^3->real->real^3) z (s * --(&1 / &2) * drop v)) =
                  max (abs((y:real^2)$1)) (abs(y$2))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 MOI_S5B_PROJ_FACTS))] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        try lhs(concl th) = `moi_s5b_proj ((Q:real^3->real->real^3) z
                                           (s * --(&1 / &2) * drop v))`
        with Failure _ -> false)) THEN
      REFL_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `max (abs((y:real^2)$1)) (abs(y$2)) <= &3 / &16 \/
                 &5 / &16 <= max (abs(y$1)) (abs(y$2))` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `max (abs((y:real^2)$1)) (abs(y$2)) <= &3 / &16 \/
                 &5 / &16 <= max (abs(y$1)) (abs(y$2))` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

let MOI_S5B_JPP_ANNULUS = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> moi_s5b_jpp Q s k UNION inside (moi_s5b_jpp Q s k) SUBSET
         {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
                     max (abs(y$1)) (abs(y$2)) < &5 / &16}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP MOI_S5B_JPP_OUTSIDE) THEN
  DISCH_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  REWRITE_TAC[TAUT `~a /\ ~b <=> ~(a \/ b)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^2) IN outside (moi_s5b_jpp (Q:real^3->real->real^3) s k)`
  MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `moi_s5b_jpp (Q:real^3->real->real^3) s k` OUTSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `moi_s5b_jpp (Q:real^3->real->real^3) s k` INSIDE_INTER_OUTSIDE) THEN
  UNDISCH_TAC `(y:real^2) IN moi_s5b_jpp (Q:real^3->real->real^3) s k UNION
               inside (moi_s5b_jpp Q s k)` THEN
  SET_TAC[]);;

let MOI_S5B_DP_CELL = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> pl_cell_with_boundary 2 (moi_s5b_dp Q c d0 s k) (moi_s5b_kp Q s k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_JPP_SPHERE) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[moi_s5b_dp] THEN
  MATCH_MP_TAC MOI_S5B_LIFT_CELL THEN MATCH_MP_TAC MOI_S5B_PLANE_DISK THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5B_CP_FACTS = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> ~(moi_s5b_cp c d0 s = c) /\ abs(moi_s5b_cp c d0 s) < &1 / &32 /\
         abs(moi_s5b_cp c d0 s - c) <= d0 /\ abs(moi_s5b_cp c d0 s) < &1 / &16`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  SUBGOAL_THEN `abs c <= &1 / &512 /\ d0 <= &1 / &64` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s5b_setting]) THEN
    REWRITE_TAC[moi_s5b_mset] THEN SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s5b_cp] THEN
  UNDISCH_TAC `abs s = &1` THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH
    `abs s = &1 ==> s = &1 \/ s = -- &1`)) THEN
  MAP_EVERY UNDISCH_TAC [`&0 < d0`; `abs c <= &1 / &512`; `d0 <= &1 / &64`] THEN
  REAL_ARITH_TAC);;

let MOI_S5B_DP_LEVEL = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> !z. z IN moi_s5b_dp Q c d0 s k
             ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_JPP_ANNULUS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_CP_FACTS) THEN
  REWRITE_TAC[moi_s5b_dp; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN
  DISCH_TAC THEN REWRITE_TAC[MOI_S5B_PROJ_LIFT; moi_s5b_otube; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s5b_jpp (Q:real^3->real->real^3) s k UNION
               inside (moi_s5b_jpp Q s k) SUBSET
               {y:real^2 | &3 / &16 < max (abs(y$1)) (abs(y$2)) /\
                           max (abs(y$1)) (abs(y$2)) < &5 / &16}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_S5B_DP_B = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> moi_s5b_dp Q c d0 s k INTER B = moi_s5b_kp Q s k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_JPP_SPHERE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_KP_LEVEL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP MOI_S5B_JPP_OUTSIDE) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s5b_dp] THEN
      TRANS_TAC SUBSET_TRANS
       `IMAGE (moi_s35_lift (moi_s5b_cp c d0 s)) (moi_s5b_jpp (Q:real^3->real->real^3) s k)` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[SUBSET_REFL]; MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
      ASM_MESON_TAC[SUBSET]]] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3)$3 = c + (s * --(&1 / &2)) * d0` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s5b_cp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `c:real`; `d0:real`; `Q:real^3->real->real^3`;
                 `s * --(&1 / &2)`] MOI_S5B_COLLAR_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    try lhs(concl th) = `z:real^3` with Failure _ -> false)) THEN
  ASM_CASES_TAC `(x:real^3) IN k` THENL
   [REWRITE_TAC[moi_s5b_kp; IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `!x. x IN B /\ x$3 = c /\ ~(x IN k)
                ==> moi_s5b_proj ((Q:real^3->real->real^3) x (s * --(&1 / &2))) IN
                    outside (moi_s5b_jpp Q s k)` THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(Q:real^3->real->real^3) x (s * --(&1 / &2)) IN moi_s5b_dp Q c d0 s k` THEN
  REWRITE_TAC[moi_s5b_dp; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[MOI_S5B_PROJ_LIFT] THEN
  MP_TAC(ISPEC `moi_s5b_jpp (Q:real^3->real->real^3) s k` OUTSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `moi_s5b_jpp (Q:real^3->real->real^3) s k` INSIDE_INTER_OUTSIDE) THEN
  UNDISCH_TAC `(y:real^2) IN moi_s5b_jpp (Q:real^3->real->real^3) s k UNION
               inside (moi_s5b_jpp Q s k)` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The swapped surface B' = a UNION D' with a = B DIFF (E' DIFF k'): the     *)
(* H-trick homeomorphism B -> B', its triangulation without vertex at the  *)
(* level c, the sphere E' UNION D', and the circles of B' at the level c.   *)
(* ------------------------------------------------------------------------- *)

let moi_s5b_ba = new_definition
 `moi_s5b_ba (B:real^3->bool) Q s k E =
    B DIFF (moi_s5b_ep Q s k E DIFF moi_s5b_kp Q s k)`;;

let moi_s5b_bp = new_definition
 `moi_s5b_bp (B:real^3->bool) Q c d0 s k E =
    moi_s5b_ba B Q s k E UNION moi_s5b_dp Q c d0 s k`;;

let MOI_S5B_CELL_POLYHEDRON = prove
 (`!n (e:real^N->bool) j. pl_cell_with_boundary n e j ==> pl_polyhedron e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `e = IMAGE (f:real^N->real^N) k` SUBST1_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ASM_MESON_TAC[pl_homeomorphism]]);;

let MOI_S5B_BA_FACTS = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> closed (moi_s5b_ba B Q s k E) /\
         moi_s5b_ba B Q s k E INTER moi_s5b_ep Q s k E = moi_s5b_kp Q s k /\
         moi_s5b_ba B Q s k E INTER moi_s5b_dp Q c d0 s k = moi_s5b_kp Q s k /\
         moi_s5b_ba B Q s k E UNION moi_s5b_ep Q s k E = B /\
         moi_s5b_ba B Q s k E = closure (B DIFF moi_s5b_ep Q s k E) /\
         locally_polyhedral (moi_s5b_ba B Q s k E) /\
         moi_s5b_ba B Q s k E SUBSET B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_EP_SETS) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "DIFF"
    with Failure _ -> false)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_OPEN) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_CLOSURE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_B) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_CELL) THEN
  SUBGOAL_THEN `closed (moi_s5b_ba B (Q:real^3->real->real^3) s k E)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5b_ba] THEN MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
    EXISTS_TAC `B:real^3->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5b_ba B (Q:real^3->real->real^3) s k E =
                closure (B DIFF moi_s5b_ep Q s k E)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s5b_ba] THEN
      MATCH_MP_TAC(SET_RULE `(B DIFF e) SUBSET c /\ k SUBSET c
                    ==> B DIFF (e DIFF k) SUBSET (c:real^3->bool)`) THEN
      ASM_REWRITE_TAC[CLOSURE_SUBSET];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[moi_s5b_ba] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[moi_s5b_ba] THEN
    UNDISCH_TAC `moi_s5b_kp (Q:real^3->real->real^3) s k SUBSET moi_s5b_ep Q s k E` THEN
    UNDISCH_TAC `moi_s5b_ep (Q:real^3->real->real^3) s k E SUBSET B` THEN SET_TAC[];
    REWRITE_TAC[moi_s5b_ba] THEN
    UNDISCH_TAC `moi_s5b_dp (Q:real^3->real->real^3) c d0 s k INTER B = moi_s5b_kp Q s k` THEN
    SET_TAC[];
    REWRITE_TAC[moi_s5b_ba] THEN
    UNDISCH_TAC `moi_s5b_ep (Q:real^3->real->real^3) s k E SUBSET B` THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_S5B_CLOSURE_DIFF_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s5b_setting] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                             "moi_s5b_setting" with Failure _ -> false)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S5B_MSET_BASIC) THEN SIMP_TAC[];
      MATCH_MP_TAC MOI_S5B_CELL_POLYHEDRON THEN
      MAP_EVERY EXISTS_TAC [`2`; `moi_s5b_kp (Q:real^3->real->real^3) s k`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[moi_s5b_ba] THEN SET_TAC[]]);;

let MOI_S5B_HSWAP = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> ?h h'. pl_homeomorphism (B,moi_s5b_bp B Q c d0 s k E) (h,h') /\
                (!y. y IN moi_s5b_ba B Q s k E ==> h y = y) /\
                IMAGE h (moi_s5b_ep Q s k E) SUBSET moi_s5b_dp Q c d0 s k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_BA_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_CELL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_CELL) THEN
  MP_TAC(ISPECL [`moi_s5b_ba B (Q:real^3->real->real^3) s k E`;
                 `moi_s5b_ep (Q:real^3->real->real^3) s k E`;
                 `moi_s5b_dp (Q:real^3->real->real^3) c d0 s k`;
                 `moi_s5b_kp (Q:real^3->real->real^3) s k`] MOI_S5B_DISK_REPLACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM moi_s5b_bp] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th ->
    try rhs(concl th) = `B:real^3->bool` &&
        fst(dest_const(fst(strip_comb(lhs(concl th))))) = "UNION"
    with Failure _ -> false)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^3->real^3` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h':real^3->real^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^3) IN moi_s5b_kp Q s k` THENL
   [SUBGOAL_THEN `(x:real^3) IN moi_s5b_ba B Q s k E` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E INTER
                   moi_s5b_ep Q s k E = moi_s5b_kp Q s k` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s5b_kp Q s k` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^3->real^3) x = x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        try is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "y" &&
            can (find_term (fun t -> t = `moi_s5b_ba`)) (concl th)
        with Failure _ -> false)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E INTER
                 moi_s5b_dp Q c d0 s k = moi_s5b_kp Q s k` THEN
    UNDISCH_TAC `(x:real^3) IN moi_s5b_kp Q s k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^3) IN moi_s5b_ba B Q s k E) /\ x IN B` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E INTER
                 moi_s5b_ep Q s k E = moi_s5b_kp Q s k` THEN
    UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E UNION
                 moi_s5b_ep Q s k E = B` THEN
    UNDISCH_TAC `~((x:real^3) IN moi_s5b_kp Q s k)` THEN
    UNDISCH_TAC `(x:real^3) IN moi_s5b_ep Q s k E` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) x IN moi_s5b_bp B Q c d0 s k E` MP_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^3->real^3) B = moi_s5b_bp B Q c d0 s k E` THEN
    UNDISCH_TAC `(x:real^3) IN B` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s5b_bp; IN_UNION] THEN
  MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^3->real^3) ((h:real^3->real^3) x) = h x` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "y" &&
          can (find_term (fun t -> t = `moi_s5b_ba`)) (concl th)
      with Failure _ -> false)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) x = x` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^3->real^3) x IN B` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E SUBSET B` THEN
      UNDISCH_TAC `(h:real^3->real^3) x IN moi_s5b_ba B Q s k E` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!x. x IN B ==> (h':real^3->real^3) ((h:real^3->real^3) x) = x` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^3` th) THEN MP_TAC(SPEC `(h:real^3->real^3) x` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~((x:real^3) IN moi_s5b_ba B Q s k E)` THEN
  UNDISCH_TAC `(h:real^3->real^3) x IN moi_s5b_ba B Q s k E` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5B_KP_OPEN_LEVEL = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> open_in (subtopology euclidean {x | x IN B /\ x$3 = moi_s5b_cp c d0 s})
                 (moi_s5b_kp Q s k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s5b_collar] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "moi_s5b_collar"
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN `abs(s * --(&1 / &2)) <= &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `c:real`; `d0:real`; `Q:real^3->real->real^3`;
                 `s * --(&1 / &2)`] MOI_S5B_COLLAR_LEVEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM moi_s5b_cp] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`{x:real^3 | x IN B /\ x$3 = c}`;
                 `\x. (Q:real^3->real->real^3) x (s * --(&1 / &2))`;
                 `IMAGE (\x. (Q:real^3->real->real^3) x (s * --(&1 / &2)))
                        {x | x IN B /\ x$3 = c}`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      UNDISCH_TAC `!x u x' u'. x IN B /\ x$3 = c /\ abs u <= &1 /\
                      x' IN B /\ x'$3 = c /\ abs u' <= &1 /\
                      (Q:real^3->real->real^3) x (s * u) = Q x' (s * u')
                      ==> x = x' /\ u = u'` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `--(&1 / &2)`; `y:real^3`; `--(&1 / &2)`]) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH `abs(--(&1 / &2)) <= &1`] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^3`) THEN
  REWRITE_TAC[moi_s5b_kp] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `{x:real^3 | x IN B /\ x$3 = c}`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5B_SIGMA_SPHERE = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> moi_s5b_ep Q s k E INTER moi_s5b_dp Q c d0 s k = moi_s5b_kp Q s k /\
         pl_sphere 2 (moi_s5b_ep Q s k E UNION moi_s5b_dp Q c d0 s k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_EP_SETS) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "DIFF"
    with Failure _ -> false)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_B) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_CELL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_CELL) THEN
  SUBGOAL_THEN `moi_s5b_ep (Q:real^3->real->real^3) s k E INTER moi_s5b_dp Q c d0 s k =
                moi_s5b_kp Q s k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `moi_s5b_dp (Q:real^3->real->real^3) c d0 s k`;
                   `moi_s5b_kp (Q:real^3->real->real^3) s k`] MOI_S5B_CELL_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `moi_s5b_dp (Q:real^3->real->real^3) c d0 s k INTER B = moi_s5b_kp Q s k` THEN
    UNDISCH_TAC `moi_s5b_ep (Q:real^3->real->real^3) s k E SUBSET B` THEN
    UNDISCH_TAC `moi_s5b_kp (Q:real^3->real->real^3) s k SUBSET moi_s5b_ep Q s k E` THEN
    UNDISCH_TAC `moi_s5b_kp (Q:real^3->real->real^3) s k SUBSET moi_s5b_dp Q c d0 s k` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5B_DISK_UNION THEN
  EXISTS_TAC `moi_s5b_kp (Q:real^3->real->real^3) s k` THEN ASM_REWRITE_TAC[]);;

let MOI_S5B_BP_TRIANG = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> ?L. simplicial_complex L /\ UNIONS L = moi_s5b_bp B Q c d0 s k E /\
             !v. {v} IN L ==> ~(v$3 = c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_BA_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S5B_HSWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_CP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_KP_LEVEL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_KP_OPEN_LEVEL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_EP_SETS) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "DIFF"
    with Failure _ -> false)) THEN
  SUBGOAL_THEN
   `simplicial_complex (K:(real^3->bool)->bool) /\ UNIONS K = B /\
    (!v. {v} IN K ==> d0 < abs(v$3 - c)) /\ &0 < d0`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s5b_setting] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                           "moi_s5b_setting" with Failure _ -> false)) THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP MOI_S5B_MSET_BASIC th) THEN
                         MP_TAC(REWRITE_RULE[moi_s5b_mset] th)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5B_TRIANG_SWAP THEN
  MAP_EVERY EXISTS_TAC
   [`K:(real^3->bool)->bool`; `moi_s5b_ep (Q:real^3->real->real^3) s k E`;
    `moi_s5b_ba B (Q:real^3->real->real^3) s k E`;
    `moi_s5b_kp (Q:real^3->real->real^3) s k`;
    `h:real^3->real^3`; `h':real^3->real^3`; `moi_s5b_cp c d0 s`] THEN
  ONCE_REWRITE_TAC[UNION_COMM] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "v" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(moi_s5b_cp c d0 s - c) <= d0` THEN
    UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ASM_MESON_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^3->real^3) x IN moi_s5b_dp Q c d0 s k` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^3->real^3) (moi_s5b_ep Q s k E) SUBSET
                   moi_s5b_dp Q c d0 s k` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s5b_ep Q s k E` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `!z. z IN moi_s5b_dp (Q:real^3->real->real^3) c d0 s k
                     ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
    DISCH_THEN(MP_TAC o SPEC `(h:real^3->real^3) x`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S5B_BP_LEVEL = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> {x | x IN moi_s5b_bp B Q c d0 s k E /\ x$3 = c} =
         {x | x IN B /\ x$3 = c} DIFF E`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_CP_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_KP_LEVEL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  SUBGOAL_THEN
   `!x:real^3. x IN moi_s5b_ep Q s k E /\ x$3 = c ==> x IN E` (LABEL_TAC "epc") THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[moi_s5b_ep; IN_UNION; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^3) IN B /\ x$3 = c` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
      UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                  ==> (Q:real^3->real->real^3) x (s * u) IN B /\
                      (Q x (s * u))$3 = c + s * u * d0 /\
                      abs((Q x (s * u))$3 - c) <= d0` THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `--(&1 / &2) <= u` THEN
      UNDISCH_TAC `u <= &0` THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    SUBGOAL_THEN `u = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `(z:real^3)$3 = c` THEN
      UNDISCH_TAC `(z:real^3) = Q (x:real^3) (s * u)` THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `c + a = c <=> a = &0`; REAL_ENTIRE] THEN
      UNDISCH_TAC `~(s = &0)` THEN UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `!x. x IN B /\ x$3 = c ==> (Q:real^3->real->real^3) x (s * &0) = x` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET E` THEN UNDISCH_TAC `(x:real^3) IN k` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s5b_bp; moi_s5b_ba; EXTENSION; IN_ELIM_THM; IN_UNION; IN_DIFF] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((x:real^3) IN moi_s5b_ep Q s k E /\ ~(x IN moi_s5b_kp Q s k))` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN E` THEN REWRITE_TAC[moi_s5b_ep] THEN SET_TAC[];
        DISCH_TAC THEN
        UNDISCH_TAC `!z. z IN moi_s5b_kp (Q:real^3->real->real^3) s k
               ==> z IN B /\ z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(moi_s5b_cp c d0 s = c)` THEN
        UNDISCH_TAC `(x:real^3)$3 = c` THEN MESON_TAC[]];
      UNDISCH_TAC `!z. z IN moi_s5b_dp (Q:real^3->real->real^3) c d0 s k
                     ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      UNDISCH_TAC `~(moi_s5b_cp c d0 s = c)` THEN
      UNDISCH_TAC `(x:real^3)$3 = moi_s5b_cp c d0 s` THEN
      UNDISCH_TAC `(x:real^3)$3 = c` THEN REAL_ARITH_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    USE_THEN "epc" (MP_TAC o SPEC `x:real^3`) THEN
    REWRITE_TAC[ASSUME `(x:real^3)$3 = c`; ASSUME `~((x:real^3) IN E)`] THEN
    MESON_TAC[]]);;

let MOI_S5B_BP_CIRCLES = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> components ({x | x IN B /\ x$3 = c} DIFF E) =
         {k2 | k2 IN components {x | x IN B /\ x$3 = c} /\ DISJOINT k2 E} /\
         CARD (components ({x | x IN B /\ x$3 = c} DIFF E)) <
         CARD (components {x:real^3 | x IN B /\ x$3 = c})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  SUBGOAL_THEN `k IN components {x:real^3 | x IN B /\ x$3 = c} /\
                FINITE (components {x:real^3 | x IN B /\ x$3 = c})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s5b_setting; moi_s5b_kset; moi_s5b_mset]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k2. k2 IN components {x:real^3 | x IN B /\ x$3 = c}
         ==> k2 SUBSET E \/ DISJOINT k2 E`
  (LABEL_TAC "dich") THENL
   [X_GEN_TAC `k2:real^3->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k2:real^3->bool = k` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (k2:real^3->bool) k` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPONENTS_NONOVERLAP; DISJOINT]; ALL_TAC] THEN
    SUBGOAL_THEN `(k2:real^3->bool) SUBSET B /\ connected k2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`{x:real^3 | x IN B /\ x$3 = c}`; `k2:real^3->bool`]
          IN_COMPONENTS_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`B:real^3->bool`; `k2:real^3->bool`; `E DIFF k:real^3->bool`;
                   `B DIFF E:real^3->bool`] MOI_S5B_CONN_TWO_OPEN_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_DIFF THEN
        ASM_SIMP_TAC[OPEN_IN_REFL; CLOSED_SUBSET; COMPACT_IMP_CLOSED];
        UNDISCH_TAC `DISJOINT (k2:real^3->bool) k` THEN
        UNDISCH_TAC `(k2:real^3->bool) SUBSET B` THEN SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^3 | x IN B /\ x$3 = c} DIFF E =
    UNIONS {k2 | k2 IN components {x:real^3 | x IN B /\ x$3 = c} /\ DISJOINT k2 E}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [UNIONS_COMPONENTS] THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k2:real^3->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `k2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "dich" (MP_TAC o SPEC `k2:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL [EXISTS_TAC `k2:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `components ({x:real^3 | x IN B /\ x$3 = c} DIFF E) =
    {k2 | k2 IN components {x:real^3 | x IN B /\ x$3 = c} /\ DISJOINT k2 E}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5B_COMPONENTS_SUBUNION THEN
    EXISTS_TAC `{x:real^3 | x IN B /\ x$3 = c}` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[PSUBSET; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
   [SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `k:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(k:real^3->bool) SUBSET E` THEN UNDISCH_TAC `~(k:real^3->bool = {})` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Components of the two halves of B' (the edge_conf clauses k0 and k1).    *)
(* ------------------------------------------------------------------------- *)

let moi_s5b_clause = new_definition
 `moi_s5b_clause (X:real^3->bool) <=>
    ?k0. k0 IN components X /\
         !k. k IN components X /\ ~(k = k0) ==> k SUBSET moi_s35_ttube`;;

let MOI_S5B_FINITE_COMPONENTS_UNIONS = prove
 (`!f:(real^N->bool)->bool.
     FINITE f /\ (!c. c IN f ==> connected c) ==> FINITE (components (UNIONS f))`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; COMPONENTS_EMPTY; FINITE_EMPTY;
              FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_COMPONENTS_UNION THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `x:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[COMPONENTS_EMPTY; FINITE_EMPTY] THEN
  SUBGOAL_THEN `components(x:real^N->bool) = {x}` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; REWRITE_TAC[FINITE_SING]]);;

let MOI_S5B_FINITE_COMP_HALF = prove
 (`!(K:(real^N->bool)->bool) H.
     FINITE K /\ (!s. s IN K ==> convex s) /\ convex H
     ==> FINITE (components (UNIONS K INTER H))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS K INTER H = UNIONS {s INTER H | (s:real^N->bool) IN K}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTER_UNIONS] THEN AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5B_FINITE_COMPONENTS_UNIONS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
  MATCH_MP_TAC CONVEX_INTER THEN ASM_SIMP_TAC[]);;

let MOI_S5B_COMPONENTS_PARTITION = prove
 (`!f:(real^N->bool)->bool.
     FINITE f /\ (!c. c IN f ==> closed c /\ connected c /\ ~(c = {})) /\
     (!c c'. c IN f /\ c' IN f /\ ~(c = c') ==> DISJOINT c c')
     ==> components (UNIONS f) = f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_UNIQUE THEN REWRITE_TAC[] THEN
  X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (c:real^N->bool) (UNIONS (f DELETE c))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC; IN_DELETE] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM DISJOINT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c':real^N->bool`; `c:real^N->bool`;
                 `UNIONS (f DELETE (c:real^N->bool))`] MOI_S5B_CONN_TWO_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
      UNDISCH_TAC `(c':real^N->bool) SUBSET UNIONS f` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT (c:real^N->bool) (UNIONS (f DELETE c))` THEN SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?y:real^N. y IN c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (c:real^N->bool) (UNIONS (f DELETE c))` THEN
  UNDISCH_TAC `(c':real^N->bool) SUBSET UNIONS (f DELETE c)` THEN
  UNDISCH_TAC `(c:real^N->bool) SUBSET c'` THEN
  UNDISCH_TAC `(y:real^N) IN c` THEN SET_TAC[]);;

let moi_s5b_hp = new_definition
 `moi_s5b_hp c s = {x:real^3 | &0 <= s * (x$3 - c)}`;;

let moi_s5b_hm = new_definition
 `moi_s5b_hm c s = {x:real^3 | s * (x$3 - c) <= &0}`;;

let MOI_S5B_HALF_SETS = prove
 (`!c s. s = &1 \/ s = -- &1
         ==> convex (moi_s5b_hp c s) /\ convex (moi_s5b_hm c s) /\
             closed (moi_s5b_hp c s) /\ closed (moi_s5b_hm c s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[moi_s5b_hp; moi_s5b_hm] THENL
   [SUBGOAL_THEN `{x:real^3 | &0 <= &1 * (x$3 - c)} = {x | x$3 >= c} /\
                  {x:real^3 | &1 * (x$3 - c) <= &0} = {x | x$3 <= c}`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `{x:real^3 | &0 <= -- &1 * (x$3 - c)} = {x | x$3 <= c} /\
                  {x:real^3 | -- &1 * (x$3 - c) <= &0} = {x | x$3 >= c}`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC]] THEN
  REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE; CONVEX_HALFSPACE_COMPONENT_LE;
              CLOSED_HALFSPACE_COMPONENT_GE; CLOSED_HALFSPACE_COMPONENT_LE]);;

let MOI_S5B_HALF_FACTS = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> (!x u. x IN B /\ x$3 = c /\ abs u <= &1
                ==> (Q x (s * u) IN moi_s5b_hp c s <=> &0 <= u) /\
                    (Q x (s * u) IN moi_s5b_hm c s <=> u <= &0)) /\
         (!x. x$3 = c ==> x IN moi_s5b_hp c s /\ x IN moi_s5b_hm c s) /\
         (!x. x$3 = moi_s5b_cp c d0 s ==> ~(x IN moi_s5b_hp c s) /\ x IN moi_s5b_hm c s) /\
         convex (moi_s5b_hp c s) /\ convex (moi_s5b_hm c s) /\
         closed (moi_s5b_hp c s) /\ closed (moi_s5b_hm c s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  SUBGOAL_THEN `s = &1 \/ s = -- &1` ASSUME_TAC THENL
   [UNDISCH_TAC `abs s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * s = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `s = &1 \/ s = -- &1` THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_HALF_SETS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                  ==> (Q:real^3->real->real^3) x (s * u) IN B /\
                      (Q x (s * u))$3 = c + s * u * d0 /\
                      abs((Q x (s * u))$3 - c) <= d0` THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[moi_s5b_hp; moi_s5b_hm; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_ARITH `(c + s * u * d) - c = s * u * d`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(CONJUNCT2 REAL_LE_MUL_EQ) THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`] THEN
      REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
      MATCH_MP_TAC(CONJUNCT2 REAL_LE_MUL_EQ) THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[moi_s5b_hp; moi_s5b_hm; IN_ELIM_THM; REAL_SUB_REFL; REAL_MUL_RZERO;
             REAL_LE_REFL];
    GEN_TAC THEN REWRITE_TAC[moi_s5b_hp; moi_s5b_hm; IN_ELIM_THM; moi_s5b_cp] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `(c + (s * x) * d) - c = s * x * d`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
    UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC]);;

let MOI_S5B_HSWAP_EQ = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> ?h h'. pl_homeomorphism (B,moi_s5b_bp B Q c d0 s k E) (h,h') /\
                (!y. y IN moi_s5b_ba B Q s k E ==> h y = y) /\
                IMAGE h (moi_s5b_ep Q s k E) = moi_s5b_dp Q c d0 s k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_BA_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S5B_HSWAP) THEN
  MAP_EVERY EXISTS_TAC [`h:real^3->real^3`; `h':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s5b_bp B Q c d0 s k E` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5b_bp] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^3. x IN B /\ (y:real^3) = (h:real^3->real^3) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^3->real^3) B = moi_s5b_bp B Q c d0 s k E` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s5b_bp B Q c d0 s k E` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^3) IN moi_s5b_ba B Q s k E` THENL
   [SUBGOAL_THEN `(h:real^3->real^3) x = x` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        try is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "y" &&
            can (find_term (fun t -> t = `moi_s5b_ba`)) (concl th)
        with Failure _ -> false)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E INTER
                 moi_s5b_dp Q c d0 s k = moi_s5b_kp Q s k` THEN
    UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E INTER
                 moi_s5b_ep Q s k E = moi_s5b_kp Q s k` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s5b_dp Q c d0 s k` THEN
    UNDISCH_TAC `(x:real^3) IN moi_s5b_ba B Q s k E` THEN
    UNDISCH_TAC `(y:real^3) = (h:real^3->real^3) x` THEN
    UNDISCH_TAC `(h:real^3->real^3) x = x` THEN SET_TAC[];
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E UNION
                 moi_s5b_ep Q s k E = B` THEN
    UNDISCH_TAC `(x:real^3) IN B` THEN
    UNDISCH_TAC `~((x:real^3) IN moi_s5b_ba B Q s k E)` THEN SET_TAC[]]);;

let MOI_S5B_NBHD = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> open_in (subtopology euclidean B)
                 {Q x (s * u) | x IN k /\ -- &1 < u /\ u < &1} /\
         k SUBSET {Q x (s * u) | x IN k /\ -- &1 < u /\ u < &1} /\
         {Q x (s * u) | x IN k /\ -- &1 < u /\ u < &1} INTER moi_s5b_hp c s
         SUBSET E /\
         {Q x (s * u) | x IN k /\ -- &1 < u /\ u < &1} INTER moi_s5b_hm c s INTER E
         SUBSET k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_HALF_FACTS) THEN
  SUBGOAL_THEN `!x:real^3. x IN k ==> x IN B /\ x$3 = c` (LABEL_TAC "k0") THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_SIDE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `d0:real`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs s = &1` THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^3`; `&0`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    UNDISCH_TAC `!x. x IN B /\ x$3 = c ==> (Q:real^3->real->real^3) x (s * &0) = x` THEN
    DISCH_THEN MATCH_MP_TAC THEN USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `u:real`
      STRIP_ASSUME_TAC)) MP_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      try lhs(concl th) = `z:real^3` with Failure _ -> false)) THEN
    USE_THEN "k0" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                ==> ((Q:real^3->real->real^3) x (s * u) IN moi_s5b_hp c s <=> &0 <= u) /\
                    (Q x (s * u) IN moi_s5b_hm c s <=> u <= &0)` THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `-- &1 < u` THEN UNDISCH_TAC `u < &1` THEN
      REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
    DISCH_TAC THEN ASM_CASES_TAC `u = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `!x. x IN B /\ x$3 = c ==> (Q:real^3->real->real^3) x (s * &0) = x` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(k:real^3->bool) SUBSET E` THEN UNDISCH_TAC `(x:real^3) IN k` THEN
      SET_TAC[];
      UNDISCH_TAC `!x u. x IN k /\ &0 < u /\ u < &1
                    ==> (Q:real^3->real->real^3) x (s * u) IN E` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 <= u` THEN UNDISCH_TAC `~(u = &0)` THEN REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `u:real`
      STRIP_ASSUME_TAC)) MP_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      try lhs(concl th) = `z:real^3` with Failure _ -> false)) THEN
    USE_THEN "k0" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                ==> ((Q:real^3->real->real^3) x (s * u) IN moi_s5b_hp c s <=> &0 <= u) /\
                    (Q x (s * u) IN moi_s5b_hm c s <=> u <= &0)` THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `-- &1 < u` THEN UNDISCH_TAC `u < &1` THEN
      REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th])] THEN
    STRIP_TAC THEN ASM_CASES_TAC `u = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `!x. x IN B /\ x$3 = c ==> (Q:real^3->real->real^3) x (s * &0) = x` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `u < &0` ASSUME_TAC THENL
       [UNDISCH_TAC `u <= &0` THEN UNDISCH_TAC `~(u = &0)` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `(Q:real^3->real->real^3) x (s * u) IN E` THEN
      UNDISCH_TAC `!x u. x IN k /\ -- &1 < u /\ u < &0
                    ==> ~((Q:real^3->real->real^3) x (s * u) IN E)` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`]) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]]]);;

let MOI_S5B_STRIP_HALF = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> moi_s5b_ep Q s k E INTER moi_s5b_hp c s SUBSET E /\
         DISJOINT (moi_s5b_dp Q c d0 s k) (moi_s5b_hp c s) /\
         moi_s5b_dp Q c d0 s k SUBSET moi_s5b_hm c s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_HALF_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s5b_ep; SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC (X_CHOOSE_THEN `x:real^3`
      (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      try lhs(concl th) = `z:real^3` with Failure _ -> false)) THEN
    SUBGOAL_THEN `(x:real^3) IN B /\ x$3 = c` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
      UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(Q:real^3->real->real^3) x (s * u) IN moi_s5b_hp c s` THEN
    UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                ==> ((Q:real^3->real->real^3) x (s * u) IN moi_s5b_hp c s <=> &0 <= u) /\
                    (Q x (s * u) IN moi_s5b_hm c s <=> u <= &0)` THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `--(&1 / &2) <= u` THEN
      UNDISCH_TAC `u <= &0` THEN REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `u = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&0 <= u` THEN UNDISCH_TAC `u <= &0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `!x. x IN B /\ x$3 = c ==> (Q:real^3->real->real^3) x (s * &0) = x` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET E` THEN UNDISCH_TAC `(x:real^3) IN k` THEN
    SET_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `!z. z IN moi_s5b_dp (Q:real^3->real->real^3) c d0 s k
                     ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN moi_s5b_hp c s` THEN
    UNDISCH_TAC `!x. x$3 = moi_s5b_cp c d0 s
                     ==> ~(x IN moi_s5b_hp c s) /\ x IN moi_s5b_hm c s` THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `!z. z IN moi_s5b_dp (Q:real^3->real->real^3) c d0 s k
                     ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `!x. x$3 = moi_s5b_cp c d0 s
                     ==> ~(x IN moi_s5b_hp c s) /\ x IN moi_s5b_hm c s` THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[]]);;

let MOI_S5B_ESIDE = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> (!Y. Y IN components (B INTER moi_s5b_hp c s) ==> Y SUBSET E \/ DISJOINT Y E) /\
         moi_s5b_bp B Q c d0 s k E INTER moi_s5b_hp c s =
         (B INTER moi_s5b_hp c s) DIFF E /\
         components (moi_s5b_bp B Q c d0 s k E INTER moi_s5b_hp c s) =
         {Y | Y IN components (B INTER moi_s5b_hp c s) /\ DISJOINT Y E}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_NBHD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_STRIP_HALF) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_EP_SETS) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "DIFF"
    with Failure _ -> false)) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean B) (B DIFF E:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_REFL; CLOSED_SUBSET; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Y. Y IN components (B INTER moi_s5b_hp c s) ==> Y SUBSET E \/ DISJOINT Y E`
  ASSUME_TAC THENL
   [X_GEN_TAC `Y:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `connected (Y:real^3->bool) /\ Y SUBSET B /\ Y SUBSET moi_s5b_hp c s`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
      MP_TAC(ISPECL [`B INTER moi_s5b_hp c s`; `Y:real^3->bool`]
        IN_COMPONENTS_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `DISJOINT (Y:real^3->bool) k` THENL
     [MP_TAC(ISPECL [`B:real^3->bool`; `Y:real^3->bool`; `E DIFF k:real^3->bool`;
                     `B DIFF E:real^3->bool`] MOI_S5B_CONN_TWO_OPEN_IN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `DISJOINT (Y:real^3->bool) k` THEN
        UNDISCH_TAC `(Y:real^3->bool) SUBSET B` THEN SET_TAC[];
        SET_TAC[]];
      DISJ1_TAC THEN
      MP_TAC(ISPECL [`B:real^3->bool`; `Y:real^3->bool`;
                     `(E DIFF k) UNION {(Q:real^3->real->real^3) x (s * u) |
                                        x IN k /\ -- &1 < u /\ u < &1}`;
                     `B DIFF E:real^3->bool`] MOI_S5B_CONN_TWO_OPEN_IN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `k SUBSET {(Q:real^3->real->real^3) x (s * u) |
                                 x IN k /\ -- &1 < u /\ u < &1}` THEN
          UNDISCH_TAC `(Y:real^3->bool) SUBSET B` THEN SET_TAC[];
          UNDISCH_TAC `{(Q:real^3->real->real^3) x (s * u) | x IN k /\ -- &1 < u /\ u < &1}
                       INTER moi_s5b_hp c s SUBSET E` THEN
          UNDISCH_TAC `(Y:real^3->bool) SUBSET moi_s5b_hp c s` THEN SET_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `(Y:real^3->bool) SUBSET (E DIFF k) UNION
          {(Q:real^3->real->real^3) x (s * u) | x IN k /\ -- &1 < u /\ u < &1}` THEN
        UNDISCH_TAC `{(Q:real^3->real->real^3) x (s * u) | x IN k /\ -- &1 < u /\ u < &1}
                     INTER moi_s5b_hp c s SUBSET E` THEN
        UNDISCH_TAC `(Y:real^3->bool) SUBSET moi_s5b_hp c s` THEN
        SPEC_TAC(`{(Q:real^3->real->real^3) x (s * u) | x IN k /\ -- &1 < u /\ u < &1}`,
                 `W:real^3->bool`) THEN
        SET_TAC[];
        UNDISCH_TAC `~DISJOINT (Y:real^3->bool) k` THEN
        UNDISCH_TAC `(Y:real^3->bool) SUBSET B DIFF E` THEN
        UNDISCH_TAC `(k:real^3->bool) SUBSET E` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5b_bp B (Q:real^3->real->real^3) c d0 s k E INTER moi_s5b_hp c s =
                (B INTER moi_s5b_hp c s) DIFF E` ASSUME_TAC THENL
   [SUBGOAL_THEN `E SUBSET moi_s5b_ep (Q:real^3->real->real^3) s k E` MP_TAC THENL
     [REWRITE_TAC[moi_s5b_ep] THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_s5b_bp; moi_s5b_ba] THEN
    UNDISCH_TAC `moi_s5b_ep (Q:real^3->real->real^3) s k E INTER moi_s5b_hp c s
                 SUBSET E` THEN
    UNDISCH_TAC `DISJOINT (moi_s5b_dp (Q:real^3->real->real^3) c d0 s k)
                          (moi_s5b_hp c s)` THEN
    UNDISCH_TAC `DISJOINT E (moi_s5b_kp (Q:real^3->real->real^3) s k)` THEN
    SPEC_TAC(`moi_s5b_ep (Q:real^3->real->real^3) s k E`,`ep:real^3->bool`) THEN
    SPEC_TAC(`moi_s5b_kp (Q:real^3->real->real^3) s k`,`kp:real^3->bool`) THEN
    SPEC_TAC(`moi_s5b_dp (Q:real^3->real->real^3) c d0 s k`,`dp:real^3->bool`) THEN
    SPEC_TAC(`moi_s5b_hp c s`,`hp:real^3->bool`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(B INTER moi_s5b_hp c s) DIFF E =
    UNIONS {Y | Y IN components (B INTER moi_s5b_hp c s) /\ DISJOINT Y (E:real^3->bool)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [UNIONS_COMPONENTS] THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `Y:real^3->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `Y:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Y:real^3->bool` o check (fun th ->
        try fst(dest_var(fst(dest_forall(concl th)))) = "Y" with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((z:real^3) IN E)` THEN UNDISCH_TAC `(z:real^3) IN Y` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `Y:real^3->bool` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL [EXISTS_TAC `Y:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT (Y:real^3->bool) E` THEN UNDISCH_TAC `(z:real^3) IN Y` THEN
      SET_TAC[]];
    MATCH_MP_TAC MOI_S5B_COMPONENTS_SUBUNION THEN
    EXISTS_TAC `B INTER moi_s5b_hp c s` THEN SET_TAC[]]);;

let MOI_S5B_DSIDE_Z = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> ?Z. Z IN components (B INTER moi_s5b_hm c s) /\ k SUBSET Z /\
             Z INTER E = k /\
             {Q x (s * u) | x IN k /\ --(&1 / &2) <= u /\ u <= &0} SUBSET Z /\
             (!Y. Y IN components (B INTER moi_s5b_hm c s) /\ ~(Y = Z)
                  ==> Y SUBSET E \/ DISJOINT Y E)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_NBHD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_HALF_FACTS) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean B) (B DIFF E:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_REFL; CLOSED_SUBSET; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET B INTER moi_s5b_hm c s` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
    UNDISCH_TAC `!x:real^3. x$3 = c ==> x IN moi_s5b_hp c s /\ x IN moi_s5b_hm c s` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B INTER moi_s5b_hm c s`; `k:real^3->bool`]
    EXISTS_COMPONENT_SUPERSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(k:real^3->bool = {})` THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET B INTER moi_s5b_hm c s` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Z:real^3->bool` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `Z:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `connected (Z:real^3->bool) /\ Z SUBSET B /\ Z SUBSET moi_s5b_hm c s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
    MP_TAC(ISPECL [`B INTER moi_s5b_hm c s`; `Z:real^3->bool`]
      IN_COMPONENTS_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `N = {(Q:real^3->real->real^3) x (s * u) | x IN k /\ -- &1 < u /\ u < &1}` THEN
  ABBREV_TAC `st = {(Q:real^3->real->real^3) x (s * u) |
                    x IN k /\ --(&1 / &2) <= u /\ u <= &0}` THEN
  SUBGOAL_THEN `(st:real^3->bool) SUBSET B INTER moi_s5b_hm c s` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_INTER] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `u:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN B /\ x$3 = c` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
      UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs u <= &1` ASSUME_TAC THENL
     [UNDISCH_TAC `--(&1 / &2) <= u` THEN UNDISCH_TAC `u <= &0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                  ==> (Q:real^3->real->real^3) x (s * u) IN B /\
                      (Q x (s * u))$3 = c + s * u * d0 /\
                      abs((Q x (s * u))$3 - c) <= d0` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      UNDISCH_TAC `!x u. x IN B /\ x$3 = c /\ abs u <= &1
                ==> ((Q:real^3->real->real^3) x (s * u) IN moi_s5b_hp c s <=> &0 <= u) /\
                    (Q x (s * u) IN moi_s5b_hm c s <=> u <= &0)` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (st:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN
    MP_TAC(ISPECL [`B:real^3->bool`; `c:real`; `d0:real`; `Q:real^3->real->real^3`;
                   `k:real^3->bool`; `s:real`; `--(&1 / &2)`; `&0`] MOI_S5B_SIDE_CONN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `abs s = &1` THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET st` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^3`; `&0`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    UNDISCH_TAC `!x. x IN B /\ x$3 = c ==> (Q:real^3->real->real^3) x (s * &0) = x` THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET {x | x IN B /\ x$3 = c}` THEN
    UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`B:real^3->bool`; `Z:real^3->bool`; `E DIFF k:real^3->bool`;
                   `(B DIFF E) UNION (N:real^3->bool)`] MOI_S5B_CONN_TWO_OPEN_IN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_UNION] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(k:real^3->bool) SUBSET N` THEN
        UNDISCH_TAC `(Z:real^3->bool) SUBSET B` THEN SET_TAC[];
        UNDISCH_TAC `(N:real^3->bool) INTER moi_s5b_hm c s INTER E SUBSET k` THEN
        UNDISCH_TAC `(Z:real^3->bool) SUBSET moi_s5b_hm c s` THEN SET_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `(k:real^3->bool) SUBSET Z` THEN
      UNDISCH_TAC `(Z:real^3->bool) SUBSET E DIFF k` THEN
      UNDISCH_TAC `~(k:real^3->bool = {})` THEN SET_TAC[];
      UNDISCH_TAC `(Z:real^3->bool) SUBSET (B DIFF E) UNION N` THEN
      UNDISCH_TAC `(N:real^3->bool) INTER moi_s5b_hm c s INTER E SUBSET k` THEN
      UNDISCH_TAC `(Z:real^3->bool) SUBSET moi_s5b_hm c s` THEN
      UNDISCH_TAC `(k:real^3->bool) SUBSET Z` THEN
      UNDISCH_TAC `(k:real^3->bool) SUBSET E` THEN SET_TAC[]];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_COMPONENTS_MAXIMAL] o check
      (fun th -> concl th = `(Z:real^3->bool) IN components (B INTER moi_s5b_hm c s)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `Z UNION st:real^3->bool` o last o CONJUNCTS) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(k:real^3->bool) SUBSET Z` THEN UNDISCH_TAC `~(k:real^3->bool = {})` THEN
        SET_TAC[];
        SET_TAC[];
        ASM_REWRITE_TAC[UNION_SUBSET] THEN
        UNDISCH_TAC `(Z:real^3->bool) SUBSET B` THEN
        UNDISCH_TAC `(Z:real^3->bool) SUBSET moi_s5b_hm c s` THEN SET_TAC[];
        MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(k:real^3->bool) SUBSET Z` THEN UNDISCH_TAC `(k:real^3->bool) SUBSET st` THEN
        UNDISCH_TAC `~(k:real^3->bool = {})` THEN SET_TAC[]];
      SET_TAC[]];
    X_GEN_TAC `Y:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `connected (Y:real^3->bool) /\ Y SUBSET B /\ DISJOINT Y k`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`B INTER moi_s5b_hm c s`; `Y:real^3->bool`]
          IN_COMPONENTS_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        MP_TAC(ISPECL [`B INTER moi_s5b_hm c s`; `Y:real^3->bool`; `Z:real^3->bool`]
          COMPONENTS_NONOVERLAP) THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(k:real^3->bool) SUBSET Z` THEN SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`B:real^3->bool`; `Y:real^3->bool`; `E DIFF k:real^3->bool`;
                   `B DIFF E:real^3->bool`] MOI_S5B_CONN_TWO_OPEN_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (Y:real^3->bool) k` THEN
      UNDISCH_TAC `(Y:real^3->bool) SUBSET B` THEN SET_TAC[];
      SET_TAC[]]]);;

let MOI_S5B_CELL_CONNECTED = prove
 (`!n (e:real^N->bool) j. pl_cell_with_boundary n e j ==> connected e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try rhs(concl th) = `e:real^N->bool` with Failure _ -> false)) THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED]);;

let MOI_S5B_DSIDE_COMP = prove
 (`!B K FF GG Q c d0 k j E s Z (h:real^3->real^3) h'.
     moi_s5b_setting B K FF GG Q c d0 k j E s /\
     Z IN components (B INTER moi_s5b_hm c s) /\ k SUBSET Z /\ Z INTER E = k /\
     {Q x (s * u) | x IN k /\ --(&1 / &2) <= u /\ u <= &0} SUBSET Z /\
     (!Y. Y IN components (B INTER moi_s5b_hm c s) /\ ~(Y = Z)
          ==> Y SUBSET E \/ DISJOINT Y E) /\
     pl_homeomorphism (B,moi_s5b_bp B Q c d0 s k E) (h,h') /\
     (!y. y IN moi_s5b_ba B Q s k E ==> h y = y) /\
     IMAGE h (moi_s5b_ep Q s k E) = moi_s5b_dp Q c d0 s k
     ==> components (moi_s5b_bp B Q c d0 s k E INTER moi_s5b_hm c s) =
         IMAGE h (Z UNION moi_s5b_ep Q s k E) INSERT
         {Y | Y IN components (B INTER moi_s5b_hm c s) /\ ~(Y = Z) /\ DISJOINT Y E} /\
         IMAGE h (Z UNION moi_s5b_ep Q s k E) SUBSET Z UNION moi_s5b_dp Q c d0 s k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dich")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hid") ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_BA_FACTS) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(rhs(concl th))))) = "closure"
    with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_STRIP_HALF) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_HALF_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_B) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_CELL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_EP_SETS) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "DIFF"
    with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "pl_homeomorphism"
      with Failure _ -> false)) THEN
  ABBREV_TAC `st = {(Q:real^3->real->real^3) x (s * u) |
                    x IN k /\ --(&1 / &2) <= u /\ u <= &0}` THEN
  SUBGOAL_THEN `moi_s5b_ep (Q:real^3->real->real^3) s k E = E UNION st` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN REWRITE_TAC[moi_s5b_ep]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5b_kp (Q:real^3->real->real^3) s k SUBSET st` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN REWRITE_TAC[moi_s5b_kp; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^3`; `--(&1 / &2)`] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^3->real^3) (Z UNION moi_s5b_ep Q s k E) =
    (Z INTER moi_s5b_ba B Q s k E) UNION moi_s5b_dp Q c d0 s k`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `(!z. z IN Z ==> h z IN (Z INTER ba) UNION dp) /\ (Z INTER ba) SUBSET IMAGE h Z
      ==> IMAGE h Z UNION dp = (Z INTER ba) UNION (dp:real^3->bool)`) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(z:real^3) IN moi_s5b_ba B Q s k E` THENL
       [USE_THEN "hid" (MP_TAC o SPEC `z:real^3`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[IN_UNION; IN_INTER];
        SUBGOAL_THEN `(z:real^3) IN moi_s5b_ep Q s k E` ASSUME_TAC THENL
         [UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E UNION
                       moi_s5b_ep Q s k E = B` THEN
          UNDISCH_TAC `~((z:real^3) IN moi_s5b_ba B Q s k E)` THEN
          UNDISCH_TAC `(z:real^3) IN Z` THEN
          UNDISCH_TAC `Z IN components (B INTER moi_s5b_hm c s)` THEN
          DISCH_THEN(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `IMAGE (h:real^3->real^3) (moi_s5b_ep Q s k E) =
                     moi_s5b_dp Q c d0 s k` THEN
        UNDISCH_TAC `(z:real^3) IN moi_s5b_ep Q s k E` THEN SET_TAC[]];
      REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN
      STRIP_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "hid" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(Z:real^3->bool) /\ connected Z /\ Z SUBSET B /\
                Z SUBSET moi_s5b_hm c s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_COMPACT THEN
      EXISTS_TAC `B INTER moi_s5b_hm c s` THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT; COMPACT_INTER_CLOSED];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
    MP_TAC(ISPECL [`B INTER moi_s5b_hm c s`; `Z:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (h:real^3->real^3) (Z UNION moi_s5b_ep Q s k E))`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:real^3->bool` THEN
      ASM_REWRITE_TAC[UNION_SUBSET];
      MATCH_MP_TAC CONNECTED_UNION THEN
      REWRITE_TAC[ASSUME `connected (Z:real^3->bool)`] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5B_CELL_CONNECTED THEN
        MAP_EVERY EXISTS_TAC [`2`; `moi_s5b_kp (Q:real^3->real->real^3) s k`] THEN
        FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(k:real^3->bool) SUBSET Z` THEN
        UNDISCH_TAC `(k:real^3->bool) SUBSET E` THEN
        UNDISCH_TAC `~(k:real^3->bool = {})` THEN SET_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  SUBGOAL_THEN
   `!Y. Y IN components (B INTER moi_s5b_hm c s) /\ ~(Y = Z)
        ==> DISJOINT Y Z /\ Y SUBSET B /\ Y SUBSET moi_s5b_hm c s /\ closed Y /\
            connected Y /\ ~(Y = {})`
  (LABEL_TAC "yfacts") THENL
   [X_GEN_TAC `Y:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`B INTER moi_s5b_hm c s`; `Y:real^3->bool`; `Z:real^3->bool`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[DISJOINT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`B INTER moi_s5b_hm c s`; `Y:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC CLOSED_IN_COMPACT THEN
      EXISTS_TAC `B INTER moi_s5b_hm c s` THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT; COMPACT_INTER_CLOSED];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Y. Y IN components (B INTER moi_s5b_hm c s) /\ ~(Y = Z)
        ==> (DISJOINT Y E ==> Y SUBSET moi_s5b_ba B Q s k E) /\
            (Y SUBSET E ==> Y INTER moi_s5b_ba B Q s k E = {})`
  (LABEL_TAC "ycases") THENL
   [X_GEN_TAC `Y:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "yfacts" (MP_TAC o SPEC `Y:real^3->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    REWRITE_TAC[moi_s5b_ba] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `(st:real^3->bool) SUBSET Z` THEN
      UNDISCH_TAC `DISJOINT (Y:real^3->bool) Z` THEN
      UNDISCH_TAC `DISJOINT (Y:real^3->bool) E` THEN
      UNDISCH_TAC `(Y:real^3->bool) SUBSET B` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT E (moi_s5b_kp (Q:real^3->real->real^3) s k)` THEN
      UNDISCH_TAC `(k:real^3->bool) SUBSET Z` THEN
      UNDISCH_TAC `DISJOINT (Y:real^3->bool) Z` THEN
      UNDISCH_TAC `(Y:real^3->bool) SUBSET E` THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `FY = {Y | Y IN components (B INTER moi_s5b_hm c s) /\ ~(Y = Z) /\
                       DISJOINT Y (E:real^3->bool)}` THEN
  SUBGOAL_THEN `!Y. Y IN FY <=> Y IN components (B INTER moi_s5b_hm c s) /\ ~(Y = Z) /\
                               DISJOINT Y (E:real^3->bool)` (LABEL_TAC "fy") THENL
   [EXPAND_TAC "FY" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (components (B INTER moi_s5b_hm c s))` ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (K:(real^3->bool)->bool) /\ simplicial_complex K /\ UNIONS K = B`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s5b_setting] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                             "moi_s5b_setting" with Failure _ -> false)) THEN
      SIMP_TAC[moi_s5b_mset];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try rhs(concl th) = `B:real^3->bool` &&
          fst(dest_const(fst(strip_comb(lhs(concl th))))) = "UNIONS"
      with Failure _ -> false)) THEN
    MATCH_MP_TAC MOI_S5B_FINITE_COMP_HALF THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s5b_bp B (Q:real^3->real->real^3) c d0 s k E INTER moi_s5b_hm c s =
    UNIONS ((Z INTER moi_s5b_ba B Q s k E UNION moi_s5b_dp Q c d0 s k) INSERT FY)`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_INSERT] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_UNIONS] THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[moi_s5b_bp; IN_UNION] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?Y. Y IN components (B INTER moi_s5b_hm c s) /\ (x:real^3) IN Y`
      STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPEC `B INTER moi_s5b_hm c s` UNIONS_COMPONENTS) THEN
        REWRITE_TAC[EXTENSION; IN_UNIONS; IN_INTER] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
        UNDISCH_TAC `moi_s5b_ba B (Q:real^3->real->real^3) s k E SUBSET B` THEN
        UNDISCH_TAC `(x:real^3) IN moi_s5b_ba B Q s k E` THEN
        UNDISCH_TAC `(x:real^3) IN moi_s5b_hm c s` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `Y:real^3->bool = Z` THENL
       [DISJ1_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      DISJ2_TAC THEN EXISTS_TAC `Y:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "fy" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "dich" (MP_TAC o SPEC `Y:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "ycases" (MP_TAC o SPEC `Y:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN Y` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s5b_ba B Q s k E` THEN SET_TAC[];
      DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
        (X_CHOOSE_THEN `Y:real^3->bool` STRIP_ASSUME_TAC)) THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(Z:real^3->bool) SUBSET moi_s5b_hm c s` THEN
        UNDISCH_TAC `(x:real^3) IN Z` THEN SET_TAC[];
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `moi_s5b_dp (Q:real^3->real->real^3) c d0 s k SUBSET moi_s5b_hm c s` THEN
        UNDISCH_TAC `(x:real^3) IN moi_s5b_dp Q c d0 s k` THEN SET_TAC[];
        UNDISCH_TAC `(Y:real^3->bool) IN FY` THEN
        USE_THEN "fy" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
        USE_THEN "ycases" (MP_TAC o SPEC `Y:real^3->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "yfacts" (MP_TAC o SPEC `Y:real^3->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `DISJOINT (Y:real^3->bool) E` THEN
        UNDISCH_TAC `(x:real^3) IN Y` THEN SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5B_COMPONENTS_PARTITION THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_INSERT] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `components (B INTER moi_s5b_hm c s)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fy" (fun th -> REWRITE_TAC[SUBSET; th]) THEN SIMP_TAC[];
    REWRITE_TAC[FORALL_IN_INSERT] THEN CONJ_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
         [MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
          MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
          ASM_MESON_TAC[MOI_S5B_CELL_COMPACT; MOI_S5B_DP_CELL]];
        FIRST_ASSUM ACCEPT_TAC;
        SUBGOAL_THEN `~(moi_s5b_kp (Q:real^3->real->real^3) s k = {})` MP_TAC THENL
         [REWRITE_TAC[moi_s5b_kp; IMAGE_EQ_EMPTY] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`2`; `moi_s5b_dp (Q:real^3->real->real^3) c d0 s k`;
                       `moi_s5b_kp (Q:real^3->real->real^3) s k`] MOI_S5B_CELL_COMPACT) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[MOI_S5B_DP_CELL]; ALL_TAC] THEN SET_TAC[]];
      X_GEN_TAC `Y:real^3->bool` THEN
      USE_THEN "fy" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      USE_THEN "yfacts" (MP_TAC o SPEC `Y:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    REWRITE_TAC[IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [`c1:real^3->bool`; `c2:real^3->bool`] THEN
    SUBGOAL_THEN
     `!Y. Y IN FY ==> DISJOINT (Z INTER moi_s5b_ba B Q s k E UNION
                                moi_s5b_dp (Q:real^3->real->real^3) c d0 s k) Y`
    ASSUME_TAC THENL
     [X_GEN_TAC `Y:real^3->bool` THEN
      USE_THEN "fy" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      USE_THEN "yfacts" (MP_TAC o SPEC `Y:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `moi_s5b_dp (Q:real^3->real->real^3) c d0 s k INTER B = moi_s5b_kp Q s k` THEN
      UNDISCH_TAC `moi_s5b_kp (Q:real^3->real->real^3) s k SUBSET st` THEN
      UNDISCH_TAC `(st:real^3->bool) SUBSET Z` THEN
      UNDISCH_TAC `DISJOINT (Y:real^3->bool) Z` THEN
      UNDISCH_TAC `(Y:real^3->bool) SUBSET B` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_MESON_TAC[DISJOINT_SYM; COMPONENTS_NONOVERLAP; DISJOINT]]);;

let MOI_S5B_CLAUSE_ESIDE = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s /\
     (?ke. ke IN components {x | x IN B /\ x$3 = c} /\ DISJOINT ke E) /\
     moi_s5b_clause (B INTER moi_s5b_hp c s)
     ==> moi_s5b_clause (moi_s5b_bp B Q c d0 s k E INTER moi_s5b_hp c s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `ke:real^3->bool` STRIP_ASSUME_TAC) MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5B_ESIDE) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "eq1")
    (LABEL_TAC "eq2"))) THEN
  USE_THEN "eq1" (fun eq1 -> USE_THEN "eq2" (fun eq2 ->
    ASSUME_TAC(REWRITE_RULE[eq1] eq2))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_HALF_FACTS) THEN
  REWRITE_TAC[moi_s5b_clause] THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `DISJOINT (k1:real^3->bool) E` THENL
   [EXISTS_TAC `k1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k1:real^3->bool) SUBSET E /\ ~(k1 = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(ke:real^3->bool) SUBSET (B INTER moi_s5b_hp c s) DIFF E /\
                connected ke /\ ~(ke = {})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`{x:real^3 | x IN B /\ x$3 = c}`; `ke:real^3->bool`]
        IN_COMPONENTS_SUBSET) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!x:real^3. x$3 = c ==> x IN moi_s5b_hp c s /\ x IN moi_s5b_hm c s` THEN
      UNDISCH_TAC `DISJOINT (ke:real^3->bool) E` THEN SET_TAC[];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(B INTER moi_s5b_hp c s) DIFF E:real^3->bool`; `ke:real^3->bool`]
    EXISTS_COMPONENT_SUPERSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(ke:real^3->bool = {})` THEN
    UNDISCH_TAC `(ke:real^3->bool) SUBSET (B INTER moi_s5b_hp c s) DIFF E` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1':real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `k1' IN {Y | Y IN components (B INTER moi_s5b_hp c s) /\
                            DISJOINT Y (E:real^3->bool)}` MP_TAC THENL
   [UNDISCH_TAC `components ((B INTER moi_s5b_hp c s) DIFF E) =
                 {Y | Y IN components (B INTER moi_s5b_hp c s) /\
                      DISJOINT Y (E:real^3->bool)}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `k1':real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `Y:real^3->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT (Y:real^3->bool) E` THEN
  UNDISCH_TAC `(k1:real^3->bool) SUBSET E` THEN UNDISCH_TAC `~(k1:real^3->bool = {})` THEN
  SET_TAC[]);;

let MOI_S5B_CLAUSE_DSIDE = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s /\
     moi_s5b_clause (B INTER moi_s5b_hm c s)
     ==> moi_s5b_clause (moi_s5b_bp B Q c d0 s k E INTER moi_s5b_hm c s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Z:real^3->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S5B_DSIDE_Z) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S5B_HSWAP_EQ) THEN
  MP_TAC(SPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`;
    `FF:real^2->real^3`; `GG:real^3->real^2`; `Q:real^3->real->real^3`;
    `c:real`; `d0:real`; `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`;
    `s:real`; `Z:real^3->bool`; `h:real^3->real^3`; `h':real^3->real^3`]
    MOI_S5B_DSIDE_COMP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `W = IMAGE (h:real^3->real^3) (Z UNION moi_s5b_ep Q s k E)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ceq") ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s5b_dp Q c d0 s k SUBSET moi_s35_ttube` ASSUME_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
    MP_TAC MOI_S5B_OTUBE THEN
    UNDISCH_TAC `!z. z IN moi_s5b_dp Q c d0 s k
                     ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s5b_clause] THEN USE_THEN "ceq" SUBST1_TAC THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `k1:real^3->bool = Z` THENL
   [EXISTS_TAC `W:real^3->bool` THEN REWRITE_TAC[] THEN
    X_GEN_TAC `Y:real^3->bool` THEN STRIP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Z:real^3->bool) SUBSET moi_s35_ttube` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^3->bool) SUBSET moi_s35_ttube` ASSUME_TAC THENL
   [UNDISCH_TAC `(W:real^3->bool) SUBSET Z UNION moi_s5b_dp Q c d0 s k` THEN
    UNDISCH_TAC `(Z:real^3->bool) SUBSET moi_s35_ttube` THEN
    UNDISCH_TAC `moi_s5b_dp Q c d0 s k SUBSET moi_s35_ttube` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `DISJOINT (k1:real^3->bool) E` THENL
   [EXISTS_TAC `k1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `Y:real^3->bool` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k1:real^3->bool) SUBSET E /\ ~(k1 = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
  EXISTS_TAC `W:real^3->bool` THEN REWRITE_TAC[] THEN
  X_GEN_TAC `Y:real^3->bool` THEN STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT (Y:real^3->bool) E` THEN
  UNDISCH_TAC `(k1:real^3->bool) SUBSET E` THEN UNDISCH_TAC `~(k1:real^3->bool = {})` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The model of an edge configuration: B = phi^-1 b with its annulus chart, *)
(* triangulation, collar width, collar and innermost inessential circle.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_GAP = prove
 (`!Z:real^3->bool c.
     compact Z /\ (!x. x IN Z ==> ~(x$3 = c))
     ==> ?d. &0 < d /\ !x. x IN Z ==> d < abs(x$3 - c)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `Z:real^3->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. abs(x$3 - c)`; `Z:real^3->bool`]
    CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN
    REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `abs((z:real^3)$3 - c) / &2` THEN
  SUBGOAL_THEN `&0 < abs((z:real^3)$3 - c)` ASSUME_TAC THENL
   [UNDISCH_TAC `!x:real^3. x IN Z ==> ~(x$3 = c)` THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [UNDISCH_TAC `&0 < abs((z:real^3)$3 - c)` THEN REAL_ARITH_TAC;
                  ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < abs((z:real^3)$3 - c)` THEN REAL_ARITH_TAC);;

let MOI_S5B_SLAB_INTERVAL = prove
 (`moi_s35_slab = interval[--vector[&1;&1;&1 / &8]:real^3,vector[&1;&1;&1 / &8]]`,
  REWRITE_TAC[moi_s35_slab; moi_s35_cube; EXTENSION; IN_ELIM_THM; IN_INTERVAL;
              DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT;
              VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S5B_PHI_SLAB = prove
 (`!phi:real^3->real^3.
     pl_map_on moi_s35_dom phi /\
     (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y)
     ==> ?pinv. pl_homeomorphism (moi_s35_slab,IMAGE phi moi_s35_slab) (phi,pinv)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5B_PL_EMBED THEN
  SUBGOAL_THEN `moi_s35_slab SUBSET moi_s35_dom` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_slab; moi_s35_dom; SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_S5B_SLAB_INTERVAL; COMPACT_INTERVAL];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
    REWRITE_TAC[MOI_S5B_SLAB_INTERVAL; POLYTOPE_INTERVAL];
    ASM SET_TAC[]]);;

let MOI_S5B_SC_POLYHEDRON = prove
 (`!K:(real^N->bool)->bool.
     simplicial_complex K ==> pl_polyhedron (UNIONS K) /\ compact (UNIONS K)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS (K:(real^N->bool)->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[simplicial_complex]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT]]);;

let MOI_S5B_PHI_EMBED = prove
 (`!(phi:real^3->real^3) X.
     pl_map_on moi_s35_dom phi /\
     (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y) /\
     X SUBSET moi_s35_dom /\ pl_polyhedron X
     ==> ?pinv. pl_homeomorphism (X,IMAGE phi X) (phi,pinv)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5B_PL_EMBED THEN
  ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ASM SET_TAC[]]);;

let MOI_S5B_MODEL_ANNULUS = prove
 (`!(phi:real^3->real^3) b b0 b1 B.
     pl_map_on moi_s35_dom phi /\
     (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y) /\
     B SUBSET moi_s35_dom /\ pl_polyhedron B /\ IMAGE phi B = b /\
     pl_annulus_with_ends b b0 b1
     ==> ?FF GG pinv.
           pl_homeomorphism
             (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
              interval(--vector[&1;&1]:real^2,vector[&1;&1]),B) (FF,GG) /\
           pl_homeomorphism (B,b) (phi,pinv) /\
           IMAGE phi (IMAGE FF (relative_frontier
             (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) = b0 /\
           IMAGE phi (IMAGE FF (relative_frontier
             (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = b1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `B:real^3->bool`] MOI_S5B_PHI_EMBED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `pinv:real^3->real^3`) THEN
  UNDISCH_TAC `pl_annulus_with_ends (b:real^3->bool) b0 b1` THEN
  REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(pinv:real^3->real^3) o (f:real^2->real^3)`;
                        `(g:real^3->real^2) o (phi:real^3->real^3)`;
                        `pinv:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `b:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN b ==> (phi:real^3->real^3) (pinv y) = y` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (B,b) (phi:real^3->real^3,pinv)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^2->real^3)
      (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])) = b`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `pl_homeomorphism
        (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
         interval(--vector[&1;&1]:real^2,vector[&1;&1]),b)
        (f:real^2->real^3,g)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MP_TAC MOI_S5B_A0_FACTS THEN
  UNDISCH_TAC
   `IMAGE (f:real^2->real^3)
      (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])) = b` THEN
  UNDISCH_TAC `!y. y IN b ==> (phi:real^3->real^3) (pinv y) = y` THEN
  SPEC_TAC(`relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`,
           `r1:real^2->bool`) THEN
  SPEC_TAC(`relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])`,
           `r2:real^2->bool`) THEN
  SPEC_TAC(`interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
            interval(--vector[&1;&1]:real^2,vector[&1;&1])`, `A0:real^2->bool`) THEN
  REWRITE_TAC[IMAGE_o] THEN
  SET_TAC[]);;

let MOI_S5B_CIRCLES_B = prove
 (`!(phi:real^3->real^3) b c B.
     B = {x | x IN moi_s35_dom /\ phi x IN b}
     ==> moi_s35_circles phi b c = {x | x IN B /\ x$3 = c}`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_s35_circles; EXTENSION; IN_ELIM_THM; CONJ_ASSOC]);;

let MOI_S5B_MODEL_MSET = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B.
     (!(K:(real^3->bool)->bool) (B:real^3->bool) c d0.
        FINITE K /\ simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &2) /\
        UNIONS K = B /\ &0 < d0 /\ (!v. {v} IN K ==> d0 < abs(v$3 - c))
        ==> ?Q. moi_s5b_collar B c d0 Q) /\
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
     B = {x | x IN moi_s35_dom /\ phi x IN b} /\
     FINITE (components (moi_s35_circles phi b c)) /\
     (!k. k IN components (moi_s35_circles phi b c)
          ==> ?j:real^2->bool. pl_sphere 1 j /\ k = IMAGE (moi_s35_lift c) j)
     ==> ?K FF GG Q d0 pinv.
           moi_s5b_mset B K FF GG Q c d0 /\
           pl_homeomorphism (B,b) (phi,pinv) /\
           IMAGE phi (IMAGE FF (relative_frontier
             (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) = b0 /\
           IMAGE phi (IMAGE FF (relative_frontier
             (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = b1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "collar") (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Bdef") STRIP_ASSUME_TAC))) THEN
  USE_THEN "Bdef" (fun bd -> DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[moi_s35_edge_conf; SYM bd] th))) THEN
  USE_THEN "Bdef" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE
    [MATCH_MP MOI_S5B_CIRCLES_B th])) THEN
  USE_THEN "Bdef" (fun th -> ASSUME_TAC(SPEC `c:real`
    (MATCH_MP MOI_S5B_CIRCLES_B th))) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `b:real^3->bool`] MOI_S5B_B_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "Bdef" (fun th -> REWRITE_TAC[SYM th]) THEN STRIP_TAC THEN
  REMOVE_THEN "Bdef" (K ALL_TAC) THEN
  MP_TAC MOI_S5B_U_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `(B:real^3->bool) SUBSET moi_s35_dom` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_s35_stube` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `moi_s35_stube SUBSET moi_s5b_u` THEN
    UNDISCH_TAC `moi_s5b_u SUBSET moi_s35_dom` THEN
    UNDISCH_TAC `(B:real^3->bool) SUBSET interior moi_s35_stube` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `UNIONS k = (B:real^3->bool)`] o
    MATCH_MP MOI_S5B_SC_POLYHEDRON o check (fun th ->
    try fst(dest_const(rator(concl th))) = "simplicial_complex"
    with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `b:real^3->bool`; `b0:real^3->bool`;
                 `b1:real^3->bool`; `B:real^3->bool`] MOI_S5B_MODEL_ANNULUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `FF:real^2->real^3` (X_CHOOSE_THEN `GG:real^3->real^2`
    (X_CHOOSE_THEN `pinv:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN k ==> aff_dim s <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5B_NO_3DIM THEN
    MAP_EVERY EXISTS_TAC [`GG:real^3->real^2`; `B:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
      REWRITE_RULE[pl_homeomorphism] o check (fun th ->
        try fst(dest_var(rand(rand(concl th)))) = "GG"
        with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^3` THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `!y:real^3. y IN B ==> (FF:real^2->real^3) (GG y) = y` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^3` th) THEN
                         MP_TAC(SPEC `y:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^3 | x IN B /\ x$3 = c} SUBSET
                {x | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`;
                   `b:real^3->bool`; `c:real`] MOI_S5B_CIRCLES_FLAT) THEN
    REWRITE_TAC[ASSUME `moi_s35_circles (phi:real^3->real^3) b c =
                        {x | x IN B /\ x$3 = c}`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_S5B_PL_BALL_3_FILL; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^3 | x IN B /\ x$3 = c} SUBSET moi_s5b_otube` ASSUME_TAC THENL
   [UNDISCH_TAC `{x:real^3 | x IN B /\ x$3 = c} SUBSET
                 {x | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}` THEN
    UNDISCH_TAC `abs c <= &1 / &512` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s5b_otube] THEN
    DISCH_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs c <= &1 / &512` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(B DIFF moi_s5b_otube) UNION {v:real^3 | {v} IN k}`; `c:real`]
    MOI_S5B_GAP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[MOI_S5B_OTUBE];
        MATCH_MP_TAC FINITE_IMP_COMPACT THEN
        MP_TAC(ISPECL [`\v:real^3. {v}`; `k:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; REWRITE_TAC[]]];
      REWRITE_TAC[IN_UNION; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
      STRIP_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN moi_s5b_otube)` THEN
        REWRITE_TAC[] THEN
        UNDISCH_TAC `{x:real^3 | x IN B /\ x$3 = c} SUBSET moi_s5b_otube` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gap"))) THEN
  USE_THEN "collar" (MP_TAC o SPECL [`k:(real^3->bool)->bool`; `B:real^3->bool`;
    `c:real`; `min (d / &2) (&1 / &64)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      USE_THEN "gap" (MP_TAC o SPEC `v:real^3`) THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM; ASSUME `{v:real^3} IN k`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Q:real^3->real->real^3`) THEN
  MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `Q:real^3->real->real^3`; `min (d / &2) (&1 / &64)`;
    `pinv:real^3->real^3`] THEN
  ASM_REWRITE_TAC[moi_s5b_mset] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "gap" (MP_TAC o SPEC `v:real^3`) THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM; ASSUME `{v:real^3} IN k`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:real^3) IN moi_s5b_otube` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "gap" (MP_TAC o SPEC `x:real^3`) THEN
    REWRITE_TAC[IN_UNION; IN_DIFF; IN_ELIM_THM; ASSUME `(x:real^3) IN B`;
                ASSUME `~((x:real^3) IN moi_s5b_otube)`] THEN
    UNDISCH_TAC `abs((x:real^3)$3 - c) <= min (d / &2) (&1 / &64)` THEN
    UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `DISJOINT (b0 UNION b1:real^3->bool) (IMAGE phi moi_s35_ttube)` THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^3) (IMAGE FF (relative_frontier
             (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) = b0` THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^3) (IMAGE FF (relative_frontier
             (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = b1` THEN
    SPEC_TAC(`IMAGE (FF:real^2->real^3) (relative_frontier
             (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`, `e1:real^3->bool`) THEN
    SPEC_TAC(`IMAGE (FF:real^2->real^3) (relative_frontier
             (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`, `e2:real^3->bool`) THEN
    SET_TAC[];
    REAL_ARITH_TAC]);;

let MOI_S5B_PHI_CELL = prove
 (`!(phi:real^3->real^3) pinv B b d j.
     pl_homeomorphism (B,b) (phi,pinv) /\
     pl_cell_with_boundary 2 d j /\ d SUBSET B
     ==> pl_cell_with_boundary 2 (IMAGE phi d) (IMAGE phi j) /\
         IMAGE phi d SUBSET b`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_S5B_CELL_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `b:real^3->bool`; `pinv:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `pl_homeomorphism (B,b) (phi:real^3->real^3,pinv)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET B` THEN SET_TAC[]]);;

let MOI_S5B_MODEL_KSET = prove
 (`!(phi:real^3->real^3) b c B K FF GG Q d0 pinv k0.
     moi_s5b_mset B K FF GG Q c d0 /\ pl_homeomorphism (B,b) (phi,pinv) /\
     (!k. k IN components {x | x IN B /\ x$3 = c}
          ==> (moi_s35_ess c k <=>
               ~(?d. pl_cell_with_boundary 2 d (IMAGE phi k) /\ d SUBSET b))) /\
     k0 IN components {x | x IN B /\ x$3 = c} /\ ~moi_s35_ess c k0
     ==> ?k j E. moi_s5b_kset B c k j E`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ess") STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`{x:real^3 | x IN B /\ x$3 = c}`; `c:real`; `k0:real^3->bool`]
    MOI_S5B_INNERMOST) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `moi_s5b_mset B K FF GG Q c d0` THEN REWRITE_TAC[moi_s5b_mset] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `j:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?d. pl_cell_with_boundary 2 d (IMAGE (phi:real^3->real^3) k) /\
                    d SUBSET b`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "ess" (MP_TAC o SPEC `k:real^3->bool`) THEN
    REWRITE_TAC[ASSUME `k IN components {x:real^3 | x IN B /\ x$3 = c}`;
                ASSUME `~moi_s35_ess c (k:real^3->bool)`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET B` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{x:real^3 | x IN B /\ x$3 = c}`; `k:real^3->bool`]
      IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    REWRITE_RULE[pl_homeomorphism] o check (fun th ->
      try fst(dest_var(rand(rand(concl th)))) = "pinv"
      with Failure _ -> false)) THEN
  SUBGOAL_THEN `IMAGE (pinv:real^3->real^3) (IMAGE phi k) = k` ASSUME_TAC THENL
   [UNDISCH_TAC `!x:real^3. x IN B ==> (pinv:real^3->real^3) (phi x) = x` THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET B` THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `j:real^2->bool`;
                        `IMAGE (pinv:real^3->real^3) d`] THEN
  REWRITE_TAC[moi_s5b_kset] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [UNDISCH_TAC `!x. x IN {x:real^3 | x IN B /\ x$3 = c}
                     ==> ~(moi_s5b_proj x IN inside j)` THEN
    REWRITE_TAC[IN_ELIM_THM];
    MP_TAC(ISPECL [`b:real^3->bool`; `B:real^3->bool`; `pinv:real^3->real^3`;
                   `phi:real^3->real^3`; `2`; `d:real^3->bool`;
                   `IMAGE (phi:real^3->real^3) k`] MOI_S5B_CELL_TRANSPORT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE (pinv:real^3->real^3) b = B` THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET b` THEN SET_TAC[]]);;

let MOI_S5B_MODEL_KE = prove
 (`!(phi:real^3->real^3) b c B K FF GG Q d0 pinv k j E ke.
     moi_s5b_mset B K FF GG Q c d0 /\ moi_s5b_kset B c k j E /\
     pl_homeomorphism (B,b) (phi,pinv) /\
     (!k. k IN components {x | x IN B /\ x$3 = c}
          ==> (moi_s35_ess c k <=>
               ~(?d. pl_cell_with_boundary 2 d (IMAGE phi k) /\ d SUBSET b))) /\
     ke IN components {x | x IN B /\ x$3 = c} /\ moi_s35_ess c ke
     ==> DISJOINT ke E`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ess")
    STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
    `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`] MOI_S5B_KSET_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d j'. pl_cell_with_boundary 2 d j' /\ d SUBSET B /\
                       j' IN components {x:real^3 | x IN B /\ x$3 = c}
                       ==> ~moi_s35_ess c j'`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "ess" (MP_TAC o SPEC `j':real^3->bool`) THEN
    REWRITE_TAC[ASSUME `j' IN components {x:real^3 | x IN B /\ x$3 = c}`] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    EXISTS_TAC `IMAGE (phi:real^3->real^3) d` THEN
    MATCH_MP_TAC MOI_S5B_PHI_CELL THEN
    MAP_EVERY EXISTS_TAC [`pinv:real^3->real^3`; `B:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s5b_kset B c k j E` THEN REWRITE_TAC[moi_s5b_kset] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try lhs(concl th) = `k:real^3->bool` with Failure _ -> false)) THEN
  SUBGOAL_THEN `~(ke:real^3->bool = k)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`E:real^3->bool`; `k:real^3->bool`] o check
      (fun th -> is_forall(concl th) && can (find_term (fun t -> t = `moi_s35_ess`))
                 (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (ke:real^3->bool) k` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN
    MP_TAC(ISPECL [`{x:real^3 | x IN B /\ x$3 = c}`; `ke:real^3->bool`;
                   `k:real^3->bool`] COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((ke:real^3->bool) SUBSET E)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:real`; `ke:real^3->bool`] MOI_S5B_ESS_LIFT) THEN
    SUBGOAL_THEN `?je:real^2->bool. pl_sphere 1 je /\ ke = IMAGE (moi_s35_lift c) je`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s5b_mset B K FF GG Q c d0` THEN REWRITE_TAC[moi_s5b_mset] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `pl_sphere 1 (ke:real^3->bool)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5B_LIFT_SPHERE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(K ALL_TAC) THEN
    UNDISCH_TAC `!j'. pl_sphere 1 j' /\ j' SUBSET E
                      ==> ?d. pl_cell_with_boundary 2 d j' /\ d SUBSET (B:real^3->bool)` THEN
    DISCH_THEN(MP_TAC o SPEC `ke:real^3->bool`) THEN
    REWRITE_TAC[ASSUME `pl_sphere 1 (ke:real^3->bool)`; ASSUME `(ke:real^3->bool) SUBSET E`] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real^3->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`dd:real^3->bool`; `ke:real^3->bool`] o check
      (fun th -> is_forall(concl th) && can (find_term (fun t -> t = `moi_s35_ess`))
                 (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ke:real^3->bool) SUBSET B /\ connected ke` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`{x:real^3 | x IN B /\ x$3 = c}`; `ke:real^3->bool`]
        IN_COMPONENTS_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN
      EXISTS_TAC `{x:real^3 | x IN B /\ x$3 = c}` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `ke:real^3->bool`; `E DIFF k:real^3->bool`;
                 `B DIFF E:real^3->bool`] MOI_S5B_CONN_TWO_OPEN_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_SIMP_TAC[OPEN_IN_REFL; COMPACT_IMP_CLOSED; CLOSED_SUBSET];
      MAP_EVERY UNDISCH_TAC [`(ke:real^3->bool) SUBSET B`; `DISJOINT (ke:real^3->bool) k`] THEN
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`~((ke:real^3->bool) SUBSET E)`] THEN SET_TAC[]);;

let MOI_S5B_MODEL = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c k0 B.
     (!(K:(real^3->bool)->bool) (B:real^3->bool) c d0.
        FINITE K /\ simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &2) /\
        UNIONS K = B /\ &0 < d0 /\ (!v. {v} IN K ==> d0 < abs(v$3 - c))
        ==> ?Q. moi_s5b_collar B c d0 Q) /\
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
     B = {x | x IN moi_s35_dom /\ phi x IN b} /\
     FINITE (components (moi_s35_circles phi b c)) /\
     (!k. k IN components (moi_s35_circles phi b c)
          ==> ?j:real^2->bool. pl_sphere 1 j /\ k = IMAGE (moi_s35_lift c) j) /\
     (!k. k IN components (moi_s35_circles phi b c)
          ==> (moi_s35_ess c k <=>
               ~(?d. pl_cell_with_boundary 2 d (IMAGE phi k) /\ d SUBSET b))) /\
     (?k. k IN components (moi_s35_circles phi b c) /\ moi_s35_ess c k) /\
     k0 IN components (moi_s35_circles phi b c) /\ ~moi_s35_ess c k0
     ==> ?K FF GG Q d0 k j E s.
           moi_s5b_setting B K FF GG Q c d0 k j E s /\
           (?ke. ke IN components {x | x IN B /\ x$3 = c} /\ DISJOINT ke E) /\
           IMAGE phi (IMAGE FF (relative_frontier
             (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) = b0 /\
           IMAGE phi (IMAGE FF (relative_frontier
             (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = b1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`;
    `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`;
    `c:real`; `B:real^3->bool`] MOI_S5B_MODEL_MSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^3->bool)->bool` (X_CHOOSE_THEN `FF:real^2->real^3`
    (X_CHOOSE_THEN `GG:real^3->real^2` (X_CHOOSE_THEN `Q:real^3->real->real^3`
    (X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `pinv:real^3->real^3`
    STRIP_ASSUME_TAC)))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MOI_S5B_CIRCLES_B
    (ASSUME `B = {x:real^3 | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}`)]) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try lhs(concl th) = `B:real^3->bool` with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `b:real^3->bool`; `c:real`; `B:real^3->bool`;
    `K:(real^3->bool)->bool`; `FF:real^2->real^3`; `GG:real^3->real^2`;
    `Q:real^3->real->real^3`; `d0:real`; `pinv:real^3->real^3`; `k0:real^3->bool`]
    MOI_S5B_MODEL_KSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kq:real^3->bool` (X_CHOOSE_THEN `j:real^2->bool`
    (X_CHOOSE_TAC `E:real^3->bool`))) THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
    `kq:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`] MOI_S5B_SETTING_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `s:real`) THEN
  MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `Q:real^3->real->real^3`; `d0:real`; `kq:real^3->bool`;
    `j:real^2->bool`; `E:real^3->bool`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S5B_MODEL_KE THEN
  MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `b:real^3->bool`; `c:real`;
    `B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `Q:real^3->real->real^3`; `d0:real`; `pinv:real^3->real^3`;
    `kq:real^3->bool`; `j:real^2->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The ball kk bounded by the swap sphere Sigma' = E' UNION D' in the model: *)
(* it lies in the open tube and misses the squares of radii 3/16 and 5/16.  *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_LIFT_CONT = prove
 (`!c (s:real^2->bool). moi_s35_lift c continuous_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONJUNCT1(SPEC `c:real` MOI_S5B_LIFT_LINEAR)] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC `c:real` MOI_S5B_LIFT_LINEAR))]);;

let MOI_S5B_STUBE_COMPL = prove
 (`connected((:real^3) DIFF moi_s35_stube) /\ bounded moi_s35_stube`,
  SUBGOAL_THEN
   `moi_s35_stube SUBSET
    interval[--vector[&3 / &8;&3 / &8;&1 / &16]:real^3,
             vector[&3 / &8;&3 / &8;&1 / &16]]`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_stube; moi_s35_n; SUBSET; IN_ELIM_THM; IN_INTERVAL;
                DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_INTERVAL]] THEN
  SUBGOAL_THEN
   `(:real^3) DIFF moi_s35_stube =
    ((:real^3) DIFF interval[--vector[&3 / &8;&3 / &8;&1 / &16],
                             vector[&3 / &8;&3 / &8;&1 / &16]]) UNION
    {x:real^3 | x$1 < &1 / &8 /\ --(&1 / &8) < x$1 /\
                x$2 < &1 / &8 /\ --(&1 / &8) < x$2}`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_s35_stube; moi_s35_n; EXTENSION; IN_UNION; IN_DIFF; IN_UNIV;
                IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
    REWRITE_TAC[DIMINDEX_3; BOUNDED_INTERVAL; CONVEX_INTERVAL] THEN ARITH_TAC;
    MATCH_MP_TAC CONVEX_CONNECTED THEN
    SUBGOAL_THEN
     `{x:real^3 | x$1 < &1 / &8 /\ --(&1 / &8) < x$1 /\
                  x$2 < &1 / &8 /\ --(&1 / &8) < x$2} =
      {x | x$1 < &1 / &8} INTER {x | x$1 > --(&1 / &8)} INTER
      {x | x$2 < &1 / &8} INTER {x | x$2 > --(&1 / &8)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT; CONVEX_HALFSPACE_COMPONENT_GT];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `vector[&0;&0;&1]:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3;
                FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let moi_s5b_wset = new_definition
 `moi_s5b_wset c =
    closure((:real^3) DIFF moi_s35_stube) UNION
    IMAGE (moi_s35_lift c)
      (interval[--vector[&3 / &16; &3 / &16],vector[&3 / &16; &3 / &16]]) UNION
    IMAGE (moi_s35_lift c)
      ((:real^2) DIFF interval(--vector[&5 / &16; &5 / &16],
                               vector[&5 / &16; &5 / &16]))`;;

let MOI_S5B_WSET = prove
 (`!c. connected (moi_s5b_wset c) /\ ~bounded (moi_s5b_wset c) /\
       (:real^3) DIFF interior moi_s35_stube SUBSET moi_s5b_wset c /\
       (!x. x$3 = c /\ (moi_s35_n x <= &3 / &16 \/ &5 / &16 <= moi_s35_n x)
            ==> x IN moi_s5b_wset c) /\
       (!x. x IN moi_s5b_wset c
            ==> ~(x IN interior moi_s35_stube) \/
                (x$3 = c /\ (moi_s35_n x <= &3 / &16 \/ &5 / &16 <= moi_s35_n x)))`,
  GEN_TAC THEN MP_TAC MOI_S5B_STUBE_COMPL THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s5b_wset; GSYM CLOSURE_COMPLEMENT] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN moi_s35_stube ==> &1 / &8 <= moi_s35_n x /\ moi_s35_n x <= &3 / &8`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_stube; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. moi_s35_n x < &1 / &8 \/ &3 / &8 < moi_s35_n x
               ==> x IN closure((:real^3) DIFF moi_s35_stube)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM UNION_ASSOC] THEN MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CLOSURE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[MOI_S5B_LIFT_CONT; CONNECTED_INTERVAL];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `moi_s35_lift c (vec 0)` THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[MOI_S5B_PROJ_LIFT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC FUN_IN_IMAGE THEN
          REWRITE_TAC[MOI_S5B_IN_BOX; VEC_COMPONENT] THEN REAL_ARITH_TAC]];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_S5B_LIFT_CONT] THEN
      MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
      REWRITE_TAC[DIMINDEX_2; LE_REFL; BOUNDED_INTERVAL; CONVEX_INTERVAL];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `moi_s35_lift c (vector[&1 / &2; &0])` THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[MOI_S5B_PROJ_LIFT; VECTOR_2] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_DIFF; IN_UNIV; MOI_S5B_IN_BOX; VECTOR_2] THEN REAL_ARITH_TAC]];
    DISCH_TAC THEN
    MP_TAC(ISPEC `moi_s35_stube` MOI_S5B_COBOUNDED_COMPL) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `closure((:real^3) DIFF moi_s35_stube) UNION
      IMAGE (moi_s35_lift c)
        (interval[--vector[&3 / &16; &3 / &16],vector[&3 / &16; &3 / &16]]) UNION
      IMAGE (moi_s35_lift c)
        ((:real^2) DIFF interval(--vector[&5 / &16; &5 / &16],
                                 vector[&5 / &16; &5 / &16]))` THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `(:real^3) DIFF moi_s35_stube` CLOSURE_SUBSET) THEN
    SET_TAC[];
    SET_TAC[];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `moi_s5b_proj x` THEN
    ASM_SIMP_TAC[MOI_S5B_PROJ_LIFT] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; MOI_S5B_IN_BOX; MOI_S5B_PROJ_FACTS] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN STRIP_TAC THENL
     [DISJ1_TAC THEN UNDISCH_TAC `x IN closure((:real^3) DIFF moi_s35_stube)` THEN
      REWRITE_TAC[CLOSURE_COMPLEMENT] THEN SET_TAC[];
      DISJ2_TAC THEN UNDISCH_TAC `x' IN interval[--vector[&3 / &16; &3 / &16]:real^2,
                                              vector[&3 / &16; &3 / &16]]` THEN
      ASM_REWRITE_TAC[MOI_S5B_PROJ_LIFT; MOI_S5B_IN_BOX] THEN REAL_ARITH_TAC;
      DISJ2_TAC THEN UNDISCH_TAC `x' IN (:real^2) DIFF
        interval(--vector[&5 / &16; &5 / &16],vector[&5 / &16; &5 / &16])` THEN
      ASM_REWRITE_TAC[MOI_S5B_PROJ_LIFT; MOI_S5B_IN_BOX; IN_DIFF; IN_UNIV] THEN
      REAL_ARITH_TAC]]);;

let MOI_S5B_KK_GEN = prove
 (`!sg:real^3->bool c.
     pl_sphere 2 sg /\ sg SUBSET interior moi_s35_stube /\
     (!x. x IN sg /\ x$3 = c ==> &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16)
     ==> compact (sg UNION inside sg) /\
         sg UNION inside sg SUBSET interior moi_s35_stube /\
         DISJOINT (sg UNION inside sg)
                  (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c) /\
         (!x. x IN sg UNION inside sg /\ x$3 = c ==> moi_s35_n x < &5 / &16)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:real` MOI_S5B_WSET) THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (sg:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON; PL_POLYHEDRON_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (sg:real^3->bool) (moi_s5b_wset c)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `!x:real^3. x IN moi_s5b_wset c
                  ==> ~(x IN interior moi_s35_stube) \/
                      x$3 = c /\ (moi_s35_n x <= &3 / &16 \/ &5 / &16 <= moi_s35_n x)` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^3) IN interior moi_s35_stube` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    UNDISCH_TAC `!x:real^3. x IN sg /\ x$3 = c
                  ==> &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (sg UNION inside sg) (moi_s5b_wset c)` ASSUME_TAC THENL
   [REWRITE_TAC[UNION_WITH_INSIDE; DISJOINT; EXTENSION; IN_INTER; IN_DIFF; IN_UNIV;
                NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[TAUT `~(~p /\ q) <=> q ==> p`] THEN
    DISCH_TAC THEN MATCH_MP_TAC UNBOUNDED_DISJOINT_IN_OUTSIDE THEN
    EXISTS_TAC `moi_s5b_wset c` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [REWRITE_TAC[BOUNDED_UNION] THEN
      ASM_SIMP_TAC[BOUNDED_INSIDE; COMPACT_IMP_BOUNDED];
      REWRITE_TAC[UNION_WITH_INSIDE; GSYM OPEN_CLOSED] THEN
      MATCH_MP_TAC OPEN_OUTSIDE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    UNDISCH_TAC `(:real^3) DIFF interior moi_s35_stube SUBSET moi_s5b_wset c` THEN
    UNDISCH_TAC `DISJOINT (sg UNION inside sg) (moi_s5b_wset c)` THEN SET_TAC[];
    SUBGOAL_THEN `moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c SUBSET
                  moi_s5b_wset c` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; moi_s35_sq; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `DISJOINT (sg UNION inside sg) (moi_s5b_wset c)` THEN SET_TAC[]];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s5b_wset c` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN sg UNION inside sg` THEN
    UNDISCH_TAC `DISJOINT (sg UNION inside sg) (moi_s5b_wset c)` THEN SET_TAC[]]);;

let moi_s5b_sg = new_definition
 `moi_s5b_sg (Q:real^3->real->real^3) c d0 s k E =
    moi_s5b_ep Q s k E UNION moi_s5b_dp Q c d0 s k`;;

let moi_s5b_kk = new_definition
 `moi_s5b_kk (Q:real^3->real->real^3) c d0 s k E =
    moi_s5b_sg Q c d0 s k E UNION inside (moi_s5b_sg Q c d0 s k E)`;;

let MOI_S5B_OTUBE_STUBE = prove
 (`moi_s5b_otube SUBSET interior moi_s35_stube`,
  MP_TAC MOI_S5B_OTUBE THEN MP_TAC MOI_S5B_U_FACTS THEN STRIP_TAC THEN STRIP_TAC THEN
  TRANS_TAC SUBSET_TRANS `interior moi_s35_ttube` THEN ASM_SIMP_TAC[SUBSET_INTERIOR]);;

let MOI_S5B_SG_FACTS = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> pl_sphere 2 (moi_s5b_sg Q c d0 s k E) /\
         moi_s5b_sg Q c d0 s k E SUBSET interior moi_s35_stube /\
         (!x. x IN moi_s5b_sg Q c d0 s k E /\ x$3 = c
              ==> &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s5b_sg] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SIGMA_SPHERE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_EP_SETS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_CP_FACTS) THEN
  SUBGOAL_THEN `B SUBSET interior moi_s35_stube /\
                {x:real^3 | x IN B /\ x$3 = c} SUBSET
                {x | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5b_setting B K FF GG Q c d0 k j E s` THEN
    REWRITE_TAC[moi_s5b_setting; moi_s5b_mset] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `moi_s5b_ep Q s k E SUBSET (B:real^3->bool)` THEN
    UNDISCH_TAC `(B:real^3->bool) SUBSET interior moi_s35_stube` THEN SET_TAC[];
    MP_TAC MOI_S5B_OTUBE_STUBE THEN
    UNDISCH_TAC `!z. z IN moi_s5b_dp Q c d0 s k
                     ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
    SET_TAC[];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [UNDISCH_TAC `{x:real^3 | x IN B /\ x$3 = c} SUBSET
                   {x | &3 / &16 < moi_s35_n x /\ moi_s35_n x < &5 / &16 /\ x$3 = c}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      UNDISCH_TAC `!z. z IN moi_s5b_dp Q c d0 s k
                       ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(moi_s5b_cp c d0 s = c)` THEN MESON_TAC[]]]);;

let MOI_S5B_KK = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> compact (moi_s5b_kk Q c d0 s k E) /\
         moi_s5b_kk Q c d0 s k E SUBSET interior moi_s35_stube /\
         DISJOINT (moi_s5b_kk Q c d0 s k E)
                  (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c) /\
         (!x. x IN moi_s5b_kk Q c d0 s k E /\ x$3 = c ==> moi_s35_n x < &5 / &16)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s5b_kk] THEN
  MATCH_MP_TAC MOI_S5B_KK_GEN THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S5B_SG_FACTS));;

(* ------------------------------------------------------------------------- *)
(* Target side helpers: disks in a 2-sphere, the flat neighbourhoods of the *)
(* cap D' in the model.                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_CELL_OPEN_CONN = prove
 (`!n (e:real^N->bool) j.
     pl_cell_with_boundary n e j ==> connected (e DIFF j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[pl_homeomorphism]) THEN
  MP_TAC(ISPECL [`&n:int`; `k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`;
                 `e:real^N->bool`] MOI_S5B_SIMPLEX_IMAGE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `e DIFF IMAGE (f:real^N->real^N) (relative_frontier k) =
                IMAGE f (relative_interior k)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
    ASM_MESON_TAC[homeomorphism];
    MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]]);;

let MOI_S5B_SPHERE_CELL = prove
 (`!s e j (w:real^3).
     s homeomorphic sphere(vec 0:real^3,&1) /\ pl_cell_with_boundary 2 e j /\
     e SUBSET s /\ w IN s /\ ~(w IN e)
     ==> open_in (subtopology euclidean s) (e DIFF j) /\
         connected (s DIFF e) /\ connected (e DIFF j) /\ ~(e DIFF j = {}) /\
         j SUBSET e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(e DIFF j:real^3->bool = {}) /\ j SUBSET e /\ connected (e DIFF j)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5B_CELL_INTERIOR_NONEMPTY THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MP_TAC(MATCH_MP MOI_S5B_CELL_COMPACT
        (ASSUME `pl_cell_with_boundary 2 e (j:real^3->bool)`)) THEN SIMP_TAC[];
      MATCH_MP_TAC MOI_S5B_CELL_OPEN_CONN THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 e (j:real^3->bool)` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[pl_homeomorphism]) THEN
  MP_TAC(ISPECL [`&2:int`; `k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                 `e:real^3->bool`] MOI_S5B_SIMPLEX_IMAGE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `e DIFF IMAGE (f:real^3->real^3) (relative_frontier k) =
                IMAGE f (relative_interior k)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_SPHERE_DISK_OPEN THEN
    MAP_EVERY EXISTS_TAC [`e:real^3->bool`; `g:real^3->real^3`; `w:real^3`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5B_SPHERE_DISK_CONN THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                          `w:real^3`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S5B_PROJ_NORM = prove
 (`!v:real^3. norm(moi_s5b_proj v) <= norm v`,
  GEN_TAC THEN REWRITE_TAC[NORM_LE; moi_s5b_proj; DOT_2; DOT_3; VECTOR_2] THEN
  MP_TAC(SPEC `(v:real^3)$3` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

let MOI_S5B_DP_NBHD = prove
 (`!B K FF GG Q c d0 k j E s y.
     moi_s5b_setting B K FF GG Q c d0 k j E s /\
     y IN moi_s5b_dp Q c d0 s k /\ ~(y IN moi_s5b_kp Q s k)
     ==> ?r. &0 < r /\ cball(y,r) SUBSET moi_s5b_otube /\
             DISJOINT (cball(y,r)) B /\
             (!x. x IN cball(y,r) /\ x$3 = moi_s5b_cp c d0 s
                  ==> x IN moi_s5b_dp Q c d0 s k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_JPP_SPHERE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_B) THEN
  ABBREV_TAC `jq = moi_s5b_jpp (Q:real^3->real->real^3) s k` THEN
  ABBREV_TAC `cq = moi_s5b_cp c d0 s` THEN
  SUBGOAL_THEN `?z:real^2. z IN inside jq /\ moi_s35_lift cq z = y` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN moi_s5b_dp Q c d0 s k` THEN
    UNDISCH_TAC `~((y:real^3) IN moi_s5b_kp Q s k)` THEN
    UNDISCH_TAC `IMAGE (moi_s35_lift cq) jq = moi_s5b_kp (Q:real^3->real->real^3) s k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[moi_s5b_dp] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(inside(jq:real^2->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_INSIDE THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON; PL_POLYHEDRON_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^3) IN B)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5b_dp Q c d0 s k INTER B = moi_s5b_kp (Q:real^3->real->real^3) s k` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s5b_dp Q c d0 s k` THEN
    UNDISCH_TAC `~((y:real^3) IN moi_s5b_kp Q s k)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `inside(jq:real^2->bool)` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `moi_s5b_otube` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[MOI_S5B_OTUBE] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `!z. z IN moi_s5b_dp Q c d0 s k
                     ==> z$3 = cq /\ z IN moi_s5b_otube` THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `(:real^3) DIFF B` OPEN_CONTAINS_BALL) THEN
  SUBGOAL_THEN `open((:real^3) DIFF B)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r1 (min r2 r3) / &2` THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < r1`; `&0 < r2`; `&0 < r3`] THEN REAL_ARITH_TAC;
    TRANS_TAC SUBSET_TRANS `ball(y:real^3,r2)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < r1`; `&0 < r2`; `&0 < r3`] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `cball(y:real^3,min r1 (min r2 r3) / &2) SUBSET ball(y,r3)` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < r1`; `&0 < r2`; `&0 < r3`] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `ball(y:real^3,r3) SUBSET (:real^3) DIFF B` THEN SET_TAC[]];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_CBALL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_s5b_proj x IN inside(jq:real^2->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(z:real^2,r1) SUBSET inside jq` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_BALL; dist] THEN
      SUBGOAL_THEN `z:real^2 = moi_s5b_proj y` SUBST1_TAC THENL
       [EXPAND_TAC "y" THEN REWRITE_TAC[MOI_S5B_PROJ_LIFT]; ALL_TAC] THEN
      MP_TAC MOI_S5B_PROJ_FACTS THEN STRIP_TAC THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_SUB th)]) THEN
      MP_TAC(SPEC `y - x:real^3` MOI_S5B_PROJ_NORM) THEN
      UNDISCH_TAC `dist(y:real^3,x) <= min r1 (min r2 r3) / &2` THEN
      REWRITE_TAC[dist] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < r1`; `&0 < r2`; `&0 < r3`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[moi_s5b_dp] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `moi_s5b_proj x` THEN
    ASM_SIMP_TAC[MOI_S5B_PROJ_LIFT; IN_UNION]]);;

let moi_s5b_tset = new_definition
 `moi_s5b_tset (phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s <=>
    moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
    B = {x | x IN moi_s35_dom /\ phi x IN b} /\
    moi_s5b_setting B K FF GG Q c d0 k j E s /\
    (?ke. ke IN components {x | x IN B /\ x$3 = c} /\ DISJOINT ke E) /\
    IMAGE phi (IMAGE FF (relative_frontier
      (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) = b0 /\
    IMAGE phi (IMAGE FF (relative_frontier
      (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))) = b1`;;

let MOI_S5B_TSET_BASIC = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> pl_map_on moi_s35_dom phi /\
         (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y) /\
         phi continuous_on moi_s35_dom /\
         B SUBSET interior moi_s35_stube /\ IMAGE phi B = b /\
         b SUBSET frontier xb /\
         frontier xb INTER IMAGE phi moi_s35_ttube SUBSET b /\
         pl_sphere 2 (frontier xb) /\
         frontier xb homeomorphic sphere(vec 0:real^3,&1) /\
         xb = frontier xb UNION inside(frontier xb) /\
         interior xb = inside(frontier xb) /\ compact xb /\ compact (frontier xb) /\
         interior moi_s35_stube SUBSET moi_s5b_u /\ moi_s5b_u SUBSET moi_s35_dom /\
         open moi_s5b_u /\ moi_s5b_u SUBSET moi_s35_slab /\
         moi_s5b_otube SUBSET interior moi_s35_stube /\
         moi_s5b_otube SUBSET moi_s35_ttube /\
         moi_s5b_ep Q s k E SUBSET B /\
         moi_s5b_dp Q c d0 s k SUBSET moi_s5b_otube /\
         moi_s5b_kp Q s k SUBSET moi_s5b_ep Q s k E /\
         moi_s5b_kp Q s k SUBSET moi_s5b_dp Q c d0 s k /\
         moi_s5b_ep Q s k E INTER moi_s5b_dp Q c d0 s k = moi_s5b_kp Q s k /\
         moi_s5b_dp Q c d0 s k INTER B = moi_s5b_kp Q s k /\
         compact B /\
         (?pinv. pl_homeomorphism (moi_s35_slab,IMAGE phi moi_s35_slab) (phi,pinv))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5b_tset] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_s35_edge_conf] th)) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `b:real^3->bool`] MOI_S5B_B_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try lhs(concl th) = `B:real^3->bool` with Failure _ -> false)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SETTING_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_EP_SETS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SIGMA_SPHERE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_B) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_PL_BALL_3_FILL o check (fun th ->
    try concl th = `pl_ball 3 (xb:real^3->bool)` with Failure _ -> false)) THEN
  MP_TAC MOI_S5B_U_FACTS THEN MP_TAC MOI_S5B_OTUBE THEN MP_TAC MOI_S5B_OTUBE_STUBE THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
    ASM_MESON_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[COMPACT_FRONTIER];
    TRANS_TAC SUBSET_TRANS `moi_s35_stube` THEN ASM_REWRITE_TAC[INTERIOR_SUBSET];
    UNDISCH_TAC `!z. z IN moi_s5b_dp Q c d0 s k
                     ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC MOI_S5B_PHI_SLAB THEN ASM_REWRITE_TAC[]]);;

let MOI_S5B_INJ_IMAGE = prove
 (`!(f:A->B) D X Y.
     (!x y. x IN D /\ y IN D /\ f x = f y ==> x = y) /\ X SUBSET D /\ Y SUBSET D
     ==> IMAGE f (X INTER Y) = IMAGE f X INTER IMAGE f Y /\
         IMAGE f (X DIFF Y) = IMAGE f X DIFF IMAGE f Y /\
         (!x. x IN D ==> (f x IN IMAGE f X <=> x IN X))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[]]);;

let MOI_S5B_RF_SQUARE = prove
 (`!r. &0 < r
       ==> relative_frontier(interval[--vector[r;r]:real^2,vector[r;r]]) =
           interval[--vector[r;r],vector[r;r]] DIFF
           interval(--vector[r;r],vector[r;r])`,
  REPEAT STRIP_TAC THEN
  W(fun (_,w) -> MP_TAC(PART_MATCH (lhand o rand)
     RELATIVE_FRONTIER_NONEMPTY_INTERIOR (lhand w))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `vec 0:real^2` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
                VECTOR_2; VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[frontier; INTERIOR_CLOSED_INTERVAL] THEN
    SIMP_TAC[CLOSURE_CLOSED; CLOSED_INTERVAL]]);;

let MOI_S5B_RF1_POINT = prove
 (`vector[&1;&0] IN relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`,
  SIMP_TAC[MOI_S5B_RF_SQUARE; REAL_LT_01] THEN
  REWRITE_TAC[IN_DIFF; MOI_S5B_IN_BOX; VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S5B_TCELLS = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> pl_cell_with_boundary 2 (IMAGE phi (moi_s5b_ep Q s k E))
                                 (IMAGE phi (moi_s5b_kp Q s k)) /\
         pl_cell_with_boundary 2 (IMAGE phi (moi_s5b_dp Q c d0 s k))
                                 (IMAGE phi (moi_s5b_kp Q s k)) /\
         pl_sphere 2 (IMAGE phi (moi_s5b_sg Q c d0 s k E)) /\
         IMAGE phi (moi_s5b_ep Q s k E) SUBSET frontier xb /\
         IMAGE phi (moi_s5b_ep Q s k E) INTER IMAGE phi (moi_s5b_dp Q c d0 s k) =
         IMAGE phi (moi_s5b_kp Q s k) /\
         frontier xb INTER IMAGE phi (moi_s5b_dp Q c d0 s k) SUBSET
         IMAGE phi (moi_s5b_kp Q s k) /\
         (?w. w IN frontier xb /\ ~(w IN IMAGE phi (moi_s5b_ep Q s k E))) /\
         IMAGE phi (moi_s5b_kp Q s k) SUBSET
         closure (frontier xb DIFF IMAGE phi (moi_s5b_ep Q s k E))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TSET_BASIC th) THEN
    MP_TAC(REWRITE_RULE[moi_s5b_tset] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_CELL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_CELL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SIGMA_SPHERE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_ENDS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_CLOSURE) THEN
  SUBGOAL_THEN `(B:real^3->bool) SUBSET moi_s35_slab /\ B SUBSET moi_s35_dom /\
                moi_s5b_dp Q c d0 s k SUBSET moi_s35_slab /\
                moi_s5b_dp Q c d0 s k SUBSET moi_s35_dom /\
                moi_s5b_dp Q c d0 s k SUBSET moi_s35_ttube`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(B:real^3->bool) SUBSET interior moi_s35_stube`;
      `interior moi_s35_stube SUBSET moi_s5b_u`; `moi_s5b_u SUBSET moi_s35_dom`;
      `moi_s5b_u SUBSET moi_s35_slab`; `moi_s5b_otube SUBSET interior moi_s35_stube`;
      `moi_s5b_otube SUBSET moi_s35_ttube`;
      `moi_s5b_dp Q c d0 s k SUBSET moi_s5b_otube`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s5b_ep Q s k E SUBSET moi_s35_slab /\
                moi_s5b_ep Q s k E SUBSET moi_s35_dom`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(B:real^3->bool) SUBSET moi_s35_slab`; `(B:real^3->bool) SUBSET moi_s35_dom`;
      `moi_s5b_ep Q s k E SUBSET (B:real^3->bool)`] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `moi_s5b_ep Q s k E`;
                 `moi_s5b_dp Q c d0 s k`] MOI_S5B_INJ_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `moi_s5b_dp Q c d0 s k`;
                 `B:real^3->bool`] MOI_S5B_INJ_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_CELL_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`moi_s35_slab`; `IMAGE (phi:real^3->real^3) moi_s35_slab`;
                          `pinv:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5B_CELL_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`moi_s35_slab`; `IMAGE (phi:real^3->real^3) moi_s35_slab`;
                          `pinv:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5B_SPHERE_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`moi_s35_slab`; `IMAGE (phi:real^3->real^3) moi_s35_slab`;
                          `pinv:real^3->real^3`] THEN
    ASM_REWRITE_TAC[moi_s5b_sg; UNION_SUBSET];
    MAP_EVERY UNDISCH_TAC [`moi_s5b_ep Q s k E SUBSET (B:real^3->bool)`;
      `IMAGE (phi:real^3->real^3) B = b`; `b SUBSET frontier (xb:real^3->bool)`] THEN
    SET_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE (phi:real^3->real^3) (moi_s5b_dp Q c d0 s k INTER B) =
                 IMAGE phi (moi_s5b_dp Q c d0 s k) INTER IMAGE phi B` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`frontier xb INTER IMAGE (phi:real^3->real^3) moi_s35_ttube SUBSET b`;
      `moi_s5b_dp Q c d0 s k SUBSET moi_s35_ttube`] THEN
    SET_TAC[];
    SUBGOAL_THEN `(FF:real^2->real^3) (vector[&1;&0]) IN B /\
                  ~(FF (vector[&1;&0]:real^2) IN moi_s5b_ep Q s k E)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC MOI_S5B_RF1_POINT THEN MP_TAC MOI_S5B_A0_FACTS THEN
      UNDISCH_TAC `moi_s5b_setting B K FF GG Q c d0 k j E s` THEN
      REWRITE_TAC[moi_s5b_setting; moi_s5b_mset; pl_homeomorphism; homeomorphism] THEN
      STRIP_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `DISJOINT (moi_s5b_ep Q s k E)
          (IMAGE FF (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
           IMAGE FF (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])))` THEN
      UNDISCH_TAC `IMAGE (FF:real^2->real^3)
          (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
           interval(--vector[&1;&1]:real^2,vector[&1;&1])) = B` THEN
      UNDISCH_TAC `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
          interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
          interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
      UNDISCH_TAC `vector[&1;&0] IN
          relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
      SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `(phi:real^3->real^3) (FF (vector[&1;&0]:real^2))` THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`IMAGE (phi:real^3->real^3) B = b`;
        `b SUBSET frontier (xb:real^3->bool)`;
        `(FF:real^2->real^3) (vector[&1;&0]) IN B`] THEN
      SET_TAC[];
      SUBGOAL_THEN `(FF:real^2->real^3) (vector[&1;&0]) IN moi_s35_dom` ASSUME_TAC THENL
       [UNDISCH_TAC `(B:real^3->bool) SUBSET moi_s35_dom` THEN
        UNDISCH_TAC `(FF:real^2->real^3) (vector[&1;&0]) IN B` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `moi_s5b_ep Q s k E`;
                     `moi_s5b_dp Q c d0 s k`] MOI_S5B_INJ_IMAGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `(FF:real^2->real^3) (vector[&1;&0])` o
                 CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[ASSUME `(FF:real^2->real^3) (vector[&1;&0]) IN moi_s35_dom`;
        ASSUME `~((FF:real^2->real^3) (vector[&1;&0]) IN moi_s5b_ep Q s k E)`] THEN
      MESON_TAC[]];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (phi:real^3->real^3) (closure (B DIFF moi_s5b_ep Q s k E))` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[] THEN TRANS_TAC SUBSET_TRANS `B:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier xb DIFF IMAGE (phi:real^3->real^3) (moi_s5b_ep Q s k E)` THEN
    REWRITE_TAC[CLOSURE_SUBSET] THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `B:real^3->bool`;
                   `moi_s5b_ep Q s k E`] MOI_S5B_INJ_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    MAP_EVERY UNDISCH_TAC [`IMAGE (phi:real^3->real^3) B = b`;
                           `b SUBSET frontier (xb:real^3->bool)`] THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The new sphere S' = a1 UNION phi D' (a1 = S minus the open disk phi E'),  *)
(* its PL sphere structure, the flatness of phi D' and the theta lemma.     *)
(* ------------------------------------------------------------------------- *)

let moi_s5b_ta1 = new_definition
 `moi_s5b_ta1 (phi:real^3->real^3) xb Q s k E =
    frontier xb DIFF
    (IMAGE phi (moi_s5b_ep Q s k E) DIFF IMAGE phi (moi_s5b_kp Q s k))`;;

let moi_s5b_tsp = new_definition
 `moi_s5b_tsp (phi:real^3->real^3) xb Q c d0 s k E =
    moi_s5b_ta1 phi xb Q s k E UNION IMAGE phi (moi_s5b_dp Q c d0 s k)`;;

let moi_s5b_txb = new_definition
 `moi_s5b_txb (phi:real^3->real^3) xb Q c d0 s k E =
    moi_s5b_tsp phi xb Q c d0 s k E UNION inside (moi_s5b_tsp phi xb Q c d0 s k E)`;;

let MOI_S5B_TA1 = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> closed (moi_s5b_ta1 phi xb Q s k E) /\
         moi_s5b_ta1 phi xb Q s k E INTER IMAGE phi (moi_s5b_ep Q s k E) =
         IMAGE phi (moi_s5b_kp Q s k) /\
         moi_s5b_ta1 phi xb Q s k E INTER IMAGE phi (moi_s5b_dp Q c d0 s k) =
         IMAGE phi (moi_s5b_kp Q s k) /\
         connected (moi_s5b_ta1 phi xb Q s k E DIFF IMAGE phi (moi_s5b_kp Q s k)) /\
         moi_s5b_ta1 phi xb Q s k E UNION IMAGE phi (moi_s5b_ep Q s k E) = frontier xb /\
         locally_polyhedral (moi_s5b_ta1 phi xb Q s k E) /\
         moi_s5b_ta1 phi xb Q s k E SUBSET frontier xb`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_TSET_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_TCELLS) THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^3) (moi_s5b_kp Q s k) SUBSET
                IMAGE phi (moi_s5b_dp Q c d0 s k)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s5b_ta1] THEN
  ABBREV_TAC `ee = IMAGE (phi:real^3->real^3) (moi_s5b_ep Q s k E)` THEN
  ABBREV_TAC `jj = IMAGE (phi:real^3->real^3) (moi_s5b_kp Q s k)` THEN
  ABBREV_TAC `dd = IMAGE (phi:real^3->real^3) (moi_s5b_dp Q c d0 s k)` THEN
  ABBREV_TAC `S = frontier (xb:real^3->bool)` THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `ee:real^3->bool`; `jj:real^3->bool`; `w:real^3`]
    MOI_S5B_SPHERE_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (S DIFF (ee DIFF jj):real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_IN_DIFF; CLOSED_IN_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(ee:real^3->bool) SUBSET S`; `(jj:real^3->bool) SUBSET ee`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(ee:real^3->bool) SUBSET S`; `(jj:real^3->bool) SUBSET ee`;
      `(S:real^3->bool) INTER dd SUBSET jj`; `(jj:real^3->bool) SUBSET dd`] THEN
    SET_TAC[];
    SUBGOAL_THEN `S DIFF (ee DIFF jj) DIFF jj = S DIFF ee:real^3->bool` SUBST1_TAC THENL
     [UNDISCH_TAC `(jj:real^3->bool) SUBSET ee` THEN SET_TAC[]; ASM_REWRITE_TAC[]];
    UNDISCH_TAC `(ee:real^3->bool) SUBSET S` THEN SET_TAC[];
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `S DIFF (ee DIFF jj) = closure(S DIFF ee:real^3->bool)` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `S DIFF ee:real^3->bool` CLOSURE_SUBSET) THEN
        UNDISCH_TAC `jj SUBSET closure (S DIFF ee:real^3->bool)` THEN SET_TAC[];
        MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
      MATCH_MP_TAC MOI_S5B_CLOSURE_DIFF_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `2` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_S5B_CELL_POLYHEDRON THEN
        MAP_EVERY EXISTS_TAC [`2`; `jj:real^3->bool`] THEN ASM_REWRITE_TAC[]]];
    SET_TAC[]]);;

let MOI_S5B_TSP_SPHERE = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> pl_sphere 2 (moi_s5b_tsp phi xb Q c d0 s k E)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_TSET_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_TCELLS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_TA1) THEN
  MP_TAC(ISPECL [`moi_s5b_ta1 (phi:real^3->real^3) xb Q s k E`;
                 `IMAGE (phi:real^3->real^3) (moi_s5b_ep Q s k E)`;
                 `IMAGE (phi:real^3->real^3) (moi_s5b_dp Q c d0 s k)`;
                 `IMAGE (phi:real^3->real^3) (moi_s5b_kp Q s k)`] MOI_S5B_DISK_REPLACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_s5b_tsp] THEN MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
  MAP_EVERY EXISTS_TAC [`frontier xb:real^3->bool`; `h:real^3->real^3`;
                        `h':real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5B_HALF_CLOSURE = prove
 (`!(f:real^3->real^3) y r a D.
     f continuous_on D /\ cball(y,r) SUBSET D /\ &0 < r
     ==> !x. x IN ball(y,r) /\ x$3 = a
             ==> f x IN closure (IMAGE f (ball(y,r) INTER {x | x$3 > a})) /\
                 f x IN closure (IMAGE f (ball(y,r) INTER {x | x$3 < a}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!h:real^3->bool. x IN closure h /\ closure(ball(y,r) INTER h) SUBSET cball(y,r)
                     ==> (f:real^3->real^3) x IN closure (IMAGE f (ball(y,r) INTER h))`
  ASSUME_TAC THENL
   [X_GEN_TAC `h:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN closure(ball(y,r) INTER h)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`ball(y:real^3,r)`; `h:real^3->bool`] OPEN_INTER_CLOSURE_SUBSET) THEN
      REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `ball(y:real^3,r) INTER h`;
                   `closure (IMAGE (f:real^3->real^3) (ball(y,r) INTER h))`]
      IMAGE_CLOSURE_SUBSET) THEN
    REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h:real^3->bool. closure(ball(y,r) INTER h) SUBSET cball(y,r)`
  ASSUME_TAC THENL
   [GEN_TAC THEN TRANS_TAC SUBSET_TRANS `closure(ball(y:real^3,r))` THEN
    ASM_SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET; CLOSURE_BALL; SUBSET_REFL];
    ALL_TAC] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSURE_HALFSPACE_COMPONENT_GT; CLOSURE_HALFSPACE_COMPONENT_LT] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5B_TFLAT = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> moi_s5b_flat (moi_s5b_ta1 phi xb Q s k E UNION
                       IMAGE phi (moi_s5b_ep Q s k E) UNION
                       IMAGE phi (moi_s5b_dp Q c d0 s k))
                      (IMAGE phi (moi_s5b_dp Q c d0 s k))
                      (IMAGE phi (moi_s5b_dp Q c d0 s k) DIFF
                       IMAGE phi (moi_s5b_kp Q s k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TSET_BASIC th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TA1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TCELLS th) THEN
    MP_TAC(REWRITE_RULE[moi_s5b_tset] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  REWRITE_TAC[moi_s5b_flat] THEN X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `~((y:real^3) IN moi_s5b_kp Q s k)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((phi:real^3->real^3) y IN IMAGE phi (moi_s5b_kp Q s k))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
    `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`; `s:real`; `y:real^3`]
    MOI_S5B_DP_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `cq = moi_s5b_cp c d0 s` THEN
  SUBGOAL_THEN `cball(y:real^3,r) SUBSET moi_s35_dom /\ ball(y,r) SUBSET moi_s5b_u /\
                ball(y,r) SUBSET cball(y,r) /\ cball(y,r) SUBSET moi_s35_ttube /\
                moi_s5b_dp Q c d0 s k SUBSET moi_s35_dom /\
                (B:real^3->bool) SUBSET moi_s35_dom`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BALL_SUBSET_CBALL] THEN
    MAP_EVERY UNDISCH_TAC
     [`cball(y:real^3,r) SUBSET moi_s5b_otube`; `moi_s5b_otube SUBSET moi_s35_ttube`;
      `moi_s5b_otube SUBSET interior moi_s35_stube`;
      `interior moi_s35_stube SUBSET moi_s5b_u`; `moi_s5b_u SUBSET moi_s35_dom`;
      `moi_s5b_dp Q c d0 s k SUBSET moi_s5b_otube`;
      `(B:real^3->bool) SUBSET interior moi_s35_stube`] THEN
    MP_TAC(ISPECL [`y:real^3`; `r:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi:real^3->real^3) (ball(y,r))`;
    `IMAGE (phi:real^3->real^3) (ball(y,r) INTER {x | x$3 > cq})`;
    `IMAGE (phi:real^3->real^3) (ball(y,r) INTER {x | x$3 < cq})`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_PHI_OPEN THEN ASM_REWRITE_TAC[OPEN_BALL];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    SUBGOAL_THEN `DISJOINT (IMAGE (phi:real^3->real^3) (ball(y,r))) (frontier xb)`
    MP_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `w0:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      SUBGOAL_THEN `(w0:real^3) IN b` MP_TAC THENL
       [UNDISCH_TAC `frontier xb INTER IMAGE (phi:real^3->real^3) moi_s35_ttube SUBSET b` THEN
        REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^3) B = b` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^3 = x'` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\
                           (phi:real^3->real^3) x = phi y ==> x = y` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT (cball(y:real^3,r)) B` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`moi_s5b_ta1 (phi:real^3->real^3) xb Q s k E SUBSET frontier xb`;
      `IMAGE (phi:real^3->real^3) (moi_s5b_ep Q s k E) SUBSET frontier xb`] THEN
    SET_TAC[];
    MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `ball(y:real^3,r)`;
                   `moi_s5b_dp Q c d0 s k`] MOI_S5B_INJ_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2 th))]) THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN ball(y,r)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(x:real^3)$3 = cq` THENL
     [SUBGOAL_THEN `(x:real^3) IN moi_s5b_dp Q c d0 s k` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `!x. x IN cball(y:real^3,r) /\ x$3 = cq
                         ==> x IN moi_s5b_dp Q c d0 s k` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `~((x:real^3) IN moi_s5b_dp Q c d0 s k)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `!z. z IN moi_s5b_dp Q c d0 s k
                         ==> z$3 = cq /\ z IN moi_s5b_otube` THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_COMPONENT_GT]];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_COMPONENT_LT]];
    MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `ball(y:real^3,r)`;
                   `moi_s5b_dp Q c d0 s k`] MOI_S5B_INJ_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1 th)]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `y:real^3`; `r:real`; `cq:real`;
                   `moi_s35_dom`] MOI_S5B_HALF_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!z. z IN moi_s5b_dp Q c d0 s k
                     ==> z$3 = cq /\ z IN moi_s5b_otube` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_SIMP_TAC[]]);;

let MOI_S5B_TTHETA = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> IMAGE phi (moi_s5b_kk Q c d0 s k E) =
         IMAGE phi (moi_s5b_sg Q c d0 s k E) UNION
         inside (IMAGE phi (moi_s5b_sg Q c d0 s k E)) /\
         moi_s5b_txb phi xb Q c d0 s k E DIFF IMAGE phi (moi_s5b_kk Q c d0 s k E) =
         xb DIFF IMAGE phi (moi_s5b_kk Q c d0 s k E)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TSET_BASIC th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TA1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TCELLS th) THEN
    ASSUME_TAC(MATCH_MP MOI_S5B_TFLAT th) THEN
    ASSUME_TAC(MATCH_MP MOI_S5B_TSP_SPHERE th) THEN
    MP_TAC(REWRITE_RULE[moi_s5b_tset] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_KK) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_SG_FACTS) THEN
  SUBGOAL_THEN `moi_s5b_kk Q c d0 s k E SUBSET moi_s5b_u /\
                moi_s5b_kk Q c d0 s k E SUBSET moi_s35_dom`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`moi_s5b_kk Q c d0 s k E SUBSET interior moi_s35_stube`;
      `interior moi_s35_stube SUBSET moi_s5b_u`; `moi_s5b_u SUBSET moi_s35_dom`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s5b_u`; `moi_s5b_sg Q c d0 s k E`]
    MOI_S5B_INSIDE_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\
                         (phi:real^3->real^3) x = phi y ==> x = y` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s5b_kk Q c d0 s k E SUBSET moi_s5b_u` THEN
      REWRITE_TAC[moi_s5b_kk]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^3) (moi_s5b_kk Q c d0 s k E) =
                IMAGE phi (moi_s5b_sg Q c d0 s k E) UNION
                inside (IMAGE phi (moi_s5b_sg Q c d0 s k E))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s5b_kk; IMAGE_UNION]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs c <= &1 / &512` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_edge_conf (phi:real^3->real^3) xa xb ww b b0 b1 c` THEN
    SIMP_TAC[moi_s35_edge_conf];
    ALL_TAC] THEN
  ABBREV_TAC `q = vector[&3 / &16; &0; c]:real^3` THEN
  SUBGOAL_THEN `(q:real^3) IN moi_s35_sq (&3 / &16) c /\ q IN moi_s35_dom`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s35_sq; moi_s35_n; IN_ELIM_THM; VECTOR_3] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `moi_s5b_u SUBSET moi_s35_dom` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[MOI_S5B_IN_U; VECTOR_3] THEN
      UNDISCH_TAC `abs c <= &1 / &512` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real^3) q IN inside(frontier xb)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try lhs(concl th) = `interior (xb:real^3->bool)` with Failure _ -> false)) THEN
    UNDISCH_TAC `moi_s35_edge_conf (phi:real^3->real^3) xa xb ww b b0 b1 c` THEN
    REWRITE_TAC[moi_s35_edge_conf] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^3) (moi_s35_sq (&3 / &16) c) SUBSET interior xb` THEN
    UNDISCH_TAC `(q:real^3) IN moi_s35_sq (&3 / &16) c` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real^3) q IN outside(IMAGE phi (moi_s5b_sg Q c d0 s k E))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~((q:real^3) IN moi_s5b_kk Q c d0 s k E)` ASSUME_TAC THENL
     [UNDISCH_TAC `DISJOINT (moi_s5b_kk Q c d0 s k E)
                     (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c)` THEN
      UNDISCH_TAC `(q:real^3) IN moi_s35_sq (&3 / &16) c` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((phi:real^3->real^3) q IN IMAGE phi (moi_s5b_kk Q c d0 s k E))`
    MP_TAC THENL
     [MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `moi_s5b_kk Q c d0 s k E`;
                     `moi_s5b_kk Q c d0 s k E`] MOI_S5B_INJ_IMAGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `q:real^3` o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[ASSUME `(q:real^3) IN moi_s35_dom`;
                  ASSUME `~((q:real^3) IN moi_s5b_kk Q c d0 s k E)`];
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `IMAGE (phi:real^3->real^3) (moi_s5b_kk Q c d0 s k E) =
                IMAGE phi (moi_s5b_sg Q c d0 s k E) UNION
                inside (IMAGE phi (moi_s5b_sg Q c d0 s k E))`] THEN
    REWRITE_TAC[UNION_WITH_INSIDE; IN_DIFF; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (phi:real^3->real^3) (moi_s5b_ep Q s k E)) /\
                compact (IMAGE (phi:real^3->real^3) (moi_s5b_dp Q c d0 s k))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S5B_CELL_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s5b_ta1 (phi:real^3->real^3) xb Q s k E`;
                 `IMAGE (phi:real^3->real^3) (moi_s5b_ep Q s k E)`;
                 `IMAGE (phi:real^3->real^3) (moi_s5b_dp Q c d0 s k)`;
                 `IMAGE (phi:real^3->real^3) (moi_s5b_kp Q s k)`;
                 `(phi:real^3->real^3) q`] MOI_S5B_THETA) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5B_CELL_OPEN_CONN THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5B_CELL_INTERIOR_NONEMPTY THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC MOI_S5B_CELL_OPEN_CONN THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5B_CELL_INTERIOR_NONEMPTY THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM moi_s5b_tsp] THEN
      MATCH_MP_TAC MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM IMAGE_UNION; GSYM moi_s5b_sg] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM IMAGE_UNION; GSYM moi_s5b_sg] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[GSYM IMAGE_UNION; GSYM moi_s5b_sg;
                                    GSYM moi_s5b_tsp]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[moi_s5b_txb] THEN
  UNDISCH_TAC `xb = frontier xb UNION inside(frontier (xb:real^3->bool))` THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The new configuration (xb',b') = (S' UNION inside S', phi B'): the edge  *)
(* configuration clauses one by one.                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_S5B_BP_FACTS = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s
     ==> moi_s5b_bp B Q c d0 s k E SUBSET interior moi_s35_stube /\
         pl_polyhedron (moi_s5b_bp B Q c d0 s k E) /\
         moi_s5b_dp Q c d0 s k SUBSET moi_s5b_bp B Q c d0 s k E /\
         moi_s5b_ba B Q s k E SUBSET moi_s5b_bp B Q c d0 s k E /\
         moi_s5b_bp B Q c d0 s k E =
         moi_s5b_ba B Q s k E UNION moi_s5b_dp Q c d0 s k /\
         moi_s5b_ba B Q s k E = B DIFF (moi_s5b_ep Q s k E DIFF moi_s5b_kp Q s k) /\
         IMAGE FF (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
         SUBSET moi_s5b_ba B Q s k E /\
         IMAGE FF (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))
         SUBSET moi_s5b_ba B Q s k E`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_EP_ENDS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S5B_BP_TRIANG) THEN
  SUBGOAL_THEN
   `(B:real^3->bool) SUBSET interior moi_s35_stube /\
    IMAGE (FF:real^2->real^3)
      (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])) = B`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5b_setting B K FF GG Q c d0 k j E s` THEN
    REWRITE_TAC[moi_s5b_setting; moi_s5b_mset; pl_homeomorphism; homeomorphism] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s5b_bp; moi_s5b_ba] THEN REPEAT CONJ_TAC THENL
   [MP_TAC MOI_S5B_OTUBE_STUBE THEN
    UNDISCH_TAC `!z. z IN moi_s5b_dp Q c d0 s k
                     ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
    UNDISCH_TAC `(B:real^3->bool) SUBSET interior moi_s35_stube` THEN SET_TAC[];
    REWRITE_TAC[GSYM moi_s5b_ba; GSYM moi_s5b_bp] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try fst(dest_const(fst(strip_comb(rhs(concl th))))) = "moi_s5b_bp"
      with Failure _ -> false)) THEN
    ASM_SIMP_TAC[MOI_S5B_SC_POLYHEDRON];
    SET_TAC[];
    SET_TAC[];
    MP_TAC MOI_S5B_A0_FACTS THEN STRIP_TAC THEN
    UNDISCH_TAC `DISJOINT (moi_s5b_ep Q s k E)
          (IMAGE FF (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
           IMAGE FF (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])))` THEN
    UNDISCH_TAC `IMAGE (FF:real^2->real^3)
      (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])) = B` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
          interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
          interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
    SET_TAC[];
    MP_TAC MOI_S5B_A0_FACTS THEN STRIP_TAC THEN
    UNDISCH_TAC `DISJOINT (moi_s5b_ep Q s k E)
          (IMAGE FF (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) UNION
           IMAGE FF (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])))` THEN
    UNDISCH_TAC `IMAGE (FF:real^2->real^3)
      (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])) = B` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
          interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
          interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
    SET_TAC[]]);;

let MOI_S5B_TXB = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     PL_SCHOENFLIES_3_STATEMENT /\
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> pl_ball 3 (moi_s5b_txb phi xb Q c d0 s k E) /\
         frontier (moi_s5b_txb phi xb Q c d0 s k E) =
         moi_s5b_tsp phi xb Q c d0 s k E /\
         interior (moi_s5b_txb phi xb Q c d0 s k E) =
         inside (moi_s5b_tsp phi xb Q c d0 s k E)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_TSP_SPHERE) THEN
  REWRITE_TAC[moi_s5b_txb] THEN CONJ_TAC THENL
   [UNDISCH_TAC `!s:real^3->bool. pl_sphere 2 s ==> pl_ball 3 (s UNION inside s)` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_FILLED_FRONTIER) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S5B_SQ_U = prove
 (`!r c. r < &1 /\ abs c < &1 / &8 ==> moi_s35_sq r c SUBSET moi_s5b_u`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; moi_s35_sq; moi_s35_n; IN_ELIM_THM; MOI_S5B_IN_U] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S5B_DOM_CUBE = prove
 (`moi_s35_dom SUBSET moi_s35_cube`,
  REWRITE_TAC[moi_s35_dom; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S5B_TCLAUSES_A = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     PL_SCHOENFLIES_3_STATEMENT /\
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> moi_s5b_txb phi xb Q c d0 s k E UNION IMAGE phi moi_s35_stube UNION
         inside (moi_s5b_txb phi xb Q c d0 s k E UNION IMAGE phi moi_s35_stube)
         SUBSET ww /\
         frontier xa INTER moi_s5b_txb phi xb Q c d0 s k E SUBSET
         IMAGE phi {x | x IN moi_s35_level c /\ moi_s35_n x < &5 / &16} /\
         frontier xa INTER frontier (moi_s5b_txb phi xb Q c d0 s k E) SUBSET
         IMAGE phi (moi_s35_aflat c) /\
         IMAGE phi (moi_s35_sq (&3 / &16) c) SUBSET
         interior (moi_s5b_txb phi xb Q c d0 s k E) /\
         DISJOINT (IMAGE phi (moi_s35_sq (&5 / &16) c))
                  (moi_s5b_txb phi xb Q c d0 s k E)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TXB th) THEN
    MP_TAC(CONJUNCT2 th)) THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TSET_BASIC th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TTHETA th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TA1 th) THEN
    MP_TAC(REWRITE_RULE[moi_s5b_tset] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
    (filter (fun t -> not (is_exists (concl t)))
      (CONJUNCTS (REWRITE_RULE[moi_s35_edge_conf] th)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_KK) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_DP_LEVEL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_CP_FACTS) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `c:real`] MOI_S5B_XA_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_MESON_TAC[MOI_S5B_PL_BALL_3_FILL];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(rand(lhs(concl th)))))) = "moi_s5b_kk"
        && is_eq(concl th) &&
        fst(dest_const(fst(strip_comb(rhs(concl th))))) = "UNION"
    with Failure _ -> false)) THEN
  SUBGOAL_THEN `moi_s5b_kk Q c d0 s k E SUBSET moi_s5b_u /\
                moi_s5b_kk Q c d0 s k E SUBSET moi_s35_dom /\
                moi_s5b_kk Q c d0 s k E SUBSET moi_s35_stube /\
                moi_s5b_dp Q c d0 s k SUBSET moi_s5b_u /\
                moi_s35_sq (&3 / &16) c SUBSET moi_s5b_u /\
                moi_s35_sq (&5 / &16) c SUBSET moi_s5b_u`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC MOI_S5B_SQ_U THEN
      UNDISCH_TAC `abs c <= &1 / &512` THEN REAL_ARITH_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`moi_s5b_kk Q c d0 s k E SUBSET interior moi_s35_stube`;
      `interior moi_s35_stube SUBSET moi_s5b_u`; `moi_s5b_u SUBSET moi_s35_dom`;
      `moi_s5b_otube SUBSET interior moi_s35_stube`;
      `moi_s5b_dp Q c d0 s k SUBSET moi_s5b_otube`] THEN
    MP_TAC(ISPEC `moi_s35_stube` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Bl = IMAGE (phi:real^3->real^3) (moi_s5b_kk Q c d0 s k E)` THEN
  ABBREV_TAC `xb' = moi_s5b_txb (phi:real^3->real^3) xb Q c d0 s k E` THEN
  SUBGOAL_THEN `!y. y IN moi_s35_dom ==> ((phi:real^3->real^3) y IN Bl <=>
                                           y IN moi_s5b_kk Q c d0 s k E)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Bl" THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `moi_s5b_kk Q c d0 s k E`;
                   `moi_s5b_kk Q c d0 s k E`] MOI_S5B_INJ_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (Bl:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Bl" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `moi_s35_dom` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Bl:real^3->bool) SUBSET IMAGE phi moi_s35_stube` ASSUME_TAC THENL
   [EXPAND_TAC "Bl" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `xb' UNION IMAGE (phi:real^3->real^3) moi_s35_stube =
                  xb UNION IMAGE phi moi_s35_stube` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`xb' DIFF Bl = xb DIFF (Bl:real^3->bool)`;
        `(Bl:real^3->bool) SUBSET IMAGE phi moi_s35_stube`] THEN SET_TAC[];
      REWRITE_TAC[GSYM UNION_ASSOC] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[UNION_ASSOC] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(z:real^3) IN Bl` THENL
     [UNDISCH_TAC `(z:real^3) IN Bl` THEN EXPAND_TAC "Bl" THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) IN moi_s5b_u /\ y IN moi_s35_cube` STRIP_ASSUME_TAC THENL
       [MP_TAC MOI_S5B_DOM_CUBE THEN
        MAP_EVERY UNDISCH_TAC [`moi_s5b_kk Q c d0 s k E SUBSET moi_s5b_u`;
          `moi_s5b_kk Q c d0 s k E SUBSET moi_s35_dom`;
          `(y:real^3) IN moi_s5b_kk Q c d0 s k E`] THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^3)$3 = c` ASSUME_TAC THENL
       [UNDISCH_TAC `!x. x IN moi_s5b_u
                         ==> ((phi:real^3->real^3) x IN xa <=> x$3 <= c) /\
                             (phi x IN interior xa <=> x$3 < c) /\
                             (phi x IN frontier xa <=> x$3 = c)` THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM; moi_s35_level] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!x. x IN moi_s5b_kk Q c d0 s k E /\ x$3 = c
                       ==> moi_s35_n x < &5 / &16` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `frontier xa INTER xb SUBSET
        IMAGE (phi:real^3->real^3) {x | x IN moi_s35_level c /\ moi_s35_n x < &5 / &16}` THEN
      MAP_EVERY UNDISCH_TAC [`xb' DIFF Bl = xb DIFF (Bl:real^3->bool)`;
        `~((z:real^3) IN Bl)`; `(z:real^3) IN xb'`; `(z:real^3) IN frontier xa`] THEN
      SPEC_TAC(`IMAGE (phi:real^3->real^3)
                  {x | x IN moi_s35_level c /\ moi_s35_n x < &5 / &16}`,
               `W:real^3->bool`) THEN
      SET_TAC[]];
    ASM_REWRITE_TAC[moi_s5b_tsp] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNION] THEN X_GEN_TAC `z:real^3` THEN
    STRIP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`frontier xa INTER frontier xb SUBSET IMAGE (phi:real^3->real^3) (moi_s35_aflat c)`;
        `moi_s5b_ta1 (phi:real^3->real^3) xb Q s k E SUBSET frontier xb`;
        `(z:real^3) IN moi_s5b_ta1 phi xb Q s k E`; `(z:real^3) IN frontier xa`] THEN
      SET_TAC[];
      UNDISCH_TAC `(z:real^3) IN IMAGE phi (moi_s5b_dp Q c d0 s k)` THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) IN moi_s5b_u` ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s5b_dp Q c d0 s k SUBSET moi_s5b_u` THEN
        UNDISCH_TAC `(y:real^3) IN moi_s5b_dp Q c d0 s k` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `!x. x IN moi_s5b_u
                       ==> ((phi:real^3->real^3) x IN xa <=> x$3 <= c) /\
                           (phi x IN interior xa <=> x$3 < c) /\
                           (phi x IN frontier xa <=> x$3 = c)` THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!z. z IN moi_s5b_dp Q c d0 s k
                       ==> z$3 = moi_s5b_cp c d0 s /\ z IN moi_s5b_otube` THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(moi_s5b_cp c d0 s = c)` THEN MESON_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((phi:real^3->real^3) y IN Bl)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN moi_s35_dom /\ ~(y IN moi_s5b_kk Q c d0 s k E)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`moi_s35_sq (&3 / &16) c SUBSET moi_s5b_u`;
          `moi_s5b_u SUBSET moi_s35_dom`;
          `DISJOINT (moi_s5b_kk Q c d0 s k E)
             (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c)`;
          `(y:real^3) IN moi_s35_sq (&3 / &16) c`] THEN SET_TAC[];
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^3->real^3) y IN interior xb` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (phi:real^3->real^3) (moi_s35_sq (&3 / &16) c) SUBSET interior xb` THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_sq (&3 / &16) c` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `interior xb INTER ((:real^3) DIFF Bl) SUBSET interior xb'` MP_TAC THENL
     [SUBGOAL_THEN `interior xb INTER ((:real^3) DIFF Bl) =
                    interior (xb' INTER ((:real^3) DIFF Bl))` SUBST1_TAC THENL
       [SUBGOAL_THEN `xb' INTER ((:real^3) DIFF Bl) = xb INTER ((:real^3) DIFF Bl)`
        SUBST1_TAC THENL
         [UNDISCH_TAC `xb' DIFF Bl = xb DIFF (Bl:real^3->bool)` THEN SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[INTERIOR_INTER] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC INTERIOR_OPEN THEN REWRITE_TAC[GSYM closed] THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]];
      UNDISCH_TAC `~((phi:real^3->real^3) y IN Bl)` THEN
      UNDISCH_TAC `(phi:real^3->real^3) y IN interior xb` THEN SET_TAC[]];
    SUBGOAL_THEN `!y. y IN moi_s35_sq (&5 / &16) c ==> ~((phi:real^3->real^3) y IN Bl)`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN moi_s35_dom /\ ~(y IN moi_s5b_kk Q c d0 s k E)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`moi_s35_sq (&5 / &16) c SUBSET moi_s5b_u`;
          `moi_s5b_u SUBSET moi_s35_dom`;
          `DISJOINT (moi_s5b_kk Q c d0 s k E)
             (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c)`;
          `(y:real^3) IN moi_s35_sq (&5 / &16) c`] THEN SET_TAC[];
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (IMAGE (phi:real^3->real^3) (moi_s35_sq (&5 / &16) c)) xb`;
      `xb' DIFF Bl = xb DIFF (Bl:real^3->bool)`;
      `!y. y IN moi_s35_sq (&5 / &16) c ==> ~((phi:real^3->real^3) y IN Bl)`] THEN
    SET_TAC[]]);;

let MOI_S5B_TCLAUSES_B = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> pl_annulus_with_ends (IMAGE phi (moi_s5b_bp B Q c d0 s k E)) b0 b1 /\
         IMAGE phi (moi_s5b_bp B Q c d0 s k E) SUBSET moi_s5b_tsp phi xb Q c d0 s k E /\
         IMAGE phi (moi_s5b_bp B Q c d0 s k E) SUBSET
         IMAGE phi (interior moi_s35_stube) /\
         moi_s5b_tsp phi xb Q c d0 s k E INTER IMAGE phi moi_s35_ttube SUBSET
         IMAGE phi (moi_s5b_bp B Q c d0 s k E)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TSET_BASIC th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TA1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TCELLS th) THEN
    MP_TAC(REWRITE_RULE[moi_s5b_tset] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_BP_FACTS) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    (try mem (fst(dest_const(fst(strip_comb(lhs(concl th))))))
             ["moi_s5b_ba"; "moi_s5b_bp"] with Failure _ -> false)))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S5B_HSWAP_EQ) THEN
  SUBGOAL_THEN `moi_s5b_bp B Q c d0 s k E SUBSET moi_s35_dom /\
                moi_s5b_ep Q s k E SUBSET moi_s35_dom /\
                moi_s5b_kp Q s k SUBSET moi_s35_dom /\
                (B:real^3->bool) SUBSET moi_s35_dom /\
                moi_s5b_ba B Q s k E SUBSET B`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5b_ba] THEN
    MAP_EVERY UNDISCH_TAC
     [`moi_s5b_bp B Q c d0 s k E SUBSET interior moi_s35_stube`;
      `(B:real^3->bool) SUBSET interior moi_s35_stube`;
      `interior moi_s35_stube SUBSET moi_s5b_u`; `moi_s5b_u SUBSET moi_s35_dom`;
      `moi_s5b_ep Q s k E SUBSET (B:real^3->bool)`;
      `moi_s5b_kp Q s k SUBSET moi_s5b_ep Q s k E`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN B
        ==> (y IN moi_s5b_ba B Q s k E <=>
             ~((phi:real^3->real^3) y IN IMAGE phi (moi_s5b_ep Q s k E) /\
               ~(phi y IN IMAGE phi (moi_s5b_kp Q s k))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s35_dom` ASSUME_TAC THENL
     [UNDISCH_TAC `(B:real^3->bool) SUBSET moi_s35_dom` THEN
      UNDISCH_TAC `(y:real^3) IN B` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `moi_s5b_ep Q s k E`;
                   `moi_s5b_kp Q s k`] MOI_S5B_INJ_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT2 o CONJUNCT2) THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `moi_s5b_kp Q s k`;
                   `moi_s5b_kp Q s k`] MOI_S5B_INJ_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[ASSUME `(y:real^3) IN moi_s35_dom`] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[moi_s5b_ba; IN_DIFF; ASSUME `(y:real^3) IN B`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s5b_bp B Q c d0 s k E`]
      MOI_S5B_PHI_EMBED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^3`)] THEN
    SUBGOAL_THEN
     `pl_homeomorphism
        (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
         interval(--vector[&1;&1]:real^2,vector[&1;&1]),B:real^3->bool)
        (FF:real^2->real^3,GG:real^3->real^2)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s5b_setting B K FF GG Q c d0 k j E s` THEN
      SIMP_TAC[moi_s5b_setting; moi_s5b_mset];
      ALL_TAC] THEN
    REWRITE_TAC[pl_annulus_with_ends] THEN
    EXISTS_TAC `(phi:real^3->real^3) o (h:real^3->real^3) o (FF:real^2->real^3)` THEN
    EXISTS_TAC `((GG:real^3->real^2) o (h':real^3->real^3)) o (g:real^3->real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `moi_s5b_bp B Q c d0 s k E` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `B:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN
     `!X. X SUBSET moi_s5b_ba B Q s k E ==> IMAGE (h:real^3->real^3) X = X`
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `!y. y IN moi_s5b_ba B Q s k E ==> (h:real^3->real^3) y = y` THEN
      UNDISCH_TAC `(X:real^3->bool) SUBSET moi_s5b_ba B Q s k E` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    REWRITE_TAC[moi_s5b_tsp; moi_s5b_ta1; moi_s5b_bp; IMAGE_UNION; UNION_SUBSET] THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN B` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s5b_ba B Q s k E SUBSET (B:real^3->bool)` THEN
      UNDISCH_TAC `(y:real^3) IN moi_s5b_ba B Q s k E` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`IMAGE (phi:real^3->real^3) B = b`;
        `b SUBSET frontier (xb:real^3->bool)`; `(y:real^3) IN B`] THEN SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN moi_s5b_ba B Q s k E` THEN
      UNDISCH_TAC `!y. y IN B
        ==> (y IN moi_s5b_ba B Q s k E <=>
             ~((phi:real^3->real^3) y IN IMAGE phi (moi_s5b_ep Q s k E) /\
               ~(phi y IN IMAGE phi (moi_s5b_kp Q s k))))` THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
      REWRITE_TAC[ASSUME `(y:real^3) IN B`] THEN MESON_TAC[]];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s5b_tsp; moi_s5b_ta1; SUBSET; IN_INTER; IN_UNION] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(z:real^3) IN b` MP_TAC THENL
       [UNDISCH_TAC `frontier xb INTER IMAGE (phi:real^3->real^3) moi_s35_ttube SUBSET b` THEN
        UNDISCH_TAC `(z:real^3) IN IMAGE phi moi_s35_ttube` THEN
        UNDISCH_TAC `(z:real^3) IN frontier xb DIFF
           (IMAGE phi (moi_s5b_ep Q s k E) DIFF IMAGE phi (moi_s5b_kp Q s k))` THEN
        SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (phi:real^3->real^3) B = b` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      EXISTS_TAC `y:real^3` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^3) IN moi_s5b_ba B Q s k E` MP_TAC THENL
       [UNDISCH_TAC `!y. y IN B
          ==> (y IN moi_s5b_ba B Q s k E <=>
               ~((phi:real^3->real^3) y IN IMAGE phi (moi_s5b_ep Q s k E) /\
                 ~(phi y IN IMAGE phi (moi_s5b_kp Q s k))))` THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
        REWRITE_TAC[ASSUME `(y:real^3) IN B`] THEN DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `(phi:real^3->real^3) y IN frontier xb DIFF
           (IMAGE phi (moi_s5b_ep Q s k E) DIFF IMAGE phi (moi_s5b_kp Q s k))` THEN
        SET_TAC[];
        UNDISCH_TAC `moi_s5b_ba B Q s k E SUBSET moi_s5b_bp B Q c d0 s k E` THEN
        SET_TAC[]];
      UNDISCH_TAC `(z:real^3) IN IMAGE phi (moi_s5b_dp Q c d0 s k)` THEN
      UNDISCH_TAC `moi_s5b_dp Q c d0 s k SUBSET moi_s5b_bp B Q c d0 s k E` THEN
      SET_TAC[]]]);;

let MOI_S5B_HPM_EQ = prove
 (`!c. (moi_s5b_hp c (&1) = {x:real^3 | c <= x$3} /\
        moi_s5b_hm c (&1) = {x:real^3 | x$3 <= c}) /\
       (moi_s5b_hp c (-- &1) = {x:real^3 | x$3 <= c} /\
        moi_s5b_hm c (-- &1) = {x:real^3 | c <= x$3})`,
  GEN_TAC THEN REWRITE_TAC[moi_s5b_hp; moi_s5b_hm; EXTENSION; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5B_CLAUSES_BOTH = prove
 (`!B K FF GG Q c d0 k j E s.
     moi_s5b_setting B K FF GG Q c d0 k j E s /\
     (?ke. ke IN components {x | x IN B /\ x$3 = c} /\ DISJOINT ke E) /\
     moi_s5b_clause (B INTER {x | x$3 <= c}) /\
     moi_s5b_clause (B INTER {x | c <= x$3})
     ==> moi_s5b_clause (moi_s5b_bp B Q c d0 s k E INTER {x | x$3 <= c}) /\
         moi_s5b_clause (moi_s5b_bp B Q c d0 s k E INTER {x | c <= x$3})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `s = &1 \/ s = -- &1` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5b_setting B K FF GG Q c d0 k j E s` THEN
    SIMP_TAC[moi_s5b_setting];
    ALL_TAC] THEN
  MP_TAC(SPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
    `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`; `s:real`]
    MOI_S5B_CLAUSE_ESIDE) THEN
  MP_TAC(SPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
    `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`; `s:real`]
    MOI_S5B_CLAUSE_DSIDE) THEN
  REWRITE_TAC[ASSUME `moi_s5b_setting B K FF GG Q c d0 k j E s`;
              ASSUME `?ke. ke IN components {x:real^3 | x IN B /\ x$3 = c} /\
                           DISJOINT ke E`] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th))) THEN
  REWRITE_TAC[MOI_S5B_HPM_EQ] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S5B_TCLAUSES_C = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> (?k0. k0 IN components
                 {x | x IN moi_s35_dom /\
                      phi x IN IMAGE phi (moi_s5b_bp B Q c d0 s k E) /\ x$3 <= c} /\
               !k2. k2 IN components
                     {x | x IN moi_s35_dom /\
                          phi x IN IMAGE phi (moi_s5b_bp B Q c d0 s k E) /\ x$3 <= c} /\
                   ~(k2 = k0) ==> k2 SUBSET moi_s35_ttube) /\
         (?k1. k1 IN components
                 {x | x IN moi_s35_dom /\
                      phi x IN IMAGE phi (moi_s5b_bp B Q c d0 s k E) /\ c <= x$3} /\
               !k2. k2 IN components
                     {x | x IN moi_s35_dom /\
                          phi x IN IMAGE phi (moi_s5b_bp B Q c d0 s k E) /\ c <= x$3} /\
                   ~(k2 = k1) ==> k2 SUBSET moi_s35_ttube) /\
         (?L:(real^3->bool)->bool.
             FINITE L /\ simplicial_complex L /\
             UNIONS L = {x | x IN moi_s35_dom /\
                             phi x IN IMAGE phi (moi_s5b_bp B Q c d0 s k E)} /\
             !v. {v} IN L ==> ~(v$3 = c))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TSET_BASIC th) THEN
    MP_TAC(REWRITE_RULE[moi_s5b_tset] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  REWRITE_TAC[moi_s35_edge_conf] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!P. {x | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b /\ P x} =
                    B INTER {x | P x}` (LABEL_TAC "Bset") THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      try lhs(concl th) = `B:real^3->bool` with Failure _ -> false)) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; CONJ_ASSOC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try lhs(concl th) = `B:real^3->bool` with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_BP_FACTS) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    (try mem (fst(dest_const(fst(strip_comb(lhs(concl th))))))
             ["moi_s5b_ba"; "moi_s5b_bp"] with Failure _ -> false)))) THEN
  SUBGOAL_THEN `moi_s5b_bp B Q c d0 s k E SUBSET moi_s35_dom` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`moi_s5b_bp B Q c d0 s k E SUBSET interior moi_s35_stube`;
      `interior moi_s35_stube SUBSET moi_s5b_u`; `moi_s5b_u SUBSET moi_s35_dom`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. {x | x IN moi_s35_dom /\
             (phi:real^3->real^3) x IN IMAGE phi (moi_s5b_bp B Q c d0 s k E) /\ P x} =
        moi_s5b_bp B Q c d0 s k E INTER {x | P x}`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `moi_s5b_bp B Q c d0 s k E`;
                   `moi_s5b_bp B Q c d0 s k E`] MOI_S5B_INJ_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!x. x IN moi_s35_dom
                       ==> ((phi:real^3->real^3) x IN
                            IMAGE phi (moi_s5b_bp B Q c d0 s k E) <=>
                            x IN moi_s5b_bp B Q c d0 s k E)` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `moi_s5b_bp B Q c d0 s k E SUBSET moi_s35_dom` THEN
        UNDISCH_TAC `(x:real^3) IN moi_s5b_bp B Q c d0 s k E` THEN SET_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN moi_s35_dom /\
         (phi:real^3->real^3) x IN IMAGE phi (moi_s5b_bp B Q c d0 s k E)} =
    moi_s5b_bp B Q c d0 s k E`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `\x:real^3. T`) THEN
    REWRITE_TAC[SET_RULE `{x:real^3 | T} = (:real^3)`; INTER_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[] (SPEC `\x:real^3. x$3 <= c` th);
                                    REWRITE_RULE[] (SPEC `\x:real^3. c <= x$3` th)]) THEN
  MP_TAC(SPECL [`B:real^3->bool`; `K:(real^3->bool)->bool`; `FF:real^2->real^3`;
    `GG:real^3->real^2`; `Q:real^3->real->real^3`; `c:real`; `d0:real`;
    `k:real^3->bool`; `j:real^2->bool`; `E:real^3->bool`; `s:real`]
    MOI_S5B_CLAUSES_BOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[moi_s5b_clause] THEN
    USE_THEN "Bset" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE
      [REWRITE_RULE[] (SPEC `\x:real^3. x$3 <= c` th);
       REWRITE_RULE[] (SPEC `\x:real^3. c <= x$3` th)])) THEN
    CONJ_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[REWRITE_RULE[moi_s5b_clause] th]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S5B_BP_TRIANG) THEN
  EXISTS_TAC `L:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `simplicial_complex (L:(real^3->bool)->bool)` THEN
  SIMP_TAC[simplicial_complex]);;

let MOI_S5B_TEDGE = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     PL_SCHOENFLIES_3_STATEMENT /\
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> moi_s35_edge_conf phi xa (moi_s5b_txb phi xb Q c d0 s k E) ww
           (IMAGE phi (moi_s5b_bp B Q c d0 s k E)) b0 b1 c`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TXB th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TCLAUSES_A th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TCLAUSES_B (CONJUNCT2 th)) THEN
    MP_TAC(MATCH_MP MOI_S5B_TCLAUSES_C (CONJUNCT2 th)) THEN
    MP_TAC(CONJUNCT1(REWRITE_RULE[moi_s5b_tset] (CONJUNCT2 th)))) THEN
  REWRITE_TAC[moi_s35_edge_conf] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
    (filter (fun t -> not(is_exists(concl t))) (CONJUNCTS th))) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5B_TCARD = prove
 (`!(phi:real^3->real^3) xa xb ww b b0 b1 c B K FF GG Q d0 k j E s.
     moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 k j E s
     ==> CARD (components (moi_s35_circles phi
                (IMAGE phi (moi_s5b_bp B Q c d0 s k E)) c)) <
         CARD (components (moi_s35_circles phi b c))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S5B_TSET_BASIC th) THEN
    MP_TAC(REWRITE_RULE[moi_s5b_tset] th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP MOI_S5B_CIRCLES_B th)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    try lhs(concl th) = `B:real^3->bool` with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_BP_FACTS) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    (try mem (fst(dest_const(fst(strip_comb(lhs(concl th))))))
             ["moi_s5b_ba"; "moi_s5b_bp"] with Failure _ -> false)))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5B_BP_CIRCLES) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5B_BP_LEVEL) THEN
  SUBGOAL_THEN `moi_s5b_bp B Q c d0 s k E SUBSET moi_s35_dom` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`moi_s5b_bp B Q c d0 s k E SUBSET interior moi_s35_stube`;
      `interior moi_s35_stube SUBSET moi_s5b_u`; `moi_s5b_u SUBSET moi_s35_dom`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s35_circles (phi:real^3->real^3) (IMAGE phi (moi_s5b_bp B Q c d0 s k E)) c =
    {x | x IN moi_s5b_bp B Q c d0 s k E /\ x$3 = c}`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->real^3`; `moi_s35_dom`; `moi_s5b_bp B Q c d0 s k E`;
                   `moi_s5b_bp B Q c d0 s k E`] MOI_S5B_INJ_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[moi_s35_circles] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!x. x IN moi_s35_dom
                       ==> ((phi:real^3->real^3) x IN
                            IMAGE phi (moi_s5b_bp B Q c d0 s k E) <=>
                            x IN moi_s5b_bp B Q c d0 s k E)` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `moi_s5b_bp B Q c d0 s k E SUBSET moi_s35_dom` THEN
        UNDISCH_TAC `(x:real^3) IN moi_s5b_bp B Q c d0 s k E` THEN SET_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem DISK_SWAP: Moise 35.1, Lemma 2 (p.250) in tube form.      *)
(* ------------------------------------------------------------------------- *)

let DISK_SWAP = prove
 (MOI_S35_DISK_SWAP,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  ANTS_TAC THENL [ACCEPT_TAC(ISPEC `(:3)` MOISE_273); DISCH_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5B_COLLAR_EXISTS) THEN
  MAP_EVERY X_GEN_TAC [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`;
    `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`;
    `c:real`; `k0:real^3->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`phi:real^3->real^3`; `xa:real^3->bool`;
    `xb:real^3->bool`; `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`;
    `b1:real^3->bool`; `c:real`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `moi_s35_ess`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  ABBREV_TAC `B = {x | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN b}` THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`;
    `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`;
    `c:real`; `k0:real^3->bool`; `B:real^3->bool`] MOI_S5B_MODEL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^3->bool)->bool` (X_CHOOSE_THEN `FF:real^2->real^3`
    (X_CHOOSE_THEN `GG:real^3->real^2` (X_CHOOSE_THEN `Q:real^3->real->real^3`
    (X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `kq:real^3->bool`
    (X_CHOOSE_THEN `j:real^2->bool` (X_CHOOSE_THEN `E:real^3->bool`
    (X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     STRIP_ASSUME_TAC))))))))))) THEN
  SUBGOAL_THEN `moi_s5b_tset phi xa xb ww b b0 b1 c B K FF GG Q d0 kq j E s`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5b_tset] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `moi_s5b_txb (phi:real^3->real^3) xb Q c d0 s kq E` THEN
  EXISTS_TAC `IMAGE (phi:real^3->real^3) (moi_s5b_bp B Q c d0 s kq E)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5B_TEDGE THEN
    MAP_EVERY EXISTS_TAC [`b:real^3->bool`; `K:(real^3->bool)->bool`;
      `FF:real^2->real^3`; `GG:real^3->real^2`; `j:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5B_TCARD THEN
    MAP_EVERY EXISTS_TAC [`xa:real^3->bool`; `xb:real^3->bool`; `ww:real^3->bool`;
      `b0:real^3->bool`; `b1:real^3->bool`; `K:(real^3->bool)->bool`;
      `FF:real^2->real^3`; `GG:real^3->real^2`; `j:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `moi_s5b_kk Q c d0 s kq E` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_KK) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5B_TTHETA) THEN
    ASM_REWRITE_TAC[]]);;

