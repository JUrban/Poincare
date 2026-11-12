(* ========================================================================= *)
(* pc_moi_tube3: the tube lemma for the shell between two nested PL 3-balls  *)
(* in real^3 (DG exists_isPLBall_sdiff_interior_tube; used by Moise Sec 34   *)
(* Operation 1 in pc_moi_s34_op1bu).  Main theorem MOI_TB3_TUBE.             *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_s35_cells.ml";;
needs "src/pc_moi_s34_scella.ml";;
needs "src/pc_moi_s34_op1b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic facts.  Interior of a union off a closed set; balls and 3-cells   *)
(* in real^3; gluing two balls along a disk (MOI_S5V_CELL_UNION); a compact  *)
(* set with nonempty interior whose frontier is a PL 2-sphere is a PL ball   *)
(* (Schoenflies, via MOI_S4V_SPHERE_FILL).                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_INTERIOR_UNION_OFF = prove
 (`!a n (z:real^N). closed n /\ ~(z IN n)
                    ==> (z IN interior (a UNION n) <=> z IN interior a)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `interior (a UNION n) INTER ((:real^N) DIFF n) SUBSET interior a`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `a UNION n:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
        MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR] THEN
        ASM_REWRITE_TAC[GSYM closed]];
      ASM SET_TAC[]];
    MP_TAC(ISPECL [`a:real^N->bool`; `a UNION n:real^N->bool`] SUBSET_INTERIOR) THEN
    REWRITE_TAC[SUBSET_UNION] THEN SET_TAC[]]);;

let MOI_TB3_BALL_CELL = prove
 (`!c:real^3->bool. pl_ball 3 c ==> pl_cell_with_boundary 3 c (frontier c)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
  EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[]);;

let MOI_TB3_CELL_BALL = prove
 (`!c b:real^3->bool. pl_cell_with_boundary 3 c b ==> pl_ball 3 c /\ b = frontier c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
    EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_TB3_GLUE = prove
 (`!y p d j:real^3->bool.
     pl_ball 3 y /\ pl_ball 3 p /\ y INTER p = d /\ pl_cell_with_boundary 2 d j /\
     d SUBSET frontier p
     ==> pl_ball 3 (y UNION p) /\
         frontier (y UNION p) = (frontier y UNION frontier p) DIFF (d DIFF j) /\
         d SUBSET frontier y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET frontier y` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (y:real^3->bool)`)) THEN
    MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (p:real^3->bool)`)) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `interior p SUBSET (:real^3) DIFF (y:real^3->bool)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(y:real^3->bool) INTER p = d`; `(d:real^3->bool) SUBSET frontier p`] THEN
      REWRITE_TAC[frontier] THEN MP_TAC(ISPEC `p:real^3->bool` INTERIOR_SUBSET) THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `closure (interior p) SUBSET closure ((:real^3) DIFF (y:real^3->bool))`
    ASSUME_TAC THENL [MATCH_MP_TAC SUBSET_CLOSURE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3->bool) SUBSET closure (interior p)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`frontier p SUBSET closure (interior (p:real^3->bool))`;
        `frontier p UNION interior p = (p:real^3->bool)`] THEN
      MP_TAC(ISPEC `interior p:real^3->bool` CLOSURE_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[frontier] THEN
    SUBGOAL_THEN `closure y = (y:real^3->bool)` SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `y:real^3->bool` INTERIOR_COMPLEMENT) THEN
    MP_TAC(ISPEC `(:real^3) DIFF y` CLOSURE_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3->bool) INTER p = d`;
      `(p:real^3->bool) SUBSET closure (interior p)`;
      `closure (interior p) SUBSET closure ((:real^3) DIFF (y:real^3->bool))`] THEN
    REWRITE_TAC[CLOSURE_COMPLEMENT] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:real^3->bool`; `frontier y:real^3->bool`; `p:real^3->bool`;
                 `frontier p:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`]
    MOI_S5V_CELL_UNION) THEN
  ASM_SIMP_TAC[MOI_TB3_BALL_CELL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_TB3_CELL_BALL) THEN SIMP_TAC[]);;

let MOI_TB3_FILL = prove
 (`!g:real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ compact g /\ pl_sphere 2 (frontier g) /\
     ~(interior g = {})
     ==> pl_ball 3 g /\ g = frontier g UNION inside (frontier g)`,
  GEN_TAC THEN ABBREV_TAC `S = frontier (g:real^3->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (g:real^3->bool) /\ bounded g` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `S SUBSET (g:real^3->bool) /\ interior g INTER S = {}` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[frontier] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:real^3->bool` MOI_S4V_SPHERE_FILL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!t:real^3->bool. connected t /\ DISJOINT S t
                                 ==> t SUBSET g \/ t INTER g = {}` (LABEL_TAC "side") THENL
   [X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:real^3->bool`; `g:real^3->bool`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT S (t:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `outside S INTER (g:real^3->bool) = {}` ASSUME_TAC THENL
   [USE_THEN "side" (MP_TAC o SPEC `outside S:real^3->bool`) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~bounded (outside S:real^3->bool)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `g:real^3->bool` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inside S SUBSET (g:real^3->bool)` ASSUME_TAC THENL
   [USE_THEN "side" (MP_TAC o SPEC `inside S:real^3->bool`) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(interior g:real^3->bool = {})` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `g:real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`(:real^3) DIFF outside S = S UNION inside S`;
      `outside S INTER (g:real^3->bool) = {}`; `inside S INTER (g:real^3->bool) = {}`;
      `interior g INTER S = {}:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->bool) = S UNION inside S` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(:real^3) DIFF outside S = S UNION inside S`;
      `outside S INTER (g:real^3->bool) = {}`; `inside S SUBSET (g:real^3->bool)`;
      `S SUBSET (g:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(g:real^3->bool) = S UNION inside S` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The bite.  A ball y inside the ball w that meets frontier w exactly in a *)
(* disk d (boundary j), together with a set c outside w except on d, whose  *)
(* union with y is a neighbourhood of the open disk d DIFF j but not of j:  *)
(* then w DIFF interior (y UNION c) is a PL ball.  It is the sphere s =     *)
(* ((frontier w DIFF d) UNION j) UNION ((frontier y DIFF d) UNION j)        *)
(* (DISK_COMPLEMENT twice, DISK_UNION) with its inside, which is interior w *)
(* DIFF y.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_CELL_COMPACT = prove
 (`!n d j:real^N->bool.
     pl_cell_with_boundary n d j ==> compact d /\ compact j /\ j SUBSET d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact (k:real^N->bool) /\ relative_frontier k SUBSET k /\
                compact (relative_frontier k:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_RELATIVE_FRONTIER; RELATIVE_FRONTIER_SUBSET;
                  COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

let MOI_TB3_CONN_SPLIT = prove
 (`!t u v:real^N->bool.
     connected t /\ open u /\ open v /\ t SUBSET u UNION v /\ u INTER v = {}
     ==> t SUBSET u \/ t SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `u INTER v = {}:real^N->bool` THEN
  UNDISCH_TAC `t SUBSET (u:real^N->bool) UNION v` THEN SET_TAC[]);;

let MOI_TB3_BITE = prove
 (`!w y d j c:real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\
     pl_ball 3 w /\ pl_ball 3 y /\ y SUBSET w /\
     pl_cell_with_boundary 2 d j /\ y INTER frontier w = d /\ d SUBSET frontier y /\
     c INTER w SUBSET d /\
     d DIFF j SUBSET interior (y UNION c) /\ j INTER interior (y UNION c) = {} /\
     (!z. z IN d DIFF j ==> ?r. &0 < r /\ ball(z,r) INTER w SUBSET y)
     ==> pl_ball 3 (w DIFF interior (y UNION c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "loc" o check (is_forall o concl)) THEN
  MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (w:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (y:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_TB3_CELL_COMPACT
    (ASSUME `pl_cell_with_boundary 2 (d:real^3->bool) j`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET frontier w` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3->bool) INTER frontier w = d` THEN SET_TAC[]; ALL_TAC] THEN
  (* the two disks and the sphere *)
  SUBGOAL_THEN `pl_cell_with_boundary 2 ((frontier w DIFF d) UNION j) (j:real^3->bool) /\
                pl_cell_with_boundary 2 ((frontier y DIFF d) UNION j) (j:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DISK_COMPLEMENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s = ((frontier w DIFF d) UNION j) UNION
                  ((frontier y DIFF d) UNION (j:real^3->bool))` THEN
  FIRST_ASSUM(LABEL_TAC "sdef") THEN
  SUBGOAL_THEN `pl_sphere 2 (s:real^3->bool)` ASSUME_TAC THENL
   [USE_THEN "sdef" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC DISK_UNION THEN EXISTS_TAC `j:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3->bool) INTER frontier w = d`; `frontier y SUBSET (y:real^3->bool)`;
      `(j:real^3->bool) SUBSET d`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S4V_SPHERE_FILL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  (* basic set facts *)
  SUBGOAL_THEN `interior w INTER frontier w = {} /\ interior y INTER frontier y = {} /\
                interior w SUBSET (w:real^3->bool) /\ interior y SUBSET (y:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_SUBSET] THEN REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c INTER interior w = {}:real^3->bool` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`c INTER w SUBSET (d:real^3->bool)`; `(d:real^3->bool) SUBSET frontier w`;
      `interior w INTER frontier w = {}:real^3->bool`;
      `interior w SUBSET (w:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier y DIFF d SUBSET interior (w:real^3->bool)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`frontier y SUBSET (y:real^3->bool)`; `(y:real^3->bool) SUBSET w`;
      `(y:real^3->bool) INTER frontier w = d`;
      `frontier w UNION interior w = (w:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(frontier y DIFF d) INTER interior (y UNION c) = {}:real^3->bool`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `interior (y UNION c) INTER interior w SUBSET interior (y:real^3->bool)`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `y UNION c:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `c INTER interior w = {}:real^3->bool` THEN SET_TAC[];
        SIMP_TAC[OPEN_INTER; OPEN_INTERIOR]];
      MAP_EVERY UNDISCH_TAC
       [`frontier y DIFF d SUBSET interior (w:real^3->bool)`;
        `interior y INTER frontier y = {}:real^3->bool`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior y SUBSET interior (y UNION c:real^3->bool) /\
                interior (y UNION c) SUBSET (y UNION c:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_SUBSET] THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[];
    ALL_TAC] THEN
  (* the new set is the sphere together with interior w DIFF y *)
  ABBREV_TAC `iyc = interior (y UNION c:real^3->bool)` THEN
  SUBGOAL_THEN `frontier w SUBSET (w:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier w UNION interior w = (w:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier w DIFF iyc SUBSET (frontier w DIFF d) UNION (j:real^3->bool) /\
    interior w DIFF iyc SUBSET (frontier y DIFF d) UNION (interior w DIFF (y:real^3->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `d DIFF j SUBSET (iyc:real^3->bool)` THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`frontier y UNION interior y = (y:real^3->bool)`;
        `interior y SUBSET (iyc:real^3->bool)`; `(d:real^3->bool) SUBSET frontier w`;
        `interior w INTER frontier w = {}:real^3->bool`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier w DIFF d SUBSET w DIFF (iyc:real^3->bool) /\
    j SUBSET w DIFF (iyc:real^3->bool) /\
    frontier y DIFF d SUBSET w DIFF (iyc:real^3->bool) /\
    interior w DIFF y SUBSET w DIFF (iyc:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`frontier w SUBSET (w:real^3->bool)`; `iyc SUBSET (y UNION c:real^3->bool)`;
        `(y:real^3->bool) INTER frontier w = d`; `c INTER w SUBSET (d:real^3->bool)`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`frontier w SUBSET (w:real^3->bool)`; `(d:real^3->bool) SUBSET frontier w`;
        `(j:real^3->bool) SUBSET d`; `j INTER iyc = {}:real^3->bool`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`frontier y SUBSET (y:real^3->bool)`; `(y:real^3->bool) SUBSET w`;
        `(frontier y DIFF d) INTER iyc = {}:real^3->bool`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`interior w SUBSET (w:real^3->bool)`; `iyc SUBSET (y UNION c:real^3->bool)`;
        `c INTER interior w = {}:real^3->bool`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `w DIFF iyc = s UNION (interior w DIFF (y:real^3->bool))` ASSUME_TAC THENL
   [USE_THEN "sdef" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`frontier w UNION interior w = (w:real^3->bool)`;
        `frontier w DIFF iyc SUBSET (frontier w DIFF d) UNION (j:real^3->bool)`;
        `interior w DIFF iyc SUBSET (frontier y DIFF d) UNION
         (interior w DIFF (y:real^3->bool))`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`frontier w DIFF d SUBSET w DIFF (iyc:real^3->bool)`;
        `j SUBSET w DIFF (iyc:real^3->bool)`;
        `frontier y DIFF d SUBSET w DIFF (iyc:real^3->bool)`;
        `interior w DIFF y SUBSET w DIFF (iyc:real^3->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the decomposition of the complement of s *)
  ABBREV_TAC `u = interior w DIFF (y:real^3->bool)` THEN
  ABBREV_TAC `v = ((:real^3) DIFF w) UNION interior y UNION (d DIFF (j:real^3->bool))` THEN
  SUBGOAL_THEN `open (u:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `u INTER v = {}:real^3->bool /\ u UNION v = (:real^3) DIFF s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN EXPAND_TAC "v" THEN USE_THEN "sdef" (SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`interior w SUBSET (w:real^3->bool)`; `interior y SUBSET (y:real^3->bool)`;
        `(y:real^3->bool) INTER frontier w = d`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`frontier w UNION interior w = (w:real^3->bool)`;
        `frontier y UNION interior y = (y:real^3->bool)`; `(y:real^3->bool) SUBSET w`;
        `(y:real^3->bool) INTER frontier w = d`; `(j:real^3->bool) SUBSET d`;
        `(d:real^3->bool) SUBSET frontier y`;
        `interior w INTER frontier w = {}:real^3->bool`;
        `interior y INTER frontier y = {}:real^3->bool`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (v:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_UNION; IN_DIFF; IN_UNIV] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `open ((:real^3) DIFF w)` MP_TAC THENL
       [REWRITE_TAC[GSYM closed] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
      MP_TAC(ISPEC `y:real^3->bool` OPEN_INTERIOR) THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
      SUBGOAL_THEN `(x:real^3) IN d DIFF j`
        (fun th -> USE_THEN "loc" (MP_TAC o C MATCH_MP th)) THENL
       [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`j:real^3->bool`; `x:real^3`] SEPARATE_POINT_CLOSED) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `de:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min r de` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `ball(x:real^3,min r de) SUBSET ball(x,r)` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `interior w INTER ball(x:real^3,min r de) SUBSET interior y`
      ASSUME_TAC THENL
       [MATCH_MP_TAC INTERIOR_MAXIMAL THEN SIMP_TAC[OPEN_INTER; OPEN_INTERIOR; OPEN_BALL] THEN
        MAP_EVERY UNDISCH_TAC
         [`ball(x:real^3,min r de) SUBSET ball(x,r)`; `ball(x:real^3,r) INTER w SUBSET y`;
          `interior w SUBSET (w:real^3->bool)`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `!q:real^3. q IN ball(x,min r de) ==> ~(q IN j)` ASSUME_TAC THENL
       [X_GEN_TAC `q:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3` o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `de:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `q:real^3` THEN
      DISCH_TAC THEN ASM_CASES_TAC `(q:real^3) IN w` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(q:real^3) IN interior w` THENL
       [DISJ1_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`interior w INTER ball(x:real^3,min r de) SUBSET interior y`;
          `(q:real^3) IN interior w`; `(q:real^3) IN ball(x,min r de)`] THEN
        SET_TAC[];
        DISJ2_TAC THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`ball(x:real^3,min r de) SUBSET ball(x,r)`; `ball(x:real^3,r) INTER w SUBSET y`;
            `frontier w UNION interior w = (w:real^3->bool)`;
            `(y:real^3->bool) INTER frontier w = d`; `(q:real^3) IN w`;
            `~((q:real^3) IN interior w)`; `(q:real^3) IN ball(x,min r de)`] THEN
          SET_TAC[];
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            is_forall (concl th) && can (find_term ((=) `de:real`)) (concl th) &&
            can (find_term ((=) `j:real^3->bool`)) (concl th))) THEN
          FIRST_ASSUM ACCEPT_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u = {}:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN DISCH_TAC THEN
    SUBGOAL_THEN `frontier w SUBSET (d:real^3->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `closure (interior w) SUBSET (y:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
         [UNDISCH_TAC `interior w DIFF y = {}:real^3->bool` THEN SET_TAC[];
          FIRST_ASSUM ACCEPT_TAC];
        MAP_EVERY UNDISCH_TAC
         [`frontier w SUBSET closure (interior (w:real^3->bool))`;
          `(y:real^3->bool) INTER frontier w = d`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO (ASSUME
      `pl_cell_with_boundary 2 ((frontier w DIFF d) UNION j) (j:real^3->bool)`)) THEN
    UNDISCH_TAC `frontier w SUBSET (d:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside s = (u:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `bounded (u:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      EXPAND_TAC "u" THEN UNDISCH_TAC `interior w SUBSET (w:real^3->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `outside s SUBSET (v:real^3->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`outside s:real^3->bool`; `u:real^3->bool`; `v:real^3->bool`]
        MOI_TB3_CONN_SPLIT) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        MAP_EVERY UNDISCH_TAC
         [`u UNION v = (:real^3) DIFF s`; `DISJOINT s (outside s:real^3->bool)`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~bounded (outside s:real^3->bool)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inside s SUBSET (u:real^3->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`inside s:real^3->bool`; `u:real^3->bool`; `v:real^3->bool`]
        MOI_TB3_CONN_SPLIT) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        MAP_EVERY UNDISCH_TAC
         [`u UNION v = (:real^3) DIFF s`; `DISJOINT s (inside s:real^3->bool)`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~(u = {}:real^3->bool)` THEN REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`u UNION v = (:real^3) DIFF s`; `u INTER v = {}:real^3->bool`;
        `(:real^3) DIFF outside s = s UNION inside s`;
        `inside s SUBSET (v:real^3->bool)`; `outside s SUBSET (v:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`u UNION v = (:real^3) DIFF s`; `u INTER v = {}:real^3->bool`;
      `(:real^3) DIFF outside s = s UNION inside s`;
      `outside s SUBSET (v:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_ball 3 (s UNION inside s:real^3->bool)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* PL homeomorphisms of real^3.  They commute with interiors, map closed    *)
(* sets to closed sets and PL balls to PL balls, and compose; the tube      *)
(* statement transfers along them; both balls can be straightened to nested *)
(* 3-simplices (MOI_SCD_COR_AMBIENT_BALL twice).                            *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_HOMEO_INTERIOR = prove
 (`!(f:real^3->real^3) g s.
     homeomorphism ((:real^3),(:real^3)) (f,g)
     ==> IMAGE f (interior s) = interior (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `(:real^3)`; `(:real^3)`;
                 `s:real^3->bool`] HOMEOMORPHISM_INTERIOR_OF) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; SUBTOPOLOGY_UNIV; EUCLIDEAN_INTERIOR_OF]);;

let MOI_TB3_HOMEO_CLOSED = prove
 (`!(f:real^3->real^3) g s.
     homeomorphism ((:real^3),(:real^3)) (f,g) /\ closed s ==> closed (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `(:real^3)`; `(:real^3)`;
                 `s:real^3->bool`] HOMEOMORPHISM_IMP_CLOSED_MAP) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN]);;

let MOI_TB3_PLH_COMPOSE = prove
 (`!(f:real^3->real^3) g h k.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
     pl_homeomorphism ((:real^3),(:real^3)) (h,k)
     ==> pl_homeomorphism ((:real^3),(:real^3)) (h o f,g o k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let MOI_TB3_PL_BALL_IMAGE = prove
 (`!(f:real^3->real^3) g b.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ pl_ball 3 b
     ==> pl_ball 3 (IMAGE f b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^3->bool`
    (X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `(f:real^3->real^3) o (h:real^3->real^3)`;
                        `(h':real^3->real^3) o (g:real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_homeomorphism (k,b) ((h:real^3->real^3),(h':real^3->real^3))` THEN
  UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),g)` THEN
  REWRITE_TAC[pl_homeomorphism] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `b:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `b:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      SUBGOAL_THEN `IMAGE (f:real^3->real^3) b = IMAGE (f o (h:real^3->real^3)) k`
      SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `homeomorphism (k,b) ((h:real^3->real^3),(h':real^3->real^3))` THEN
        SIMP_TAC[homeomorphism];
        ALL_TAC] THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
        ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
        MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      UNDISCH_TAC `homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),g)` THEN
      REWRITE_TAC[homeomorphism; IN_UNIV] THEN SET_TAC[]]]);;

let MOI_TB3_TRANSFER = prove
 (`!(f:real^3->real^3) h x w k.
     pl_homeomorphism ((:real^3),(:real^3)) (f,h) /\
     (?n. compact n /\ DISJOINT n (IMAGE f k) /\
          pl_ball 3 (IMAGE f w DIFF interior (IMAGE f x UNION n)))
     ==> ?n. compact n /\ DISJOINT n k /\ pl_ball 3 (w DIFF interior (x UNION n))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),h) /\
                homeomorphism ((:real^3),(:real^3)) ((h:real^3->real^3),f) /\
                pl_homeomorphism ((:real^3),(:real^3)) ((h:real^3->real^3),f)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),h)` THEN
    REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y. (f:real^3->real^3) (h y) = y) /\ (!y. h (f y) = y) /\
                (h:real^3->real^3) continuous_on (:real^3)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),h)` THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (h:real^3->real^3) n` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    UNDISCH_TAC `DISJOINT n (IMAGE (f:real^3->real^3) k)` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`h:real^3->real^3`; `f:real^3->real^3`;
                   `IMAGE (f:real^3->real^3) x UNION n`] MOI_TB3_HOMEO_INTERIOR) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `IMAGE (h:real^3->real^3) (IMAGE (f:real^3->real^3) x UNION n) = x UNION IMAGE h n /\
                  IMAGE (h:real^3->real^3) (IMAGE (f:real^3->real^3) w) = w`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IMAGE_UNION; GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
      ALL_TAC] THEN
    SUBGOAL_THEN `w DIFF interior (x UNION IMAGE (h:real^3->real^3) n) =
                  IMAGE h (IMAGE (f:real^3->real^3) w DIFF interior (IMAGE (f:real^3->real^3) x UNION n))` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`h:real^3->real^3`; `IMAGE (f:real^3->real^3) w`;
                     `interior (IMAGE (f:real^3->real^3) x UNION n)`] IMAGE_DIFF_INJ) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_TB3_PL_BALL_IMAGE THEN EXISTS_TAC `f:real^3->real^3` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

let MOI_TB3_STRAIGHTEN = prove
 (`!x w:real^3->bool.
     PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     pl_ball 3 x /\ pl_ball 3 w /\ x SUBSET interior w
     ==> ?f h. pl_homeomorphism ((:real^3),(:real^3)) (f,h) /\
               &3 simplex (IMAGE f x) /\ &3 simplex (IMAGE f w) /\
               IMAGE f x SUBSET interior (IMAGE f w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "amb" o MATCH_MP MOI_SCD_COR_AMBIENT_BALL) THEN
  MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (w:real^3->bool)`)) THEN
  STRIP_TAC THEN
  USE_THEN "amb" (MP_TAC o SPECL [`frontier w:real^3->bool`; `(:real^3)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_UNIV; OPEN_UNIV; SUBSET_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` (X_CHOOSE_THEN `f1:real^3->real^3`
    (X_CHOOSE_THEN `h1:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `IMAGE (f1:real^3->real^3) w = k1` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f1:real^3->real^3) (frontier w UNION inside (frontier w)) = k1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism ((:real^3),(:real^3)) ((f1:real^3->real^3),h1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) ((f1:real^3->real^3),h1)` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  ABBREV_TAC `x1 = IMAGE (f1:real^3->real^3) x` THEN
  SUBGOAL_THEN `pl_ball 3 (x1:real^3->bool) /\ x1 SUBSET interior k1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_TB3_PL_BALL_IMAGE THEN EXISTS_TAC `h1:real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (f1:real^3->real^3) w = k1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`f1:real^3->real^3`; `h1:real^3->real^3`; `w:real^3->bool`]
        MOI_TB3_HOMEO_INTERIOR) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4V_BALL_SIDES (ASSUME `pl_ball 3 (x1:real^3->bool)`)) THEN
  STRIP_TAC THEN
  USE_THEN "amb" (MP_TAC o SPECL [`frontier x1:real^3->bool`; `interior k1:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_INTERIOR THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `x1:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` (X_CHOOSE_THEN `f2:real^3->real^3`
    (X_CHOOSE_THEN `h2:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `IMAGE (f2:real^3->real^3) x1 = k2` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f2:real^3->real^3) (frontier x1 UNION inside (frontier x1)) = k2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y. (f2:real^3->real^3) (h2 y) = y) /\ (!y. h2 (f2 y) = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) ((f2:real^3->real^3),h2)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f2:real^3->real^3) k1 = k1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k1:real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`!y. (f2:real^3->real^3) (h2 y) = y`; `!y. (h2:real^3->real^3) (f2 y) = y`;
      `!x. ~(x IN interior k1) ==> (f2:real^3->real^3) x = x`] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(f2:real^3->real^3) o (f1:real^3->real^3)`;
                        `(h1:real^3->real^3) o (h2:real^3->real^3)`] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_TB3_PLH_COMPOSE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The simplex case, part 1.  The path crosses the shell: a sub-path from a *)
(* point of frontier x to a point of frontier w whose other points lie      *)
(* outside x and inside interior w.  Local structure of a polytope near a   *)
(* relative interior point of a facet: locally it is the supporting         *)
(* half-space.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_SHELL_PATH = prove
 (`!x w (p:real^3) p1 (g:real^1->real^3).
     closed x /\ x SUBSET interior w /\ p IN x /\ ~(p1 IN w) /\
     path g /\ pathstart g = p /\ pathfinish g = p1
     ==> ?h. path h /\ path_image h SUBSET path_image g /\
             pathstart h IN frontier x /\ pathfinish h IN frontier w /\
             (!t. t IN path_image h /\ ~(t = pathstart h) ==> ~(t IN x)) /\
             (!t. t IN path_image h /\ ~(t = pathfinish h) ==> t IN interior w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((p1:real^3) IN x) /\ interior w SUBSET (w:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_SUBSET] THEN
    MP_TAC(ISPEC `w:real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC [`x SUBSET interior (w:real^3->bool)`; `~((p1:real^3) IN w)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`reversepath (g:real^1->real^3)`; `(:real^3) DIFF x`]
    EXISTS_PATH_SUBPATH_TO_FRONTIER) THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                  IN_DIFF; IN_UNIV; PATH_IMAGE_REVERSEPATH; FRONTIER_COMPLEMENT;
                  INTERIOR_COMPLEMENT] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^1->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pathfinish (h1:real^1->real^3) IN interior w` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a b c x:real^3. x IN a /\ a SUBSET b /\ b SUBSET c ==> x IN c`) THEN
    MAP_EVERY EXISTS_TAC [`frontier x:real^3->bool`; `x:real^3->bool`] THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`reversepath (h1:real^1->real^3)`; `interior w:real^3->bool`]
    EXISTS_PATH_SUBPATH_TO_FRONTIER) THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                  PATH_IMAGE_REVERSEPATH; INTERIOR_INTERIOR] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `interior w SUBSET (w:real^3->bool)` THEN
    UNDISCH_TAC `~((p1:real^3) IN w)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^1->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h2:real^1->real^3` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `path_image (h1:real^1->real^3)` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `w:real^3->bool` FRONTIER_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `pathfinish (h2:real^1->real^3) IN frontier (interior w)` THEN
    SET_TAC[];
    X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `path_image h1 DELETE pathfinish h1 SUBSET (:real^3) DIFF x` THEN
    UNDISCH_TAC `path_image (h2:real^1->real^3) SUBSET path_image h1` THEN
    MAP_EVERY UNDISCH_TAC [`(t:real^3) IN path_image h2`; `~((t:real^3) = pathfinish h1)`] THEN
    SET_TAC[];
    X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `path_image h2 DELETE pathfinish h2 SUBSET interior (w:real^3->bool)` THEN
    MAP_EVERY UNDISCH_TAC [`(t:real^3) IN path_image h2`; `~((t:real^3) = pathfinish h2)`] THEN
    SET_TAC[]]);;

let MOI_TB3_FACET_LOCAL = prove
 (`!s (z:real^3) e.
     polytope s /\ ~(interior s = {}) /\ z IN frontier s /\ &0 < e
     ==> ?a nu c r. ~(nu = vec 0) /\ nu dot a = c /\ &0 < r /\
                    ball(a,r) SUBSET ball(z,e) /\
                    s SUBSET {y | nu dot y <= c} /\
                    (!y. y IN ball(a,r) ==> (y IN s <=> nu dot y <= c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `polyhedron (s:real^3->bool) /\ convex s /\ closed s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON; POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `?f:real^3->bool. f facet_of s /\ z IN f` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^3->bool` RELATIVE_FRONTIER_OF_POLYHEDRON) THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `f:real^3->bool`] FACET_OF_POLYHEDRON) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nu:real^3` (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `convex (f:real^3->bool) /\ closed (f:real^3->bool)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^3->bool) face_of s` ASSUME_TAC THENL
     [MATCH_MP_TAC FACET_OF_IMP_FACE_OF THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN EXISTS_TAC `s:real^3->bool` THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC FACE_OF_IMP_CLOSED THEN EXISTS_TAC `s:real^3->bool` THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^3. a IN relative_interior f /\ dist(a,z) < e / &2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `f:real^3->bool` CONVEX_CLOSURE_RELATIVE_INTERIOR) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `closure f = (f:real^3->bool)` SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o REWRITE_RULE[EXTENSION]) THEN
    REWRITE_TAC[ASSUME `(z:real^3) IN f`; CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `f:real^3->bool`]
    OPEN_IN_RELATIVE_FRONTIER_INTERIOR_FACET) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier s = frontier (s:real^3->bool)` SUBST1_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:real^3) IN u /\ a IN f /\ relative_interior f SUBSET (f:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
    MP_TAC(ISPEC `f:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`relative_interior f = frontier s INTER (u:real^3->bool)`;
      `(a:real^3) IN relative_interior f`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `u:real^3->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `nu:real^3`; `c:real`; `min r1 (e / &2)`] THEN
  SUBGOAL_THEN `(nu:real^3) dot a = c` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(f:real^3->bool) = s INTER {x | nu dot x = c}`; `(a:real^3) IN f`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < r1` THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN
    UNDISCH_TAC `dist(a:real^3,z) < e / &2` THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
   [UNDISCH_TAC `s SUBSET {x:real^3 | nu dot x <= c}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    DISCH_TAC] THEN
  ASM_CASES_TAC `(y:real^3) IN s` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?q:real^3. q IN interior s /\ q IN ball(a,min r1 (e / &2))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^3->bool` CONVEX_CLOSURE_INTERIOR) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `closure s = (s:real^3->bool)` SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^3` o REWRITE_RULE[EXTENSION]) THEN
    SUBGOAL_THEN `(a:real^3) IN s` (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC
       [`(f:real^3->bool) = s INTER {x | nu dot x = c}`; `(a:real^3) IN f`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `min r1 (e / &2)`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < r1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_BALL] THEN MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t:real^3. t IN segment[q,y] /\ t IN frontier s` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`segment[q:real^3,y]`; `s:real^3->bool`] CONNECTED_INTER_FRONTIER) THEN
    REWRITE_TAC[CONNECTED_SEGMENT] THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
       [EXISTS_TAC `q:real^3` THEN REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT] THEN
        MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(q:real^3) IN interior s` THEN SET_TAC[];
        EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[IN_DIFF; ENDS_IN_SEGMENT]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3) IN ball(a,min r1 (e / &2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^3,min r1 (e / &2))`; `q:real^3`; `y:real^3`]
      (REWRITE_RULE[IMP_CONJ] SEGMENT_SUBSET_CONVEX)) THEN
    ASM_REWRITE_TAC[CONVEX_BALL] THEN UNDISCH_TAC `(t:real^3) IN segment[q,y]` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nu:real^3) dot t = c` ASSUME_TAC THENL
   [SUBGOAL_THEN `(t:real^3) IN u` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(a:real^3,r1) SUBSET u` THEN
      UNDISCH_TAC `(t:real^3) IN ball(a,min r1 (e / &2))` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN MESON_TAC[REAL_LT_MIN];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(f:real^3->bool) = s INTER {x | nu dot x = c}`;
      `relative_interior f SUBSET (f:real^3->bool)`;
      `relative_interior f = frontier s INTER (u:real^3->bool)`;
      `(t:real^3) IN u`; `(t:real^3) IN frontier s`] THEN
    REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nu:real^3) dot q < c` ASSUME_TAC THENL
   [SUBGOAL_THEN `interior s SUBSET {x:real^3 | nu dot x < c}` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM INTERIOR_HALFSPACE_LE] THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(q:real^3) IN interior s` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((t:real^3) = y)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((y:real^3) IN s)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(t:real^3) IN frontier s` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(t:real^3) IN segment[q,y]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `l = &1` THENL
   [UNDISCH_TAC `~((t:real^3) = y)` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - l) * ((nu:real^3) dot q) < (&1 - l) * c /\
                l * ((nu:real^3) dot y) <= l * c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(nu:real^3) dot t = c` THEN ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cutting a polytope by a plane through its interior: both halves are PL    *)
(* 3-balls, the section is a PL 2-cell whose relative interior is the        *)
(* section of the interior, and it lies in the frontiers of both halves      *)
(* (used for the end boxes at the two facets).                               *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_CELL_IMP_BALL = prove
 (`!c b:real^3->bool. pl_cell_with_boundary 3 c b ==> pl_ball 3 c`,
  MESON_TAC[MOI_TB3_CELL_BALL]);;

let MOI_TB3_HALF_BALL = prove
 (`!P (nu:real^3) c.
     polytope P /\ ~(nu = vec 0) /\ ~(interior P INTER {y | nu dot y = c} = {})
     ==> pl_ball 3 (P INTER {y | nu dot y <= c}) /\
         pl_ball 3 (P INTER {y | nu dot y >= c})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_ELIM_THM]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPEC `interior P:real^3->bool` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `m:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(nu:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `t = r / (&2 * norm(nu:real^3))` THEN
  SUBGOAL_THEN `&0 < t /\ t * norm(nu:real^3) < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> r / (&2 * n) * n = r / &2`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m - t % nu:real^3) IN interior P /\ (m + t % nu:real^3) IN interior P`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `ball(m:real^3,r)`)) (concl th))) THEN
    REWRITE_TAC[IN_BALL; NORM_ARITH `dist(m:real^3,m - x) = norm x`;
                NORM_ARITH `dist(m:real^3,m + x) = norm x`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nu:real^3) dot (m - t % nu) < c /\ nu dot (m + t % nu) > c`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DOT_RSUB; DOT_RADD; DOT_RMUL; real_gt] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < t * ((nu:real^3) dot nu)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (P INTER {y:real^3 | nu dot y <= c}) /\
                polytope (P INTER {y:real^3 | nu dot y >= c})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
    ASM_REWRITE_TAC[POLYHEDRON_HALFSPACE_LE; POLYHEDRON_HALFSPACE_GE];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_TB3_CELL_IMP_BALL THENL
   [EXISTS_TAC `relative_frontier (P INTER {y:real^3 | nu dot y <= c})`;
    EXISTS_TAC `relative_frontier (P INTER {y:real^3 | nu dot y >= c})`] THEN
  MATCH_MP_TAC MOI_S4A_POLY_CELL_3 THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM DIMINDEX_3] THEN
  MATCH_MP_TAC AFF_DIM_NONEMPTY_INTERIOR THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THENL
   [EXISTS_TAC `m - t % nu:real^3`; EXISTS_TAC `m + t % nu:real^3`] THEN
  MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THENL
   [EXISTS_TAC `interior P INTER {y:real^3 | nu dot y < c}`;
    EXISTS_TAC `interior P INTER {y:real^3 | nu dot y > c}`] THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  MATCH_MP_TAC INTERIOR_MAXIMAL THEN
  SIMP_TAC[OPEN_INTER; OPEN_INTERIOR; OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
  MP_TAC(ISPEC `P:real^3->bool` INTERIOR_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE; real_gt; real_ge]);;

let MOI_TB3_PLANE_SECTION = prove
 (`!P (nu:real^3) c.
     polytope P /\ ~(nu = vec 0) /\ ~(interior P INTER {y | nu dot y = c} = {})
     ==> pl_cell_with_boundary 2 (P INTER {y | nu dot y = c})
                                (relative_frontier (P INTER {y | nu dot y = c})) /\
         relative_interior (P INTER {y | nu dot y = c}) =
         interior P INTER {y | nu dot y = c} /\
         P INTER {y | nu dot y = c} SUBSET frontier (P INTER {y | nu dot y <= c}) /\
         P INTER {y | nu dot y = c} SUBSET frontier (P INTER {y | nu dot y >= c})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (P:real^3->bool) /\ closed P` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_CLOSED]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4A_POLY_CELL_2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_REWRITE_TAC[POLYHEDRON_HYPERPLANE];
      ALL_TAC] THEN
    MATCH_MP_TAC(INT_ARITH `a <= &2 /\ &2 <= a ==> a:int = &2`) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`P INTER {y:real^3 | nu dot y = c}`; `{y:real^3 | nu dot y = c}`]
        AFF_DIM_SUBSET) THEN
      ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; DIMINDEX_3; INTER_SUBSET] THEN
      CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{y:real^3 | nu dot y = c}`; `interior P:real^3->bool`]
      AFF_DIM_CONVEX_INTER_OPEN) THEN
    ASM_SIMP_TAC[CONVEX_HYPERPLANE; OPEN_INTERIOR; AFF_DIM_HYPERPLANE; DIMINDEX_3] THEN
    ANTS_TAC THENL [ONCE_REWRITE_TAC[INTER_COMM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`{y:real^3 | nu dot y = c} INTER interior P`;
                   `P INTER {y:real^3 | nu dot y = c}`] AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL [MP_TAC(ISPEC `P:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
    MATCH_MP_TAC RELATIVE_INTERIOR_CONVEX_INTER_AFFINE THEN
    ASM_REWRITE_TAC[AFFINE_HYPERPLANE];
    REWRITE_TAC[frontier] THEN
    SUBGOAL_THEN `closure (P INTER {y:real^3 | nu dot y <= c}) = P INTER {y | nu dot y <= c}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC CLOSED_INTER THEN
      ASM_REWRITE_TAC[CLOSED_HALFSPACE_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `interior (P INTER {y:real^3 | nu dot y <= c}) SUBSET {y | nu dot y < c}`
    MP_TAC THENL
     [ASM_SIMP_TAC[GSYM INTERIOR_HALFSPACE_LE] THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LE_REFL; REAL_LT_REFL];
    REWRITE_TAC[frontier] THEN
    SUBGOAL_THEN `closure (P INTER {y:real^3 | nu dot y >= c}) = P INTER {y | nu dot y >= c}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC CLOSED_INTER THEN
      ASM_REWRITE_TAC[CLOSED_HALFSPACE_GE];
      ALL_TAC] THEN
    SUBGOAL_THEN `interior (P INTER {y:real^3 | nu dot y >= c}) SUBSET {y | nu dot y > c}`
    MP_TAC THENL
     [ASM_SIMP_TAC[GSYM INTERIOR_HALFSPACE_GE] THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_ELIM_THM; real_ge; real_gt] THEN
    MESON_TAC[REAL_LE_REFL; REAL_LT_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The integer lattice, beads (cubes of half-width 1/4 at lattice points)   *)
(* and necks (thin boxes of half-width 1/8 between adjacent beads), at unit *)
(* scale.  Distinct beads are disjoint, necks of different edges are        *)
(* disjoint, a bead meets a neck only at the ends of its edge, and then in  *)
(* a square lying in both frontiers.                                        *)
(* ------------------------------------------------------------------------- *)

let moi_tb3_lat = new_definition
 `moi_tb3_lat (g:real^3) <=> !i. 1 <= i /\ i <= 3 ==> integer (g$i)`;;

let moi_tb3_step = new_definition
 `moi_tb3_step (g:real^3) (g':real^3) <=>
    moi_tb3_lat g /\ ?k. 1 <= k /\ k <= 3 /\ (g' = g + basis k \/ g' = g - basis k)`;;

let moi_tb3_bead = new_definition
 `moi_tb3_bead (g:real^3) =
    interval[(lambda i. g$i - inv(&4)):real^3,(lambda i. g$i + inv(&4))]`;;

let moi_tb3_neck = new_definition
 `moi_tb3_neck (g:real^3) (g':real^3) =
    interval[(lambda i. if g$i = g'$i then g$i - inv(&8)
                        else min (g$i) (g'$i) + inv(&4)):real^3,
             (lambda i. if g$i = g'$i then g$i + inv(&8)
                        else max (g$i) (g'$i) - inv(&4))]`;;

let MOI_TB3_INT_EQ = prove
 (`!a b. integer a /\ integer b /\ abs(a - b) < &1 ==> a = b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `a - b = &0 ==> a = b`) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPEC `a - b:real` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC);;

let MOI_TB3_IN_BEAD = prove
 (`!g y:real^3. y IN moi_tb3_bead g <=>
                !i. 1 <= i /\ i <= 3 ==> abs(y$i - g$i) <= inv(&4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_tb3_bead; IN_INTERVAL; DIMINDEX_3] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3;
           REAL_ARITH `abs(y - g) <= e <=> g - e <= y /\ y <= g + e`]);;

let MOI_TB3_IN_NECK = prove
 (`!g g' y:real^3. y IN moi_tb3_neck g g' <=>
     !i. 1 <= i /\ i <= 3
         ==> (if g$i = g'$i then abs(y$i - g$i) <= inv(&8)
              else min (g$i) (g'$i) + inv(&4) <= y$i /\
                   y$i <= max (g$i) (g'$i) - inv(&4))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_tb3_neck; IN_INTERVAL; DIMINDEX_3] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

let MOI_TB3_NECK_SYM = prove
 (`!g g':real^3. moi_tb3_neck g g' = moi_tb3_neck g' g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; MOI_TB3_IN_NECK] THEN
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[REAL_ARITH `min a b = min b a /\ max a b = max b a`] THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!a b. min a b = min b a /\ max a b = max b a` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let MOI_TB3_STEP_COORDS = prove
 (`!g g':real^3.
     moi_tb3_step g g'
     ==> moi_tb3_lat g /\ moi_tb3_lat g' /\
         ?k. 1 <= k /\ k <= 3 /\
             (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> g'$i = g$i) /\
             abs(g'$k - g$k) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_tb3_step; moi_tb3_lat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; BASIS_COMPONENT;
                  DIMINDEX_3] THEN
     COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ADD_RID; REAL_SUB_RZERO];
     EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
       ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; BASIS_COMPONENT;
                    DIMINDEX_3] THEN
       REAL_ARITH_TAC;
       ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; BASIS_COMPONENT;
                    DIMINDEX_3] THEN
       REAL_ARITH_TAC]]));;

let MOI_TB3_BEAD_DISJ = prove
 (`!g h:real^3. moi_tb3_lat g /\ moi_tb3_lat h /\ ~(g = h)
                ==> DISJOINT (moi_tb3_bead g) (moi_tb3_bead h)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; MOI_TB3_IN_BEAD] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `~(g:real^3 = h)` THEN REWRITE_TAC[CART_EQ; DIMINDEX_3] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_TB3_INT_EQ THEN
  RULE_ASSUM_TAC(REWRITE_RULE[moi_tb3_lat]) THEN ASM_SIMP_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let MOI_TB3_NOT_INT_FRAC = prove
 (`!d. integer d /\ inv(&8) <= d /\ d <= &7 / &8 ==> F`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `d:real` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_TB3_MIN_MAX_INT = prove
 (`!a b. integer a /\ integer b /\ abs(b - a) = &1
         ==> integer (min a b) /\ max a b = min a b + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `a <= b \/ b <= a:real`) THEN
  ASM_SIMP_TAC[REAL_ARITH `a <= b ==> min a b = a /\ max a b = b`;
               REAL_ARITH `b <= a ==> min a b = b /\ max a b = a`] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_TB3_NECK_DISJ = prove
 (`!g g' h h' y:real^3.
     moi_tb3_step g g' /\ moi_tb3_step h h' /\
     y IN moi_tb3_neck g g' /\ y IN moi_tb3_neck h h'
     ==> (h = g /\ h' = g') \/ (h = g' /\ h' = g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS)
    (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) MP_TAC)) THEN
  REWRITE_TAC[MOI_TB3_IN_NECK; moi_tb3_lat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "n1") (LABEL_TAC "n2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lh") (CONJUNCTS_THEN2 (LABEL_TAC "lh'")
    (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lg") (CONJUNCTS_THEN2 (LABEL_TAC "lg'")
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~((g:real^3)$k = (g':real^3)$k) /\ ~((h:real^3)$m = (h':real^3)$m)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:real^3)$k`; `(g':real^3)$k`] MOI_TB3_MIN_MAX_INT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`(h:real^3)$m`; `(h':real^3)$m`] MOI_TB3_MIN_MAX_INT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  USE_THEN "n1" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= k`) (ASSUME `k <= 3`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "n2" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= m`) (ASSUME `m <= 3`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `m:num = k` THENL
   [ALL_TAC;
    SUBGOAL_THEN `(h':real^3)$k = (h:real^3)$k` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `m:num`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "n2" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= k`) (ASSUME `k <= 3`))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC MOI_TB3_NOT_INT_FRAC THEN
    EXISTS_TAC `(h:real^3)$k - min ((g:real^3)$k) ((g':real^3)$k)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[INTEGER_CLOSED]; ASM_REAL_ARITH_TAC]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> (h:real^3)$i = (g:real^3)$i`
  (LABEL_TAC "tr") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_TB3_INT_EQ THEN
    ASM_SIMP_TAC[] THEN
    REMOVE_THEN "n1" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= i`) (ASSUME `i <= 3`))) THEN
    REMOVE_THEN "n2" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= i`) (ASSUME `i <= 3`))) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `min ((h:real^3)$k) ((h':real^3)$k) = min ((g:real^3)$k) ((g':real^3)$k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_TB3_INT_EQ THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3)$k = (g:real^3)$k /\ (h':real^3)$k = (g':real^3)$k \/
                (h:real^3)$k = (g':real^3)$k /\ (h':real^3)$k = (g:real^3)$k` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`min ((h:real^3)$k) ((h':real^3)$k) = min ((g:real^3)$k) ((g':real^3)$k)`;
      `max ((h:real^3)$k) ((h':real^3)$k) = min ((h:real^3)$k) ((h':real^3)$k) + &1`;
      `max ((g:real^3)$k) ((g':real^3)$k) = min ((g:real^3)$k) ((g':real^3)$k) + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3] THEN STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "tr" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `k:num`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_TB3_INT_01 = prove
 (`!d. integer d /\ &0 <= d /\ d <= &1 ==> d = &0 \/ d = &1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = &0` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `d:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_TB3_BEAD_NECK = prove
 (`!g g' h y:real^3.
     moi_tb3_step g g' /\ moi_tb3_lat h /\
     y IN moi_tb3_bead h /\ y IN moi_tb3_neck g g'
     ==> h = g \/ h = g'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) MP_TAC) THEN
  REWRITE_TAC[MOI_TB3_IN_NECK; MOI_TB3_IN_BEAD; moi_tb3_lat] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lh") (CONJUNCTS_THEN2 (LABEL_TAC "b")
    (LABEL_TAC "n"))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lg") (CONJUNCTS_THEN2 (LABEL_TAC "lg'")
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~((g:real^3)$k = (g':real^3)$k)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:real^3)$k`; `(g':real^3)$k`] MOI_TB3_MIN_MAX_INT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> (h:real^3)$i = (g:real^3)$i`
  (LABEL_TAC "tr") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_TB3_INT_EQ THEN
    ASM_SIMP_TAC[] THEN
    USE_THEN "n" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= i`) (ASSUME `i <= 3`))) THEN
    USE_THEN "b" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= i`) (ASSUME `i <= 3`))) THEN
    SUBGOAL_THEN `(g:real^3)$i = (g':real^3)$i` (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "n" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= k`) (ASSUME `k <= 3`))) THEN
  USE_THEN "b" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= k`) (ASSUME `k <= 3`))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPEC `(h:real^3)$k - min ((g:real^3)$k) ((g':real^3)$k)` MOI_TB3_INT_01) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[INTEGER_CLOSED]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `min ((g:real^3)$k) ((g':real^3)$k) = g$k /\
                max ((g:real^3)$k) ((g':real^3)$k) = g'$k \/
                min ((g:real^3)$k) ((g':real^3)$k) = g'$k /\
                max ((g:real^3)$k) ((g':real^3)$k) = g$k` MP_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC; DISJ2_TAC; DISJ2_TAC; DISJ1_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_CASES_TAC `i:num = k` THEN
  ASM_REWRITE_TAC[] THEN TRY ASM_REAL_ARITH_TAC THEN
  REMOVE_THEN "tr" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN TRY REFL_TAC THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_TB3_BOX_BALL = prove
 (`!l u:real^3. (!i. 1 <= i /\ i <= 3 ==> l$i < u$i) ==> pl_ball 3 (interval[l,u])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_TB3_CELL_IMP_BALL THEN
  EXISTS_TAC `relative_frontier(interval[l:real^3,u])` THEN
  MP_TAC(ISPECL [`l:real^3`; `u:real^3`] MOI_S5N_BOX_CELL) THEN ASM_SIMP_TAC[]);;

let MOI_TB3_BEAD_BALL = prove
 (`!g:real^3. pl_ball 3 (moi_tb3_bead g)`,
  GEN_TAC THEN REWRITE_TAC[moi_tb3_bead] THEN MATCH_MP_TAC MOI_TB3_BOX_BALL THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3] THEN REAL_ARITH_TAC);;

let MOI_TB3_NECK_BALL = prove
 (`!g g':real^3. moi_tb3_step g g' ==> pl_ball 3 (moi_tb3_neck g g')`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[moi_tb3_neck] THEN MATCH_MP_TAC MOI_TB3_BOX_BALL THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = k` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((g:real^3)$k = (g':real^3)$k)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(g:real^3)$i = (g':real^3)$i` (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]]);;

let MOI_TB3_FLAT_BOX = prove
 (`!l u:real^3 k.
     1 <= k /\ k <= 3 /\ l$k = u$k /\
     (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> l$i < u$i)
     ==> pl_cell_with_boundary 2 (interval[l,u]) (relative_frontier (interval[l,u]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4A_POLY_CELL_2 THEN
  REWRITE_TAC[POLYTOPE_INTERVAL; AFF_DIM_INTERVAL] THEN
  SUBGOAL_THEN `~(interval[l:real^3,u] = {})` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_3] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `i:num = k` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{i | 1 <= i /\ i <= dimindex(:3) /\ (l:real^3)$i < (u:real^3)$i} = {1,2,3} DELETE k`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_3] THEN
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    EQ_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `1 <= i /\ i <= 3` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:num) IN {1,2,3}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE; FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN `CARD {1,2,3} = 3` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    CONV_TAC NUM_REDUCE_CONV]);;

let MOI_TB3_FACE = prove
 (`!g g':real^3.
     moi_tb3_step g g'
     ==> pl_cell_with_boundary 2 (moi_tb3_bead g INTER moi_tb3_neck g g')
           (relative_frontier (moi_tb3_bead g INTER moi_tb3_neck g g')) /\
         moi_tb3_bead g INTER moi_tb3_neck g g' SUBSET frontier (moi_tb3_bead g) /\
         moi_tb3_bead g INTER moi_tb3_neck g g' SUBSET frontier (moi_tb3_neck g g')`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(g':real^3)$k = (g:real^3)$k + &1 \/ (g':real^3)$k = (g:real^3)$k - &1`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_tb3_bead; moi_tb3_neck; INTER_INTERVAL] THEN
  REWRITE_TAC[FRONTIER_CLOSED_INTERVAL] THEN
  SIMP_TAC[SUBSET; IN_INTERVAL; IN_DIFF; LAMBDA_BETA; DIMINDEX_3] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_TB3_FLAT_BOX THEN EXISTS_TAC `k:num` THEN
    ASM_SIMP_TAC[LAMBDA_BETA; DIMINDEX_3] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `~((g:real^3)$k = (g':real^3)$k)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(g:real^3)$i = (g':real^3)$i` (fun th -> REWRITE_TAC[th]) THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `k:num` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((g:real^3)$k = (g':real^3)$k)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `k:num` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((g:real^3)$k = (g':real^3)$k)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Chains of beads and necks along a simple lattice walk, and gluing a      *)
(* chain to a ball that meets it in a disk of its first bead.               *)
(* ------------------------------------------------------------------------- *)

let moi_tb3_walk = define
 `(moi_tb3_walk [] <=> F) /\
  (moi_tb3_walk (CONS (g:real^3) []) <=> moi_tb3_lat g) /\
  (moi_tb3_walk (CONS g (CONS g' l)) <=> moi_tb3_step g g' /\ moi_tb3_walk (CONS g' l))`;;

let moi_tb3_chain = define
 `(moi_tb3_chain [] = {}:real^3->bool) /\
  (moi_tb3_chain (CONS (g:real^3) []) = moi_tb3_bead g) /\
  (moi_tb3_chain (CONS g (CONS g' l)) =
     moi_tb3_bead g UNION moi_tb3_neck g g' UNION moi_tb3_chain (CONS g' l))`;;

let MOI_TB3_STEP_SYM = prove
 (`!g g':real^3. moi_tb3_step g g' ==> moi_tb3_step g' g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  UNDISCH_TAC `moi_tb3_step (g:real^3) g'` THEN REWRITE_TAC[moi_tb3_step] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN VECTOR_ARITH_TAC; DISJ1_TAC THEN VECTOR_ARITH_TAC]);;

let MOI_TB3_STEP_DISTINCT = prove
 (`!g g':real^3. moi_tb3_step g g' ==> ~(g = g')`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `abs((g':real^3)$k - g'$k) = &1` THEN REAL_ARITH_TAC);;

let MOI_TB3_WALK_CONS = prove
 (`!(h:real^3) t. moi_tb3_walk (CONS h t)
                  ==> moi_tb3_lat h /\ (~(t = []) ==> moi_tb3_walk t)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[moi_tb3_walk; NOT_CONS_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) THEN SIMP_TAC[]);;

let MOI_TB3_WALK_LAT = prove
 (`!l (x:real^3). moi_tb3_walk l /\ MEM x l ==> moi_tb3_lat x`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[moi_tb3_walk]; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[MEM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP MOI_TB3_WALK_CONS) MP_TAC) THEN
  STRIP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `MEM (x:real^3) []` THEN REWRITE_TAC[MEM]);;

let MOI_TB3_CHAIN_CONS = prove
 (`!(g:real^3) t.
     moi_tb3_chain (CONS g t) =
     moi_tb3_bead g UNION
     (if t = [] then {} else moi_tb3_neck g (HD t) UNION moi_tb3_chain t)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[moi_tb3_chain; NOT_CONS_NIL; HD; UNION_EMPTY] THEN SET_TAC[]);;

let MOI_TB3_WALK_STEP = prove
 (`!(g:real^3) t. moi_tb3_walk (CONS g t) /\ ~(t = [])
                  ==> moi_tb3_step g (HD t) /\ moi_tb3_walk t`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[moi_tb3_walk; NOT_CONS_NIL; HD]);;

let MOI_TB3_DISJ_UNION_R = prove
 (`!s t u:real^3->bool. DISJOINT s (t UNION u) <=> DISJOINT s t /\ DISJOINT s u`,
  SET_TAC[]);;

let MOI_TB3_CHAIN_AVOID_BEAD = prove
 (`!l (h:real^3). moi_tb3_walk l /\ moi_tb3_lat h /\ ~(MEM h l)
                  ==> DISJOINT (moi_tb3_bead h) (moi_tb3_chain l)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[moi_tb3_walk]; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[MEM; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[MOI_TB3_CHAIN_CONS] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_TB3_WALK_CONS) THEN
  REWRITE_TAC[MOI_TB3_DISJ_UNION_R] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_TB3_BEAD_DISJ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[DISJOINT_EMPTY; MOI_TB3_DISJ_UNION_R] THEN
  MP_TAC(ISPECL [`h:real^3`; `t:(real^3)list`] MOI_TB3_WALK_STEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^3`; `HD t:real^3`; `x:real^3`; `y:real^3`] MOI_TB3_BEAD_NECK) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MEM (HD t:real^3) t` (fun th -> ASM_MESON_TAC[th]) THEN
    UNDISCH_TAC `~(t:(real^3)list = [])` THEN
    STRUCT_CASES_TAC(ISPEC `t:(real^3)list` list_CASES) THEN REWRITE_TAC[MEM; HD];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_TB3_HD_MEM = prove
 (`!t:(real^3)list. ~(t = []) ==> MEM (HD t) t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; HD; NOT_CONS_NIL]);;

let MOI_TB3_CHAIN_AVOID_EDGE = prove
 (`!l (h:real^3) h'.
     moi_tb3_walk l /\ moi_tb3_step h h' /\ ~(MEM h l) /\ ~(MEM h' l)
     ==> DISJOINT (moi_tb3_neck h h') (moi_tb3_chain l)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[moi_tb3_walk]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `x':real^3`] THEN
  REWRITE_TAC[MEM; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[MOI_TB3_CHAIN_CONS] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_TB3_WALK_CONS) THEN
  REWRITE_TAC[MOI_TB3_DISJ_UNION_R] THEN CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `x':real^3`; `h:real^3`; `y:real^3`] MOI_TB3_BEAD_NECK) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[DISJOINT_EMPTY; MOI_TB3_DISJ_UNION_R] THEN
  MP_TAC(ISPECL [`h:real^3`; `t:(real^3)list`] MOI_TB3_WALK_STEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (HD t:real^3) t` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_TB3_HD_MEM THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `x':real^3`; `h:real^3`; `HD t:real^3`; `y:real^3`]
      MOI_TB3_NECK_DISJ) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_TB3_CHAIN_GLUE = prove
 (`!l (g:real^3) y d j.
     moi_tb3_walk (CONS g l) /\ PAIRWISE (\a b. ~(a = b)) (CONS g l) /\
     pl_ball 3 y /\ y INTER moi_tb3_chain (CONS g l) = d /\ d SUBSET moi_tb3_bead g /\
     pl_cell_with_boundary 2 d j /\ d SUBSET frontier (moi_tb3_bead g)
     ==> pl_ball 3 (y UNION moi_tb3_chain (CONS g l))`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[moi_tb3_chain] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^3->bool`; `moi_tb3_bead g`; `d:real^3->bool`; `j:real^3->bool`]
      MOI_TB3_GLUE) THEN
    ASM_REWRITE_TAC[MOI_TB3_BEAD_BALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:real^3`; `y:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`] THEN
  REWRITE_TAC[moi_tb3_walk; PAIRWISE; ALL; moi_tb3_chain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~MEM (g:real^3) (CONS h t) /\ ~MEM (h:real^3) t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEM] THEN
    MAP_EVERY UNDISCH_TAC [`ALL (\b. ~((g:real^3) = b)) t`; `ALL (\b. ~((h:real^3) = b)) t`;
                           `~((g:real^3) = h)`] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_tb3_lat (g:real^3) /\ moi_tb3_lat (h:real^3)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3`; `h:real^3`] MOI_TB3_FACE) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:real^3`; `g:real^3`] MOI_TB3_FACE) THEN
  ANTS_TAC THENL [MATCH_MP_TAC MOI_TB3_STEP_SYM THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o ONCE_REWRITE_RULE[MOI_TB3_NECK_SYM]) THEN
  SUBGOAL_THEN `DISJOINT (moi_tb3_bead g) (moi_tb3_chain (CONS (h:real^3) t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_TB3_CHAIN_AVOID_BEAD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_tb3_neck g h INTER moi_tb3_chain (CONS (h:real^3) t) =
                moi_tb3_bead h INTER moi_tb3_neck g h` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MOI_TB3_CHAIN_CONS] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[UNION_EMPTY] THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^3`; `t:(real^3)list`] MOI_TB3_WALK_STEP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `MEM (HD t:real^3) t` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_TB3_HD_MEM THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (moi_tb3_neck g h) (moi_tb3_neck h (HD t:real^3)) /\
                  DISJOINT (moi_tb3_neck g h) (moi_tb3_chain (t:(real^3)list))`
    MP_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`g:real^3`; `h:real^3`; `h:real^3`; `HD t:real^3`; `z:real^3`]
          MOI_TB3_NECK_DISJ) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `~MEM (g:real^3) (CONS h t)` THEN REWRITE_TAC[MEM] THEN
        UNDISCH_TAC `MEM (HD t:real^3) t` THEN UNDISCH_TAC `~((g:real^3) = h)` THEN
        MESON_TAC[];
        MATCH_MP_TAC MOI_TB3_CHAIN_AVOID_EDGE THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~MEM (g:real^3) (CONS h t)` THEN REWRITE_TAC[MEM] THEN
        MESON_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:real^3->bool`; `moi_tb3_bead g`; `d:real^3->bool`; `j:real^3->bool`]
    MOI_TB3_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_TB3_BEAD_BALL] THEN
    UNDISCH_TAC `y INTER (moi_tb3_bead g UNION moi_tb3_neck g h UNION
                 moi_tb3_chain (CONS (h:real^3) t)) = d` THEN
    UNDISCH_TAC `d SUBSET moi_tb3_bead (g:real^3)` THEN SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`y UNION moi_tb3_bead (g:real^3)`; `moi_tb3_neck g (h:real^3)`;
                 `moi_tb3_bead g INTER moi_tb3_neck g (h:real^3)`;
                 `relative_frontier (moi_tb3_bead g INTER moi_tb3_neck g (h:real^3))`]
    MOI_TB3_GLUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_TB3_NECK_BALL] THEN
    UNDISCH_TAC `y INTER (moi_tb3_bead g UNION moi_tb3_neck g h UNION
                 moi_tb3_chain (CONS (h:real^3) t)) = d` THEN
    UNDISCH_TAC `d SUBSET moi_tb3_bead (g:real^3)` THEN SET_TAC[];
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`h:real^3`; `(y UNION moi_tb3_bead (g:real^3)) UNION moi_tb3_neck g (h:real^3)`;
    `moi_tb3_bead h INTER moi_tb3_neck g (h:real^3)`;
    `relative_frontier (moi_tb3_bead h INTER moi_tb3_neck g (h:real^3))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PAIRWISE; INTER_SUBSET] THEN
    MAP_EVERY UNDISCH_TAC
     [`y INTER (moi_tb3_bead g UNION moi_tb3_neck g h UNION
       moi_tb3_chain (CONS (h:real^3) t)) = d`;
      `d SUBSET moi_tb3_bead (g:real^3)`;
      `DISJOINT (moi_tb3_bead g) (moi_tb3_chain (CONS (h:real^3) t))`;
      `moi_tb3_neck g h INTER moi_tb3_chain (CONS (h:real^3) t) =
       moi_tb3_bead h INTER moi_tb3_neck g h`] THEN
    SET_TAC[];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lazy lattice walks (consecutive points equal or adjacent), and the       *)
(* extraction of a simple walk (shortest lazy walk) with the same ends      *)
(* inside the same set of lattice points.                                   *)
(* ------------------------------------------------------------------------- *)

let moi_tb3_lstep = new_definition
 `moi_tb3_lstep (g:real^3) g' <=> moi_tb3_lat g /\ (g' = g \/ moi_tb3_step g g')`;;

let moi_tb3_lwalk = define
 `(moi_tb3_lwalk [] <=> F) /\
  (moi_tb3_lwalk (CONS (g:real^3) []) <=> moi_tb3_lat g) /\
  (moi_tb3_lwalk (CONS g (CONS g' l)) <=> moi_tb3_lstep g g' /\ moi_tb3_lwalk (CONS g' l))`;;

let MOI_TB3_LWALK_CONS_EQ = prove
 (`!(h:real^3) m.
     moi_tb3_lwalk (CONS h m) <=>
     moi_tb3_lat h /\ (m = [] \/ moi_tb3_lstep h (HD m) /\ moi_tb3_lwalk m)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[moi_tb3_lwalk; NOT_CONS_NIL; HD; moi_tb3_lstep] THEN
  MESON_TAC[]);;

let MOI_TB3_LWALK_LAT_HD = prove
 (`!(x:real^3) r. moi_tb3_lwalk (CONS x r) ==> moi_tb3_lat x`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MOI_TB3_LWALK_CONS_EQ] THEN SIMP_TAC[]);;

let MOI_TB3_LWALK_SPLIT = prove
 (`!u (x:real^3) r.
     moi_tb3_lwalk (APPEND u (CONS x r)) <=>
     moi_tb3_lwalk (APPEND u [x]) /\ moi_tb3_lwalk (CONS x r)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; moi_tb3_lwalk] THEN MESON_TAC[MOI_TB3_LWALK_LAT_HD];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THEN
  GEN_REWRITE_TAC LAND_CONV [MOI_TB3_LWALK_CONS_EQ] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [MOI_TB3_LWALK_CONS_EQ] THEN
  REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL; HD_APPEND; HD] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
    [SPECL [`x:real^3`; `r:(real^3)list`] th]) THEN
  CONV_TAC TAUT);;

let MOI_TB3_MEM_SPLIT = prove
 (`!l (x:real^3). MEM x l ==> ?u v. l = APPEND u (CONS x v)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`[]:(real^3)list`; `t:(real^3)list`] THEN
    ASM_REWRITE_TAC[APPEND];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:(real^3)list` (X_CHOOSE_THEN `v:(real^3)list`
      SUBST1_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:real^3) u`; `v:(real^3)list`] THEN
    REWRITE_TAC[APPEND]]);;

let MOI_TB3_NOT_PAIRWISE = prove
 (`!l:(real^3)list.
     ~PAIRWISE (\a b. ~(a = b)) l
     ==> ?u v w x. l = APPEND u (CONS x (APPEND v (CONS x w)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[PAIRWISE; DE_MORGAN_THM] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `MEM (h:real^3) t` MP_TAC THENL
     [UNDISCH_TAC `~ALL (\b. ~((h:real^3) = b)) t` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_TB3_MEM_SPLIT) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:(real^3)list` (X_CHOOSE_THEN `w:(real^3)list`
      SUBST1_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`[]:(real^3)list`; `v:(real^3)list`; `w:(real^3)list`;
                          `h:real^3`] THEN
    REWRITE_TAC[APPEND];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:(real^3)list` (X_CHOOSE_THEN `v:(real^3)list`
      (X_CHOOSE_THEN `w:(real^3)list` (X_CHOOSE_THEN `x:real^3` SUBST1_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:real^3) u`; `v:(real^3)list`; `w:(real^3)list`;
                          `x:real^3`] THEN
    REWRITE_TAC[APPEND]]);;

let MOI_TB3_SIMPLE_LWALK = prove
 (`!s (a:real^3) b.
     (?l. moi_tb3_lwalk l /\ HD l = a /\ LAST l = b /\ ALL (\x. x IN s) l)
     ==> ?l. moi_tb3_lwalk l /\ HD l = a /\ LAST l = b /\ ALL (\x. x IN s) l /\
             PAIRWISE (\x y. ~(x = y)) l`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [MESON[] `(?l:(real^3)list. P l) <=> (?n l. LENGTH l = n /\ P l)`] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [num_WOP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l:(real^3)list` STRIP_ASSUME_TAC) (LABEL_TAC "min"))) THEN
  EXISTS_TAC `l:(real^3)list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_TB3_NOT_PAIRWISE) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^3)list` (X_CHOOSE_THEN `v:(real^3)list`
    (X_CHOOSE_THEN `w:(real^3)list` (X_CHOOSE_THEN `x:real^3` ASSUME_TAC)))) THEN
  REMOVE_THEN "min" (MP_TAC o SPEC `LENGTH (APPEND u (CONS (x:real^3) w))`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [UNDISCH_TAC `LENGTH (l:(real^3)list) = n` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_tb3_lwalk (APPEND u [x:real^3]) /\ moi_tb3_lwalk (CONS (x:real^3) w)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:(real^3)list`; `x:real^3`; `APPEND v (CONS (x:real^3) w)`]
      MOI_TB3_LWALK_SPLIT) THEN
    MP_TAC(ISPECL [`CONS (x:real^3) v`; `x:real^3`; `w:(real^3)list`]
      MOI_TB3_LWALK_SPLIT) THEN
    REWRITE_TAC[APPEND] THEN
    UNDISCH_TAC `moi_tb3_lwalk (l:(real^3)list)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `APPEND u (CONS (x:real^3) w)` THEN
  ONCE_REWRITE_TAC[MOI_TB3_LWALK_SPLIT] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `HD (l:(real^3)list) = a` THEN UNDISCH_TAC `LAST (l:(real^3)list) = b` THEN
  UNDISCH_TAC `ALL (\x:real^3. x IN s) l` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LAST (CONS (x:real^3) (APPEND v (CONS x w))) = LAST (CONS x w)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `CONS (x:real^3) (APPEND v (CONS x w)) = APPEND (CONS x v) (CONS x w)`
    SUBST1_TAC THENL [REWRITE_TAC[APPEND]; REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL]];
    ALL_TAC] THEN
  REWRITE_TAC[ALL_APPEND; ALL; HD_APPEND; HD; LAST_APPEND; NOT_CONS_NIL;
              APPEND_EQ_NIL] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_TB3_WALK_CONS_EQ = prove
 (`!(h:real^3) m.
     moi_tb3_walk (CONS h m) <=>
     moi_tb3_lat h /\ (m = [] \/ moi_tb3_step h (HD m) /\ moi_tb3_walk m)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[moi_tb3_walk; NOT_CONS_NIL; HD] THEN
  MESON_TAC[MOI_TB3_STEP_COORDS]);;

let MOI_TB3_SIMPLE_IMP_WALK = prove
 (`!l:(real^3)list.
     moi_tb3_lwalk l /\ PAIRWISE (\x y. ~(x = y)) l ==> moi_tb3_walk l`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[moi_tb3_lwalk]; ALL_TAC] THEN
  REWRITE_TAC[PAIRWISE] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MOI_TB3_LWALK_CONS_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [MOI_TB3_WALK_CONS_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  SUBGOAL_THEN `~(t:(real^3)list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `moi_tb3_lwalk ([]:(real^3)list)` THEN
    REWRITE_TAC[moi_tb3_lwalk];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `~(HD t = (h:real^3))` ASSUME_TAC THENL
     [UNDISCH_TAC `ALL (\y. ~((h:real^3) = y)) t` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      DISCH_THEN(MP_TAC o SPEC `HD t:real^3`) THEN
      ANTS_TAC THENL [MATCH_MP_TAC MOI_TB3_HD_MEM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_tb3_lstep (h:real^3) (HD t)` THEN
    ASM_REWRITE_TAC[moi_tb3_lstep] THEN SIMP_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Rounding to the lattice, half-cubes, and lazy walks along a path.        *)

let moi_tb3_round = new_definition
 `moi_tb3_round (x:real^3) = (lambda i. floor (x$i + inv(&2))):real^3`;;

let moi_tb3_cube = new_definition
 `moi_tb3_cube (g:real^3) =
    interval[(lambda i. g$i - inv(&2)):real^3,(lambda i. g$i + inv(&2))]`;;

let MOI_TB3_ROUND = prove
 (`!x:real^3. moi_tb3_lat (moi_tb3_round x) /\
              !i. 1 <= i /\ i <= 3 ==> abs(x$i - (moi_tb3_round x)$i) <= inv(&2)`,
  GEN_TAC THEN REWRITE_TAC[moi_tb3_lat; moi_tb3_round] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; FLOOR] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(SPEC `(x:real^3)$i + inv(&2)` FLOOR) THEN REAL_ARITH_TAC);;

let MOI_TB3_IN_CUBE = prove
 (`!g y:real^3. y IN moi_tb3_cube g <=>
                !i. 1 <= i /\ i <= 3 ==> abs(y$i - g$i) <= inv(&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_tb3_cube; IN_INTERVAL; DIMINDEX_3] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3;
           REAL_ARITH `abs(y - g) <= e <=> g - e <= y /\ y <= g + e`]);;

let MOI_TB3_LWALK_SNOC = prove
 (`!l (p:real^3). moi_tb3_lwalk l /\ moi_tb3_lstep (LAST l) p
                  ==> moi_tb3_lwalk (APPEND l [p])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(l:(real^3)list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `moi_tb3_lwalk ([]:(real^3)list)` THEN
    REWRITE_TAC[moi_tb3_lwalk];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
    [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  ONCE_REWRITE_TAC[MOI_TB3_LWALK_SPLIT] THEN
  ASM_SIMP_TAC[APPEND_BUTLAST_LAST] THEN
  REWRITE_TAC[moi_tb3_lwalk] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_tb3_lstep (LAST l) (p:real^3)` THEN
  REWRITE_TAC[moi_tb3_lstep] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) THEN SIMP_TAC[]);;

let MOI_TB3_INT_ABS_LE1 = prove
 (`!d. integer d /\ abs d <= &1 ==> d = &0 \/ d = &1 \/ d = -- &1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = &0` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `d:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_TB3_LSTEP_BASIS = prove
 (`!(g:real^3) d k.
     moi_tb3_lat g /\ 1 <= k /\ k <= 3 /\ (d = &0 \/ d = &1 \/ d = -- &1)
     ==> moi_tb3_lstep g (g + d % basis k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_tb3_lstep] THEN
  REWRITE_TAC[moi_tb3_step] THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN VECTOR_ARITH_TAC;
    DISJ2_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN VECTOR_ARITH_TAC;
    DISJ2_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN VECTOR_ARITH_TAC]);;

let MOI_TB3_CONNECT = prove
 (`!(q:real^3) q'.
     moi_tb3_lat q /\ moi_tb3_lat q' /\
     (!i. 1 <= i /\ i <= 3 ==> abs(q'$i - q$i) <= &1)
     ==> ?p1 p2. moi_tb3_lstep q p1 /\ moi_tb3_lstep p1 p2 /\ moi_tb3_lstep p2 q' /\
                 (!i. 1 <= i /\ i <= 3
                      ==> abs((p1:real^3)$i - q$i) <= &1 /\ abs((p2:real^3)$i - q$i) <= &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[moi_tb3_lat; FORALL_3]) THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3
                    ==> (q':real^3)$i - (q:real^3)$i = &0 \/ q'$i - q$i = &1 \/
                        q'$i - q$i = -- &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_3] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_TB3_INT_ABS_LE1 THEN
    ASM_SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(q:real^3) + ((q':real^3)$1 - q$1) % basis 1`;
    `(q:real^3) + ((q':real^3)$1 - q$1) % basis 1 + ((q':real^3)$2 - q$2) % basis 2`] THEN
  SUBGOAL_THEN
   `q' = ((q:real^3) + ((q':real^3)$1 - q$1) % basis 1 + ((q':real^3)$2 - q$2) % basis 2) +
         ((q':real^3)$3 - q$3) % basis 3`
  (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV) [th]) THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_tb3_lat ((q:real^3) + ((q':real^3)$1 - q$1) % basis 1) /\
                moi_tb3_lat ((q:real^3) + ((q':real^3)$1 - q$1) % basis 1 +
                             ((q':real^3)$2 - q$2) % basis 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_tb3_lat; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_TB3_LSTEP_BASIS THEN ASM_REWRITE_TAC[moi_tb3_lat; FORALL_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    REWRITE_TAC[VECTOR_ADD_ASSOC] THEN MATCH_MP_TAC MOI_TB3_LSTEP_BASIS THEN
    ASM_REWRITE_TAC[GSYM VECTOR_ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    MATCH_MP_TAC MOI_TB3_LSTEP_BASIS THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN FIRST_X_ASSUM(MP_TAC o SPEC `3`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    REWRITE_TAC[FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC]);;

let MOI_TB3_INT_ABS_LT2 = prove
 (`!d. integer d /\ abs d < &2 ==> abs d <= &1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 < d \/ d < -- &1` DISJ_CASES_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC; ALL_TAC] THENL
   [MP_TAC(SPEC `d - &1` REAL_ABS_INTEGER_LEMMA);
    MP_TAC(SPEC `d + &1` REAL_ABS_INTEGER_LEMMA)] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC);;

let MOI_TB3_CUBE_NEAR = prove
 (`!(x:real^3) p r.
     (!i. 1 <= i /\ i <= 3 ==> abs(p$i - x$i) <= r)
     ==> moi_tb3_cube p SUBSET ball(x,&3 * r + &2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; MOI_TB3_IN_CUBE; IN_BALL; dist] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `x - y:real^3` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_forall o concl))) THEN
  REWRITE_TAC[FORALL_3] THEN REAL_ARITH_TAC);;

let MOI_TB3_PATH_WALK = prove
 (`!v (gam:real^1->real^3).
     path gam /\ (!t. t IN interval[vec 0,vec 1] ==> ball(gam t,&7) SUBSET v)
     ==> ?l. moi_tb3_lwalk l /\ HD l = moi_tb3_round (pathstart gam) /\
             LAST l = moi_tb3_round (pathfinish gam) /\
             ALL (\q. moi_tb3_cube q SUBSET v) l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`gam:real^1->real^3`; `interval[vec 0:real^1,vec 1]`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL] THEN ASM_MESON_TAC[path]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&4)`) THEN
  ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `d:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!k. k <= N
        ==> ?l. moi_tb3_lwalk l /\ HD l = moi_tb3_round ((gam:real^1->real^3) (vec 0)) /\
                LAST l = moi_tb3_round (gam (lift(&k / &N))) /\
                ALL (\q. moi_tb3_cube q SUBSET v) l`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; LIFT_NUM; pathstart; pathfinish]] THEN
  SUBGOAL_THEN `!k. k <= N ==> lift(&k / &N) IN interval[vec 0:real^1,vec 1]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `~(N = 0) ==> 0 < N`; REAL_MUL_LID; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `[moi_tb3_round ((gam:real^1->real^3) (vec 0))]` THEN
    REWRITE_TAC[moi_tb3_lwalk; HD; LAST; ALL; MOI_TB3_ROUND] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; LIFT_NUM] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((gam:real^1->real^3) (vec 0),&7)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball((gam:real^1->real^3) (vec 0),&3 * inv(&2) + &2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_TB3_CUBE_NEAR THEN
        MP_TAC(ISPEC `(gam:real^1->real^3) (vec 0)` MOI_TB3_ROUND) THEN
        MESON_TAC[REAL_ABS_SUB];
        REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^3)list` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `x = (gam:real^1->real^3) (lift(&k / &N))` THEN
  ABBREV_TAC `x' = (gam:real^1->real^3) (lift(&(SUC k) / &N))` THEN
  SUBGOAL_THEN `dist(x':real^3,x) < inv(&4)` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN EXPAND_TAC "x'" THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `d:real`)) (concl th) && is_forall (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `lift`)) (concl th) && is_forall (concl th))) THEN
      ASM_ARITH_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `lift`)) (concl th) && is_forall (concl th))) THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[DIST_LIFT; GSYM REAL_OF_NUM_SUC] THEN
      SUBGOAL_THEN `(&k + &1) / &N - &k / &N = inv(&N)` SUBST1_TAC THENL
       [UNDISCH_TAC `~(N = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
        CONV_TAC REAL_FIELD;
        ASM_REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM]]];
    ALL_TAC] THEN
  ABBREV_TAC `q = moi_tb3_round (x:real^3)` THEN
  ABBREV_TAC `q' = moi_tb3_round (x':real^3)` THEN
  SUBGOAL_THEN `moi_tb3_lat (q:real^3) /\ moi_tb3_lat (q':real^3) /\
                (!i. 1 <= i /\ i <= 3 ==> abs((x:real^3)$i - (q:real^3)$i) <= inv(&2)) /\
                (!i. 1 <= i /\ i <= 3 ==> abs((x':real^3)$i - (q':real^3)$i) <= inv(&2))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN EXPAND_TAC "q'" THEN REWRITE_TAC[MOI_TB3_ROUND]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3 ==> abs((x':real^3)$i - (x:real^3)$i) < inv(&4)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm(x' - x:real^3)` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN MATCH_ACCEPT_TAC COMPONENT_LE_NORM;
      ASM_REWRITE_TAC[GSYM dist]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3`; `q':real^3`] MOI_TB3_CONNECT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_TB3_INT_ABS_LT2 THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_tb3_lat (q:real^3)` THEN UNDISCH_TAC `moi_tb3_lat (q':real^3)` THEN
      REWRITE_TAC[moi_tb3_lat] THEN ASM_SIMP_TAC[INTEGER_CLOSED];
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `inv(&2)`)) (concl th) ||
        is_forall (concl th) && can (find_term ((=) `inv(&4)`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^3` (X_CHOOSE_THEN `p2:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(l:(real^3)list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `moi_tb3_lwalk ([]:(real^3)list)` THEN
    REWRITE_TAC[moi_tb3_lwalk];
    ALL_TAC] THEN
  EXISTS_TAC `APPEND (APPEND (APPEND l [p1:real^3]) [p2]) [q']` THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC MOI_TB3_LWALK_SNOC THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL; LAST];
    ASM_REWRITE_TAC[HD_APPEND; APPEND_EQ_NIL];
    REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL; LAST];
    ASM_REWRITE_TAC[ALL_APPEND; ALL] THEN
    SUBGOAL_THEN `ball(x:real^3,&7) SUBSET v /\ ball(x':real^3,&7) SUBSET v`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN EXPAND_TAC "x'" THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!p:real^3. (!i. 1 <= i /\ i <= 3 ==> abs(p$i - (x:real^3)$i) <= &3 / &2)
                             ==> moi_tb3_cube p SUBSET v` (LABEL_TAC "cx") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(x:real^3,&3 * (&3 / &2) + &2)` THEN
      ASM_SIMP_TAC[MOI_TB3_CUBE_NEAR] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(x:real^3,&7)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REMOVE_THEN "cx" MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REMOVE_THEN "cx" MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x':real^3,&3 * inv(&2) + &2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_TB3_CUBE_NEAR THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl))) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x':real^3,&7)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* The virtual column next to an end bead.  The neck from g to g - 3u (u a    *)
(* signed basis vector) lies in the beads and necks of g - u, g - 2u, g - 3u; *)
(* if these are not on a walk through g, the chain of the walk meets that     *)
(* column only in the face of the bead at g.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_UNION_INTER_SUBSET = prove
 (`!s t u v:real^3->bool.
     (s UNION t) INTER u SUBSET v <=> s INTER u SUBSET v /\ t INTER u SUBSET v`,
  SET_TAC[]);;

let MOI_TB3_CHAIN_NECK1 = prove
 (`!l (g:real^3) g'.
     moi_tb3_walk l /\ moi_tb3_step g g' /\ ~(MEM g' l)
     ==> moi_tb3_chain l INTER moi_tb3_neck g g' SUBSET moi_tb3_bead g`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[moi_tb3_walk]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `x':real^3`] THEN
  REWRITE_TAC[MEM; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[MOI_TB3_CHAIN_CONS] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_TB3_WALK_CONS) THEN
  REWRITE_TAC[MOI_TB3_UNION_INTER_SUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `x':real^3`; `h:real^3`; `y:real^3`] MOI_TB3_BEAD_NECK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INTER_EMPTY; EMPTY_SUBSET] THEN
  MP_TAC(ISPECL [`h:real^3`; `t:(real^3)list`] MOI_TB3_WALK_STEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_TB3_UNION_INTER_SUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `x':real^3`; `h:real^3`; `HD t:real^3`; `y:real^3`]
      MOI_TB3_NECK_DISJ) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MEM (HD t:real^3) t` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_TB3_HD_MEM THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_TB3_LAT_SHIFT = prove
 (`!(g:real^3) a k. moi_tb3_lat g /\ integer a /\ 1 <= k /\ k <= 3
                    ==> moi_tb3_lat (g + a % basis k)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `moi_tb3_lat (g:real^3)` THEN
  REWRITE_TAC[moi_tb3_lat] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED; REAL_MUL_RID; REAL_MUL_RZERO]);;

let MOI_TB3_LAT_U = prove
 (`!(g:real^3) t k u. moi_tb3_lat g /\ integer t /\ 1 <= k /\ k <= 3 /\
                      (u = basis k \/ u = --basis k)
                      ==> moi_tb3_lat (g + t % u)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[MOI_TB3_LAT_SHIFT];
    REWRITE_TAC[VECTOR_MUL_RNEG; GSYM VECTOR_MUL_LNEG] THEN
    MATCH_MP_TAC MOI_TB3_LAT_SHIFT THEN ASM_REWRITE_TAC[INTEGER_NEG]]);;

let MOI_TB3_STEP_U = prove
 (`!(h:real^3) k u. moi_tb3_lat h /\ 1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k)
                    ==> moi_tb3_step h (h + u) /\ moi_tb3_step h (h - u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_tb3_step] THEN
  REWRITE_TAC[VECTOR_ARITH `(h:real^3) + --b = h - b /\ h - --b = h + b`] THEN
  CONJ_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]);;

let MOI_TB3_FORALL_K = prove
 (`!k. 1 <= k /\ k <= 3
       ==> !P. ((!i. 1 <= i /\ i <= 3 ==> P i) <=>
                (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> P i) /\ P k)`,
  MESON_TAC[]);;

let MOI_TB3_U_COORD = prove
 (`!k (u:real^3). 1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k)
     ==> (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> u$i = &0) /\
         (u$k = &1 \/ u$k = -- &1) /\
         (!z:real^3. z dot u = z$k * u$k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; DOT_RNEG; DOT_BASIS] THEN
  REAL_ARITH_TAC);;

let MOI_TB3_NECK_COL = prove
 (`!(g:real^3) k u a b y.
     1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k) /\ a + &1 <= b
     ==> (y IN moi_tb3_neck (g - a % u) (g - b % u) <=>
          (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&8)) /\
          a + inv(&4) <= (g - y) dot u /\ (g - y) dot u <= b - inv(&4))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `u:real^3`] MOI_TB3_U_COORD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `1 <= k /\ k <= 3 /\ a + &1 <= b` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_TB3_IN_NECK] THEN
  REWRITE_TAC[MATCH_MP MOI_TB3_FORALL_K (CONJ (ASSUME `1 <= k`) (ASSUME `k <= 3`))] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; REAL_SUB_RNEG] THEN
  MATCH_MP_TAC(TAUT `(b <=> c) ==> (a /\ b <=> a /\ c)`) THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_TB3_BEAD_COL = prove
 (`!(g:real^3) k u a y.
     1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k)
     ==> (y IN moi_tb3_bead (g - a % u) <=>
          (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&4)) /\
          abs((g - y) dot u - a) <= inv(&4))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `u:real^3`] MOI_TB3_U_COORD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `1 <= k /\ k <= 3` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_TB3_IN_BEAD] THEN
  REWRITE_TAC[MATCH_MP MOI_TB3_FORALL_K (CONJ (ASSUME `1 <= k`) (ASSUME `k <= 3`))] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; REAL_SUB_RNEG] THEN
  MATCH_MP_TAC(TAUT `(b <=> c) ==> (a /\ b <=> a /\ c)`) THEN
  REAL_ARITH_TAC);;

let MOI_TB3_CUBE_COL = prove
 (`!(g:real^3) k u a y.
     1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k)
     ==> (y IN moi_tb3_cube (g - a % u) <=>
          (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&2)) /\
          abs((g - y) dot u - a) <= inv(&2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `u:real^3`] MOI_TB3_U_COORD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `1 <= k /\ k <= 3` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_TB3_IN_CUBE] THEN
  REWRITE_TAC[MATCH_MP MOI_TB3_FORALL_K (CONJ (ASSUME `1 <= k`) (ASSUME `k <= 3`))] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; REAL_SUB_RNEG] THEN
  MATCH_MP_TAC(TAUT `(b <=> c) ==> (a /\ b <=> a /\ c)`) THEN
  REAL_ARITH_TAC);;

let MOI_TB3_COLUMN = prove
 (`!(g:real^3) k u.
     moi_tb3_lat g /\ 1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k)
     ==> moi_tb3_neck g (g - &3 % u) SUBSET
           moi_tb3_neck g (g - u) UNION moi_tb3_bead (g - u) UNION
           moi_tb3_neck (g - u) (g - &2 % u) UNION moi_tb3_bead (g - &2 % u) UNION
           moi_tb3_neck (g - &2 % u) (g - &3 % u) /\
         moi_tb3_bead g INTER moi_tb3_neck g (g - &3 % u) =
           moi_tb3_bead g INTER moi_tb3_neck g (g - u) /\
         DISJOINT (moi_tb3_bead g INTER moi_tb3_neck g (g - u))
                  (interior (moi_tb3_neck g (g - &3 % u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k:real^3)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3.
      (y IN moi_tb3_neck g (g - &3 % u) <=>
       (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&8)) /\
       &0 + inv(&4) <= (g - y) dot u /\ (g - y) dot u <= &3 - inv(&4)) /\
      (y IN moi_tb3_neck g (g - u) <=>
       (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&8)) /\
       &0 + inv(&4) <= (g - y) dot u /\ (g - y) dot u <= &1 - inv(&4)) /\
      (y IN moi_tb3_neck (g - u) (g - &2 % u) <=>
       (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&8)) /\
       &1 + inv(&4) <= (g - y) dot u /\ (g - y) dot u <= &2 - inv(&4)) /\
      (y IN moi_tb3_neck (g - &2 % u) (g - &3 % u) <=>
       (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&8)) /\
       &2 + inv(&4) <= (g - y) dot u /\ (g - y) dot u <= &3 - inv(&4)) /\
      (y IN moi_tb3_bead g <=>
       (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&4)) /\
       abs((g - y) dot u - &0) <= inv(&4)) /\
      (y IN moi_tb3_bead (g - u) <=>
       (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&4)) /\
       abs((g - y) dot u - &1) <= inv(&4)) /\
      (y IN moi_tb3_bead (g - &2 % u) <=>
       (!i. 1 <= i /\ i <= 3 /\ ~(i = k) ==> abs(y$i - g$i) <= inv(&4)) /\
       abs((g - y) dot u - &2) <= inv(&4))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN
    MP_TAC(SPECL [`g:real^3`; `k:num`; `u:real^3`; `&0`; `&3`; `y:real^3`]
      MOI_TB3_NECK_COL) THEN
    MP_TAC(SPECL [`g:real^3`; `k:num`; `u:real^3`; `&0`; `&1`; `y:real^3`]
      MOI_TB3_NECK_COL) THEN
    MP_TAC(SPECL [`g:real^3`; `k:num`; `u:real^3`; `&1`; `&2`; `y:real^3`]
      MOI_TB3_NECK_COL) THEN
    MP_TAC(SPECL [`g:real^3`; `k:num`; `u:real^3`; `&2`; `&3`; `y:real^3`]
      MOI_TB3_NECK_COL) THEN
    MP_TAC(SPECL [`g:real^3`; `k:num`; `u:real^3`; `&0`; `y:real^3`] MOI_TB3_BEAD_COL) THEN
    MP_TAC(SPECL [`g:real^3`; `k:num`; `u:real^3`; `&1`; `y:real^3`] MOI_TB3_BEAD_COL) THEN
    MP_TAC(SPECL [`g:real^3`; `k:num`; `u:real^3`; `&2`; `y:real^3`] MOI_TB3_BEAD_COL) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO; VECTOR_MUL_LID] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th]));
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `p8 <=> !i. 1 <= i /\ i <= 3 /\ ~(i = k)
                           ==> abs((y:real^3)$i - (g:real^3)$i) <= inv(&8)` THEN
    ABBREV_TAC `p4 <=> !i. 1 <= i /\ i <= 3 /\ ~(i = k)
                           ==> abs((y:real^3)$i - (g:real^3)$i) <= inv(&4)` THEN
    SUBGOAL_THEN `p8 ==> p4` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p8"; "p4"] THEN
      MESON_TAC[REAL_ARITH `x <= inv(&8) ==> x <= inv(&4)`];
      ALL_TAC] THEN
    ASM_CASES_TAC `p8:bool` THEN ASM_CASES_TAC `p4:bool` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[EXTENSION; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `p8 <=> !i. 1 <= i /\ i <= 3 /\ ~(i = k)
                           ==> abs((y:real^3)$i - (g:real^3)$i) <= inv(&8)` THEN
    ABBREV_TAC `p4 <=> !i. 1 <= i /\ i <= 3 /\ ~(i = k)
                           ==> abs((y:real^3)$i - (g:real^3)$i) <= inv(&4)` THEN
    ASM_CASES_TAC `p8:bool` THEN ASM_CASES_TAC `p4:bool` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_INTERIOR] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `norm(u:real^3) = &1 /\ (u:real^3) dot u = &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k:real^3)` THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC[NORM_NEG; NORM_BASIS; DIMINDEX_3; DOT_RNEG; DOT_LNEG; DOT_BASIS_BASIS] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(y + (e / &2) % u:real^3) IN moi_tb3_neck g (g - &3 % u)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,e) SUBSET moi_tb3_neck g (g - &3 % u)` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_BALL; NORM_ARITH `dist(y:real^3,y + x) = norm x`; NORM_MUL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 + inv(&4) <= (g - (y + (e / &2) % u:real^3)) dot u /\
                  abs((g - y:real^3) dot u - &0) <= inv(&4)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_LSUB; DOT_LADD; DOT_LMUL; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_TB3_BEAD_SUBSET_CHAIN = prove
 (`!l (g:real^3). MEM g l ==> moi_tb3_bead g SUBSET moi_tb3_chain l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN X_GEN_TAC `g:real^3` THEN
  ONCE_REWRITE_TAC[MOI_TB3_CHAIN_CONS] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    SUBGOAL_THEN `~(t:(real^3)list = [])` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:real^3`) THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_TB3_COL_STEPS = prove
 (`!(g:real^3) k u.
     moi_tb3_lat g /\ 1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k)
     ==> moi_tb3_step g (g - u) /\ moi_tb3_step (g - u) (g - &2 % u) /\
         moi_tb3_step (g - &2 % u) (g - &3 % u) /\
         moi_tb3_lat (g - u) /\ moi_tb3_lat (g - &2 % u) /\ moi_tb3_lat (g - &3 % u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `g - &2 % u:real^3 = (g - u) - u /\ g - &3 % u = ((g - u) - u) - u`
    (fun th -> REWRITE_TAC[th]) THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!h:real^3. moi_tb3_lat h ==> moi_tb3_step h (h - u) /\ moi_tb3_lat (h - u)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`h:real^3`; `k:num`; `u:real^3`] MOI_TB3_STEP_U) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[MOI_TB3_STEP_COORDS];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_TB3_CHAIN_COLUMN = prove
 (`!l (g:real^3) k u.
     moi_tb3_walk l /\ MEM g l /\ moi_tb3_lat g /\ 1 <= k /\ k <= 3 /\
     (u = basis k \/ u = --basis k) /\
     ~(MEM (g - u) l) /\ ~(MEM (g - &2 % u) l) /\ ~(MEM (g - &3 % u) l)
     ==> moi_tb3_chain l INTER moi_tb3_neck g (g - &3 % u) =
         moi_tb3_bead g INTER moi_tb3_neck g (g - u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `moi_tb3_lat (g:real^3) /\ 1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k:real^3)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_TB3_COLUMN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_TB3_COL_STEPS) THEN
  SUBGOAL_THEN `moi_tb3_walk (l:(real^3)list) /\ MEM (g:real^3) l /\
                ~(MEM (g - u) l) /\ ~(MEM (g - &2 % u) l) /\ ~(MEM (g - &3 % u) l)`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^3)list`; `g:real^3`; `g - u:real^3`] MOI_TB3_CHAIN_NECK1) THEN
  MP_TAC(ISPECL [`l:(real^3)list`; `g - u:real^3`] MOI_TB3_CHAIN_AVOID_BEAD) THEN
  MP_TAC(ISPECL [`l:(real^3)list`; `g - &2 % u:real^3`] MOI_TB3_CHAIN_AVOID_BEAD) THEN
  MP_TAC(ISPECL [`l:(real^3)list`; `g - u:real^3`; `g - &2 % u:real^3`]
    MOI_TB3_CHAIN_AVOID_EDGE) THEN
  MP_TAC(ISPECL [`l:(real^3)list`; `g - &2 % u:real^3`; `g - &3 % u:real^3`]
    MOI_TB3_CHAIN_AVOID_EDGE) THEN
  MP_TAC(ISPECL [`l:(real^3)list`; `g:real^3`] MOI_TB3_BEAD_SUBSET_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`moi_tb3_neck g (g - &3 % u) SUBSET
       moi_tb3_neck g (g - u) UNION moi_tb3_bead (g - u) UNION
       moi_tb3_neck (g - u) (g - &2 % u) UNION moi_tb3_bead (g - &2 % u) UNION
       moi_tb3_neck (g - &2 % u) (g - &3 % u:real^3)`;
    `moi_tb3_bead g INTER moi_tb3_neck g (g - &3 % u) =
     moi_tb3_bead g INTER moi_tb3_neck g (g - u:real^3)`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* An end of the tube at a facet plane nu dot y = c.  A dominant coordinate k *)
(* of nu and a lattice point g at height between 3/2 and 5/2 (in units of the *)
(* dominant coefficient) on the side nu dot y > c, within 5 of the facet      *)
(* point a in every coordinate.                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_DOT_BOUND = prove
 (`!(nu:real^3) (z:real^3) m b.
     (!i. 1 <= i /\ i <= 3 ==> abs(nu$i) <= m /\ abs(z$i) <= b)
     ==> abs(nu dot z) <= &3 * m * b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DOT_3; FORALL_3] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs((nu:real^3)$1 * (z:real^3)$1) <= m * b /\
                abs(nu$2 * z$2) <= m * b /\ abs(nu$3 * z$3) <= m * b` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    REAL_ARITH_TAC]);;

let MOI_TB3_END = prove
 (`!(nu:real^3) c (a:real^3).
     ~(nu = vec 0) /\ nu dot a = c
     ==> ?g k u. moi_tb3_lat g /\ 1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k) /\
                 (!i. 1 <= i /\ i <= 3 ==> abs(nu$i) <= nu dot u) /\
                 &3 / &2 * (nu dot u) < nu dot g - c /\
                 nu dot g - c <= &5 / &2 * (nu dot u) /\
                 (!i. 1 <= i /\ i <= 3 ==> abs(g$i - a$i) <= &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= 3 /\
                    !i. 1 <= i /\ i <= 3 ==> abs((nu:real^3)$i) <= abs(nu$k)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_3] THEN
    ASM_CASES_TAC `abs((nu:real^3)$1) <= abs(nu$3) /\ abs(nu$2) <= abs(nu$3)` THENL
     [EXISTS_TAC `3` THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `abs((nu:real^3)$1) <= abs(nu$2)` THENL
     [EXISTS_TAC `2` THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((nu:real^3)$k = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(nu:real^3 = vec 0)` THEN
    REWRITE_TAC[CART_EQ; VEC_COMPONENT; DIMINDEX_3] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^3. (u = basis k \/ u = --basis k) /\ (nu:real^3) dot u = abs(nu$k)`
  (X_CHOOSE_THEN `u:real^3` (CONJUNCTS_THEN ASSUME_TAC)) THENL
   [ASM_CASES_TAC `&0 < (nu:real^3)$k` THENL
     [EXISTS_TAC `basis k:real^3`; EXISTS_TAC `--basis k:real^3`] THEN
    ASM_SIMP_TAC[DOT_RNEG; DOT_BASIS; DIMINDEX_3] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!i. 1 <= i /\ i <= 3 ==> abs((nu:real^3)$i) <= nu dot u) /\
                &0 < (nu:real^3) dot u` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(nu:real^3) dot u = abs(nu$k)` THEN DISCH_THEN(K ALL_TAC) THEN
  ABBREV_TAC `m = (nu:real^3) dot u` THEN
  MP_TAC(ISPEC `a:real^3` MOI_TB3_ROUND) THEN
  ABBREV_TAC `r = moi_tb3_round (a:real^3)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs((nu:real^3) dot (r - a)) <= &3 * m * inv(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_TB3_DOT_BOUND THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `d0 = (nu:real^3) dot r - c` THEN
  SUBGOAL_THEN `(nu:real^3) dot (r - a) = d0` ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN ASM_REWRITE_TAC[DOT_RSUB]; ALL_TAC] THEN
  SUBGOAL_THEN `?s. integer s /\ abs s <= &4 /\ &3 / &2 * m < d0 + s * m /\
                    d0 + s * m <= &5 / &2 * m`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `&1 / &2 * m < d0` THENL
     [EXISTS_TAC `&1` THEN REWRITE_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `-- &1 / &2 * m < d0` THENL
     [EXISTS_TAC `&2` THEN REWRITE_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `-- &3 / &2 * m < d0` THENL
     [EXISTS_TAC `&3` THEN REWRITE_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `&4` THEN REWRITE_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r + s % u:real^3`; `k:num`; `u:real^3`] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL; ASSUME `(nu:real^3) dot u = m`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_TB3_LAT_U THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`k:num`; `u:real^3`] MOI_TB3_U_COORD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `abs((u:real^3)$i) <= &1` ASSUME_TAC THENL
     [ASM_CASES_TAC `i:num = k` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
          is_eq(lhand(concl th)) && type_of(lhand(lhand(concl th))) = `:real`)) THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(s * (u:real^3)$i) <= &4` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBST1_TAC(REAL_ARITH `&4 = &4 * &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((a:real^3)$i - (r:real^3)$i) <= inv(&2)` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `inv(&2)`)) (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let MOI_TB3_COORD_NORM = prove
 (`!(z:real^3) r. (!i. 1 <= i /\ i <= 3 ==> abs(z$i) <= r) ==> norm z <= &3 * r`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `z:real^3` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN REWRITE_TAC[FORALL_3] THEN
  REAL_ARITH_TAC);;

let MOI_TB3_BEAD_SUBSET_CUBE = prove
 (`!g:real^3. moi_tb3_bead g SUBSET moi_tb3_cube g`,
  REWRITE_TAC[SUBSET; MOI_TB3_IN_BEAD; MOI_TB3_IN_CUBE] THEN
  MESON_TAC[REAL_ARITH `x <= inv(&4) ==> x <= inv(&2)`]);;

let MOI_TB3_END_FACTS = prove
 (`!(nu:real^3) c (a:real^3) g k u.
     ~(nu = vec 0) /\ nu dot a = c /\ moi_tb3_lat g /\ 1 <= k /\ k <= 3 /\
     (u = basis k \/ u = --basis k) /\
     (!i. 1 <= i /\ i <= 3 ==> abs(nu$i) <= nu dot u) /\
     &3 / &2 * (nu dot u) < nu dot g - c /\ nu dot g - c <= &5 / &2 * (nu dot u) /\
     (!i. 1 <= i /\ i <= 3 ==> abs(g$i - a$i) <= &5)
     ==> (!t y. y IN moi_tb3_cube (g + t % u) ==> c + t * (nu dot u) < nu dot y) /\
         (!t. moi_tb3_cube (g + t % u) SUBSET ball(a,&17 + &3 * abs t)) /\
         ~(interior (moi_tb3_neck g (g - &3 % u)) INTER {y | nu dot y = c} = {}) /\
         moi_tb3_neck g (g - &3 % u) SUBSET ball(a,&30) /\
         (!j. &1 <= j /\ j <= &3
              ==> nu dot (g - j % u) <= c + &3 / &2 * norm nu /\
                  dist(g - j % u,a) < &30) /\
         norm nu <= &3 * (nu dot u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(u:real^3) = &1 /\ (u:real^3) dot u = &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k:real^3)` THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_NEG; NORM_BASIS; DIMINDEX_3; DOT_RNEG; DOT_LNEG; DOT_BASIS_BASIS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `u:real^3`] MOI_TB3_U_COORD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3 ==> abs((u:real^3)$i) <= &1` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_CASES_TAC `i:num = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
        is_eq(lhand(concl th)) && type_of(lhand(lhand(concl th))) = `:real`)) THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!i. 1 <= i /\ i <= 3 ==> abs((nu:real^3)$i) <= nu dot u) /\
                &3 / &2 * (nu dot u) < nu dot g - c /\ nu dot g - c <= &5 / &2 * (nu dot u) /\
                (!i. 1 <= i /\ i <= 3 ==> abs((g:real^3)$i - (a:real^3)$i) <= &5)`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `m = (nu:real^3) dot u` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(nu:real^3) <= &3 * m` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_TB3_COORD_NORM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `m <= norm(nu:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`nu:real^3`; `u:real^3`] NORM_CAUCHY_SCHWARZ) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[MOI_TB3_IN_CUBE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`nu:real^3`; `y - (g + t % u):real^3`; `m:real`; `inv(&2)`]
      MOI_TB3_DOT_BOUND) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[VECTOR_SUB_COMPONENT]; ALL_TAC] THEN
    REWRITE_TAC[DOT_RSUB; DOT_RADD; DOT_RMUL; ASSUME `(nu:real^3) dot u = m`] THEN
    ASM_REAL_ARITH_TAC;
    GEN_TAC THEN
    SUBGOAL_THEN `&17 + &3 * abs t = &3 * (&5 + abs t) + &2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_TB3_CUBE_NEAR THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `abs(t * (u:real^3)$i) <= abs t` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((g:real^3)$i - (a:real^3)$i) <= &5` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    EXISTS_TAC `g - ((nu dot g - c) / m) % u:real^3` THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[DOT_RSUB; DOT_RMUL; ASSUME `(nu:real^3) dot u = m`] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC] THEN
    REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `inv(&8)` THEN
    CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g:real^3`; `k:num`; `u:real^3`; `&0`; `&3`; `y:real^3`]
      MOI_TB3_NECK_COL) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    ABBREV_TAC `p = g - ((nu dot g - c) / m) % u:real^3` THEN
    SUBGOAL_THEN `&3 / &2 < ((nu:real^3) dot g - c) / m /\ (nu dot g - c) / m <= &5 / &2`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(g - y:real^3) dot u = (nu dot g - c) / m + (p - y) dot u` SUBST1_TAC THENL
     [EXPAND_TAC "p" THEN
      REWRITE_TAC[DOT_LSUB; DOT_LMUL; ASSUME `(u:real^3) dot u = &1`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((p - y:real^3) dot u) < inv(&8)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p - y:real^3`; `u:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
      ASM_REWRITE_TAC[REAL_MUL_RID] THEN
      UNDISCH_TAC `dist(p:real^3,y) < inv(&8)` THEN REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p - y:real^3`; `i:num`] COMPONENT_LE_NORM) THEN
    EXPAND_TAC "p" THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
    UNDISCH_TAC `dist(p:real^3,y) < inv(&8)` THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN
    MP_TAC(SPECL [`g:real^3`; `k:num`; `u:real^3`; `&0`; `&3`; `y:real^3`]
      MOI_TB3_NECK_COL) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &3 * &8 ==> x < &30`) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC MOI_TB3_COORD_NORM THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    SUBGOAL_THEN `abs((y:real^3)$i - (g:real^3)$i) <= &3` MP_TAC THENL
     [ASM_CASES_TAC `i:num = k` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MP_TAC(SPECL [`k:num`; `u:real^3`] MOI_TB3_U_COORD) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `g - y:real^3` o CONJUNCT2 o CONJUNCT2) THEN
        FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
          is_eq(lhand(concl th)) && type_of(lhand(lhand(concl th))) = `:real`)) THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `abs((y:real^3)$i - (g:real^3)$i) <= &1 / &8` MP_TAC THENL
         [ASM_MESON_TAC[]; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((g:real^3)$i - (a:real^3)$i) <= &5` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `j:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[DOT_RSUB; DOT_RMUL; ASSUME `(nu:real^3) dot u = m`] THEN
      SUBGOAL_THEN `m <= j * m` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `x <= &3 * &8 ==> x < &30`) THEN
      REWRITE_TAC[dist] THEN MATCH_MP_TAC MOI_TB3_COORD_NORM THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `abs(j * (u:real^3)$i) <= &3` MP_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL] THEN SUBST1_TAC(REAL_ARITH `&3 = &3 * &1`) THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `abs((g:real^3)$i - (a:real^3)$i) <= &5` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The walk.  Straight column walks at both ends, joined by the lazy walk of *)
(* a path with margin 7; then a simple walk between the ends.                *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_LWALK_JOIN = prove
 (`!l1 l2:(real^3)list.
     moi_tb3_lwalk l1 /\ moi_tb3_lwalk l2 /\ LAST l1 = HD l2
     ==> moi_tb3_lwalk (APPEND l1 (TL l2)) /\ HD (APPEND l1 (TL l2)) = HD l1 /\
         LAST (APPEND l1 (TL l2)) = LAST l2 /\
         (!P. ALL P l1 /\ ALL P l2 ==> ALL P (APPEND l1 (TL l2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(l1:(real^3)list = []) /\ ~(l2:(real^3)list = [])` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_tb3_lwalk]; ALL_TAC] THEN
  MP_TAC(ISPEC `l2:(real^3)list` list_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3` (X_CHOOSE_THEN `t:(real^3)list` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN REWRITE_TAC[HD; TL] THEN
  SUBGOAL_THEN `l1 = APPEND (BUTLAST l1) [h:real^3]` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    ASM_SIMP_TAC[APPEND_BUTLAST_LAST];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_tb3_lwalk (APPEND (BUTLAST l1) [h:real^3])` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    ASM_SIMP_TAC[APPEND_BUTLAST_LAST];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  ASM_REWRITE_TAC[MOI_TB3_LWALK_SPLIT; HD_APPEND; LAST_APPEND; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[ALL_APPEND; ALL] THEN MESON_TAC[]);;

let MOI_TB3_COL_LWALK = prove
 (`!(g:real^3) k u.
     moi_tb3_lat g /\ 1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k)
     ==> !N. ?l. moi_tb3_lwalk l /\ HD l = g /\ LAST l = g + &N % u /\
                 ALL (\q. ?j. j <= N /\ q = g + &j % u) l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `[g:real^3]` THEN
    REWRITE_TAC[MOI_TB3_LWALK_CONS_EQ; HD; LAST; ALL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[LE_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l:(real^3)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `APPEND l [g + &(SUC N) % u:real^3]` THEN
  SUBGOAL_THEN `~(l:(real^3)list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_tb3_lwalk]; ALL_TAC] THEN
  ASM_REWRITE_TAC[HD_APPEND; LAST_APPEND; NOT_CONS_NIL; LAST; ALL_APPEND; ALL] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_TB3_LWALK_SNOC THEN ASM_REWRITE_TAC[moi_tb3_lstep] THEN
    SUBGOAL_THEN `moi_tb3_lat (g + &N % u:real^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_TB3_LAT_U THEN EXISTS_TAC `k:num` THEN
      ASM_REWRITE_TAC[INTEGER_CLOSED];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    SUBGOAL_THEN `g + &(SUC N) % u:real^3 = (g + &N % u) + u` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`g + &N % u:real^3`; `k:num`; `u:real^3`] MOI_TB3_STEP_U) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC ALL_IMP THEN
    EXISTS_TAC `\q:real^3. ?j. j <= N /\ q = g + &j % u` THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[ARITH_RULE `j <= N ==> j <= SUC N`];
    EXISTS_TAC `SUC N` THEN REWRITE_TAC[LE_REFL]]);;

let MOI_TB3_ROUND_LAT = prove
 (`!g:real^3. moi_tb3_lat g ==> moi_tb3_round g = g`,
  REWRITE_TAC[moi_tb3_lat; moi_tb3_round] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_3] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

let MOI_TB3_WALK_EXISTS = prove
 (`!v (g0:real^3) k u g1 k' u' (P:real^1->real^3) N.
     moi_tb3_lat g0 /\ 1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k) /\
     moi_tb3_lat g1 /\ 1 <= k' /\ k' <= 3 /\ (u' = basis k' \/ u' = --basis k') /\
     (!j. j <= N ==> moi_tb3_cube (g0 + &j % u) SUBSET v) /\
     (!j. j <= N ==> moi_tb3_cube (g1 + &j % u') SUBSET v) /\
     path P /\ pathstart P = g0 + &N % u /\ pathfinish P = g1 + &N % u' /\
     (!t. t IN interval[vec 0,vec 1] ==> ball(P t,&7) SUBSET v)
     ==> ?l. moi_tb3_walk l /\ HD l = g0 /\ LAST l = g1 /\
             PAIRWISE (\x y. ~(x = y)) l /\ ALL (\q. moi_tb3_cube q SUBSET v) l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_tb3_lat (g0:real^3) /\ 1 <= k /\ k <= 3 /\
                (u = basis k \/ u = --basis k:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_tb3_lat (g1:real^3) /\ 1 <= k' /\ k' <= 3 /\
                (u' = basis k' \/ u' = --basis k':real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(!j. j <= N ==> moi_tb3_cube (g0 + &j % u:real^3) SUBSET v) /\
                (!j. j <= N ==> moi_tb3_cube (g1 + &j % u':real^3) SUBSET v)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_tb3_lat (g0 + &N % u:real^3) /\ moi_tb3_lat (g1 + &N % u':real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_TB3_LAT_U THENL
     [EXISTS_TAC `k:num`; EXISTS_TAC `k':num`] THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_tb3_lat (g1 + &N % u':real^3) /\ 1 <= k' /\ k' <= 3 /\
                (--u' = basis k' \/ --u' = --basis k':real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u' = basis k' \/ u' = --basis k':real^3` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_NEG_NEG];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3`; `k:num`; `u:real^3`] MOI_TB3_COL_LWALK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:(real^3)list` STRIP_ASSUME_TAC o SPEC `N:num`) THEN
  MP_TAC(SPECL [`g1 + &N % u':real^3`; `k':num`; `--u':real^3`] MOI_TB3_COL_LWALK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:(real^3)list` STRIP_ASSUME_TAC o SPEC `N:num`) THEN
  MP_TAC(ISPECL [`v:real^3->bool`; `P:real^1->real^3`] MOI_TB3_PATH_WALK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_TB3_ROUND_LAT] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:(real^3)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`l2:(real^3)list`; `l3:(real^3)list`] MOI_TB3_LWALK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l1:(real^3)list`; `APPEND l2 (TL l3):(real^3)list`] MOI_TB3_LWALK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{q:real^3 | moi_tb3_cube q SUBSET v}`; `g0:real^3`; `g1:real^3`]
    MOI_TB3_SIMPLE_LWALK) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `APPEND l1 (TL (APPEND l2 (TL l3))):(real^3)list` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC `\q:real^3. ?j. j <= N /\ q = g0 + &j % u` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC `\q:real^3. moi_tb3_cube q SUBSET v` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[];
      MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC `\q:real^3. ?j. j <= N /\ q = (g1 + &N % u') + &j % --u'` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `q:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `q = g1 + &(N - j) % u':real^3` SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN VECTOR_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `u':real^3`)) (concl th) &&
          can (find_term ((=) `moi_tb3_cube`)) (concl th))) THEN
        ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^3)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l:(real^3)list` THEN ASM_SIMP_TAC[MOI_TB3_SIMPLE_IMP_WALK] THEN
  UNDISCH_TAC `ALL (\x. x IN {q:real^3 | moi_tb3_cube q SUBSET v}) l` THEN
  REWRITE_TAC[IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas for the assembly at unit scale.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_HALF_LOCAL = prove
 (`!s (a:real^3) R (nu:real^3) c.
     closed s /\ ~(nu = vec 0) /\ (!y. y IN ball(a,R) ==> (y IN s <=> c <= nu dot y))
     ==> (!y. y IN ball(a,R) ==> (y IN interior s <=> c < nu dot y)) /\
         (!y. y IN ball(a,R) ==> (y IN frontier s <=> nu dot y = c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN ball(a,R) ==> (y IN interior s <=> c < (nu:real^3) dot y)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `interior s INTER ball(a:real^3,R) = {y | nu dot y > c} INTER ball(a,R)`
    MP_TAC THENL
     [SUBGOAL_THEN `s INTER ball(a:real^3,R) = {y | nu dot y >= c} INTER ball(a,R)` MP_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_ge] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `interior:(real^3->bool)->real^3->bool`) THEN
      REWRITE_TAC[INTERIOR_INTER] THEN
      ASM_SIMP_TAC[INTERIOR_HALFSPACE_GE; INTERIOR_OPEN; OPEN_BALL];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; IN_DIFF] THEN REAL_ARITH_TAC);;

let MOI_TB3_SUBSET_FRONTIER = prove
 (`!t p c:real^3->bool.
     t SUBSET p /\ p SUBSET c /\ DISJOINT t (interior c) ==> t SUBSET frontier p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `p:real^3->bool` CLOSURE_SUBSET) THEN
  MP_TAC(ISPECL [`p:real^3->bool`; `c:real^3->bool`] SUBSET_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;


let MOI_TB3_MEM_LAST = prove
 (`!l:(real^3)list. ~(l = []) ==> MEM (LAST l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; LAST; MEM] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let MOI_TB3_NECK_IN_CUBES = prove
 (`!q q':real^3.
     moi_tb3_step q q' ==> moi_tb3_neck q q' SUBSET moi_tb3_cube q UNION moi_tb3_cube q'`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_TB3_STEP_COORDS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[SUBSET; IN_UNION; MOI_TB3_IN_NECK; MOI_TB3_IN_CUBE] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3 /\ ~(i = k)
                    ==> abs((y:real^3)$i - (q:real^3)$i) <= inv(&8)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `y:real^3`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `min ((q:real^3)$k) ((q':real^3)$k) + inv(&4) <= (y:real^3)$k /\
                y$k <= max (q$k) (q'$k) - inv(&4)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `min:real->real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `abs((y:real^3)$k - (q:real^3)$k) <= inv(&2)` THENL
   [DISJ1_TAC; DISJ2_TAC] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  (ASM_CASES_TAC `i:num = k` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= inv(&8) ==> x <= inv(&2)`) THEN ASM_SIMP_TAC[]);;

let MOI_TB3_CHAIN_SUBSET = prove
 (`!l (v:real^3->bool).
     moi_tb3_walk l /\ ALL (\q. moi_tb3_cube q SUBSET v) l ==> moi_tb3_chain l SUBSET v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[moi_tb3_walk; ALL] THEN
  X_GEN_TAC `v:real^3->bool` THEN STRIP_TAC THEN ONCE_REWRITE_TAC[MOI_TB3_CHAIN_CONS] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_tb3_cube h` THEN
    ASM_REWRITE_TAC[MOI_TB3_BEAD_SUBSET_CUBE];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET; UNION_SUBSET] THEN
  MP_TAC(ISPECL [`h:real^3`; `t:(real^3)list`] MOI_TB3_WALK_STEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_tb3_cube h UNION moi_tb3_cube (HD t)` THEN
    ASM_SIMP_TAC[MOI_TB3_NECK_IN_CUBES; UNION_SUBSET] THEN
    UNDISCH_TAC `ALL (\q. moi_tb3_cube q SUBSET (v:real^3->bool)) t` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MOI_TB3_HD_MEM];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_TB3_CHAIN_COMPACT = prove
 (`!l:(real^3)list. compact (moi_tb3_chain l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[moi_tb3_chain; COMPACT_EMPTY] THEN
  ONCE_REWRITE_TAC[MOI_TB3_CHAIN_CONS] THEN
  MATCH_MP_TAC COMPACT_UNION THEN REWRITE_TAC[moi_tb3_bead; COMPACT_INTERVAL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[COMPACT_EMPTY] THEN
  MATCH_MP_TAC COMPACT_UNION THEN ASM_REWRITE_TAC[moi_tb3_neck; COMPACT_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* The assembly at unit scale.  Glue the outer half of the end column at x  *)
(* to x, the chain to that, the inner half of the end column at w to the    *)
(* result, and bite the outer half of that column out of w.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_ASSEMBLE = prove
 (`!x w k (a:real^3) nu c (a':real^3) nu' c' R l g0 k0 u0 g1 k1 u1.
     PL_SCHOENFLIES_3_STATEMENT /\
     pl_ball 3 x /\ pl_ball 3 w /\ x SUBSET interior w /\ closed k /\
     ~(nu = vec 0) /\ (!y. y IN ball(a,R) ==> (y IN x <=> nu dot y <= c)) /\
     ball(a,R) SUBSET interior w /\ DISJOINT (ball(a,R)) k /\
     ~(nu' = vec 0) /\ (!y. y IN ball(a',R) ==> (y IN w <=> c' <= nu' dot y)) /\
     DISJOINT (ball(a',R)) x /\ DISJOINT (ball(a',R)) k /\
     moi_tb3_walk l /\ PAIRWISE (\x y. ~(x = y)) l /\ HD l = g0 /\ LAST l = g1 /\
     moi_tb3_chain l SUBSET interior w DIFF x DIFF k /\
     moi_tb3_lat g0 /\ 1 <= k0 /\ k0 <= 3 /\ (u0 = basis k0 \/ u0 = --basis k0) /\
     ~(MEM (g0 - u0) l) /\ ~(MEM (g0 - &2 % u0) l) /\ ~(MEM (g0 - &3 % u0) l) /\
     moi_tb3_neck g0 (g0 - &3 % u0) SUBSET ball(a,R) /\
     ~(interior (moi_tb3_neck g0 (g0 - &3 % u0)) INTER {y | nu dot y = c} = {}) /\
     moi_tb3_bead g0 SUBSET {y | c < nu dot y} /\
     moi_tb3_lat g1 /\ 1 <= k1 /\ k1 <= 3 /\ (u1 = basis k1 \/ u1 = --basis k1) /\
     ~(MEM (g1 - u1) l) /\ ~(MEM (g1 - &2 % u1) l) /\ ~(MEM (g1 - &3 % u1) l) /\
     moi_tb3_neck g1 (g1 - &3 % u1) SUBSET ball(a',R) /\
     ~(interior (moi_tb3_neck g1 (g1 - &3 % u1)) INTER {y | nu' dot y = c'} = {}) /\
     moi_tb3_bead g1 SUBSET {y | c' < nu' dot y} /\
     DISJOINT (moi_tb3_neck g0 (g0 - &3 % u0)) (moi_tb3_neck g1 (g1 - &3 % u1))
     ==> ?n. compact n /\ DISJOINT n k /\ pl_ball 3 (w DIFF interior (x UNION n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `~(l:(real^3)list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_tb3_walk]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (g0:real^3) l /\ MEM (g1:real^3) l` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_TB3_HD_MEM; MOI_TB3_MEM_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (x:real^3->bool) /\ compact (w:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4D_PL_BALL_COMPACT]; ALL_TAC] THEN
  (* columns, steps, chain meets *)
  MP_TAC(SPECL [`g0:real^3`; `k0:num`; `u0:real^3`] MOI_TB3_COLUMN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(SPECL [`g1:real^3`; `k1:num`; `u1:real^3`] MOI_TB3_COLUMN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(SPECL [`g0:real^3`; `k0:num`; `u0:real^3`] MOI_TB3_COL_STEPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(SPECL [`g1:real^3`; `k1:num`; `u1:real^3`] MOI_TB3_COL_STEPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(SPECL [`l:(real^3)list`; `g0:real^3`; `k0:num`; `u0:real^3`]
    MOI_TB3_CHAIN_COLUMN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`l:(real^3)list`; `g1:real^3`; `k1:num`; `u1:real^3`]
    MOI_TB3_CHAIN_COLUMN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3`; `g0 - u0:real^3`] MOI_TB3_FACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g1:real^3`; `g1 - u1:real^3`] MOI_TB3_FACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope (moi_tb3_neck g0 (g0 - &3 % u0:real^3)) /\
                polytope (moi_tb3_neck g1 (g1 - &3 % u1:real^3)) /\
                compact (moi_tb3_neck g0 (g0 - &3 % u0:real^3)) /\
                compact (moi_tb3_neck g1 (g1 - &3 % u1:real^3))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_tb3_neck; POLYTOPE_INTERVAL; COMPACT_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_tb3_neck g0 (g0 - &3 % u0:real^3)`; `nu:real^3`; `c:real`]
    MOI_TB3_HALF_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_tb3_neck g0 (g0 - &3 % u0:real^3)`; `nu:real^3`; `c:real`]
    MOI_TB3_PLANE_SECTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_tb3_neck g1 (g1 - &3 % u1:real^3)`; `nu':real^3`; `c':real`]
    MOI_TB3_HALF_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_tb3_neck g1 (g1 - &3 % u1:real^3)`; `nu':real^3`; `c':real`]
    MOI_TB3_PLANE_SECTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `CX = moi_tb3_neck g0 (g0 - &3 % u0:real^3)` THEN
  ABBREV_TAC `CW = moi_tb3_neck g1 (g1 - &3 % u1:real^3)` THEN
  ABBREV_TAC `TX = moi_tb3_bead g0 INTER moi_tb3_neck g0 (g0 - u0:real^3)` THEN
  ABBREV_TAC `TW = moi_tb3_bead g1 INTER moi_tb3_neck g1 (g1 - u1:real^3)` THEN
  (* the faces *)
  SUBGOAL_THEN `TX SUBSET moi_tb3_bead g0 /\ TX SUBSET CX /\
                TW SUBSET moi_tb3_bead g1 /\ TW SUBSET CW` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`moi_tb3_bead g0 INTER CX = TX`; `moi_tb3_bead g1 INTER CW = TW`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `TX SUBSET {y:real^3 | nu dot y >= c} /\ TW SUBSET {y:real^3 | nu' dot y >= c'}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`TX SUBSET moi_tb3_bead g0`; `moi_tb3_bead g0 SUBSET {y:real^3 | c < nu dot y}`;
      `TW SUBSET moi_tb3_bead g1`; `moi_tb3_bead g1 SUBSET {y:real^3 | c' < nu' dot y}`] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* glue the outer half of the x column to x *)
  SUBGOAL_THEN `x INTER (CX INTER {y:real^3 | nu dot y >= c}) = CX INTER {y | nu dot y = c}`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`CX SUBSET ball(a:real^3,R)`;
      `!y. y IN ball(a:real^3,R) ==> (y IN x <=> nu dot y <= c)`] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; SUBSET; real_ge] THEN
    MESON_TAC[REAL_LE_ANTISYM; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `CX INTER {y:real^3 | nu dot y >= c}`;
                 `CX INTER {y:real^3 | nu dot y = c}`;
                 `relative_frontier(CX INTER {y:real^3 | nu dot y = c})`] MOI_TB3_GLUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  (* glue the chain *)
  SUBGOAL_THEN `(x UNION CX INTER {y:real^3 | nu dot y >= c}) INTER moi_tb3_chain l = TX`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`moi_tb3_chain l INTER CX = TX`; `moi_tb3_chain l SUBSET interior w DIFF x DIFF k`;
      `TX SUBSET {y:real^3 | nu dot y >= c}`; `TX SUBSET (CX:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`TL l:(real^3)list`; `g0:real^3`;
                 `x UNION CX INTER {y:real^3 | nu dot y >= c}`;
                 `TX:real^3->bool`; `relative_frontier TX:real^3->bool`] MOI_TB3_CHAIN_GLUE) THEN
  SUBGOAL_THEN `CONS (g0:real^3) (TL l) = l` SUBST1_TAC THENL
   [ASM_MESON_TAC[CONS_HD_TL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* glue the inner half of the w column *)
  SUBGOAL_THEN `((x UNION CX INTER {y:real^3 | nu dot y >= c}) UNION moi_tb3_chain l) INTER
                (CW INTER {y:real^3 | nu' dot y >= c'}) = TW` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`moi_tb3_chain l INTER CW = TW`; `DISJOINT (CX:real^3->bool) CW`;
      `CW SUBSET ball(a':real^3,R)`; `DISJOINT (ball(a':real^3,R)) x`;
      `TW SUBSET {y:real^3 | nu' dot y >= c'}`; `TW SUBSET (CW:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `TW SUBSET frontier (CW INTER {y:real^3 | nu' dot y >= c'})` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_TB3_SUBSET_FRONTIER THEN EXISTS_TAC `CW:real^3->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET; SUBSET_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(x UNION CX INTER {y:real^3 | nu dot y >= c}) UNION moi_tb3_chain l`;
                 `CW INTER {y:real^3 | nu' dot y >= c'}`; `TW:real^3->bool`;
                 `relative_frontier TW:real^3->bool`] MOI_TB3_GLUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `F0 = (x UNION CX INTER {y:real^3 | nu dot y >= c}) UNION moi_tb3_chain l` THEN
  ABBREV_TAC `Y = F0 UNION CW INTER {y:real^3 | nu' dot y >= c'}` THEN
  (* the bite *)
  MP_TAC(ISPECL [`w:real^3->bool`; `a':real^3`; `R:real`; `nu':real^3`; `c':real`]
    MOI_TB3_HALF_LOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; STRIP_TAC] THEN
  SUBGOAL_THEN `interior w INTER frontier w = {}:real^3->bool` ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `F0 SUBSET interior (w:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN
    MAP_EVERY UNDISCH_TAC
     [`x SUBSET interior (w:real^3->bool)`; `CX SUBSET ball(a:real^3,R)`;
      `ball(a:real^3,R) SUBSET interior w`; `moi_tb3_chain l SUBSET interior w DIFF x DIFF k`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (F0:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_HALFSPACE_GE];
      SIMP_TAC[COMPACT_IMP_CLOSED; MOI_TB3_CHAIN_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN CW ==> y IN ball(a',R)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `CW INTER {y:real^3 | nu' dot y >= c'} SUBSET w` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; real_ge] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y SUBSET (w:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN MP_TAC(ISPEC `w:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(CW INTER {y:real^3 | nu' dot y >= c'}) INTER frontier w =
                CW INTER {y | nu' dot y = c'}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_ge] THEN X_GEN_TAC `y:real^3` THEN
    ASM_CASES_TAC `(y:real^3) IN CW` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN ball(a',R)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Y INTER frontier w = CW INTER {y:real^3 | nu' dot y = c'}` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN
    MAP_EVERY UNDISCH_TAC
     [`F0 SUBSET interior (w:real^3->bool)`; `interior w INTER frontier w = {}:real^3->bool`;
      `(CW INTER {y:real^3 | nu' dot y >= c'}) INTER frontier w =
       CW INTER {y | nu' dot y = c'}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CW INTER {y:real^3 | nu' dot y = c'} SUBSET frontier Y` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_TB3_SUBSET_FRONTIER THEN EXISTS_TAC `w:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`interior w INTER frontier w = {}:real^3->bool`;
      `Y INTER frontier w = CW INTER {y:real^3 | nu' dot y = c'}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(CW INTER {y:real^3 | nu' dot y <= c'}) INTER w SUBSET
                CW INTER {y | nu' dot y = c'}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN ball(a',R)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `c' <= (nu':real^3) dot y` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Y UNION CW INTER {y:real^3 | nu' dot y <= c'} = F0 UNION CW` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM; real_ge] THEN
    MESON_TAC[REAL_LE_TOTAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `CW INTER {y:real^3 | nu' dot y = c'} DIFF
                relative_frontier (CW INTER {y | nu' dot y = c'}) SUBSET interior CW`
  ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    MP_TAC(ISPEC `CW INTER {y:real^3 | nu' dot y = c'}` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `relative_interior (CW INTER {y:real^3 | nu' dot y = c'}) =
                 interior CW INTER {y | nu' dot y = c'}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CW INTER {y:real^3 | nu' dot y = c'} DIFF
                relative_frontier (CW INTER {y | nu' dot y = c'}) SUBSET interior (F0 UNION CW)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior CW:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier (CW INTER {y:real^3 | nu' dot y = c'}) INTER
                interior (F0 UNION CW) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `closed (CW INTER {y:real^3 | nu' dot y = c'})` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_HYPERPLANE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN CW INTER {y | nu' dot y = c'} /\
                  ~(z IN relative_interior (CW INTER {y | nu' dot y = c'}))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN relative_frontier (CW INTER {y | nu' dot y = c'})` THEN
      ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((z:real^3) IN F0)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`F0 SUBSET interior (w:real^3->bool)`; `interior w INTER frontier w = {}:real^3->bool`;
        `Y INTER frontier w = CW INTER {y:real^3 | nu' dot y = c'}`;
        `(z:real^3) IN CW INTER {y | nu' dot y = c'}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN interior CW` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`CW:real^3->bool`; `F0:real^3->bool`; `z:real^3`]
        MOI_TB3_INTERIOR_UNION_OFF) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`relative_interior (CW INTER {y:real^3 | nu' dot y = c'}) =
       interior CW INTER {y | nu' dot y = c'}`;
      `~((z:real^3) IN relative_interior (CW INTER {y | nu' dot y = c'}))`;
      `(z:real^3) IN CW INTER {y | nu' dot y = c'}`; `(z:real^3) IN interior CW`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN CW INTER {y:real^3 | nu' dot y = c'} DIFF
                     relative_frontier (CW INTER {y | nu' dot y = c'})
                     ==> ?r. &0 < r /\ ball(z,r) INTER w SUBSET Y` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN interior CW` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERIOR] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `CW INTER {y:real^3 | nu' dot y >= c'}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; real_ge] THEN X_GEN_TAC `p:real^3` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(p:real^3) IN CW` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(p:real^3) IN ball(a',R)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      EXPAND_TAC "Y" THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^3->bool`; `Y:real^3->bool`; `CW INTER {y:real^3 | nu' dot y = c'}`;
                 `relative_frontier (CW INTER {y:real^3 | nu' dot y = c'})`;
                 `CW INTER {y:real^3 | nu' dot y <= c'}`] MOI_TB3_BITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the conclusion *)
  EXISTS_TAC `CX UNION moi_tb3_chain l UNION CW:real^3->bool` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNION; MOI_TB3_CHAIN_COMPACT];
    MAP_EVERY UNDISCH_TAC
     [`CX SUBSET ball(a:real^3,R)`; `DISJOINT (ball(a:real^3,R)) k`;
      `moi_tb3_chain l SUBSET interior w DIFF x DIFF k`;
      `CW SUBSET ball(a':real^3,R)`; `DISJOINT (ball(a':real^3,R)) k`] THEN
    SET_TAC[];
    SUBGOAL_THEN `x UNION CX UNION moi_tb3_chain l UNION CW = F0 UNION CW:real^3->bool`
      SUBST1_TAC THENL
     [EXPAND_TAC "F0" THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM; real_ge] THEN
      X_GEN_TAC `y:real^3` THEN ASM_CASES_TAC `(y:real^3) IN CX` THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(y:real^3) IN x \/ c <= nu dot y` MP_TAC THENL
         [SUBGOAL_THEN `(y:real^3) IN ball(a,R)` ASSUME_TAC THENL
           [ASM SET_TAC[]; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
          MESON_TAC[]];
        ASM_REWRITE_TAC[] THEN MESON_TAC[]];
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Margins near the ends at unit scale.                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_COL_NOT_IN_CUBE = prove
 (`!(g:real^3) k u s t.
     1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k) /\ &1 <= abs(s - t)
     ==> ~(g + s % u IN moi_tb3_cube (g + t % u))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `u:real^3`] MOI_TB3_U_COORD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[MOI_TB3_IN_CUBE] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REAL_ARITH_TAC);;

let MOI_TB3_SEG_MARGIN = prove
 (`!(nu:real^3) c (a:real^3) (g:real^3) (u:real^3) R.
     ~(nu = vec 0) /\ nu dot a = c /\ &1000 <= R /\
     &3 / &2 * (nu dot u) < nu dot g - c /\ norm nu <= &3 * (nu dot u) /\
     (!i. 1 <= i /\ i <= 3 ==> abs(g$i - a$i) <= &5) /\
     (!i. 1 <= i /\ i <= 3 ==> abs(u$i) <= &1)
     ==> !y. y IN segment[g + &40 % u, a + (R / &2) % (inv(norm nu) % nu)]
             ==> ball(y,&7) SUBSET
                 ball(a,R - &30) INTER {p | c + &3 / &2 * norm nu < nu dot p}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(nu:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = a + (R / &2) % (inv(norm nu) % nu):real^3` THEN
  SUBGOAL_THEN `(nu:real^3) dot q = c + R / &2 * norm nu /\ norm(q - a:real^3) = R / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; VECTOR_ARITH `(a + x) - a:real^3 = x`; NORM_MUL] THEN
    REWRITE_TAC[DOT_SQUARE_NORM; REAL_ABS_INV; REAL_ABS_NORM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(R / &2) = R / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&1000 <= R` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < norm(nu:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[g + &40 % u,q] SUBSET
                cball(a:real^3,R - &37) INTER {p | nu dot p >= c + &17 / &2 * norm nu}`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `cball(a:real^3,R - &37) INTER {p | nu dot p >= c + &17 / &2 * norm nu}`
      CONVEX_CONTAINS_SEGMENT) THEN
    SIMP_TAC[CONVEX_INTER; CONVEX_CBALL; CONVEX_HALFSPACE_GE] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_INTER; IN_CBALL; IN_ELIM_THM; real_ge] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &3 * &45 /\ &1000 <= R ==> x <= R - &37`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_TB3_COORD_NORM THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `abs((g:real^3)$i - (a:real^3)$i) <= &5 /\ abs((u:real^3)$i) <= &1`
        MP_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&17 / &2 * norm(nu:real^3) <= R / &2 * norm nu` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `dist(a:real^3,y) <= R - &37 /\ nu dot y >= c + &17 / &2 * norm(nu:real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN segment[g + &40 % u,q]` THEN
    UNDISCH_TAC `segment[g + &40 % u,q] SUBSET
                 cball(a:real^3,R - &37) INTER {p | nu dot p >= c + &17 / &2 * norm nu}` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_CBALL; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a:real^3`; `y:real^3`; `p:real^3`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nu:real^3`; `p - y:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  SUBGOAL_THEN `norm(nu:real^3) * norm(p - y:real^3) < norm nu * &7` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RSUB] THEN ASM_REAL_ARITH_TAC);;

let MOI_TB3_U_ABS = prove
 (`!k (u:real^3). 1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k)
                  ==> !i. 1 <= i /\ i <= 3 ==> abs(u$i) <= &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `u:real^3`] MOI_TB3_U_COORD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_CASES_TAC `i:num = k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
      is_eq(lhand(concl th)) && type_of(lhand(lhand(concl th))) = `:real`)) THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_TB3_CUBES_END = prove
 (`!(nu:real^3) c (a:real^3) g k u.
     1 <= k /\ k <= 3 /\ (u = basis k \/ u = --basis k) /\
     (!t y. y IN moi_tb3_cube (g + t % u) ==> c + t * (nu dot u) < nu dot y) /\
     (!t. moi_tb3_cube (g + t % u) SUBSET ball(a,&17 + &3 * abs t)) /\
     norm nu <= &3 * (nu dot u)
     ==> !j. j <= 40
             ==> moi_tb3_cube (g + &j % u) SUBSET ball(a,&137) INTER {y | c < nu dot y} /\
                 ~(g - u IN moi_tb3_cube (g + &j % u)) /\
                 ~(g - &2 % u IN moi_tb3_cube (g + &j % u)) /\
                 ~(g - &3 % u IN moi_tb3_cube (g + &j % u))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (nu:real^3) dot u` ASSUME_TAC THENL
   [MP_TAC(ISPEC `nu:real^3` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&j <= &40` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN ball(a,&17 + &3 * abs(&j))` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_BALL; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `c + &j * (nu:real^3) dot u < nu dot y` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &j * (nu:real^3) dot u` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[VECTOR_ARITH `g - u:real^3 = g + -- &1 % u`];
    REWRITE_TAC[VECTOR_ARITH `g - &2 % u:real^3 = g + -- &2 % u`];
    REWRITE_TAC[VECTOR_ARITH `g - &3 % u:real^3 = g + -- &3 % u`]] THEN
  MATCH_MP_TAC MOI_TB3_COL_NOT_IN_CUBE THEN EXISTS_TAC `k:num` THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `j:num` REAL_POS) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tube at unit scale, from two half-space balls at the facets and a     *)
(* path between them with margin 100.                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_UNIT = prove
 (`!x w k (a:real^3) nu c (a':real^3) nu' c' R (P:real^1->real^3).
     PL_SCHOENFLIES_3_STATEMENT /\
     pl_ball 3 x /\ pl_ball 3 w /\ x SUBSET interior w /\ closed k /\ &1000 <= R /\
     ~(nu = vec 0) /\ nu dot a = c /\
     (!y. y IN ball(a,R) ==> (y IN x <=> nu dot y <= c)) /\
     ball(a,R) SUBSET interior w /\ DISJOINT (ball(a,R)) k /\
     ~(nu' = vec 0) /\ nu' dot a' = c' /\
     (!y. y IN ball(a',R) ==> (y IN w <=> c' <= nu' dot y)) /\
     DISJOINT (ball(a',R)) x /\ DISJOINT (ball(a',R)) k /\
     path P /\ pathstart P = a + (R / &2) % (inv(norm nu) % nu) /\
     pathfinish P = a' + (R / &2) % (inv(norm nu') % nu') /\
     (!t. t IN interval[vec 0,vec 1] ==> ball(P t,&100) SUBSET interior w DIFF x DIFF k)
     ==> ?n. compact n /\ DISJOINT n k /\ pl_ball 3 (w DIFF interior (x UNION n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `compact (x:real^3->bool) /\ compact (w:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4D_PL_BALL_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^3->bool`; `a':real^3`; `R:real`; `nu':real^3`; `c':real`]
    MOI_TB3_HALF_LOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; STRIP_TAC] THEN
  SUBGOAL_THEN `(a:real^3) IN ball(a,R) /\ (a':real^3) IN ball(a',R)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3) IN x` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `~((a':real^3) IN interior w)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `R <= dist(a:real^3,a')` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a':real^3) IN ball(a,R)` MP_TAC THENL [ASM_REWRITE_TAC[IN_BALL]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nu:real^3`; `c:real`; `a:real^3`] MOI_TB3_END) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^3` (X_CHOOSE_THEN `k0:num` (X_CHOOSE_THEN `u0:real^3`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))) THEN
  MP_TAC(ISPECL [`nu:real^3`; `c:real`; `a:real^3`; `g0:real^3`; `k0:num`; `u0:real^3`]
    MOI_TB3_END_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`nu':real^3`; `c':real`; `a':real^3`] MOI_TB3_END) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:real^3`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))) THEN
  MP_TAC(ISPECL [`nu':real^3`; `c':real`; `a':real^3`; `g1:real^3`; `k1:num`; `u1:real^3`]
    MOI_TB3_END_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`nu:real^3`; `c:real`; `a:real^3`; `g0:real^3`; `k0:num`; `u0:real^3`]
    MOI_TB3_CUBES_END) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`nu':real^3`; `c':real`; `a':real^3`; `g1:real^3`; `k1:num`; `u1:real^3`]
    MOI_TB3_CUBES_END) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the virtual points *)
  SUBGOAL_THEN `!s:real^3. (s = g0 - u0 \/ s = g0 - &2 % u0 \/ s = g0 - &3 % u0)
                           ==> dist(s,a) < &30 /\ nu dot s <= c + &3 / &2 * norm nu`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ONCE_REWRITE_TAC[VECTOR_ARITH `g0 - u0:real^3 = g0 - &1 % u0`]; ALL_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_OF_NUM_LE; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3. (s = g1 - u1 \/ s = g1 - &2 % u1 \/ s = g1 - &3 % u1)
                           ==> dist(s,a') < &30 /\ nu' dot s <= c' + &3 / &2 * norm nu'`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ONCE_REWRITE_TAC[VECTOR_ARITH `g1 - u1:real^3 = g1 - &1 % u1`]; ALL_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_OF_NUM_LE; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `S = {g0 - u0, g0 - &2 % u0, g0 - &3 % u0,
                   g1 - u1, g1 - &2 % u1, g1 - &3 % u1:real^3}` THEN
  ABBREV_TAC `v = (interior w DIFF x DIFF k) DIFF (S:real^3->bool)` THEN
  SUBGOAL_THEN `!s:real^3. s IN S
                  ==> dist(s,a) < &30 /\ nu dot s <= c + &3 / &2 * norm nu \/
                      dist(s,a') < &30 /\ nu' dot s <= c' + &3 / &2 * norm nu'`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the regions near the facets *)
  SUBGOAL_THEN `ball(a:real^3,R - &30) INTER {p | c + &3 / &2 * norm nu < nu dot p} SUBSET v`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^3) IN ball(a,R)` ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^3) IN ball(a,R - &30)` THEN REWRITE_TAC[IN_BALL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((p:real^3) IN x)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_NOT_LE] THEN MP_TAC(ISPEC `nu:real^3` NORM_POS_LE) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((p:real^3) IN S)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `S:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE; REAL_NOT_LT] THEN
      MP_TAC(ISPECL [`a:real^3`; `p:real^3`; `a':real^3`] DIST_TRIANGLE) THEN
      UNDISCH_TAC `(p:real^3) IN ball(a,R - &30)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "v" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a':real^3,R - &30) INTER {p | c' + &3 / &2 * norm nu' < nu' dot p} SUBSET v`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^3) IN ball(a',R)` ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^3) IN ball(a',R - &30)` THEN REWRITE_TAC[IN_BALL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) IN interior w` ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN MP_TAC(ISPEC `nu':real^3` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((p:real^3) IN S)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `S:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE; REAL_NOT_LT] THEN
      MP_TAC(ISPECL [`a':real^3`; `p:real^3`; `a:real^3`] DIST_TRIANGLE) THEN
      UNDISCH_TAC `(p:real^3) IN ball(a',R - &30)` THEN REWRITE_TAC[IN_BALL] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "v" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the column cubes *)
  SUBGOAL_THEN `!j. j <= 40 ==> moi_tb3_cube (g0 + &j % u0:real^3) SUBSET v` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `j <= 40`) o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `g0 - &2 % u0:real^3`)) (concl th) &&
      can (find_term ((=) `&137`)) (concl th))) THEN
    STRIP_TAC THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^3) IN ball(a,&137) /\ c < nu dot p` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) IN ball(a,R)` ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^3) IN ball(a,&137)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((p:real^3) IN x)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_NOT_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `~((p:real^3) IN S)` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC; ALL_TAC; ALL_TAC] THEN
      (SUBGOAL_THEN `dist(p:real^3,a') < &30` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
       MP_TAC(ISPECL [`a:real^3`; `p:real^3`; `a':real^3`] DIST_TRIANGLE) THEN
       UNDISCH_TAC `(p:real^3) IN ball(a,&137)` THEN REWRITE_TAC[IN_BALL] THEN
       ASM_REAL_ARITH_TAC);
      ALL_TAC] THEN
    EXPAND_TAC "v" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j <= 40 ==> moi_tb3_cube (g1 + &j % u1:real^3) SUBSET v` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `j <= 40`) o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `g1 - &2 % u1:real^3`)) (concl th) &&
      can (find_term ((=) `&137`)) (concl th))) THEN
    STRIP_TAC THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^3) IN ball(a',&137) /\ c' < nu' dot p` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) IN ball(a',R)` ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^3) IN ball(a',&137)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) IN interior w` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((p:real^3) IN S)` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THENL
       [ALL_TAC; ALL_TAC; ALL_TAC; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]] THEN
      (SUBGOAL_THEN `dist(p:real^3,a) < &30` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
       MP_TAC(ISPECL [`a':real^3`; `p:real^3`; `a:real^3`] DIST_TRIANGLE) THEN
       UNDISCH_TAC `(p:real^3) IN ball(a',&137)` THEN REWRITE_TAC[IN_BALL] THEN
       ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC);
      ALL_TAC] THEN
    EXPAND_TAC "v" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the middle path *)
  SUBGOAL_THEN `!q. q IN path_image (P:real^1->real^3) ==> ball(q,&7) SUBSET v`
  ASSUME_TAC THENL
   [REWRITE_TAC[path_image; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ball((P:real^1->real^3) t,&100) SUBSET interior w DIFF x DIFF k`
      ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^3) IN interior w DIFF x DIFF k` ASSUME_TAC THENL
     [UNDISCH_TAC `ball((P:real^1->real^3) t,&100) SUBSET interior w DIFF x DIFF k` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((p:real^3) IN S)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `S:real^3->bool`)) (concl th) &&
        can (find_term ((=) `a':real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [SUBGOAL_THEN `(a:real^3) IN interior w DIFF x DIFF k` MP_TAC THENL
         [UNDISCH_TAC `ball((P:real^1->real^3) t,&100) SUBSET interior w DIFF x DIFF k` THEN
          REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
          MP_TAC(ISPECL [`(P:real^1->real^3) t`; `p:real^3`; `a:real^3`] DIST_TRIANGLE) THEN
          ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]];
        SUBGOAL_THEN `(a':real^3) IN interior w DIFF x DIFF k` MP_TAC THENL
         [UNDISCH_TAC `ball((P:real^1->real^3) t,&100) SUBSET interior w DIFF x DIFF k` THEN
          REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
          MP_TAC(ISPECL [`(P:real^1->real^3) t`; `p:real^3`; `a':real^3`] DIST_TRIANGLE) THEN
          ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]]];
      ALL_TAC] THEN
    EXPAND_TAC "v" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3 ==> abs((u0:real^3)$i) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_TB3_U_ABS THEN EXISTS_TAC `k0:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3 ==> abs((u1:real^3)$i) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_TB3_U_ABS THEN EXISTS_TAC `k1:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`nu:real^3`; `c:real`; `a:real^3`; `g0:real^3`; `u0:real^3`; `R:real`]
    MOI_TB3_SEG_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`nu':real^3`; `c':real`; `a':real^3`; `g1:real^3`; `u1:real^3`; `R:real`]
    MOI_TB3_SEG_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `gam = linepath(g0 + &40 % u0:real^3,pathstart P) ++
                    (P ++ linepath(pathfinish P,g1 + &40 % u1))` THEN
  SUBGOAL_THEN `path (gam:real^1->real^3) /\ pathstart gam = g0 + &40 % u0 /\
                pathfinish gam = g1 + &40 % u1 /\
                path_image gam = segment[g0 + &40 % u0,pathstart P] UNION path_image P UNION
                                 segment[pathfinish P,g1 + &40 % u1]` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gam" THEN
    SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATH_LINEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1] ==> ball((gam:real^1->real^3) t,&7) SUBSET v`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(gam:real^1->real^3) t IN path_image gam` MP_TAC THENL
     [REWRITE_TAC[path_image] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(a:real^3,R - &30) INTER {p | c + &3 / &2 * norm nu < nu dot p}` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `segment[g0 + &40 % u0:real^3,
          a + (R / &2) % (inv(norm nu) % nu)]`)) (concl th))) THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(a':real^3,R - &30) INTER {p | c' + &3 / &2 * norm nu' < nu' dot p}` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `segment[g1 + &40 % u1:real^3,
          a' + (R / &2) % (inv(norm nu') % nu')]`)) (concl th))) THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the walk *)
  MP_TAC(ISPECL [`v:real^3->bool`; `g0:real^3`; `k0:num`; `u0:real^3`; `g1:real^3`;
                 `k1:num`; `u1:real^3`; `gam:real^1->real^3`; `40`] MOI_TB3_WALK_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^3)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_tb3_chain l SUBSET interior w DIFF x DIFF k` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `v:real^3->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_TB3_CHAIN_SUBSET THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "v" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3. s IN S ==> ~(MEM s l)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `ALL (\q. moi_tb3_cube q SUBSET v) (l:(real^3)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `s:real^3`) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `s:real^3`) THEN
    REWRITE_TAC[MOI_TB3_IN_CUBE; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    EXPAND_TAC "v" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g0 - u0) IN S /\ (g0 - &2 % u0) IN S /\ (g0 - &3 % u0) IN S /\
                (g1 - u1) IN S /\ (g1 - &2 % u1) IN S /\ (g1 - &3 % u1:real^3) IN S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  (* assembly *)
  MATCH_MP_TAC MOI_TB3_ASSEMBLE THEN
  MAP_EVERY EXISTS_TAC
   [`a:real^3`; `nu:real^3`; `c:real`; `a':real^3`; `nu':real^3`; `c':real`; `R:real`;
    `l:(real^3)list`; `g0:real^3`; `k0:num`; `u0:real^3`; `g1:real^3`; `k1:num`;
    `u1:real^3`] THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^3,&30)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_tb3_cube (g0 + &0 % u0:real^3)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; MOI_TB3_BEAD_SUBSET_CUBE];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `c + &0 * (nu:real^3) dot u0 < nu dot y` MP_TAC THENL
       [ASM_MESON_TAC[]; REAL_ARITH_TAC]];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a':real^3,&30)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_tb3_cube (g1 + &0 % u1:real^3)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; MOI_TB3_BEAD_SUBSET_CUBE];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `c' + &0 * (nu':real^3) dot u1 < nu' dot y` MP_TAC THENL
       [ASM_MESON_TAC[]; REAL_ARITH_TAC]];
    MATCH_MP_TAC(SET_RULE `!s t u v:real^3->bool. s SUBSET u /\ t SUBSET v /\
                             DISJOINT u v ==> DISJOINT s t`) THEN
    MAP_EVERY EXISTS_TAC [`ball(a:real^3,&30)`; `ball(a':real^3,&30)`] THEN
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
    X_GEN_TAC `p:real^3` THEN
    MP_TAC(ISPECL [`a:real^3`; `p:real^3`; `a':real^3`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`a':real^3`; `p:real^3`] DIST_SYM) THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Rescaling.  The unit-scale tube lemma transferred to any scale d by the   *)
(* PL homeomorphism y -> inv d % y of real^3.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_TB3_SCALE_PLH = prove
 (`!d. &0 < d
       ==> pl_homeomorphism ((:real^3),(:real^3)) ((\y:real^3. inv d % y),(\y. d % y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^3` THEN
    EXISTS_TAC `d % y:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SCALING];
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^3` THEN
    EXISTS_TAC `inv d % y:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID];
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SCALING];
    SUBGOAL_THEN `(\y:real^3. inv d % y) = (\x. (\y. inv d % y) x + vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; LINEAR_SCALING];
    SUBGOAL_THEN `(\y:real^3. d % y) = (\x. (\y. d % y) x + vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; LINEAR_SCALING]]);;

let MOI_TB3_IN_SCALE = prove
 (`!d s (y:real^3). &0 < d ==> (y IN IMAGE (\y. inv d % y) s <=> d % y IN s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID];
    DISCH_TAC THEN EXISTS_TAC `d % y:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID]]);;

let MOI_TB3_BALL_SCALE = prove
 (`!d (a:real^3) r y. &0 < d ==> (y IN ball(inv d % a,r / d) <=> d % y IN ball(a,r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_BALL; dist] THEN
  SUBGOAL_THEN `a - d % y:real^3 = d % (inv d % a - y)` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC);;

let MOI_TB3_SCALE_LE = prove
 (`!d t c. &0 < d ==> (d * t <= c <=> t <= inv d * c) /\ (c <= d * t <=> inv d * c <= t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t:real`; `inv d * c`; `d:real`] REAL_LE_LMUL_EQ) THEN
  MP_TAC(SPECL [`inv d * c`; `t:real`; `d:real`] REAL_LE_LMUL_EQ) THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID]);;

let MOI_TB3_UNIT_SCALED = prove
 (`!x w k (a:real^3) nu c (a':real^3) nu' c' r d (P:real^1->real^3).
     PL_SCHOENFLIES_3_STATEMENT /\
     pl_ball 3 x /\ pl_ball 3 w /\ x SUBSET interior w /\ closed k /\
     &0 < d /\ &1000 * d <= r /\
     ~(nu = vec 0) /\ nu dot a = c /\
     (!y. y IN ball(a,r) ==> (y IN x <=> nu dot y <= c)) /\
     ball(a,r) SUBSET interior w /\ DISJOINT (ball(a,r)) k /\
     ~(nu' = vec 0) /\ nu' dot a' = c' /\
     (!y. y IN ball(a',r) ==> (y IN w <=> c' <= nu' dot y)) /\
     DISJOINT (ball(a',r)) x /\ DISJOINT (ball(a',r)) k /\
     path P /\ pathstart P = a + (r / &2) % (inv(norm nu) % nu) /\
     pathfinish P = a' + (r / &2) % (inv(norm nu') % nu') /\
     (!t. t IN interval[vec 0,vec 1] ==> ball(P t,&100 * d) SUBSET interior w DIFF x DIFF k)
     ==> ?n. compact n /\ DISJOINT n k /\ pl_ball 3 (w DIFF interior (x UNION n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `d:real` MOI_TB3_SCALE_PLH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `homeomorphism ((:real^3),(:real^3)) ((\y:real^3. inv d % y),(\y. d % y))`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_TB3_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`\y:real^3. inv d % y`; `\y:real^3. d % y`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s:real^3->bool. interior (IMAGE (\y:real^3. inv d % y) s) =
                                 IMAGE (\y. inv d % y) (interior s)` ASSUME_TAC THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_TB3_HOMEO_INTERIOR THEN
    EXISTS_TAC `\y:real^3. d % y` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_TB3_UNIT THEN
  MAP_EVERY EXISTS_TAC
   [`inv d % a:real^3`; `nu:real^3`; `inv d * c`; `inv d % a':real^3`; `nu':real^3`;
    `inv d * c'`; `r / d`; `(\y:real^3. inv d % y) o (P:real^1->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_TB3_PL_BALL_IMAGE THEN EXISTS_TAC `\y:real^3. d % y` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_TB3_PL_BALL_IMAGE THEN EXISTS_TAC `\y:real^3. d % y` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_TB3_HOMEO_CLOSED THEN EXISTS_TAC `\y:real^3. d % y` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    REWRITE_TAC[DOT_RMUL] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN ASM_SIMP_TAC[MOI_TB3_BALL_SCALE; MOI_TB3_IN_SCALE] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[DOT_RMUL; MOI_TB3_SCALE_LE];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN
    ASM_SIMP_TAC[MOI_TB3_BALL_SCALE; MOI_TB3_IN_SCALE] THEN ASM SET_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^3` THEN
    ASM_SIMP_TAC[MOI_TB3_BALL_SCALE; MOI_TB3_IN_SCALE] THEN ASM SET_TAC[];
    REWRITE_TAC[DOT_RMUL] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN ASM_SIMP_TAC[MOI_TB3_BALL_SCALE; MOI_TB3_IN_SCALE] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[DOT_RMUL; MOI_TB3_SCALE_LE];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^3` THEN
    ASM_SIMP_TAC[MOI_TB3_BALL_SCALE; MOI_TB3_IN_SCALE] THEN ASM SET_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^3` THEN
    ASM_SIMP_TAC[MOI_TB3_BALL_SCALE; MOI_TB3_IN_SCALE] THEN ASM SET_TAC[];
    MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SCALING];
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_AC];
    ASM_REWRITE_TAC[PATHFINISH_COMPOSE; VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_AC];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; SUBSET] THEN
    X_GEN_TAC `y:real^3` THEN
    SUBGOAL_THEN `&100 = (&100 * d) / d` SUBST1_TAC THENL
     [UNDISCH_TAC `~(d = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_TB3_BALL_SCALE; IN_DIFF; MOI_TB3_IN_SCALE] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `d % (y:real^3) IN interior w DIFF x DIFF k` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `d % y:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID]]);;

let MOI_TB3_PATH_ENDS = prove
 (`!q:real^1->real^3 e e'.
     path q /\ &0 < e /\ &0 < e'
     ==> ?t0 t1. t0 IN interval[vec 0,vec 1] /\ t1 IN interval[vec 0,vec 1] /\
                 &0 < drop t0 /\ drop t0 <= drop t1 /\ drop t1 < &1 /\
                 q t0 IN ball(pathstart q,e) /\ q t1 IN ball(pathfinish q,e')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `path (q:real^1->real^3)` THEN REWRITE_TAC[path; continuous_on] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `vec 1:real^1` th) THEN MP_TAC(SPEC `vec 0:real^1` th)) THEN
  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e':real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t0 = lift(min (d0 / &2) (&1 / &3))` THEN
  ABBREV_TAC `t1 = lift(max (&1 - d1 / &2) (&2 / &3))` THEN
  SUBGOAL_THEN `&0 < drop t0 /\ drop t0 <= &1 / &3 /\ &2 / &3 <= drop t1 /\ drop t1 < &1 /\
                drop t0 < d0 /\ &1 - drop t1 < d1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t0"; "t1"] THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 IN interval[vec 0:real^1,vec 1] /\ t1 IN interval[vec 0:real^1,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t0:real^1`; `t1:real^1`] THEN
  ASM_REWRITE_TAC[pathstart; pathfinish; IN_BALL] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[DIST_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC);;

let MOI_TB3_UNIT_STEP = prove
 (`!(a:real^3) v s.
     ~(v = vec 0) /\ &0 <= s
     ==> dist(a,a + s % (inv(norm v) % v)) = s /\
         v dot (a + s % (inv(norm v) % v)) = v dot a + s * norm v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(norm(v:real^3) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[NORM_ARITH `dist(a:real^3,a + y) = norm y`; NORM_MUL; DOT_RADD; DOT_RMUL] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM; DOT_SQUARE_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`] THEN
  UNDISCH_TAC `~(norm(v:real^3) = &0)` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The main theorem.  Straighten both balls to nested simplices by a PL      *)
(* homeomorphism of real^3 and transfer the simplex case back.               *)
(* ------------------------------------------------------------------------- *)

(* The simplex case, by the lattice construction of the preceding sections.  *)

let MOI_TB3_TUBE_SIMPLEX = prove
 (`!x w k (p:real^3) p1 (g:real^1->real^3).
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     &3 simplex x /\ &3 simplex w /\ x SUBSET interior w /\ closed k /\
     p IN interior x /\ ~(p1 IN w) /\
     path g /\ pathstart g = p /\ pathfinish g = p1 /\ DISJOINT (path_image g) k
     ==> ?n. compact n /\ DISJOINT n k /\ pl_ball 3 (w DIFF interior (x UNION n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `polytope (x:real^3->bool) /\ polytope (w:real^3->bool) /\ convex w /\
                compact x /\ compact w /\ closed x /\ closed w /\
                pl_ball 3 x /\ pl_ball 3 w` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(MATCH_MP SIMPLEX_IMP_POLYTOPE (ASSUME t)) THEN
                        MP_TAC(MATCH_MP SIMPLEX_IMP_CONVEX (ASSUME t)) THEN
                        MP_TAC(MATCH_MP SIMPLEX_IMP_COMPACT (ASSUME t)) THEN
                        MP_TAC(MATCH_MP SIMPLEX_IMP_CLOSED (ASSUME t)) THEN
                        MP_TAC(MATCH_MP PL_BALL_SIMPLEX (ASSUME t)))
      [`&3 simplex (x:real^3->bool)`; `&3 simplex (w:real^3->bool)`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN x /\ ~(interior x = {}:real^3->bool) /\
                ~(interior w = {}:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `x:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  (* the shell path and an arc in it *)
  MP_TAC(ISPECL [`x:real^3->bool`; `w:real^3->bool`; `p:real^3`; `p1:real^3`;
                 `g:real^1->real^3`] MOI_TB3_SHELL_PATH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `z = pathstart (h:real^1->real^3)` THEN
  ABBREV_TAC `z' = pathfinish (h:real^1->real^3)` THEN
  SUBGOAL_THEN `(z:real^3) IN x /\ z IN interior w /\ ~((z':real^3) IN interior w) /\
                ~(z' IN x) /\ ~(z IN k) /\ ~(z' IN k) /\ ~(z = z')` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^3) IN path_image g /\ (z':real^3) IN path_image g` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["z"; "z'"] THEN
      MP_TAC(ISPEC `h:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
      MP_TAC(ISPEC `h:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
      UNDISCH_TAC `path_image (h:real^1->real^3) SUBSET path_image g` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `x:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN frontier x`; `(z':real^3) IN frontier w`;
      `x SUBSET interior (w:real^3->bool)`; `DISJOINT (path_image (g:real^1->real^3)) k`] THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^1->real^3`; `z:real^3`; `z':real^3`] PATH_CONTAINS_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^3` STRIP_ASSUME_TAC) THEN
  (* local balls at z *)
  SUBGOAL_THEN `?e. &0 < e /\ ball(z:real^3,e) SUBSET interior w /\
                    DISJOINT (ball(z,e)) k /\ connected (ball(z,e) DIFF x)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3) DIFF k` OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[GSYM closed] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `interior w:real^3->bool` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`x:real^3->bool`; `z:real^3`] MOI_S4V_POLY_OUT_LOCAL) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e1 (min e2 r0)` THEN
    SUBGOAL_THEN `ball(z:real^3,min e1 (min e2 r0)) SUBSET ball(z,e1) /\
                  ball(z:real^3,min e1 (min e2 r0)) SUBSET ball(z,e2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM SET_TAC[];
      ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `z:real^3`; `e:real`] MOI_TB3_FACET_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `nu:real^3` (X_CHOOSE_THEN `c:real`
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)))) THEN
  (* local balls at z' *)
  SUBGOAL_THEN `?e'. &0 < e' /\ DISJOINT (ball(z':real^3,e')) x /\ DISJOINT (ball(z',e')) k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3) DIFF (x UNION k)` OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[GSYM closed; CLOSED_UNION] THEN
    DISCH_THEN(MP_TAC o SPEC `z':real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^3->bool`; `z':real^3`; `e':real`] MOI_TB3_FACET_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a':real^3` (X_CHOOSE_THEN `mu:real^3` (X_CHOOSE_THEN `dd:real`
    (X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC)))) THEN
  (* the deep points next to the two facets *)
  ABBREV_TAC `rr = min r r'` THEN
  SUBGOAL_THEN `&0 < rr /\ rr <= r /\ rr <= r'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN ball(a',r') ==> (y IN w <=> --dd <= --mu dot y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[DOT_LNEG; REAL_LE_NEG2] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^3->bool`; `a':real^3`; `r':real`; `--mu:real^3`; `--dd:real`]
    MOI_TB3_HALF_LOCAL) THEN
  ASM_REWRITE_TAC[VECTOR_NEG_EQ_0] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `nu:real^3`; `rr / &2`] MOI_TB3_UNIT_STEP) THEN
  MP_TAC(ISPECL [`a':real^3`; `--mu:real^3`; `rr / &2`] MOI_TB3_UNIT_STEP) THEN
  ASM_REWRITE_TAC[VECTOR_NEG_EQ_0] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `q0 = a + (rr / &2) % (inv(norm nu) % nu):real^3` THEN
  ABBREV_TAC `q1 = a' + (rr / &2) % (inv(norm(--mu)) % --mu):real^3` THEN
  SUBGOAL_THEN `ball(a:real^3,rr) SUBSET ball(a,r) /\ ball(a':real^3,rr) SUBSET ball(a',r')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(q0:real^3) IN ball(a,r) /\ (q1:real^3) IN ball(a',r')` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q0:real^3) IN ball(z,e) DIFF x` ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_NOT_LE] THEN
    MP_TAC(ISPEC `nu:real^3` NORM_POS_LT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < y ==> c < c + y`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q1:real^3) IN ball(z',e') INTER interior w` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPEC `--mu:real^3` NORM_POS_LT) THEN ASM_REWRITE_TAC[VECTOR_NEG_EQ_0] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < rr / &2 * norm(--mu:real^3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_LNEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the open shell and the arc inside it *)
  ABBREV_TAC `O = interior w DIFF x DIFF (k:real^3->bool)` THEN
  SUBGOAL_THEN `open (O:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(z:real^3,e) DIFF x SUBSET O /\
                ball(z':real^3,e') INTER interior w SUBSET O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    MAP_EVERY UNDISCH_TAC
     [`ball(z:real^3,e) SUBSET interior w`; `DISJOINT (ball(z:real^3,e)) k`;
      `DISJOINT (ball(z':real^3,e')) x`; `DISJOINT (ball(z':real^3,e')) k`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^1->real^3`; `e:real`; `e':real`] MOI_TB3_PATH_ENDS) THEN
  ASM_SIMP_TAC[ARC_IMP_PATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^1` (X_CHOOSE_THEN `t1:real^1` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!s. s IN interval[vec 0,vec 1] /\ drop t0 <= drop s /\ drop s <= drop t1
                    ==> (q:real^1->real^3) s IN O` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(q:real^1->real^3) s IN path_image h` ASSUME_TAC THENL
     [UNDISCH_TAC `path_image (q:real^1->real^3) SUBSET path_image h` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((q:real^1->real^3) s = z) /\ ~((q:real^1->real^3) s = z')`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `arc (q:real^1->real^3)` THEN REWRITE_TAC[arc] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      DISCH_THEN(fun th -> MP_TAC(SPECL [`s:real^1`; `vec 0:real^1`] th) THEN
                           MP_TAC(SPECL [`s:real^1`; `vec 1:real^1`] th)) THEN
      UNDISCH_TAC `pathstart (q:real^1->real^3) = z` THEN
      UNDISCH_TAC `pathfinish (q:real^1->real^3) = z'` THEN
      REWRITE_TAC[pathstart; pathfinish] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      REPEAT STRIP_TAC THENL
       [SUBGOAL_THEN `s = vec 0:real^1` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `drop t0 <= drop (vec 0:real^1)` THEN REWRITE_TAC[DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `s = vec 1:real^1` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `drop (vec 1:real^1) <= drop t1` THEN REWRITE_TAC[DROP_VEC] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "O" THEN REWRITE_TAC[IN_DIFF] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      UNDISCH_TAC `DISJOINT (path_image (g:real^1->real^3)) k` THEN
      UNDISCH_TAC `path_image (h:real^1->real^3) SUBSET path_image g` THEN
      UNDISCH_TAC `(q:real^1->real^3) s IN path_image h` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* a path from q0 to q1 inside O *)
  SUBGOAL_THEN `path_component O (q0:real^3) q1` MP_TAC THENL
   [MATCH_MP_TAC PATH_COMPONENT_TRANS THEN EXISTS_TAC `(q:real^1->real^3) t0` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `path_component (ball(z:real^3,e) DIFF x) q0 ((q:real^1->real^3) t0)`
      MP_TAC THENL
       [SUBGOAL_THEN `path_connected (ball(z:real^3,e) DIFF x)` MP_TAC THENL
         [MATCH_MP_TAC CONNECTED_OPEN_PATH_CONNECTED THEN
          ASM_SIMP_TAC[OPEN_DIFF; OPEN_BALL];
          ALL_TAC] THEN
        REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_DIFF] THEN
        SUBGOAL_THEN `(q:real^1->real^3) t0 IN O` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
        EXPAND_TAC "O" THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(z:real^3,e) DIFF x`; `O:real^3->bool`; `q0:real^3`]
        PATH_COMPONENT_MONO) THEN
      ASM_REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PATH_COMPONENT_TRANS THEN EXISTS_TAC `(q:real^1->real^3) t1` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[path_component] THEN EXISTS_TAC `subpath t0 t1 (q:real^1->real^3)` THEN
      ASM_SIMP_TAC[PATH_SUBPATH; ARC_IMP_PATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                   PATH_IMAGE_SUBPATH] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `s:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `path_component (ball(z':real^3,e') INTER interior w)
                                 ((q:real^1->real^3) t1) q1` MP_TAC THENL
     [SUBGOAL_THEN `path_connected (ball(z':real^3,e') INTER interior w)` MP_TAC THENL
       [MATCH_MP_TAC CONVEX_IMP_PATH_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        ASM_SIMP_TAC[CONVEX_BALL; CONVEX_INTERIOR];
        ALL_TAC] THEN
      REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      SUBGOAL_THEN `(q:real^1->real^3) t1 IN O` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      EXPAND_TAC "O" THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ball(z':real^3,e') INTER interior w`; `O:real^3->bool`;
                   `(q:real^1->real^3) t1`] PATH_COMPONENT_MONO) THEN
    ASM_REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[path_component] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^1->real^3` STRIP_ASSUME_TAC) THEN
  (* its margin *)
  MP_TAC(ISPECL [`path_image (P:real^1->real^3)`; `(:real^3) DIFF O`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PATH_IMAGE; GSYM OPEN_CLOSED] THEN
    UNDISCH_TAC `path_image (P:real^1->real^3) SUBSET O` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `dl = min (m / &100) (rr / &1000)` THEN
  SUBGOAL_THEN `&0 < dl /\ &1000 * dl <= rr /\ &100 * dl <= m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1]
                    ==> ball((P:real^1->real^3) t,&100 * dl) SUBSET O` ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(P:real^1->real^3) t`; `y:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `m:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    SUBGOAL_THEN `(P:real^1->real^3) t IN path_image P` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[path_image] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the half-space balls of radius rr *)
  SUBGOAL_THEN `!y:real^3. y IN ball(a,rr) ==> (y IN x <=> nu dot y <= c)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN ball(a',rr) ==> (y IN w <=> --dd <= --(mu dot y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_NEG2] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^3,rr) SUBSET interior w /\ DISJOINT (ball(a:real^3,rr)) k /\
                DISJOINT (ball(a':real^3,rr)) x /\ DISJOINT (ball(a':real^3,rr)) k`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`ball(a:real^3,rr) SUBSET ball(a,r)`; `ball(a:real^3,r) SUBSET ball(z,e)`;
      `ball(z:real^3,e) SUBSET interior w`; `DISJOINT (ball(z:real^3,e)) k`;
      `ball(a':real^3,rr) SUBSET ball(a',r')`; `ball(a':real^3,r') SUBSET ball(z',e')`;
      `DISJOINT (ball(z':real^3,e')) x`; `DISJOINT (ball(z':real^3,e')) k`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the unit-scale construction at scale dl *)
  MATCH_MP_TAC MOI_TB3_UNIT_SCALED THEN
  MAP_EVERY EXISTS_TAC
   [`a:real^3`; `nu:real^3`; `c:real`; `a':real^3`; `--mu:real^3`; `--dd:real`; `rr:real`;
    `dl:real`; `P:real^1->real^3`] THEN
  ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_LNEG] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let MOI_TB3_TUBE = prove
 (`!x w k (p:real^3) p1 (g:real^1->real^3).
     PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
     pl_ball 3 x /\ pl_ball 3 w /\ x SUBSET interior w /\ closed k /\
     p IN interior x /\ ~(p1 IN w) /\ path g /\ pathstart g = p /\ pathfinish g = p1 /\
     DISJOINT (path_image g) k
     ==> ?n. compact n /\ DISJOINT n k /\ pl_ball 3 (w DIFF interior (x UNION n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `w:real^3->bool`] MOI_TB3_STRAIGHTEN) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `h:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),h)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),h)` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y. (f:real^3->real^3) (h y) = y) /\ (!y. h (f y) = y) /\
                (f:real^3->real^3) continuous_on (:real^3)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism ((:real^3),(:real^3)) ((f:real^3->real^3),h)` THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_TB3_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `h:real^3->real^3`] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_TB3_TUBE_SIMPLEX THEN
  MAP_EVERY EXISTS_TAC [`(f:real^3->real^3) p`; `(f:real^3->real^3) p1`;
                        `(f:real^3->real^3) o (g:real^1->real^3)`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC MOI_TB3_HOMEO_CLOSED THEN EXISTS_TAC `h:real^3->real^3` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL [`f:real^3->real^3`; `h:real^3->real^3`; `x:real^3->bool`]
      MOI_TB3_HOMEO_INTERIOR) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ASM_REWRITE_TAC[PATHSTART_COMPOSE];
    ASM_REWRITE_TAC[PATHFINISH_COMPOSE];
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN
    UNDISCH_TAC `DISJOINT (path_image (g:real^1->real^3)) k` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    ASM_MESON_TAC[]]);;

