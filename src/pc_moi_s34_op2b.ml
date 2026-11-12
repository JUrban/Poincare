(* ========================================================================= *)
(* pc_moi_s34_op2b: Moise GTM 47, Sec 34, p.242, Operation 2 (Fig. 34.1,     *)
(* Lemma 7): the bigon slide at one face s, applied to the face-ball         *)
(* family.  Main theorem OP2 : |- MOI_S34_OP2 (pc_moi_s34_stmt.ml).  The     *)
(* generic slide MOI_S4P_SLIDE is in pc_moi_s34_op2a.  Contents:             *)
(*  two PL 3-balls meeting in a 2-cell of both frontiers;                    *)
(*  generic local lemmas: sides of a cell in a surface, chart segments,      *)
(*      change of surface for curve crossings, maps fixing a set off K;      *)
(*  the op2 witness and its separation facts;                                *)
(*  the open set W0, the ball U2 and the slide data;                         *)
(*  transport of the face-ball clauses under the slide; OP2.                 *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_s34_op1b.ml";;
needs "src/pc_moi_s34_resida.ml";;
needs "src/pc_moi_s35_cells.ml";;
needs "src/pc_moi_s34_op2a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Two PL 3-balls meeting exactly in a 2-cell of both frontiers form a PL    *)
(* 3-ball (from MOI_S5V_CELL_UNION of pc_moi_s35_cells), with its frontier   *)
(* sphere and inside.  The filling lemma is MOI_S5C_FILL_CHAR of             *)
(* pc_moi_s35_minc, which is in this load closure (through op1b).            *)
(* ------------------------------------------------------------------------- *)

(* A PL 3-ball in real^3 is a PL 3-cell with its frontier as boundary. *)

let MOI_S4W_BALL_CELL = prove
 (`!c:real^3->bool. pl_ball 3 c ==> pl_cell_with_boundary 3 c (frontier c)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^3->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^3->real^3` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^3->real^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN EXISTS_TAC `g:real^3->real^3` THEN
  ASM_REWRITE_TAC[]);;

(* Two PL 3-balls meeting in a 2-cell of both frontiers. *)

let MOI_S4W_BALL_UNION = prove
 (`!(c1:real^3->bool) c2 dd jj.
     pl_ball 3 c1 /\ pl_ball 3 c2 /\ c1 INTER c2 = dd /\ pl_cell_with_boundary 2 dd jj /\
     dd SUBSET frontier c1 /\ dd SUBSET frontier c2
     ==> pl_ball 3 (c1 UNION c2) /\
         frontier (c1 UNION c2) = (frontier c1 UNION frontier c2) DIFF (dd DIFF jj) /\
         pl_sphere 2 (frontier (c1 UNION c2)) /\
         interior (c1 UNION c2) = inside (frontier (c1 UNION c2)) /\
         frontier (c1 UNION c2) UNION inside (frontier (c1 UNION c2)) = c1 UNION c2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c1:real^3->bool`; `frontier c1:real^3->bool`; `c2:real^3->bool`;
                 `frontier c2:real^3->bool`; `dd:real^3->bool`; `jj:real^3->bool`]
                MOI_S5V_CELL_UNION) THEN
  ASM_SIMP_TAC[MOI_S4W_BALL_CELL] THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `u = c1 UNION c2:real^3->bool` THEN
  SUBGOAL_THEN `pl_ball 3 (u:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[pl_ball] THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (relative_frontier k) = frontier u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN EXISTS_TAC `g:real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (frontier u:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_BALL_BOUNDARY_PLH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior u:real^3->bool = {})` ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `b:real^3` o MATCH_MP MOI_FN1_SIMPLEX_3_INTERIOR) THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `u:real^3->bool`; `f:real^3->real^3`;
                   `g:real^3->real^3`] MOI_FN1_HOMEOMORPHISM_INTERIOR) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier u:real^3->bool`; `u:real^3->bool`] MOI_S5C_FILL_CHAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; DIMINDEX_3; ARITH] THEN
    ASM_MESON_TAC[MOI_SCD_PL_BALL_FACTS];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Generic local lemmas.  A connected set off the boundary of               *)
(* a cell that meets its interior lies in it; a curve crossing at a point  *)
(* of the closure of the open cell, with the crossing curves missing the   *)
(* open cell, is impossible (a chart segment parallel to one axis);        *)
(* change of the ambient surface of a curve crossing; maps that fix the    *)
(* complement of a compact set; transport of crossings, components and of *)
(* H_1-carrying under homeomorphisms.                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_S4W_SIDE = prove
 (`!(m:real^N->bool) d j q.
     closed d /\ open_in (subtopology euclidean m) (d DIFF j) /\
     connected q /\ q SUBSET m /\ q INTER j = {} /\ ~(q INTER (d DIFF j) = {})
     ==> q SUBSET d DIFF j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `open_in (subtopology euclidean m) (d DIFF j:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `connected (q:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `q INTER d:real^N->bool`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `q INTER d = q INTER (oo:real^N->bool)` SUBST1_TAC THENL
       [ASM SET_TAC[]; MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]];
    ASM SET_TAC[]]);;

(* A curve crossing in a surface m at a point x of the closure of an open  *)
(* cell d DIFF j, where both curves miss d DIFF j and j is in the second  *)
(* curve near x, is impossible: from a point y of d DIFF j near x the     *)
(* chart segment parallel to the first axis runs to the first curve       *)
(* without meeting the second curve, so it stays in d DIFF j.               *)

let MOI_S4W_QUAD_CONTRA = prove
 (`!(m:real^N->bool) tr rr (x:real^N) d j n.
     pl_curve_crossing_at m tr rr x /\ d SUBSET m /\ closed d /\
     open_in (subtopology euclidean m) (d DIFF j) /\ x IN closure (d DIFF j) /\
     DISJOINT (d DIFF j) tr /\ DISJOINT (d DIFF j) rr /\
     open n /\ x IN n /\ j INTER n SUBSET rr
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^2`
      (X_CHOOSE_THEN `g:real^2->real^N` STRIP_ASSUME_TAC)) o
     REWRITE_RULE[pl_curve_crossing_at; pl_homeomorphism; homeomorphism])
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET m` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP OPEN_IN_IMP_SUBSET); ALL_TAC] THEN
  (* a ball around 0 in the chart image, mapped into n *)
  SUBGOAL_THEN `?r. &0 < r /\ ball(vec 0:real^2,r) SUBSET IMAGE (f:real^N->real^2) u /\
                    (!y. y IN ball(vec 0,r) ==> (g:real^2->real^N) y IN n)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^2->real^N`; `IMAGE (f:real^N->real^2) u`; `n:real^N->bool`]
      CONTINUOUS_OPEN_PREIMAGE) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(g:real^2->real^N) (vec 0) = x` (fun th -> ASM_REWRITE_TAC[th]) THEN
        SUBGOAL_THEN `(g:real^2->real^N) ((f:real^N->real^2) x) = x` MP_TAC THENL
         [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]]];
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(vec 0:real^2,r) SUBSET
                   {y | y IN IMAGE (f:real^N->real^2) u /\ (g:real^2->real^N) y IN n}` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the chart preimage of the ball is a neighbourhood of x in m *)
  SUBGOAL_THEN `open_in (subtopology euclidean m)
                  {z | z IN u /\ (f:real^N->real^2) z IN ball(vec 0,r)}`
  MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `o2:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN o2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^N) IN {z | z IN u /\ (f:real^N->real^2) z IN ball(vec 0,r)}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]; ASM SET_TAC[]];
    ALL_TAC] THEN
  (* a point y of d DIFF j near x *)
  SUBGOAL_THEN `?y:real^N. y IN d DIFF j /\ y IN o2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`o2:real^N->bool`; `d DIFF j:real^N->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN u /\ (f:real^N->real^2) y IN ball(vec 0,r)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^N) IN m INTER o2` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `{z | z IN u /\ (f:real^N->real^2) z IN ball(vec 0,r)} = m INTER o2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  (* membership of chart points in the two curves *)
  SUBGOAL_THEN `!z:real^2. z IN IMAGE (f:real^N->real^2) u
                           ==> ((g:real^2->real^N) z IN tr <=> z$1 = &0) /\
                               (g z IN rr <=> z$2 = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^2->real^N) z IN u /\ (f:real^N->real^2) (g z) = z`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [EQ_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `(z:real^2) IN IMAGE (f:real^N->real^2) (tr INTER u)` MP_TAC THENL
         [UNDISCH_TAC `(f:real^N->real^2) (g z) = z` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          ASM_REWRITE_TAC[IN_INTER];
          ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
        DISCH_TAC THEN
        SUBGOAL_THEN `(z:real^2) IN IMAGE (f:real^N->real^2) (tr INTER u)` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
        DISCH_THEN(X_CHOOSE_THEN `t:real^N` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(g:real^2->real^N) z = t` (fun th -> ASM_REWRITE_TAC[th]) THEN
        ASM_SIMP_TAC[]];
      EQ_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `(z:real^2) IN IMAGE (f:real^N->real^2) (rr INTER u)` MP_TAC THENL
         [UNDISCH_TAC `(f:real^N->real^2) (g z) = z` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          ASM_REWRITE_TAC[IN_INTER];
          ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
        DISCH_TAC THEN
        SUBGOAL_THEN `(z:real^2) IN IMAGE (f:real^N->real^2) (rr INTER u)` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
        DISCH_THEN(X_CHOOSE_THEN `t:real^N` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(g:real^2->real^N) z = t` (fun th -> ASM_REWRITE_TAC[th]) THEN
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `p0 = (f:real^N->real^2) y` THEN
  SUBGOAL_THEN `(g:real^2->real^N) p0 = y` ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p0:real^2) IN IMAGE (f:real^N->real^2) u` ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((p0:real^2)$1 = &0) /\ ~(p0$2 = &0)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o
      C MP (ASSUME `(p0:real^2) IN IMAGE (f:real^N->real^2) u`) o SPEC `p0:real^2` o
      check (fun th -> is_forall (concl th) &&
                       can (find_term (fun t -> t = `rr:real^N->bool`)) (concl th) &&
                       can (find_term (fun t -> t = `tr:real^N->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the chart segment from p0 to the first axis *)
  ABBREV_TAC `z0:real^2 = vector[&0; (p0:real^2)$2]` THEN
  SUBGOAL_THEN `(z0:real^2)$1 = &0 /\ z0$2 = (p0:real^2)$2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN REWRITE_TAC[VECTOR_2]; ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^2) IN ball(vec 0,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `(p0:real^2) IN ball(vec 0,r)` THEN
    REWRITE_TAC[IN_BALL_0] THEN MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < r ==> a < r`) THEN
    REWRITE_TAC[NORM_LE; DOT_2] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `(p0:real^2)$1` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p0:real^2,z0] SUBSET ball(vec 0,r)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`vec 0:real^2`; `r:real`] CONVEX_BALL) THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN segment[p0,z0] ==> z$2 = (p0:real^2)$2` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^N) (segment[p0,z0]) SUBSET d DIFF j` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4W_SIDE THEN EXISTS_TAC `m:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (f:real^N->real^2) u` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^2->real^N) (IMAGE (f:real^N->real^2) u)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ASM SET_TAC[]];
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `w:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^2) IN IMAGE (f:real^N->real^2) u /\ (g:real^2->real^N) z IN n`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^2->real^N) z IN rr` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o
        check (fun th -> is_forall (concl th) &&
                         can (find_term (fun t -> t = `rr:real^N->bool`)) (concl th) &&
                         can (find_term (fun t -> t = `tr:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_IMAGE] THEN EXISTS_TAC `p0:real^2` THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  (* the end g z0 lies on the first curve and in d DIFF j *)
  SUBGOAL_THEN `(g:real^2->real^N) z0 IN tr` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z0:real^2) IN IMAGE (f:real^N->real^2) u` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) z0 IN d DIFF j` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^2->real^N) (segment[p0,z0]) SUBSET d DIFF j` THEN
    MP_TAC(ISPECL [`p0:real^2`; `z0:real^2`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* Change of the ambient surface of a curve crossing (the surfaces agree   *)
(* on an open set around the point).                                        *)

let MOI_S4W_CROSS_SURF = prove
 (`!(m:real^N->bool) m' j k x w.
     pl_curve_crossing_at m j k x /\ open w /\ x IN w /\ m INTER w = m' INTER w
     ==> pl_curve_crossing_at m' j k x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_curve_crossing_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `f:real^N->real^2` (X_CHOOSE_THEN `g:real^2->real^N`
      STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET m` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP OPEN_IN_IMP_SUBSET); ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `u:real^N->bool`; `m INTER w:real^N->bool`;
                 `f:real^N->real^2`; `g:real^2->real^N`] MOI_FGB_CHART_RESTRICT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_IN_OPEN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `u INTER (m INTER w) = u INTER (w:real^N->bool)` SUBST1_TAC THENL
   [UNDISCH_TAC `(u:real^N->bool) SUBSET m` THEN SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!a b:real^N. a IN u /\ b IN u /\ (f:real^N->real^2) a = f b ==> a = b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,IMAGE f u) ((f:real^N->real^2),(g:real^2->real^N))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^2) (u INTER w) SUBSET IMAGE f u` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u INTER w:real^N->bool`; `f:real^N->real^2`;
                        `g:real^2->real^N`] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean m) (u:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `o1 INTER w:real^N->bool` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER]; ALL_TAC] THEN
    UNDISCH_TAC `(m:real^N->bool) INTER w = m' INTER w` THEN
    UNDISCH_TAC `(u:real^N->bool) = m INTER o1` THEN SET_TAC[];
    SUBGOAL_THEN `j INTER u INTER w = (j INTER u) INTER (u INTER w:real^N->bool)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^N->real^2`; `j INTER u:real^N->bool`;
                   `u INTER w:real^N->bool`; `u:real^N->bool`]
      MOI_FGB_INJ_IMAGE_INTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INTER_SUBSET]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^2) (u INTER w) SUBSET IMAGE f u` THEN
    SET_TAC[];
    SUBGOAL_THEN `k INTER u INTER w = (k INTER u) INTER (u INTER w:real^N->bool)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^N->real^2`; `k INTER u:real^N->bool`;
                   `u INTER w:real^N->bool`; `u:real^N->bool`]
      MOI_FGB_INJ_IMAGE_INTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INTER_SUBSET]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^2) (u INTER w) SUBSET IMAGE f u` THEN
    SET_TAC[]]);;

(* A map that is the identity off K and maps K onto K preserves every set  *)
(* that agrees near K with a preserved set.                                 *)

let MOI_S4W_FIX_LOCAL = prove
 (`!(phi:real^N->real^N) kk w x y.
     (!z. ~(z IN kk) ==> phi z = z) /\ IMAGE phi kk = kk /\ kk SUBSET w /\
     IMAGE phi x = x /\ y INTER w = x INTER w
     ==> IMAGE phi y = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^N` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(t:real^N) IN kk` THENL
     [SUBGOAL_THEN `(t:real^N) IN x` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(phi:real^N->real^N) t IN x /\ phi t IN kk` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    DISCH_TAC THEN ASM_CASES_TAC `(z:real^N) IN kk` THENL
     [SUBGOAL_THEN `?t:real^N. t IN x /\ (phi:real^N->real^N) t = z` STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `(z:real^N) IN x` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `IMAGE (phi:real^N->real^N) x = x` THEN SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `t:real^N` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(t:real^N) IN kk` THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      EXISTS_TAC `z:real^N` THEN ASM_MESON_TAC[]]]);;

(* PL homeomorphisms of real^N: inverse laws and images of closures,       *)
(* interiors and frontiers.                                                  *)

let MOI_S4W_PLH_FACTS = prove
 (`!(f:real^N->real^N) g.
     pl_homeomorphism ((:real^N),(:real^N)) (f,g)
     ==> (!x. g(f x) = x) /\ (!y. f(g y) = y) /\
         (!s. closure(IMAGE f s) = IMAGE f (closure s)) /\
         (!s. interior(IMAGE f s) = IMAGE f (interior s)) /\
         (!s. frontier(IMAGE f s) = IMAGE f (frontier s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!x. (g:real^N->real^N) ((f:real^N->real^N) x) = x) /\ (!y. f(g y) = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism ((:real^N),(:real^N)) ((f:real^N->real^N),g)` THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. closure(IMAGE (f:real^N->real^N) s) = IMAGE f (closure s)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`; `(:real^N)`; `(:real^N)`;
                   `s:real^N->bool`] HOMEOMORPHISM_CLOSURE) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; INTER_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. interior(IMAGE (f:real^N->real^N) s) = IMAGE f (interior s)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`; `(:real^N)`; `(:real^N)`;
                   `s:real^N->bool`] HOMEOMORPHISM_INTERIOR_OF) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; SUBTOPOLOGY_UNIV; EUCLIDEAN_INTERIOR_OF] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[frontier] THEN GEN_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y. (f:real^N->real^N) x = f y ==> x = y)
    ==> IMAGE f a DIFF IMAGE f b = IMAGE f (a DIFF b)`) THEN
  ASM_MESON_TAC[]);;

(* Transport of a 3D crossing chart by a PL homeomorphism of real^3. *)

let MOI_S4W_CROSS3_IMAGE = prove
 (`!(phi:real^3->real^3) phi' s t x.
     pl_homeomorphism ((:real^3),(:real^3)) (phi,phi') /\ pl_crossing_at s t x
     ==> pl_crossing_at (IMAGE phi s) (IMAGE phi t) (phi x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^3->bool`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_PLH_FACTS) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `phi':real^3->real^3`; `u:real^3->bool`]
    MOI_S4P_PLH_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (phi':real^3->real^3) (IMAGE phi u) = u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (phi:real^3->real^3) u`;
                        `(f:real^3->real^3) o (phi':real^3->real^3)`;
                        `(phi:real^3->real^3) o (g:real^3->real^3)`] THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `IMAGE (phi':real^3->real^3) (IMAGE phi s INTER IMAGE phi u) = s INTER u`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. (h:real^3->real^3) ((k:real^3->real^3) x) = x) /\
        (!x y. k x = k y ==> x = y)
        ==> IMAGE h (IMAGE k a INTER IMAGE k b) = a INTER b`) THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (phi':real^3->real^3) (IMAGE phi t INTER IMAGE phi u) = t INTER u`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. (h:real^3->real^3) ((k:real^3->real^3) x) = x) /\
        (!x y. k x = k y ==> x = y)
        ==> IMAGE h (IMAGE k a INTER IMAGE k b) = a INTER b`) THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* Components of a homeomorphic image. *)

let MOI_S4W_COMPONENTS_HOMEO = prove
 (`!(f:real^M->real^N) g s t.
     homeomorphism (s,t) (f,g)
     ==> components t = IMAGE (IMAGE f) (components s) /\
         (FINITE (components s) ==> CARD (components t) = CARD (components s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `components t = IMAGE (IMAGE (f:real^M->real^N)) (components s)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[components; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `c:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(g:real^N->real^M) y IN s` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `connected_component s ((g:real^N->real^M) y)` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^M`; `s:real^M->bool`;
                       `t:real^N->bool`; `(g:real^N->real^M) y`]
          HOMEOMORPHISM_CONNECTED_COMPONENT) THEN
        ASM_SIMP_TAC[];
        EXISTS_TAC `(g:real^N->real^M) y` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `(f:real^M->real^N) x` THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^M`; `s:real^M->bool`;
                     `t:real^N->bool`; `x:real^M`]
        HOMEOMORPHISM_CONNECTED_COMPONENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c1:real^M->bool`; `c2:real^M->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c1:real^M->bool) SUBSET s /\ (c2:real^M->bool) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^M->bool. c SUBSET s ==> IMAGE (g:real^N->real^M) (IMAGE f c) = c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* H_1-carrying is preserved by a self-homeomorphism of the carrier space. *)

let MOI_S4W_CARRIES_HOMEO = prove
 (`!(f:real^N->real^N) f' j t.
     carries_h1 j t /\ homeomorphism (t,t) (f,f') /\ j SUBSET t
     ==> carries_h1 (IMAGE f j) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[carries_h1] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) j SUBSET t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `X = subtopology euclidean (j:real^N->bool)` THEN
  ABBREV_TAC `X' = subtopology euclidean (IMAGE (f:real^N->real^N) j)` THEN
  ABBREV_TAC `Tt = subtopology euclidean (t:real^N->bool)` THEN
  SUBGOAL_THEN `continuous_map (X,Tt) (\x:real^N. x)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Tt"] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; CONTINUOUS_ON_ID; IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (X',Tt) (\x:real^N. x)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X'"; "Tt"] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; CONTINUOUS_ON_ID; IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (X,X') (f:real^N->real^N)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "X'"] THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; SUBSET_REFL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (Tt,Tt) (f:real^N->real^N) /\
                continuous_map (Tt,Tt) (f':real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Tt" THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `topspace Tt = (t:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Tt" THEN REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  (* the two factorizations of f restricted to j *)
  SUBGOAL_THEN
   `hom_induced (&1) (X',{}) (Tt,{}) (\x:real^N. x) o hom_induced (&1) (X,{}) (X',{}) f =
    hom_induced (&1) (Tt,{}) (Tt,{}) (f:real^N->real^N) o
    hom_induced (&1) (X,{}) (Tt,{}) (\x:real^N. x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `X:(real^N)topology`; `X':(real^N)topology`;
                   `Tt:(real^N)topology`; `f:real^N->real^N`; `\x:real^N. x`]
      HOM_INDUCED_COMPOSE_EMPTY) THEN
    MP_TAC(ISPECL [`&1:int`; `X:(real^N)topology`; `Tt:(real^N)topology`;
                   `Tt:(real^N)topology`; `\x:real^N. x`; `f:real^N->real^N`]
      HOM_INDUCED_COMPOSE_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x:real^N. x) o (f:real^N->real^N) = f /\ f o (\x:real^N. x) = f`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (Tt,Tt) ((f:real^N->real^N) o (f':real^N->real^N)) /\
                (!x. x IN topspace Tt ==> (f o f') x = x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `Tt:(real^N)topology` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[o_THM]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[group_image; SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,X':(real^N)topology)` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `c:((num->real)->real^N)frag->bool` THEN DISCH_TAC THEN
  ABBREV_TAC `c' = hom_induced (&1) (Tt,{}) (Tt,{}) (f':real^N->real^N) c` THEN
  SUBGOAL_THEN `c' IN group_carrier (homology_group(&1,Tt:(real^N)topology))` ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,Tt:(real^N)topology)` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `hom_induced (&1) (Tt,{}) (Tt,{}) (f:real^N->real^N) c' = c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `Tt:(real^N)topology`; `Tt:(real^N)topology`;
                   `Tt:(real^N)topology`; `f':real^N->real^N`; `f:real^N->real^N`]
      HOM_INDUCED_COMPOSE_EMPTY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C AP_THM `c:((num->real)->real^N)frag->bool`) THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HOM_INDUCED_ID_GEN THEN
    ASM_REWRITE_TAC[GSYM homology_group];
    ALL_TAC] THEN
  SUBGOAL_THEN `c' IN group_image (homology_group(&1,X:(real^N)topology),
                                   homology_group(&1,Tt:(real^N)topology))
                                  (hom_induced (&1) (X,{}) (Tt,{}) (\x:real^N. x))`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[group_image; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:((num->real)->real^N)frag->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `hom_induced (&1) (X,{}) (X',{}) (f:real^N->real^N) w` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C AP_THM `w:((num->real)->real^N)frag->bool` o
      check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
                       can (find_term (fun t -> t = `X':(real^N)topology`)) (lhs (concl th)))) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `hom_induced (&1) (Tt,{}) (Tt,{}) (f:real^N->real^N) c' = c` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,X:(real^N)topology)` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]]);;

(* A PL homeomorphism of real^3 maps PL 3-balls to PL 3-balls. *)

let MOI_S4W_BALL_IMAGE = prove
 (`!(phi:real^3->real^3) phi' c.
     pl_homeomorphism ((:real^3),(:real^3)) (phi,phi') /\ pl_ball 3 c
     ==> pl_ball 3 (IMAGE phi c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `phi:real^3->real^3`; `phi':real^3->real^3`; `(:real^3)`;
                 `(:real^3)`; `c:real^3->bool`; `frontier c:real^3->bool`]
    MOI_S4N_CELL_IMAGE) THEN
  ASM_SIMP_TAC[SUBSET_UNIV; MOI_S4W_BALL_CELL] THEN
  REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The op2 witness and its separation facts.  moi_s4w_ctx is                *)
(* the hypothesis of OP2 with the witness of moi_s34_op2 (j replaced by     *)
(* a UNION a'); moi_s4w_ctx2 adds the other end w of the edge g.  A disk   *)
(* in A_v has no interior point on a rim, and its interior is open in      *)
(* F = f1(Bd N).                                                             *)
(* ------------------------------------------------------------------------- *)

let moi_s4w_ctx = new_definition
 `moi_s4w_ctx (tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep (f1:real^N->real^3)
              car (cb:(real^N->bool)->real^3->bool) (s:real^N->bool) (v:real^N)
              (g:real^N->bool) (a:real^3->bool) a' aa d <=>
   moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
   moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
   s IN moi_s34_simp kk (&2) /\
   {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
   pl_cell_with_boundary 1 a aa /\ a SUBSET frontier (cb s) /\
   a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
   aa SUBSET IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) /\
   a INTER moi_s34_rims tt kk f1 = aa /\
   pl_cell_with_boundary 1 a' aa /\
   a' SUBSET IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) /\
   a INTER a' = aa /\
   pl_cell_with_boundary 2 d (a UNION a') /\
   d SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
   (!s'. s' IN moi_s34_simp kk (&2)
         ==> DISJOINT (d DIFF (a UNION a')) (frontier (cb s')))`;;

let moi_s4w_ctx2 = new_definition
 `moi_s4w_ctx2 (tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep (f1:real^N->real^3)
               car (cb:(real^N->bool)->real^3->bool) (s:real^N->bool) (v:real^N)
               (w:real^N) (g:real^N->bool) (a:real^3->bool) a' aa d <=>
   moi_s4w_ctx tt kk h ep f1 car cb s v g a a' aa d /\
   ~(w = v) /\ {w} IN kk /\ segment[v,w] = g /\
   moi_s34_vb tt kk v INTER moi_s34_vb tt kk w = moi_s34_sd tt kk g /\
   v IN s /\ w IN s`;;

(* The other end w of g; both ends lie in s. *)

let MOI_S4W_STRUCT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v g a a' aa d.
     moi_s4w_ctx tt kk h ep f1 car cb s v g a a' aa d
     ==> ?w. moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s4w_ctx2] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4w_ctx]) THEN
  SUBGOAL_THEN `~(aa:real^3->bool = {}) /\ aa SUBSET a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(MATCH_MP MOI_S4L_CELL1_PL_ARC
        (ASSUME `pl_cell_with_boundary 1 (a:real^3->bool) aa`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
    IMAGE f1 (moi_s34_sd tt kk g) /\
    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
    IMAGE f1 (moi_s34_vb tt kk v)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  (* v is a vertex of g *)
  SUBGOAL_THEN `(v:real^N) IN g` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_IMAGES
      (CONJ (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)
            (ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`))) THEN
    DISCH_THEN(MP_TAC o SPECL [`g:real^N->bool`; `v:real^N`] o CONJUNCT1 o
               funpow 5 CONJUNCT2) THEN
    ASM_CASES_TAC `(v:real^N) IN g` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(aa:real^3->bool = {})` THEN REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the other end *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                 `v:real^N`] MOI_S4B_SD_PAIR) THEN
  ASM_REWRITE_TAC[MOI_S4L_SKEL_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `w:real^N`] MOI_S4L_EDGE_SD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y:real^N. y IN moi_s34_sd tt kk g` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(aa:real^3->bool = {})` THEN
    UNDISCH_TAC `(aa:real^3->bool) SUBSET
                 IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] = g` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4B_SD_UNIQ THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* both ends lie in s, by the avoidance clause of fb1 *)
  SUBGOAL_THEN `moi_s34_fb1 tt kk h f1 car s ((cb:(real^N->bool)->real^3->bool) s)`
  MP_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
    REWRITE_TAC[moi_s34_fbinv] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4YC_BALL_DIFF_FRONTIER]; ALL_TAC] THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_CASES_TAC `(v:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o
      check (fun th -> is_forall (concl th) &&
                       can (find_term (fun t -> t = `DISJOINT:(real^3->bool)->(real^3->bool)->bool`))
                           (concl th) &&
                       not (can (find_term (fun t -> t = `s':real^N->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(aa:real^3->bool = {})` THEN ASM SET_TAC[];
    ASM_CASES_TAC `(w:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o
      check (fun th -> is_forall (concl th) &&
                       can (find_term (fun t -> t = `DISJOINT:(real^3->bool)->(real^3->bool)->bool`))
                           (concl th) &&
                       not (can (find_term (fun t -> t = `s':real^N->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET
                  IMAGE f1 (moi_s34_vb tt kk w)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `~(aa:real^3->bool = {})` THEN ASM SET_TAC[]]);;

(* A disk d in A_v: its interior misses the rims. *)

let MOI_S4W_DJ_RIMS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v d j.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     pl_cell_with_boundary 2 d j /\
     d SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
     ==> DISJOINT (d DIFF j) (moi_s34_rims tt kk f1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_ball 3 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) /\
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                SUBSET frontier (IMAGE f1 (moi_s34_vb tt kk v))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_vb tt kk v SUBSET moi_s34_nb tt kk /\
                moi_s34_bd tt kk SUBSET moi_s34_nb tt (kk:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4K_NB_UNION_CELLS; MOI_S4K_VB_CELL]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4L_IMAGES
    (CONJ (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)
          (ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`))) THEN
  STRIP_TAC THEN
  (* x lies in another vertex ball *)
  SUBGOAL_THEN `?u:real^N. {u} IN kk /\ ~(u = v) /\
                           x IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)` THEN
    REWRITE_TAC[moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
      MOI_S4L_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u1) /\
                  x IN IMAGE f1 (moi_s34_vb tt kk u2)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN r` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `u1:real^N = v` THENL
     [EXISTS_TAC `u2:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      EXISTS_TAC `u1:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `u:real^N`; `x:real^3`]
    MOI_S4L_AV_NO_OTHER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN d DIFF j`;
      `(d:real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
    SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `u:real^N`] MOI_S4L_EDGE_SD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the splitting disk D of segment[v,u] and its rim R *)
  SUBGOAL_THEN `pl_cell_with_boundary 2
                  (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u))
                  (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u INTER
                             moi_s34_bd tt kk))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `segment[v:real^N,u]` o CONJUNCT1 o funpow 7 CONJUNCT2) THEN
    ASM_REWRITE_TAC[INTER_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u)
                SUBSET frontier (IMAGE f1 (moi_s34_vb tt kk v))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o last o CONJUNCTS) THEN
    MATCH_MP_TAC(SET_RULE `!t. (a:real^3->bool) SUBSET t /\ t IN f
                                ==> a SUBSET c UNION UNIONS f`) THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,u]))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `segment[v:real^N,u]` THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u) INTER
                IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
                IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_s34_vb tt kk v INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk =
                  (moi_s34_vb tt kk v INTER moi_s34_vb tt kk (u:real^N)) INTER
                  (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `moi_s34_vb tt kk (u:real^N) SUBSET moi_s34_nb tt kk` MP_TAC THENL
     [ASM_MESON_TAC[MOI_S4K_VB_CELL]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`moi_s34_vb tt kk v SUBSET moi_s34_nb tt (kk:(real^N->bool)->bool)`;
      `moi_s34_bd tt kk SUBSET moi_s34_nb tt (kk:(real^N->bool)->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* a neighbourhood of x in the sphere frontier f1(C_v) inside d DIFF j *)
  SUBGOAL_THEN `(d:real^3->bool) SUBSET frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?oo. open oo /\ (x:real^3) IN oo /\
                     frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) INTER oo
                     SUBSET d DIFF j`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4YC_CELL2_OPEN THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4YC_BALL_BD_CHART THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MAP_EVERY UNDISCH_TAC
         [`(d:real^3->bool) SUBSET
           frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
          `(x:real^3) IN d DIFF j`] THEN SET_TAC[]];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u)` THEN
  ABBREV_TAC `R = IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `Av = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `Sv = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
  MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
    (ASSUME `pl_cell_with_boundary 2 (D:real^3->bool) R`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN closure (D DIFF R)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN R`; `(R:real^3->bool) SUBSET D`;
      `(D:real^3->bool) SUBSET closure (D DIFF R)`] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`oo:real^3->bool`; `D DIFF R:real^3->bool`]
    OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`(x:real^3) IN oo`; `(x:real^3) IN closure (D DIFF R)`;
    `(D:real^3->bool) SUBSET Sv`; `Sv INTER oo SUBSET (d:real^3->bool) DIFF j`;
    `(d:real^3->bool) SUBSET Av`; `(D:real^3->bool) INTER Av = R`] THEN
  SET_TAC[]);;

(* ... and is open in F. *)

let MOI_S4W_DJ_OPEN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v d j.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     pl_cell_with_boundary 2 d j /\
     d SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
     ==> open_in (subtopology euclidean (IMAGE f1 (moi_s34_bd tt kk))) (d DIFF j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `d:real^3->bool`;
                 `j:real^3->bool`] MOI_S4W_DJ_RIMS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_ball 3 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) /\
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                SUBSET frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                SUBSET IMAGE f1 (moi_s34_vb tt kk v) /\
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                SUBSET IMAGE f1 (moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_UNION] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  (* y is in no other vertex ball *)
  SUBGOAL_THEN `!w. {w} IN kk /\ ~(w = v)
                    ==> ~((y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`; `y:real^3`]
      MOI_S4L_AV_NO_OTHER) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3) IN d DIFF j`;
      `(d:real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
      `DISJOINT ((d:real^3->bool) DIFF j) (moi_s34_rims tt kk (f1:real^N->real^3))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `y:real^3`]
    MOI_S4L_LOCAL_AV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3) IN d DIFF j`;
      `(d:real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
       SUBSET IMAGE f1 (moi_s34_vb tt kk v)`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `o1:real^3->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `?o2. open o2 /\ (y:real^3) IN o2 /\
                     frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) INTER o2
                     SUBSET d DIFF j`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4YC_CELL2_OPEN THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4YC_BALL_BD_CHART THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MAP_EVERY UNDISCH_TAC
         [`(d:real^3->bool) SUBSET
           frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
          `(y:real^3) IN d DIFF j`] THEN SET_TAC[]];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER (o1 INTER o2)` THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_INTER] THEN
  MAP_EVERY UNDISCH_TAC
   [`(y:real^3) IN d DIFF j`; `(y:real^3) IN o1`; `(y:real^3) IN o2`;
    `(d:real^3->bool) SUBSET
     IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
     SUBSET IMAGE f1 (moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
     SUBSET frontier (IMAGE f1 (moi_s34_vb tt kk v))`;
    `frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) INTER o2
     SUBSET d DIFF j`;
    `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER o1 SUBSET
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The separation facts for an op2 witness.                                  *)
(* SEP_A: the interior of d misses the rims and is open in F;                *)
(* d meets the rims, and R_g, exactly in a'; d misses the vertex balls of  *)
(* the vertices other than v, w.  SEP_B: no face-ball frontier meets       *)
(* a' DIFF aa (QUAD_CONTRA at a crossing with R_g).  SEP_C: frontier C     *)
(* meets d exactly in a, and d misses the other face balls.  SEP_D: the   *)
(* trace and the rim do not accumulate at the interior points of a, a'.  *)
(* ------------------------------------------------------------------------- *)

(* Unfold the context assumption moi_s4w_ctx2 (selected by its constant). *)

let MOI_S4W_UNFOLD_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4w_ctx2; moi_s4w_ctx] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "moi_s4w_ctx2"
                     with Failure _ -> false));;

let MOI_S4W_CTX_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d
     ==> compact a /\ connected a /\ ~(aa = {}) /\ aa SUBSET a /\ aa SUBSET a' /\
         compact d /\ a SUBSET d /\ a' SUBSET d /\
         d SUBSET closure (d DIFF (a UNION a')) /\
         connected (d DIFF (a UNION a')) /\
         d SUBSET IMAGE f1 (moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
         moi_s34_rims tt kk f1 /\
         IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
         IMAGE f1 (moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
         IMAGE f1 (moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_bd tt kk) INTER interior (IMAGE f1 (moi_s34_nb tt kk)) = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4w_ctx2; moi_s4w_ctx] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
    (ASSUME `pl_cell_with_boundary 2 (d:real^3->bool) (a UNION a')`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4L_FRAME_F1
    (ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `compact (a:real^3->bool) /\ connected a /\ ~(aa:real^3->bool = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_CELL1_PL_ARC
      (ASSUME `pl_cell_with_boundary 1 (a:real^3->bool) aa`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    UNDISCH_TAC `path_image (p:real^1->real^3) = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(MATCH_MP ARC_IMP_PATH (ASSUME `arc (p:real^1->real^3)`)) THEN
    SIMP_TAC[COMPACT_PATH_IMAGE; CONNECTED_PATH_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aa:real^3->bool) SUBSET a /\ aa SUBSET a'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^3->bool) INTER a' = aa` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET d /\ a' SUBSET d` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^3->bool) UNION a' SUBSET d` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
                moi_s34_rims tt kk f1` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_rims] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
                IMAGE f1 (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The interior of d and the rims; the other vertex balls. *)

let MOI_S4W_SEP_A = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d
     ==> DISJOINT (d DIFF (a UNION a')) (moi_s34_rims tt kk f1) /\
         open_in (subtopology euclidean (IMAGE f1 (moi_s34_bd tt kk)))
                 (d DIFF (a UNION a')) /\
         d INTER moi_s34_rims tt kk f1 = a' /\
         d INTER IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) = a' /\
         (!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
              ==> DISJOINT d (IMAGE f1 (moi_s34_vb tt kk u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_CTX_FACTS) THEN
  MOI_S4W_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `d:real^3->bool`;
                 `a UNION a':real^3->bool`] MOI_S4W_DJ_RIMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `d:real^3->bool`;
                 `a UNION a':real^3->bool`] MOI_S4W_DJ_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(d:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = a'`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`DISJOINT ((d:real^3->bool) DIFF (a UNION a')) (moi_s34_rims tt kk (f1:real^N->real^3))`;
      `(a:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = aa`;
      `(aa:real^3->bool) SUBSET a'`; `(a':real^3->bool) SUBSET d`;
      `(a':real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
       moi_s34_rims tt kk f1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(d:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = a'`;
      `(a':real^3->bool) SUBSET d`;
      `(a':real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
       moi_s34_rims tt kk f1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `u:real^N`; `x:real^3`]
    MOI_S4L_AV_NO_OTHER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN d`;
      `(d:real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
    SET_TAC[];
    STRIP_TAC] THEN
  (* x is on a' inside R_g, so in the vertex balls of v, w and u *)
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) /\
                x IN IMAGE f1 (moi_s34_vb tt kk w) /\
                x IN IMAGE f1 (moi_s34_vb tt kk u)` MP_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN
                  IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`
    MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN d`; `(x:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)`;
        `(d:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = a'`;
        `(a':real^3->bool) SUBSET
         IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
      IMAGE f1 (moi_s34_vb tt kk v) /\
      IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
      IMAGE f1 (moi_s34_vb tt kk w)` MP_TAC THENL
     [UNDISCH_TAC `moi_s34_vb tt kk v INTER moi_s34_vb tt kk w =
                   moi_s34_sd tt kk (g:real^N->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4L_IMAGES
    (CONJ (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)
          (ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`))) THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `w:real^N`; `u:real^N`] o CONJUNCT1 o
             funpow 3 CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`~(w:real^N = v)`; `~(u:real^N = v)`; `~(u:real^N = w)`] THEN
    MESON_TAC[];
    SET_TAC[]]);;

(* No face-ball frontier meets a' DIFF aa. *)

let MOI_S4W_SEP_B = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d s'.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d /\ s' IN moi_s34_simp kk (&2)
     ==> DISJOINT (a' DIFF aa) (frontier (cb s'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SEP_A) THEN
  MOI_S4W_UNFOLD_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_fb1 tt kk h f1 car s' ((cb:(real^N->bool)->real^3->bool) s')`
  MP_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
    REWRITE_TAC[moi_s34_fbinv] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s34_fb1] THEN
  DISCH_THEN(MP_TAC o SPECL [`g:real^N->bool`; `x:real^3`] o CONJUNCT1 o
             funpow 5 CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN a' DIFF aa`;
      `(a':real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`] THEN
    SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
    `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s')`;
    `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
    `x:real^3`; `d:real^3->bool`; `a UNION a':real^3->bool`;
    `(:real^3) DIFF a`] MOI_S4W_QUAD_CONTRA) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; OPEN_DIFF; OPEN_UNIV] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN a' DIFF aa`; `(a':real^3->bool) SUBSET d`;
      `(d:real^3->bool) SUBSET closure (d DIFF (a UNION a'))`] THEN
    SET_TAC[];
    MATCH_MP_TAC(SET_RULE `!f. DISJOINT (s:real^3->bool) f /\ t SUBSET f ==> DISJOINT s t`) THEN
    EXISTS_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s')` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[moi_s34_trace; INTER_SUBSET];
    MATCH_MP_TAC(SET_RULE `!f. DISJOINT (s:real^3->bool) f /\ t SUBSET f ==> DISJOINT s t`) THEN
    EXISTS_TAC `moi_s34_rims tt kk (f1:real^N->real^3)` THEN ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN a' DIFF aa`; `(a:real^3->bool) INTER a' = aa`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`(a':real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`] THEN
    SET_TAC[]]);;

(* frontier C meets d exactly in a; d misses the other face balls. *)

let MOI_S4W_SEP_C = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d
     ==> frontier (cb s) INTER d = a /\
         (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> DISJOINT d (cb s'))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SEP_A) THEN
  MOI_S4W_UNFOLD_TAC THEN
  SUBGOAL_THEN `!s'. s' IN moi_s34_simp kk (&2)
                     ==> DISJOINT ((a':real^3->bool) DIFF aa)
                                  (frontier ((cb:(real^N->bool)->real^3->bool) s'))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4W_SEP_B THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
      `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`; `w:real^N`;
      `g:real^N->bool`; `a:real^3->bool`; `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      ASM_CASES_TAC `(x:real^3) IN a` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^3) IN a'` ASSUME_TAC THENL
       [MP_TAC(SPEC `s:real^N->bool` (ASSUME
          `!s'. s' IN moi_s34_simp kk (&2)
                ==> DISJOINT ((d:real^3->bool) DIFF (a UNION a'))
                             (frontier ((cb:(real^N->bool)->real^3->bool) s'))`)) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`(x:real^3) IN d`; `~((x:real^3) IN a)`;
          `(x:real^3) IN frontier ((cb:(real^N->bool)->real^3->bool) s)`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~((x:real^3) IN a' DIFF aa)` MP_TAC THENL
       [MP_TAC(SPEC `s:real^N->bool` (ASSUME
          `!s'. s' IN moi_s34_simp kk (&2)
                ==> DISJOINT ((a':real^3->bool) DIFF aa)
                             (frontier ((cb:(real^N->bool)->real^3->bool) s'))`)) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:real^3) IN frontier ((cb:(real^N->bool)->real^3->bool) s)` THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(aa:real^3->bool) SUBSET a`; `~((x:real^3) IN a)`; `(x:real^3) IN a'`] THEN
        SET_TAC[]];
      ASM_REWRITE_TAC[SUBSET_INTER]];
    ALL_TAC] THEN
  X_GEN_TAC `s'':real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s'':real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* a misses the other ball: it lies in C and in F, and C meets it inside Int N *)
  SUBGOAL_THEN `(a:real^3->bool) INTER (cb:(real^N->bool)->real^3->bool) s'' = {}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s INTER cb s'' SUBSET
                  interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` MP_TAC THENL
     [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
      REWRITE_TAC[moi_s34_fbinv; moi_s34_fb2] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `s'':real^N->bool`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `~(s'':real^N->bool = s)` THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(a:real^3->bool) SUBSET frontier ((cb:(real^N->bool)->real^3->bool) s)`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s`;
      `(a:real^3->bool) SUBSET d`;
      `(d:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER
       interior (IMAGE f1 (moi_s34_nb tt kk)) = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the open cell misses the other ball *)
  SUBGOAL_THEN `((d:real^3->bool) DIFF (a UNION a')) INTER
                (cb:(real^N->bool)->real^3->bool) s'' = {}` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `((d:real^3->bool) DIFF (a UNION a')) DIFF
                  (cb:(real^N->bool)->real^3->bool) s'' = {}` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(d:real^3->bool) DIFF (a UNION a')`;
                     `(cb:(real^N->bool)->real^3->bool) s''`] CONNECTED_INTER_FRONTIER) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `s'':real^N->bool` (ASSUME
        `!s'. s' IN moi_s34_simp kk (&2)
              ==> DISJOINT ((d:real^3->bool) DIFF (a UNION a'))
                           (frontier ((cb:(real^N->bool)->real^3->bool) s'))`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[DISJOINT]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(d:real^3->bool) SUBSET (cb:(real^N->bool)->real^3->bool) s''`
    MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure ((d:real^3->bool) DIFF (a UNION a'))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `((d:real^3->bool) DIFF (a UNION a')) DIFF
                   (cb:(real^N->bool)->real^3->bool) s'' = {}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(a:real^3->bool) INTER (cb:(real^N->bool)->real^3->bool) s'' = {}`;
      `(a:real^3->bool) SUBSET d`; `~(aa:real^3->bool = {})`;
      `(aa:real^3->bool) SUBSET a`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* a point of d in the other ball lies on a' DIFF aa and on its frontier *)
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN a' DIFF aa` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN d`; `(x:real^3) IN (cb:(real^N->bool)->real^3->bool) s''`;
      `(a:real^3->bool) INTER (cb:(real^N->bool)->real^3->bool) s'' = {}`;
      `((d:real^3->bool) DIFF (a UNION a')) INTER
       (cb:(real^N->bool)->real^3->bool) s'' = {}`;
      `(aa:real^3->bool) SUBSET a`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^3) IN interior ((cb:(real^N->bool)->real^3->bool) s''))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`interior ((cb:(real^N->bool)->real^3->bool) s'')`;
                   `(d:real^3->bool) DIFF (a UNION a')`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `(cb:(real^N->bool)->real^3->bool) s''` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN interior ((cb:(real^N->bool)->real^3->bool) s'')`;
      `(x:real^3) IN d`;
      `(d:real^3->bool) SUBSET closure (d DIFF (a UNION a'))`;
      `((d:real^3->bool) DIFF (a UNION a')) INTER
       (cb:(real^N->bool)->real^3->bool) s'' = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN frontier ((cb:(real^N->bool)->real^3->bool) s'')`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED; IN_DIFF]; ALL_TAC] THEN
  MP_TAC(SPEC `s'':real^N->bool` (ASSUME
    `!s'. s' IN moi_s34_simp kk (&2)
          ==> DISJOINT ((a':real^3->bool) DIFF aa)
                       (frontier ((cb:(real^N->bool)->real^3->bool) s'))`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(x:real^3) IN a' DIFF aa`;
    `(x:real^3) IN frontier ((cb:(real^N->bool)->real^3->bool) s'')`] THEN
  SET_TAC[]);;

(* The trace of C and the rim R_g do not accumulate at interior points of a, a'. *)

let MOI_S4W_SEP_D = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d
     ==> moi_s34_trace tt kk f1 (cb s) INTER d = a /\
         closure (moi_s34_trace tt kk f1 (cb s) DIFF a) INTER d SUBSET aa /\
         closure (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF a') INTER d
         SUBSET aa`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SEP_A) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SEP_C) THEN
  MOI_S4W_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `tr = moi_s34_trace tt kk (f1:real^N->real^3)
                     ((cb:(real^N->bool)->real^3->bool) s)` THEN
  SUBGOAL_THEN `(tr:real^3->bool) INTER d = a` ASSUME_TAC THENL
   [EXPAND_TAC "tr" THEN REWRITE_TAC[moi_s34_trace] THEN
    MAP_EVERY UNDISCH_TAC
     [`frontier ((cb:(real^N->bool)->real^3->bool) s) INTER d = a`;
      `(d:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* the trace: the component through x is a circle containing a *)
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN a` ASSUME_TAC THENL
     [SUBGOAL_THEN `closure ((tr:real^3->bool) DIFF a) SUBSET tr` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(x:real^3) IN closure ((tr:real^3->bool) DIFF a)`; `(x:real^3) IN d`;
          `(tr:real^3->bool) INTER d = a`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^3) IN aa` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:real^3->bool) SUBSET tr` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(tr:real^3->bool) INTER d = a`] THEN SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `J = connected_component (tr:real^3->bool) x` THEN
    SUBGOAL_THEN `(J:real^3->bool) IN components tr /\ (a:real^3->bool) SUBSET J`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "J" THEN REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?ov. open ov /\ (x:real^3) IN ov /\ J INTER ov SUBSET a DIFF aa`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4YC_CELL1_OPEN THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      MATCH_MP_TAC MOI_S4YC_SPHERE1_CHART THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tr:real^3->bool`; `J:real^3->bool`] MOI_S5C_COMPONENT_OPEN_IN) THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`ov INTER o1:real^3->bool`; `(tr:real^3->bool) DIFF a`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN
    SUBGOAL_THEN `(x:real^3) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN closure ((tr:real^3->bool) DIFF a)`; `(x:real^3) IN ov`;
      `(x:real^3) IN J`; `(J:real^3->bool) = tr INTER o1`;
      `(J:real^3->bool) INTER ov SUBSET a DIFF aa`] THEN
    SET_TAC[];
    (* the rim: a 1-manifold near x *)
    ABBREV_TAC `rg = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
    SUBGOAL_THEN `pl_cell_with_boundary 2
                    (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)) rg` ASSUME_TAC THENL
     [EXPAND_TAC "rg" THEN
      UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
      REWRITE_TAC[moi_s34_frame] THEN
      DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o CONJUNCT1 o funpow 7 CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS) THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN a'` ASSUME_TAC THENL
     [SUBGOAL_THEN `closure ((rg:real^3->bool) DIFF a') SUBSET rg` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(x:real^3) IN closure ((rg:real^3->bool) DIFF a')`; `(x:real^3) IN d`;
          `(d:real^3->bool) INTER rg = a'`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^3) IN aa` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?ov. open ov /\ (x:real^3) IN ov /\ rg INTER ov SUBSET a' DIFF aa`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4YC_CELL1_OPEN THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      MATCH_MP_TAC MOI_S4YC_CELL2_BD_CHART THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(x:real^3) IN a'`; `(a':real^3->bool) SUBSET rg`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ov:real^3->bool`; `(rg:real^3->bool) DIFF a'`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN closure ((rg:real^3->bool) DIFF a')`; `(x:real^3) IN ov`;
      `(rg:real^3->bool) INTER ov SUBSET a' DIFF aa`] THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The open set W0 around d: inside                                          *)
(* car s, away from h(Bd s), from the other face balls and from the vertex *)
(* balls of the vertices other than v and w (local finiteness: op1b's      *)
(* MOI_S4V_FB_AVOID and op1a's MOI_S4N_POINT_AVOID).                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S4W_D_CAR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d
     ==> d SUBSET car {v} /\ d SUBSET car s /\
         DISJOINT d (IMAGE h (relative_frontier s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_CTX_FACTS) THEN
  MOI_S4W_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET car {v:real^N}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {v}` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `s:real^N->bool`] o CONJUNCT1 o
               funpow 5 CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN SIMP_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET];
    ALL_TAC] THEN
  (* h(Bd s) misses F *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`] MOI_S4N_KFACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(d:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
    `IMAGE (h:real^N->real^3) (relative_frontier s) INTER
     IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = {}`] THEN
  SET_TAC[]);;

(* The local avoidance at one point of d. *)

let MOI_S4W_W0_POINT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d y.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d /\ y IN d
     ==> ?oy. open oy /\ y IN oy /\
              (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> DISJOINT oy (cb s')) /\
              (!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
                   ==> DISJOINT oy (IMAGE f1 (moi_s34_vb tt kk u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SEP_A) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SEP_C) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_D_CAR) THEN
  MOI_S4W_UNFOLD_TAC THEN
  (* finitely many other face balls near y *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `y:real^3`] MOI_S4V_FB_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN d` THEN
    MP_TAC(SPEC `s':real^N->bool` (ASSUME
      `!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s)
            ==> DISJOINT (d:real^3->bool) ((cb:(real^N->bool)->real^3->bool) s')`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u1:real^3->bool` STRIP_ASSUME_TAC)] THEN
  (* the vertex balls other than those of v and w avoid a neighbourhood of y *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `{v:real^N,w}`; `y:real^3`]
    MOI_S4N_POINT_AVOID) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {v}` THEN CONJ_TAC THENL
       [EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY]; ASM SET_TAC[]];
      X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
      MP_TAC(SPEC `u:real^N` (ASSUME
        `!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
             ==> DISJOINT (d:real^3->bool)
                          (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN UNDISCH_TAC `(y:real^3) IN d` THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `w1:real^3->bool` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `ff = {s' | s' IN moi_s34_simp kk (&2) /\ ~(s' = s) /\
                         ~((cb:(real^N->bool)->real^3->bool) s' INTER u1 = {})}` THEN
  EXISTS_TAC `(u1 INTER w1) DIFF UNIONS (IMAGE (cb:(real^N->bool)->real^3->bool) ff)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_INTER] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `s':real^N->bool` THEN EXPAND_TAC "ff" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s':real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    REWRITE_TAC[IN_DIFF; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `s':real^N->bool` THEN EXPAND_TAC "ff" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(SPEC `s':real^N->bool` (ASSUME
      `!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s)
            ==> DISJOINT (d:real^3->bool) ((cb:(real^N->bool)->real^3->bool) s')`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3) IN d`; `(y:real^3) IN (cb:(real^N->bool)->real^3->bool) s'`] THEN
    SET_TAC[];
    X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(cb:(real^N->bool)->real^3->bool) s' INTER u1 = {}` THENL
     [UNDISCH_TAC `(cb:(real^N->bool)->real^3->bool) s' INTER u1 = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s' SUBSET UNIONS (IMAGE cb ff)`
    MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE
        `(x:real^N->bool) IN t ==> (f:(real^N->bool)->real^3->bool) x SUBSET
                                   UNIONS (IMAGE f t)`) THEN
      EXPAND_TAC "ff" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `DISJOINT (w1:real^3->bool) t ==> DISJOINT ((u1 INTER w1) DIFF k) t`) THEN
    ASM_SIMP_TAC[]]);;

(* The open set W0. *)

let MOI_S4W_W0 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d
     ==> ?W0. open W0 /\ d SUBSET W0 /\ W0 SUBSET car s /\
              DISJOINT W0 (IMAGE h (relative_frontier s)) /\
              (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> DISJOINT W0 (cb s')) /\
              (!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
                   ==> DISJOINT W0 (IMAGE f1 (moi_s34_vb tt kk u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_D_CAR) THEN
  MOI_S4W_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`] MOI_S4N_KFACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v:real^N`; `w:real^N`; `g:real^N->bool`;
                 `a:real^3->bool`; `a':real^3->bool`; `aa:real^3->bool`; `d:real^3->bool`]
    MOI_S4W_W0_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `oo:real^3->real^3->bool`) THEN
  SUBGOAL_THEN `open ((car:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o funpow 4 CONJUNCT2) THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `aff_dim (s:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `(car:(real^N->bool)->real^3->bool) s INTER
              ((:real^3) DIFF IMAGE (h:real^N->real^3) (relative_frontier s)) INTER
              UNIONS (IMAGE (oo:real^3->real^3->bool) d)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED] THEN
    MATCH_MP_TAC OPEN_UNIONS THEN ASM_SIMP_TAC[FORALL_IN_IMAGE];
    REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNIV; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]; EXISTS_TAC `y:real^3` THEN ASM_SIMP_TAC[]];
    SET_TAC[];
    SET_TAC[];
    X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `oo:real^3->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `s':real^N->bool` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `oo:real^3->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The ball U2 = f1(C_v) UNION f1(C_w) and its frontier sphere S             *)
(* (MOI_S4W_BALL_UNION); near d the tube, its boundary F and the face torus  *)
(* agree with U2 and S (inside W0); the hypotheses of MOI_S4P_SLIDE for      *)
(* tau = trace C INTER S and rho = R_g.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4W_LOCAL_INTERIOR = prove
 (`!(w:real^N->bool) x y.
     open w /\ w INTER x = w INTER y ==> w INTER interior x = w INTER interior y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^N->bool. w INTER interior z = interior (w INTER z)`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[INTERIOR_INTER; INTERIOR_OPEN]);;

let MOI_S4W_U2_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d
     ==> pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w)) /\
         pl_sphere 2 (frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                                IMAGE f1 (moi_s34_vb tt kk w))) /\
         interior (IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w)) =
         inside (frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                           IMAGE f1 (moi_s34_vb tt kk w))) /\
         frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w)) UNION
         inside (frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                           IMAGE f1 (moi_s34_vb tt kk w))) =
         IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w) /\
         d SUBSET frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                            IMAGE f1 (moi_s34_vb tt kk w)) /\
         IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
         frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_CTX_FACTS) THEN
  MOI_S4W_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `w:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4L_IMAGES
    (CONJ (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)
          (ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_vb tt kk v SUBSET moi_s34_nb tt kk /\
                moi_s34_vb tt kk w SUBSET moi_s34_nb tt kk /\
                moi_s34_bd tt kk SUBSET moi_s34_nb tt (kk:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4K_NB_UNION_CELLS; MOI_S4K_VB_CELL]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN g /\ (w:real^N) IN g` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[v:real^N,w] = g` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  (* the two balls meet in the splitting disk *)
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) INTER
                IMAGE f1 (moi_s34_vb tt kk w) = IMAGE f1 (moi_s34_sd tt kk g)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_vb tt kk v INTER moi_s34_vb tt kk w =
                 moi_s34_sd tt kk (g:real^N->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))
                  (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o CONJUNCT1 o funpow 7 CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET
                frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
                IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET
                frontier (IMAGE f1 (moi_s34_vb tt kk w))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!t. (a:real^3->bool) SUBSET t /\ t IN f
                                ==> a SUBSET c UNION UNIONS f`) THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
    REWRITE_TAC[SUBSET_REFL; IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`]
    MOI_S4W_BALL_UNION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
                frontier (IMAGE f1 (moi_s34_vb tt kk v))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_UNION]; ALL_TAC] THEN
  (* d and R_g lie in A_v, which misses the open splitting disk *)
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
                IMAGE f1 (moi_s34_sd tt kk g) SUBSET
                IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) /\
                IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
                IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_s34_sd tt kk g SUBSET moi_s34_vb tt kk (v:real^N)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s34_vb tt kk v INTER moi_s34_vb tt kk w =
                   moi_s34_sd tt kk (g:real^N->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`moi_s34_vb tt kk v INTER moi_s34_bd tt (kk:(real^N->bool)->bool)`;
                     `moi_s34_sd tt kk (g:real^N->bool)`]
        (ASSUME `!a b. a SUBSET moi_s34_nb tt kk /\ b SUBSET moi_s34_nb tt kk
                       ==> IMAGE (f1:real^N->real^3) (a INTER b) =
                           IMAGE f1 a INTER IMAGE f1 b`)) THEN
      ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`moi_s34_vb tt kk v SUBSET moi_s34_nb tt (kk:(real^N->bool)->bool)`;
          `moi_s34_sd tt kk g SUBSET moi_s34_vb tt kk (v:real^N)`] THEN
        SET_TAC[];
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
      MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `moi_s34_sd tt kk g SUBSET moi_s34_vb tt kk (v:real^N)` THEN SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  UNDISCH_TAC
   `frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) UNION
              IMAGE f1 (moi_s34_vb tt kk w)) =
    (frontier (IMAGE f1 (moi_s34_vb tt kk v)) UNION
     frontier (IMAGE f1 (moi_s34_vb tt kk w))) DIFF
    (IMAGE f1 (moi_s34_sd tt kk g) DIFF
     IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))` THEN
  DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`(d:real^3->bool) SUBSET
     IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
     frontier (IMAGE f1 (moi_s34_vb tt kk v))`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
     IMAGE f1 (moi_s34_sd tt kk g) SUBSET
     IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
  SET_TAC[]);;

(* Inside W0 the tube, its interior and boundary, and the face torus agree with U2. *)

let MOI_S4W_W0_LOCAL = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d W0.
     moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d /\ open W0 /\
     (!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
          ==> DISJOINT W0 (IMAGE f1 (moi_s34_vb tt kk u)))
     ==> W0 INTER IMAGE f1 (moi_s34_nb tt kk) =
         W0 INTER (IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w)) /\
         W0 INTER IMAGE f1 (moi_s34_ft tt kk s) =
         W0 INTER (IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w)) /\
         W0 INTER interior (IMAGE f1 (moi_s34_nb tt kk)) =
         W0 INTER interior (IMAGE f1 (moi_s34_vb tt kk v) UNION
                            IMAGE f1 (moi_s34_vb tt kk w)) /\
         W0 INTER IMAGE f1 (moi_s34_bd tt kk) =
         W0 INTER frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                            IMAGE f1 (moi_s34_vb tt kk w)) /\
         (!g'. g' IN moi_s34_simp kk (&1) /\ ~(g' = g)
               ==> DISJOINT W0 (IMAGE f1 (moi_s34_sd tt kk g' INTER moi_s34_bd tt kk)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_U2_FACTS) THEN
  MOI_S4W_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4K_NB_UNION_CELLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U2 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) UNION
                   IMAGE f1 (moi_s34_vb tt kk w)` THEN
  (* the tube near W0 *)
  SUBGOAL_THEN `W0 INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) = W0 INTER U2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "U2" THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN W0` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
      ASM_CASES_TAC `u:real^N = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `u:real^N = w` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `u:real^N` (ASSUME
        `!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
             ==> DISJOINT (W0:real^3->bool)
                          (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      ASM_MESON_TAC[];
      STRIP_TAC THEN EXISTS_TAC `x':real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the face torus near W0 *)
  SUBGOAL_THEN `W0 INTER IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) = W0 INTER U2`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_ft] THEN EXPAND_TAC "U2" THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN W0` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
      ASM_CASES_TAC `u:real^N = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `u:real^N = w` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `u:real^N` (ASSUME
        `!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
             ==> DISJOINT (W0:real^3->bool)
                          (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      ASM_MESON_TAC[];
      STRIP_TAC THEN EXISTS_TAC `x':real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `W0 INTER interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) =
                W0 INTER interior U2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4W_LOCAL_INTERIOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* F = f1(N) DIFF Int f1(N) and frontier U2 = U2 DIFF Int U2 *)
    SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) =
                  IMAGE f1 (moi_s34_nb tt kk) DIFF interior (IMAGE f1 (moi_s34_nb tt kk))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
      REWRITE_TAC[moi_s34_frame] THEN
      DISCH_THEN(ACCEPT_TAC o SYM o CONJUNCT1 o funpow 3 CONJUNCT2);
      ALL_TAC] THEN
    SUBGOAL_THEN `frontier (U2:real^3->bool) = U2 DIFF interior U2` SUBST1_TAC THENL
     [REWRITE_TAC[frontier] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      ASM_MESON_TAC[MOI_S4L_PL_BALL_COMPACT];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`W0 INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) = W0 INTER U2`;
      `W0 INTER interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) =
       W0 INTER interior U2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the other rims have an end outside {v, w} *)
  X_GEN_TAC `g':real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g':real^N->bool`]
    MOI_S4L_EDGE_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?u:real^N. {u} IN kk /\ ~(u = v) /\ ~(u = w) /\
                           moi_s34_sd tt kk g' SUBSET moi_s34_vb tt kk u`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(u1:real^N = v \/ u1 = w) /\ (u2 = v \/ u2 = w)` THENL
     [UNDISCH_TAC `~(g':real^N->bool = g)` THEN
      UNDISCH_TAC `segment[v:real^N,w] = g` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
      ASM_MESON_TAC[SEGMENT_SYM];
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[DE_MORGAN_THM] o check (is_neg o concl)) THEN
      STRIP_TAC THENL
       [EXISTS_TAC `u1:real^N` THEN ASM_REWRITE_TAC[INTER_SUBSET];
        EXISTS_TAC `u2:real^N` THEN ASM_REWRITE_TAC[INTER_SUBSET]]];
    ALL_TAC] THEN
  MP_TAC(SPEC `u:real^N` (ASSUME
    `!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
         ==> DISJOINT (W0:real^3->bool)
                      (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `(b:real^3->bool) SUBSET c ==> DISJOINT w c ==> DISJOINT w b`) THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]);;

(* The slide of op2a applied to the bigon d in the sphere S = frontier U2. *)

let MOI_S4W_SLIDE_APPLY = prove
 (`PL_SCHOENFLIES_3_AMBIENT_STATEMENT
   ==> !(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d W0.
         moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d /\ open W0 /\ d SUBSET W0 /\
         W0 INTER IMAGE f1 (moi_s34_bd tt kk) =
         W0 INTER frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                            IMAGE f1 (moi_s34_vb tt kk w))
         ==> ?phi phi' K.
               pl_homeomorphism ((:real^3),(:real^3)) (phi,phi') /\
               compact K /\ K SUBSET W0 /\
               (!x. ~(x IN K) ==> phi x = x) /\ IMAGE phi K = K /\
               IMAGE phi (frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                                    IMAGE f1 (moi_s34_vb tt kk w))) =
               frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                         IMAGE f1 (moi_s34_vb tt kk w)) /\
               IMAGE phi (inside (frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                                            IMAGE f1 (moi_s34_vb tt kk w)))) =
               inside (frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                                 IMAGE f1 (moi_s34_vb tt kk w))) /\
               (moi_s34_trace tt kk f1 (cb s) INTER
                frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                          IMAGE f1 (moi_s34_vb tt kk w))) INTER
               IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) INTER K = aa /\
               IMAGE phi (moi_s34_trace tt kk f1 (cb s) INTER
                          frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                                    IMAGE f1 (moi_s34_vb tt kk w))) INTER
               IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) INTER K = {}`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SEP_A) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SEP_D) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_U2_FACTS) THEN
  MOI_S4W_UNFOLD_TAC THEN
  SUBGOAL_THEN `moi_s34_fb1 tt kk h f1 car s ((cb:(real^N->bool)->real^3->bool) s)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
    REWRITE_TAC[moi_s34_fbinv] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the two corners *)
  MP_TAC(MATCH_MP MOI_S4L_CELL1_PL_ARC
    (ASSUME `pl_cell_with_boundary 1 (a:real^3->bool) aa`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:real^1->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `p = pathstart (pp:real^1->real^3)` THEN
  ABBREV_TAC `q = pathfinish (pp:real^1->real^3)` THEN
  SUBGOAL_THEN `~(p:real^3 = q)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN
    MP_TAC(MATCH_MP ARC_DISTINCT_ENDS (ASSUME `arc (pp:real^1->real^3)`)) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) UNION
                            IMAGE f1 (moi_s34_vb tt kk w))` THEN
  ABBREV_TAC `rho = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `trc = moi_s34_trace tt kk (f1:real^N->real^3)
                      ((cb:(real^N->bool)->real^3->bool) s)` THEN
  (* the crossings at the corners, moved from F to S *)
  SUBGOAL_THEN `!z:real^3. z IN aa ==> pl_curve_crossing_at S (trc INTER S) rho z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pl_curve_crossing_at (IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk))
                    trc rho (z:real^3)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s34_fb1 tt kk h f1 car s ((cb:(real^N->bool)->real^3->bool) s)` THEN
      REWRITE_TAC[moi_s34_fb1] THEN
      DISCH_THEN(MP_TAC o SPECL [`g:real^N->bool`; `z:real^3`] o CONJUNCT1 o
                 funpow 5 CONJUNCT2) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(z:real^3) IN aa`; `(aa:real^3->bool) SUBSET a`;
        `(a:real^3->bool) SUBSET frontier ((cb:(real^N->bool)->real^3->bool) s)`;
        `(aa:real^3->bool) SUBSET rho`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FGB_CURVE_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`trc:real^3->bool`; `S:real^3->bool`] THEN
    REWRITE_TAC[OPEN_IN_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4W_CROSS_SURF THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`; `W0:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(z:real^3) IN aa`; `(aa:real^3->bool) SUBSET a`; `(a:real^3->bool) SUBSET d`;
          `(d:real^3->bool) SUBSET W0`] THEN SET_TAC[];
        ASM_MESON_TAC[INTER_COMM]];
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(z:real^3) IN aa`; `(aa:real^3->bool) SUBSET a`; `(a:real^3->bool) SUBSET d`;
          `(d:real^3->bool) SUBSET S`] THEN SET_TAC[];
        SET_TAC[]]];
    ALL_TAC] THEN
  (* the remaining hypotheses of the slide *)
  SUBGOAL_THEN `((trc:real^3->bool) INTER S) INTER d = a /\ trc INTER S SUBSET S /\
                (rho:real^3->bool) INTER d = a' /\
                closure ((trc INTER S) DIFF a) INTER d SUBSET aa`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(trc:real^3->bool) INTER d = a`; `(d:real^3->bool) SUBSET S`] THEN SET_TAC[];
      SET_TAC[];
      UNDISCH_TAC `(d:real^3->bool) INTER rho = a'` THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!c. (x:real^3->bool) SUBSET c /\ c INTER d SUBSET e
                                  ==> x INTER d SUBSET e`) THEN
      EXISTS_TAC `closure ((trc:real^3->bool) DIFF a)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_curve_crossing_at S ((trc:real^3->bool) INTER S) rho p /\
                pl_curve_crossing_at S (trc INTER S) rho q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  UNDISCH_TAC `aa = {p:real^3,q}` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`S:real^3->bool`; `d:real^3->bool`; `a:real^3->bool`; `a':real^3->bool`;
                `trc INTER S:real^3->bool`; `rho:real^3->bool`; `p:real^3`; `q:real^3`;
                `W0:real^3->bool`]
    (MP MOI_S4P_SLIDE (ASSUME `PL_SCHOENFLIES_3_AMBIENT_STATEMENT`))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^3` (X_CHOOSE_THEN `phi':real^3->real^3`
    (X_CHOOSE_THEN `K:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `phi':real^3->real^3`; `K:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The slide data and the generic                                            *)
(* behaviour of a PL homeomorphism of real^3 that is the identity off a    *)
(* compact set K mapping K onto K.                                           *)
(* ------------------------------------------------------------------------- *)

let moi_s4w_slid = new_definition
 `moi_s4w_slid (tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep (f1:real^N->real^3)
               car (cb:(real^N->bool)->real^3->bool) (s:real^N->bool) (v:real^N)
               (w:real^N) (g:real^N->bool) (a:real^3->bool) a' aa d W0
               (phi:real^3->real^3) phi' K <=>
   moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d /\
   open W0 /\ d SUBSET W0 /\ W0 SUBSET car s /\
   DISJOINT W0 (IMAGE h (relative_frontier s)) /\
   (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> DISJOINT W0 (cb s')) /\
   (!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
        ==> DISJOINT W0 (IMAGE f1 (moi_s34_vb tt kk u))) /\
   pl_homeomorphism ((:real^3),(:real^3)) (phi,phi') /\
   compact K /\ K SUBSET W0 /\
   (!x. ~(x IN K) ==> phi x = x) /\ IMAGE phi K = K /\
   IMAGE phi (frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                        IMAGE f1 (moi_s34_vb tt kk w))) =
   frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w)) /\
   IMAGE phi (inside (frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                                IMAGE f1 (moi_s34_vb tt kk w)))) =
   inside (frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                     IMAGE f1 (moi_s34_vb tt kk w))) /\
   (moi_s34_trace tt kk f1 (cb s) INTER
    frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION IMAGE f1 (moi_s34_vb tt kk w))) INTER
   IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) INTER K = aa /\
   IMAGE phi (moi_s34_trace tt kk f1 (cb s) INTER
              frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                        IMAGE f1 (moi_s34_vb tt kk w))) INTER
   IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) INTER K = {}`;;

(* The slide data exist for every op2 witness. *)

let MOI_S4W_SLID_EXISTS = prove
 (`PL_SCHOENFLIES_3_AMBIENT_STATEMENT
   ==> !(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d.
         moi_s4w_ctx2 tt kk h ep f1 car cb s v w g a a' aa d
         ==> ?W0 phi phi' K.
               moi_s4w_slid tt kk h ep f1 car cb s v w g a a' aa d W0 phi phi' K`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4W_W0) THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v:real^N`; `w:real^N`; `g:real^N->bool`;
                 `a:real^3->bool`; `a':real^3->bool`; `aa:real^3->bool`; `d:real^3->bool`;
                 `W0:real^3->bool`] MOI_S4W_W0_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                `s:real^N->bool`; `v:real^N`; `w:real^N`; `g:real^N->bool`;
                `a:real^3->bool`; `a':real^3->bool`; `aa:real^3->bool`; `d:real^3->bool`;
                `W0:real^3->bool`]
    (MP MOI_S4W_SLIDE_APPLY (ASSUME `PL_SCHOENFLIES_3_AMBIENT_STATEMENT`))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^3` (X_CHOOSE_THEN `phi':real^3->real^3`
    (X_CHOOSE_THEN `K:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`W0:real^3->bool`; `phi:real^3->real^3`; `phi':real^3->real^3`;
                        `K:real^3->bool`] THEN
  ASM_REWRITE_TAC[moi_s4w_slid]);;

(* A PL homeomorphism that is the identity off K and maps K onto K. *)

let MOI_S4W_PHI_GEN = prove
 (`!(phi:real^N->real^N) phi' kk.
     pl_homeomorphism ((:real^N),(:real^N)) (phi,phi') /\
     (!x. ~(x IN kk) ==> phi x = x) /\ IMAGE phi kk = kk
     ==> (!x y. phi x = phi y ==> x = y) /\
         (!x. phi x IN kk <=> x IN kk) /\
         (!X. IMAGE phi X SUBSET X UNION kk) /\
         (!X. IMAGE phi X DIFF kk = X DIFF kk) /\
         (!X Y. IMAGE phi (X INTER Y) = IMAGE phi X INTER IMAGE phi Y) /\
         (!X y. phi y IN IMAGE phi X <=> y IN X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_PLH_FACTS) THEN
  SUBGOAL_THEN `!x y. (phi:real^N->real^N) x = phi y ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `phi':real^N->real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. (phi:real^N->real^N) x IN kk <=> x IN kk` ASSUME_TAC THENL
   [GEN_TAC THEN EQ_TAC THENL
     [ASM_CASES_TAC `(x:real^N) IN kk` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(phi:real^N->real^N) x = x` SUBST1_TAC THENL
       [MATCH_MP_TAC(ASSUME `!x. ~(x IN kk) ==> (phi:real^N->real^N) x = x`) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      DISCH_TAC THEN UNDISCH_TAC `IMAGE (phi:real^N->real^N) kk = kk` THEN
      UNDISCH_TAC `(x:real^N) IN kk` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN kk` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(phi:real^N->real^N) y = y` SUBST1_TAC THENL
     [MATCH_MP_TAC(ASSUME `!x. ~(x IN kk) ==> (phi:real^N->real^N) x = x`) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      SUBGOAL_THEN `~((z:real^N) IN kk)` ASSUME_TAC THENL
       [UNDISCH_TAC `~((y:real^N) IN kk)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(phi:real^N->real^N) z = z` ASSUME_TAC THENL
       [MATCH_MP_TAC(ASSUME `!x. ~(x IN kk) ==> (phi:real^N->real^N) x = x`) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC(ASSUME `!x. ~(x IN kk) ==> (phi:real^N->real^N) x = x`) THEN
      ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x y. (f:real^N->real^N) x = f y ==> x = y)
      ==> IMAGE f (a INTER b) = IMAGE f a INTER IMAGE f b`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[ASSUME `!x y. (phi:real^N->real^N) x = phi y ==> x = y`]]);;

(* ------------------------------------------------------------------------- *)
(* Transport of the face-ball clauses under the slide.                       *)
(* C' = IMAGE phi C.  phi preserves F, f1(N), its                            *)
(* interior, the face torus and h(Bd s); C' agrees with C off K; the rim   *)
(* crossings of C' are those of C minus the corners aa.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4W_UNFOLD_SLID_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4w_slid] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "moi_s4w_slid"
                     with Failure _ -> false));;

let MOI_S4W_SLID_ENV = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d
    W0 phi phi' K.
     moi_s4w_slid tt kk h ep f1 car cb s v w g a a' aa d W0 phi phi' K
     ==> IMAGE phi (IMAGE f1 (moi_s34_bd tt kk)) = IMAGE f1 (moi_s34_bd tt kk) /\
         IMAGE phi (IMAGE f1 (moi_s34_nb tt kk)) = IMAGE f1 (moi_s34_nb tt kk) /\
         IMAGE phi (interior (IMAGE f1 (moi_s34_nb tt kk))) =
         interior (IMAGE f1 (moi_s34_nb tt kk)) /\
         IMAGE phi (IMAGE f1 (moi_s34_ft tt kk s)) = IMAGE f1 (moi_s34_ft tt kk s) /\
         IMAGE phi (IMAGE h (relative_frontier s)) = IMAGE h (relative_frontier s) /\
         W0 INTER IMAGE f1 (moi_s34_bd tt kk) =
         W0 INTER frontier (IMAGE f1 (moi_s34_vb tt kk v) UNION
                            IMAGE f1 (moi_s34_vb tt kk w)) /\
         (!g'. g' IN moi_s34_simp kk (&1) /\ ~(g' = g)
               ==> DISJOINT W0 (IMAGE f1 (moi_s34_sd tt kk g' INTER moi_s34_bd tt kk)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MOI_S4W_UNFOLD_SLID_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_U2_FACTS) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v:real^N`; `w:real^N`; `g:real^N->bool`;
                 `a:real^3->bool`; `a':real^3->bool`; `aa:real^3->bool`; `d:real^3->bool`;
                 `W0:real^3->bool`] MOI_S4W_W0_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_PLH_FACTS o
    check (fun th -> can (find_term (fun t -> t = `(:real^3)`)) (concl th) &&
                     try fst(dest_const(fst(strip_comb(concl th)))) = "pl_homeomorphism"
                     with Failure _ -> false)) THEN
  ABBREV_TAC `U2 = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) UNION
                   IMAGE f1 (moi_s34_vb tt kk w)` THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^3) U2 = U2` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier U2 UNION inside (frontier U2) = (U2:real^3->bool)` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV) [SYM th] THEN
                         GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[IMAGE_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3->bool. y INTER W0 = U2 INTER W0 ==> IMAGE (phi:real^3->real^3) y = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4W_FIX_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`K:real^3->bool`; `W0:real^3->bool`; `U2:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4W_FIX_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`K:real^3->bool`; `W0:real^3->bool`;
                          `frontier U2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `IMAGE (phi:real^3->real^3) (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) =
                  IMAGE f1 (moi_s34_nb tt kk)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4W_FIX_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`K:real^3->bool`; `W0:real^3->bool`; `{}:real^3->bool`] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; INTER_EMPTY] THEN
    UNDISCH_TAC `DISJOINT (W0:real^3->bool) (IMAGE (h:real^N->real^3) (relative_frontier s))` THEN
    SET_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The new ball C' = IMAGE phi C: frontier, trace, and the rim crossings. *)

let MOI_S4W_SLID_BALL = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d
    W0 phi phi' K.
     moi_s4w_slid tt kk h ep f1 car cb s v w g a a' aa d W0 phi phi' K
     ==> pl_ball 3 (IMAGE phi (cb s)) /\
         frontier (IMAGE phi (cb s)) = IMAGE phi (frontier (cb s)) /\
         interior (IMAGE phi (cb s)) = IMAGE phi (interior (cb s)) /\
         moi_s34_trace tt kk f1 (IMAGE phi (cb s)) =
         IMAGE phi (moi_s34_trace tt kk f1 (cb s)) /\
         frontier (IMAGE phi (cb s)) DIFF K = frontier (cb s) DIFF K /\
         IMAGE phi (cb s) SUBSET cb s UNION K /\
         frontier (IMAGE phi (cb s)) SUBSET frontier (cb s) UNION K /\
         frontier (IMAGE phi (cb s)) INTER moi_s34_rims tt kk f1 =
         (frontier (cb s) INTER moi_s34_rims tt kk f1) DIFF aa /\
         frontier (IMAGE phi (cb s)) INTER moi_s34_rims tt kk f1 INTER K = {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SLID_ENV) THEN
  MOI_S4W_UNFOLD_SLID_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_CTX_FACTS) THEN
  MOI_S4W_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `phi':real^3->real^3`; `K:real^3->bool`]
    MOI_S4W_PHI_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_PLH_FACTS o
    check (fun th -> can (find_term (fun t -> t = `(:real^3)`)) (concl th) &&
                     try fst(dest_const(fst(strip_comb(concl th)))) = "pl_homeomorphism"
                     with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_ball 3 ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fb1 tt kk h f1 car s ((cb:(real^N->bool)->real^3->bool) s)` THEN
    REWRITE_TAC[moi_s34_fb1] THEN SIMP_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_trace]) THEN REWRITE_TAC[moi_s34_trace] THEN
  ABBREV_TAC `C = (cb:(real^N->bool)->real^3->bool) s` THEN
  ABBREV_TAC `Fb = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  ABBREV_TAC `S = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) UNION
                            IMAGE f1 (moi_s34_vb tt kk w))` THEN
  ABBREV_TAC `rho = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `rims = moi_s34_rims tt kk (f1:real^N->real^3)` THEN

  SUBGOAL_THEN `pl_ball 3 (IMAGE (phi:real^3->real^3) C)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4W_BALL_IMAGE THEN EXISTS_TAC `phi':real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* rims inside K lie on rho *)
  SUBGOAL_THEN `rims INTER (K:real^3->bool) SUBSET rho` ASSUME_TAC THENL
   [EXPAND_TAC "rims" THEN EXPAND_TAC "rho" THEN
    REWRITE_TAC[SUBSET; IN_INTER; moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g':real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC) THEN
    ASM_CASES_TAC `g':real^N->bool = g` THENL
     [UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g':real^N->bool` o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `W0:real^3->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd"))
            (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN t`; `(x:real^3) IN K`; `(K:real^3->bool) SUBSET W0`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the old crossings in K are the corners *)
  SUBGOAL_THEN `frontier C INTER rims INTER (K:real^3->bool) = aa` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`((frontier C INTER Fb) INTER S) INTER rho INTER (K:real^3->bool) = aa`;
      `rims INTER (K:real^3->bool) SUBSET rho`; `(rho:real^3->bool) SUBSET rims`;
      `(rho:real^3->bool) SUBSET Fb`; `(K:real^3->bool) SUBSET W0`;
      `W0 INTER (Fb:real^3->bool) = W0 INTER S`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* no new crossing in K *)
  SUBGOAL_THEN `IMAGE (phi:real^3->real^3) (frontier C) INTER rims INTER K = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN rho` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN rims`; `(x:real^3) IN K`; `rims INTER (K:real^3->bool) SUBSET rho`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (phi:real^3->real^3) (frontier C)` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN K` ASSUME_TAC THENL
     [UNDISCH_TAC `(phi:real^3->real^3) y IN K` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN Fb` ASSUME_TAC THENL
     [SUBGOAL_THEN `(phi:real^3->real^3) y IN IMAGE phi Fb` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (phi:real^3->real^3) Fb = Fb` THEN DISCH_THEN SUBST1_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`(phi:real^3->real^3) y IN rho`; `(rho:real^3->bool) SUBSET Fb`] THEN
        SET_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN S` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN K`; `(y:real^3) IN Fb`; `(K:real^3->bool) SUBSET W0`;
        `W0 INTER (Fb:real^3->bool) = W0 INTER S`] THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^3) ((frontier C INTER Fb) INTER S) INTER rho INTER K =
                 {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(phi:real^3->real^3) y`) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MP_TAC(SPEC `frontier C:real^3->bool` (ASSUME
    `!X. IMAGE (phi:real^3->real^3) X DIFF K = X DIFF K`)) THEN
  MAP_EVERY UNDISCH_TAC
   [`IMAGE (phi:real^3->real^3) (frontier C) INTER rims INTER K = {}`;
    `frontier C INTER rims INTER (K:real^3->bool) = aa`] THEN
  SET_TAC[]);;

(* The one-face conditions for C'. *)

let MOI_S4W_SLID_FB1 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d
    W0 phi phi' K.
     moi_s4w_slid tt kk h ep f1 car cb s v w g a a' aa d W0 phi phi' K
     ==> moi_s34_fb1 tt kk h f1 car s (IMAGE phi (cb s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SLID_BALL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SLID_ENV) THEN
  MOI_S4W_UNFOLD_SLID_TAC THEN
  MOI_S4W_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `phi':real^3->real^3`; `K:real^3->bool`]
    MOI_S4W_PHI_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `homeomorphism ((:real^3),(:real^3)) ((phi:real^3->real^3),phi')`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_fb1 tt kk h f1 car s ((cb:(real^N->bool)->real^3->bool) s)`
  MP_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
    REWRITE_TAC[moi_s34_fbinv] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC THEN
  ABBREV_TAC `C = (cb:(real^N->bool)->real^3->bool) s` THEN
  ABBREV_TAC `Fb = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  ABBREV_TAC `T0 = IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
  ABBREV_TAC `tr = moi_s34_trace tt kk (f1:real^N->real^3) C` THEN
  REPEAT CONJ_TAC THENL
   [(* a PL ball *)
    FIRST_ASSUM ACCEPT_TAC;
    (* h(Bd s) inside *)
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^3) (IMAGE (h:real^N->real^3) (relative_frontier s)) =
                 IMAGE h (relative_frontier s)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    FIRST_ASSUM ACCEPT_TAC;
    (* frontier in the carrier *)
    MAP_EVERY UNDISCH_TAC
     [`frontier (IMAGE (phi:real^3->real^3) C) SUBSET frontier C UNION K`;
      `frontier C SUBSET (car:(real^N->bool)->real^3->bool) s`;
      `(K:real^3->bool) SUBSET W0`; `W0 SUBSET (car:(real^N->bool)->real^3->bool) s`] THEN
    SET_TAC[];
    (* the foreign vertex balls *)
    X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(u:real^N = v) /\ ~(u = w)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~((u:real^N) IN s)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `u:real^N` (ASSUME
      `!w. {w} IN kk /\ ~(w IN s)
           ==> DISJOINT C (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPEC `u:real^N` (ASSUME
      `!u. {u} IN kk /\ ~(u = v) /\ ~(u = w)
           ==> DISJOINT (W0:real^3->bool)
                        (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT C (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))`;
      `DISJOINT (W0:real^3->bool) (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))`] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (phi:real^3->real^3) C SUBSET C UNION K`; `(K:real^3->bool) SUBSET W0`] THEN
    SET_TAC[];
    (* crossing with F *)
    ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (phi:real^3->real^3) Fb = Fb` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S4W_CROSS3_IMAGE THEN EXISTS_TAC `phi':real^3->real^3` THEN
    ASM_SIMP_TAC[];
    (* crossings with the rims, off K *)
    MAP_EVERY X_GEN_TAC [`g':real^N->bool`; `x:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g' INTER moi_s34_bd tt kk)
                  SUBSET moi_s34_rims tt kk f1` ASSUME_TAC THENL
     [REWRITE_TAC[moi_s34_rims] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g':real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((x:real^3) IN K) /\ x IN frontier C` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN frontier (IMAGE (phi:real^3->real^3) C) INTER
         IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g' INTER moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g' INTER moi_s34_bd tt kk)
         SUBSET moi_s34_rims tt kk f1`;
        `frontier (IMAGE (phi:real^3->real^3) C) INTER moi_s34_rims tt kk (f1:real^N->real^3)
         INTER K = {}`;
        `frontier (IMAGE (phi:real^3->real^3) C) DIFF K = frontier C DIFF K`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FGB_CURVE_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`tr:real^3->bool`; `Fb INTER ((:real^3) DIFF K)`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`g':real^N->bool`; `x:real^3`] o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> is_const t &&
                                   fst(dest_const t) = "pl_curve_crossing_at")) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC
       `(x:real^3) IN frontier (IMAGE (phi:real^3->real^3) C) INTER
        IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g' INTER moi_s34_bd tt kk)` THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
      ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED];
      SUBGOAL_THEN `(x:real^3) IN Fb` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(x:real^3) IN frontier (IMAGE (phi:real^3->real^3) C) INTER
           IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g' INTER moi_s34_bd tt kk)`] THEN
        EXPAND_TAC "Fb" THEN
        MATCH_MP_TAC(SET_RULE `(b:real^3->bool) SUBSET c ==> x IN a INTER b ==> x IN c`) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
        UNDISCH_TAC `~((x:real^3) IN K)` THEN SET_TAC[]];
      MAP_EVERY EXPAND_TAC ["tr"] THEN REWRITE_TAC[moi_s34_trace] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `frontier C:real^3->bool` (ASSUME
        `!X. IMAGE (phi:real^3->real^3) X DIFF K = X DIFF K`)) THEN
      SET_TAC[]];
    (* finitely many trace components *)
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `phi':real^3->real^3`; `tr:real^3->bool`;
                   `IMAGE (phi:real^3->real^3) tr`] MOI_S4W_COMPONENTS_HOMEO) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    MATCH_MP_TAC FINITE_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    (* finitely many rim crossings *)
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_DIFF THEN FIRST_ASSUM ACCEPT_TAC;
    (* H_1 carried *)
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (phi:real^3->real^3) tr INTER T0 = IMAGE phi (tr INTER T0)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `IMAGE (phi:real^3->real^3) T0 = T0` THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4W_CARRIES_HOMEO THEN EXISTS_TAC `phi':real^3->real^3` THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

(* The two-face condition for C' against the other faces, and the rank drop. *)

let MOI_S4W_SLID_FB2 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d
    W0 phi phi' K s'.
     moi_s4w_slid tt kk h ep f1 car cb s v w g a a' aa d W0 phi phi' K /\
     s' IN moi_s34_simp kk (&2) /\ ~(s' = s)
     ==> IMAGE phi (cb s) INTER cb s' SUBSET interior (IMAGE f1 (moi_s34_nb tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SLID_BALL) THEN
  MOI_S4W_UNFOLD_SLID_TAC THEN
  MOI_S4W_UNFOLD_TAC THEN
  SUBGOAL_THEN `(cb:(real^N->bool)->real^3->bool) s INTER cb s' SUBSET
                interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
    REWRITE_TAC[moi_s34_fbinv; moi_s34_fb2] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(s':real^N->bool = s)` THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `s':real^N->bool` (ASSUME
    `!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s)
          ==> DISJOINT (W0:real^3->bool) ((cb:(real^N->bool)->real^3->bool) s')`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`IMAGE (phi:real^3->real^3) ((cb:(real^N->bool)->real^3->bool) s) SUBSET cb s UNION K`;
    `(K:real^3->bool) SUBSET W0`;
    `DISJOINT (W0:real^3->bool) ((cb:(real^N->bool)->real^3->bool) s')`;
    `(cb:(real^N->bool)->real^3->bool) s INTER cb s' SUBSET
     interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`] THEN
  SET_TAC[]);;

let MOI_S4W_SLID_RANK = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w g a a' aa d
    W0 phi phi' K.
     moi_s4w_slid tt kk h ep f1 car cb s v w g a a' aa d W0 phi phi' K
     ==> moi_s34_rank tt kk f1 (IMAGE phi (cb s)) < moi_s34_rank tt kk f1 (cb s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_SLID_BALL) THEN
  MOI_S4W_UNFOLD_SLID_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4W_CTX_FACTS) THEN
  MOI_S4W_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `FINITE (frontier ((cb:(real^N->bool)->real^3->bool) s) INTER
                        moi_s34_rims tt kk (f1:real^N->real^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fb1 tt kk h f1 car s ((cb:(real^N->bool)->real^3->bool) s)` THEN
    REWRITE_TAC[moi_s34_fb1] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism ((:real^3),(:real^3)) ((phi:real^3->real^3),phi')`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  ABBREV_TAC `tr = moi_s34_trace tt kk (f1:real^N->real^3)
                     ((cb:(real^N->bool)->real^3->bool) s)` THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `phi':real^3->real^3`; `tr:real^3->bool`;
                 `IMAGE (phi:real^3->real^3) tr`] MOI_S4W_COMPONENTS_HOMEO) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s34_rank] THEN ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `!z:real^3. z IN aa /\ aa SUBSET x ==> x DIFF aa PSUBSET x`) THEN
  UNDISCH_TAC `~(aa:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN EXISTS_TAC `z:real^3` THEN
  ASM_REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(aa:real^3->bool) SUBSET a`;
      `(a:real^3->bool) SUBSET frontier ((cb:(real^N->bool)->real^3->bool) s)`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`(aa:real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
       moi_s34_rims tt kk f1`] THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* OP2 (Moise p.242, Operation 2).  From an op2 witness the                  *)
(* slide gives C' = IMAGE phi (cb s); the family changed only at s keeps    *)
(* the invariants (MOI_S4V_FBINV_OUT of op1b) and the rank at s drops.     *)
(* ------------------------------------------------------------------------- *)

let OP2 = prove
 (MOI_S34_OP2,
  REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s34_op2 tt kk (f1:real^N->real^3)
                 (cb:(real^N->bool)->real^3->bool) (s:real^N->bool)` THEN
  REWRITE_TAC[moi_s34_op2] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `g:real^N->bool`
    (X_CHOOSE_THEN `a:real^3->bool` (X_CHOOSE_THEN `a':real^3->bool`
      (X_CHOOSE_THEN `aa:real^3->bool` (X_CHOOSE_THEN `d:real^3->bool`
        (X_CHOOSE_THEN `j:real^3->bool` STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `moi_s4w_ctx tt kk (h:real^N->real^3) ep (f1:real^N->real^3) car
                  (cb:(real^N->bool)->real^3->bool) s v g a a' aa d`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4w_ctx] THEN
    UNDISCH_TAC `(j:real^3->bool) = a UNION a'` THEN DISCH_THEN(SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:real^N` o MATCH_MP MOI_S4W_STRUCT) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                `s:real^N->bool`; `v:real^N`; `w:real^N`; `g:real^N->bool`;
                `a:real^3->bool`; `a':real^3->bool`; `aa:real^3->bool`; `d:real^3->bool`]
    (MP MOI_S4W_SLID_EXISTS (ASSUME `PL_SCHOENFLIES_3_AMBIENT_STATEMENT`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:real^3->bool` (X_CHOOSE_THEN `phi:real^3->real^3`
    (X_CHOOSE_THEN `phi':real^3->real^3` (X_CHOOSE_TAC `K:real^3->bool`)))) THEN
  EXISTS_TAC `\s':real^N->bool. if s' = s then IMAGE (phi:real^3->real^3) (cb s)
                                else (cb:(real^N->bool)->real^3->bool) s'` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4V_FBINV_OUT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4W_SLID_FB1 THEN
      MAP_EVERY EXISTS_TAC [`ep:real^N->real`; `v:real^N`; `w:real^N`; `g:real^N->bool`;
        `a:real^3->bool`; `a':real^3->bool`; `aa:real^3->bool`; `d:real^3->bool`;
        `W0:real^3->bool`; `phi':real^3->real^3`; `K:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_S4W_SLID_FB2 THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
        `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`;
        `g:real^N->bool`; `a:real^3->bool`; `a':real^3->bool`; `aa:real^3->bool`;
        `d:real^3->bool`; `W0:real^3->bool`; `phi':real^3->real^3`; `K:real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `s':real^N->bool` THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4W_SLID_RANK THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
      `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`; `g:real^N->bool`;
      `a:real^3->bool`; `a':real^3->bool`; `aa:real^3->bool`; `d:real^3->bool`;
      `W0:real^3->bool`; `phi':real^3->real^3`; `K:real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

