(* ========================================================================= *)
(* pc_moi_lt_cuta2: the disk swap of Moise GTM 47, p.185, Case 2 (lt_cut_a2 *)
(* of the C25 cut).  Main theorem                                           *)
(*   SWAP_FROM_CAP : |- MOI_LT3_CLEAN_CAP ==> MOI_LT2_CUT_SWAP.              *)
(* Sections:                                                                *)
(*  1   plane facts: PL circles bound PL 2-cells (Schoenflies), the nested  *)
(*      and separate cases of two disjoint circles.                          *)
(*  2   crossing2 charts are local: they transfer to a map agreeing with f  *)
(*      near the double point.                                               *)
(*  3   the replacement lemma: changing f on a closed set Z by an injective *)
(*      g whose image misses the rest of the image gives a normal2 disk     *)
(*      whose double image is a union of components of the old one.        *)
(*  4   PL tools: complements of polyhedra, pasting, cone extension of a   *)
(*      rim homeomorphism to PL 2-cells.                                     *)
(*  5   the common facts and the nested case (f o phi on D2).               *)
(*  6   the separate case from the clean cap, and the swap (conditional on *)
(*      the statements of MOI_LA1_IMAGE_COMPONENT and MOI_LA1_CASE2_BIJ of  *)
(*      pc_moi_lt_cuta1).                                                    *)
(*  7   the main theorem SWAP_FROM_CAP.                                     *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt2.ml";;
needs "src/pc_moi_lt_charts.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_fnd1.ml";;
needs "src/pc_moi_loop_stmt3.ml";;
needs "src/pc_moi_lt_cuta1.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Plane facts.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LA2_PL_SPHERE_1_HOMEOMORPHIC = prove
 (`!j:real^2->bool. pl_sphere 1 j ==> j homeomorphic sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `relative_frontier k:real^2->bool`;
                 `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] RELATIVE_FRONTIER_CBALL) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
  ASM_SIMP_TAC[CONVEX_CBALL; BOUNDED_CBALL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
                  ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  REWRITE_TAC[AFF_DIM_CBALL; REAL_LT_01; DIMINDEX_2]);;

(* A PL circle in the plane bounds the PL 2-cell j UNION inside j. *)

let MOI_LA2_JORDAN_DISK = prove
 (`!j:real^2->bool.
     pl_sphere 1 j
     ==> pl_cell_with_boundary 2 (j UNION inside j) j /\
         compact (j UNION inside j) /\ frontier (j UNION inside j) = j /\
         interior (j UNION inside j) = inside j /\
         open (inside j) /\ connected (j UNION inside j) /\
         compact j /\ connected j /\ ~(j = {}) /\ ~(inside j = {}) /\
         inside j INTER j = {} /\
         inside j UNION outside j = (:real^2) DIFF j /\
         inside j INTER outside j = {}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LA2_PL_SPHERE_1_HOMEOMORPHIC) THEN
  MP_TAC(ISPEC `j:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (j:real^2->bool) /\ connected (j:real^2->bool) /\ ~(j = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`j:real^2->bool`; `sphere(vec 0:real^2,&1)`]
        HOMEOMORPHIC_COMPACTNESS) THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE];
      MP_TAC(ISPECL [`j:real^2->bool`; `sphere(vec 0:real^2,&1)`]
        HOMEOMORPHIC_CONNECTEDNESS) THEN
      ASM_REWRITE_TAC[CONNECTED_SPHERE_EQ; DIMINDEX_2; LE_REFL];
      DISCH_TAC THEN UNDISCH_TAC `~(inside j:real^2->bool = {})` THEN
      ASM_REWRITE_TAC[INSIDE_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (j UNION inside j:real^2->bool) = j` ASSUME_TAC THENL
   [SUBGOAL_THEN `j UNION inside j:real^2->bool = (:real^2) DIFF outside j`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `j:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
      MAP_EVERY UNDISCH_TAC
       [`inside j UNION outside j:real^2->bool = (:real^2) DIFF j`;
        `inside j INTER outside j:real^2->bool = {}`] THEN
      SET_TAC[];
      ASM_REWRITE_TAC[FRONTIER_COMPLEMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (j UNION inside j:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_WITH_INSIDE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inside j INTER j:real^2->bool = {}` ASSUME_TAC THENL
   [REWRITE_TAC[INSIDE_NO_OVERLAP]; ALL_TAC] THEN
  SUBGOAL_THEN `interior (j UNION inside j:real^2->bool) = inside j` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `j UNION inside j:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `frontier (j UNION inside j:real^2->bool) = j` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `j:real^2->bool` (REWRITE_RULE[PL_SCHOENFLIES_2_STATEMENT]
      PL_SCHOENFLIES_2)) THEN
    ASM_REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `p:real^2->real^2`
      (X_CHOOSE_THEN `q:real^2->real^2` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `p:real^2->real^2`; `q:real^2->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frontier (j UNION inside j:real^2->bool) = j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_PL2_FRONTIER_PL_BALL_2 THEN
    EXISTS_TAC `q:real^2->real^2` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_WITH_INSIDE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

(* A connected set missing s lies inside or outside s (the same as         *)
(* MOI_S5C_CONNECTED_SIDE of pc_moi_s35_minc, outside this closure).        *)

let MOI_LA2_CONNECTED_SIDE = prove
 (`!s t:real^N->bool.
     connected t /\ DISJOINT s t ==> t SUBSET inside s \/ t SUBSET outside s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
    INSIDE_OUTSIDE_INTERSECT_CONNECTED) THEN
  MP_TAC(ISPEC `s:real^N->bool` INSIDE_UNION_OUTSIDE) THEN
  ASM SET_TAC[]);;

(* Two disjoint circles, the second missing the inside of the first: either *)
(* the closed disk of the first lies inside the second (nested), or the two *)
(* closed disks are disjoint (separate).                                     *)

let MOI_LA2_NEST_CASES = prove
 (`!j1 j2:real^2->bool.
     pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ DISJOINT j1 j2 /\ DISJOINT j2 (inside j1)
     ==> j1 UNION inside j1 SUBSET inside j2 \/
         DISJOINT (j1 UNION inside j1) (j2 UNION inside j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `j1:real^2->bool` MOI_LA2_JORDAN_DISK) THEN
  MP_TAC(ISPEC `j2:real^2->bool` MOI_LA2_JORDAN_DISK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`j2:real^2->bool`; `j1 UNION inside j1:real^2->bool`]
    MOI_LA2_CONNECTED_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
     [`DISJOINT (j1:real^2->bool) j2`; `DISJOINT (j2:real^2->bool) (inside j1)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISJ2_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`j1 UNION inside j1 SUBSET outside (j2:real^2->bool)`;
    `inside j2 INTER outside j2:real^2->bool = {}`;
    `inside j2 UNION outside j2:real^2->bool = (:real^2) DIFF j2`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. Crossing2 charts are local.  A chart can be shrunk into any           *)
(* open set around the double point (rescale a smaller ball of the chart);  *)
(* so a map that agrees with f near the double point, with the same double *)
(* image there, has a crossing2 chart there too.                            *)
(* ------------------------------------------------------------------------- *)

(* Rescaling the part of a cone in the unit ball that lies in a smaller     *)
(* ball onto the part in the unit ball.                                     *)

let MOI_LA2_CONE_SCALE = prove
 (`!r (cc:real^3->bool).
     &0 < r /\ r <= &1 /\ (!z t. z IN cc /\ &0 < t ==> t % z IN cc)
     ==> IMAGE (\z. inv r % (z - vec 0)) (ball(vec 0,&1) INTER cc INTER ball(vec 0,r)) =
         ball(vec 0,&1) INTER cc`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_BALL_0] THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; MOI_LCH_INV_LT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ]];
    STRIP_TAC THEN EXISTS_TAC `r % z:real^3` THEN
    SUBGOAL_THEN `inv r % r % z = z:real^3 /\ r % z IN (cc:real^3->bool) /\
                  r * norm(z:real^3) < r * &1 /\ r * &1 <= &1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                   REAL_LT_LMUL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN ASM_REAL_ARITH_TAC]]);;

(* The sets met in charts are cones. *)

let MOI_LA2_CONES = prove
 (`(!z t. z IN (:real^3) /\ &0 < t ==> t % z IN (:real^3)) /\
   (!z t. z IN {z:real^3 | &0 <= z$3} /\ &0 < t ==> t % z IN {z:real^3 | &0 <= z$3}) /\
   (!i z t. z IN {z:real^3 | z$i = &0} /\ &0 < t ==> t % z IN {z:real^3 | z$i = &0}) /\
   (!z t. z IN {z:real^3 | z$1 = &0 /\ z$2 = &0} /\ &0 < t
          ==> t % z IN {z:real^3 | z$1 = &0 /\ z$2 = &0}) /\
   (!(a:real^3->bool) b.
       (!z t. z IN a /\ &0 < t ==> t % z IN a) /\ (!z t. z IN b /\ &0 < t ==> t % z IN b)
       ==> (!z t. z IN a INTER b /\ &0 < t ==> t % z IN a INTER b))`,
  REWRITE_TAC[IN_UNIV; IN_ELIM_THM; IN_INTER; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_LE_MUL; REAL_LT_IMP_LE]);;

let MOI_LA2_CROSSING2_LOCAL = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) f' y w0.
     moi_lt_crossing2_at c f y /\ open w0 /\ y IN w0 /\
     (!x. x IN std_triangle /\ f x IN w0 ==> f' x = f x) /\
     (!x. x IN std_triangle /\ f' x IN w0 ==> f x IN w0) /\
     moi_lt_double_image f' INTER w0 = moi_lt_double_image f INTER w0
     ==> moi_lt_crossing2_at c f' y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_lt_crossing2_at] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `n1:real^2->bool`
      (X_CHOOSE_THEN `n2:real^2->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 (LABEL_TAC "case") STRIP_ASSUME_TAC)))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  (* the shape of the chart: the unit ball cut by a cone *)
  SUBGOAL_THEN `?cc:real^3->bool. IMAGE (h:real^N->real^3) u = ball(vec 0,&1) INTER cc /\
                                  (!z t. z IN cc /\ &0 < t ==> t % z IN cc)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "case" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[INTER_UNIV; MOI_LA2_CONES];
      EXISTS_TAC `{z:real^3 | &0 <= z$3}` THEN ASM_REWRITE_TAC[MOI_LA2_CONES]];
    ALL_TAC] THEN
  (* a radius *)
  SUBGOAL_THEN `?r. &0 < r /\ r <= &1 /\
                    !z. z IN IMAGE (h:real^N->real^3) u /\ z IN ball(vec 0,r)
                        ==> (h':real^3->real^N) z IN w0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real^N->real^3`; `h':real^3->real^N`; `u:real^N->bool`;
                   `IMAGE (h:real^N->real^3) u`; `u INTER w0:real^N->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[OPEN_IN_OPEN_INTER]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(vec 0:real^3) IN oo` ASSUME_TAC THENL
     [SUBGOAL_THEN `(vec 0:real^3) IN IMAGE (h:real^N->real^3) (u INTER w0)` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r0 (&1)` THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (h:real^N->real^3) (u INTER w0)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      MP_TAC(ISPECL [`vec 0:real^3`; `min r0 (&1)`; `r0:real`] SUBSET_BALL) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `ball(vec 0:real^3,r0) SUBSET oo` THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,min r0 (&1))` THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the shrunk chart *)
  ABBREV_TAC `u' = {p:real^N | p IN u /\ (h:real^N->real^3) p IN ball(vec 0,r)}` THEN
  SUBGOAL_THEN `(u':real^N->bool) SUBSET u /\ u' SUBSET w0 /\ (y:real^N) IN u' /\
                IMAGE (h:real^N->real^3) u' = IMAGE h u INTER ball(vec 0,r) /\
                (!a. IMAGE h (a INTER u') = IMAGE h (a INTER u) INTER ball(vec 0,r)) /\
                (!a. IMAGE h (u' INTER a) = IMAGE h (u INTER a) INTER ball(vec 0,r)) /\
                open_in (subtopology euclidean u) u'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u'" THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(p:real^N) = h'((h:real^N->real^3) p)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
      SET_TAC[];
      SET_TAC[];
      SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (u':real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* scaling the cone pieces of the small ball back to the unit ball *)
  SUBGOAL_THEN
   `!pp:real^3->bool. (!z t. z IN pp /\ &0 < t ==> t % z IN pp)
        ==> IMAGE (\z. inv r % (z - vec 0))
                  ((IMAGE (h:real^N->real^3) u INTER pp) INTER ball(vec 0,r)) =
            IMAGE h u INTER pp`
  ASSUME_TAC THENL
   [X_GEN_TAC `pp:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:real`; `cc INTER pp:real^3->bool`] MOI_LA2_CONE_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_LA2_CONES)))) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM INTER_ASSOC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z. inv r % (z - vec 0)) (IMAGE (h:real^N->real^3) u') = IMAGE h u`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(:real^3)` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[INTER_UNIV; CONJUNCT1 MOI_LA2_CONES] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (h:real^N->real^3) u = ball(vec 0,&1) INTER cc` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `!x. x IN std_triangle
                    ==> ((f':real^2->real^N) x IN u' <=> (f:real^2->real^N) x IN u')`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(f:real^2->real^N) x IN w0` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(f':real^2->real^N) x = f x` (fun th -> ASM_MESON_TAC[th]) THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `(f':real^2->real^N) x = f x` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `m1 = {x | x IN n1 /\ (f:real^2->real^N) x IN u'}` THEN
  ABBREV_TAC `m2 = {x | x IN n2 /\ (f:real^2->real^N) x IN u'}` THEN
  SUBGOAL_THEN `{x | x IN std_triangle /\ (f':real^2->real^N) x IN u'} = m1 UNION m2 /\
                {x | x IN std_triangle /\ (f:real^2->real^N) x IN u'} = m1 UNION m2`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
      UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
      UNDISCH_TAC `(u':real^N->bool) SUBSET u` THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN m1 UNION m2 ==> (f':real^2->real^N) x = f x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^2) IN m1 UNION m2` THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u'} = m1 UNION m2` THEN
    UNDISCH_TAC `(u':real^N->bool) SUBSET w0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) m1 =
                IMAGE (h o f) n1 INTER ball(vec 0,r) /\
                IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) m2 =
                IMAGE (h o f) n2 INTER ball(vec 0,r)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m1"; "m2"; "u'"] THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM; IN_UNION; o_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lt_double_image (f':real^2->real^N) INTER u' =
                moi_lt_double_image (f:real^2->real^N) INTER u'` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_double_image (f':real^2->real^N) INTER w0 =
                 moi_lt_double_image (f:real^2->real^N) INTER w0` THEN
    UNDISCH_TAC `(u':real^N->bool) SUBSET w0` THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`u':real^N->bool`; `(\z:real^3. inv r % (z - vec 0)) o (h:real^N->real^3)`;
    `(h':real^3->real^N) o (\w:real^3. vec 0 + r % w)`; `m1:real^2->bool`;
    `m2:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the chart is a PL homeomorphism *)
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (h:real^N->real^3) u'` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
       [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
        MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `IMAGE (h:real^N->real^3) u`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `open_in (subtopology euclidean u) (u':real^N->bool)` THEN
        REWRITE_TAC[OPEN_IN_OPEN] THEN
        DISCH_THEN(X_CHOOSE_THEN `ww:real^N->bool` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
        ASM_MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL]];
      UNDISCH_TAC `IMAGE (\z. inv r % (z - vec 0)) (IMAGE (h:real^N->real^3) u') =
                   IMAGE h u` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MOI_LCH_SCALE_PLH THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN
      ASM_MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL]];
    (* the centre *)
    ASM_REWRITE_TAC[o_THM; VECTOR_SUB_REFL; VECTOR_MUL_RZERO];
    (* interior or boundary point *)
    USE_THEN "case" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `{z:real^3 | z$3 = &0}` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
      REWRITE_TAC[MOI_LA2_CONES] THEN ASM_REWRITE_TAC[]];
    (* the two sheets are disjoint *)
    MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN SET_TAC[];
    (* the first sheet *)
    SUBGOAL_THEN `IMAGE (f':real^2->real^N) m1 = IMAGE f m1` SUBST1_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[IN_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (h:real^N->real^3) (IMAGE (f:real^2->real^N) m1) = IMAGE (h o f) m1`
    SUBST1_TAC THENL [REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{z:real^3 | z$1 = &0}` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[MOI_LA2_CONES];
    (* the second sheet *)
    SUBGOAL_THEN `IMAGE (f':real^2->real^N) m2 = IMAGE f m2` SUBST1_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[IN_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (h:real^N->real^3) (IMAGE (f:real^2->real^N) m2) = IMAGE (h o f) m2`
    SUBST1_TAC THENL [REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{z:real^3 | z$2 = &0}` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[MOI_LA2_CONES];
    (* the double image *)
    FIRST_X_ASSUM(MP_TAC o SPEC `{z:real^3 | z$1 = &0 /\ z$2 = &0}` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[MOI_LA2_CONES] THEN ASM_REWRITE_TAC[];
    (* the sheets are open in the preimage *)
    UNDISCH_TAC `open_in (subtopology euclidean {x | x IN std_triangle /\
                    (f:real^2->real^N) x IN u}) n1` THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `o1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
    UNDISCH_TAC `n1:real^2->bool = (n1 UNION n2) INTER o1` THEN
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN SET_TAC[];
    UNDISCH_TAC `open_in (subtopology euclidean {x | x IN std_triangle /\
                    (f:real^2->real^N) x IN u}) n2` THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o2:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `o2:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
    UNDISCH_TAC `n2:real^2->bool = (n1 UNION n2) INTER o2` THEN
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The replacement lemma. F = f off a compact set zz in the open triangle *)
(* and an injective g on zz whose image misses the rest of the image and the *)
(* boundary of c: F is a singular disk, its double image is the double image *)
(* of f minus f(zz), a union of components of the old one (each component is *)
(* all in or all out: MOI_LA1_IMAGE_COMPONENT of pc_moi_lt_cuta1, an         *)
(* antecedent here, discharged in section 7), the crossing2 charts transfer  *)
(* (section 2), and a component k covered by f(zz) disappears.               *)
(* ------------------------------------------------------------------------- *)

(* The statement of MOI_LA1_IMAGE_COMPONENT (pc_moi_lt_cuta1). *)

let moi_la2_image_component =
 `!c (f:real^2->real^N) k j.
     moi_lt_singular_disk c f /\ k IN components (moi_lt_double_image f) /\
     j SUBSET {x | x IN std_triangle /\ f x IN k} /\ compact j /\ ~(j = {}) /\
     closed ({x | x IN std_triangle /\ f x IN k} DIFF j)
     ==> IMAGE f j = k`;;

(* Basic facts on the double image of a normal disk. *)

let MOI_LA2_NORMAL_BASIC = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_normal_disk c f
     ==> moi_lt_singular_disk c f /\ f continuous_on std_triangle /\
         compact (moi_lt_double_image f) /\
         (!k. k IN components (moi_lt_double_image f) ==> compact k /\ connected k) /\
         (!y. y IN moi_lt_double_image f
              ==> y IN IMAGE f std_triangle /\
                  ?x x'. x IN std_triangle /\ x' IN std_triangle /\ ~(x = x') /\
                         f x = y /\ f x' = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_normal_disk] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[moi_lt_singular_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (moi_lt_double_image (f:real^2->real^N))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      can (find_term (fun t -> t = `moi_lt_double_image (f:real^2->real^N)`)) (concl th))) THEN
    MP_TAC(ISPEC `s:(real^N->bool)->bool` MOI_LTD_FINITE_COMPLEX_CLOSED) THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC `moi_lt_double_image (f:real^2->real^N)` THEN
        ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN ASM_MESON_TAC[IN_COMPONENTS_SUBSET];
        MATCH_MP_TAC CLOSED_COMPONENTS THEN
        EXISTS_TAC `moi_lt_double_image (f:real^2->real^N)` THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]];
    REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]]);;

(* The new map is a singular disk. *)

let MOI_LA2_REPLACE_SINGULAR = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^N) zz.
     moi_lt_singular_disk c f /\
     zz SUBSET std_triangle DIFF relative_frontier std_triangle /\
     pl_map_on std_triangle (\x. if x IN zz then g x else f x) /\
     IMAGE g zz SUBSET UNIONS c DIFF complex_boundary c /\
     (!x y. x IN zz /\ y IN zz /\ g x = g y ==> x = y) /\
     DISJOINT (IMAGE g zz) (IMAGE f (std_triangle DIFF zz))
     ==> moi_lt_singular_disk c (\x. if x IN zz then g x else f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    COND_CASES_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^2->real^N) zz SUBSET UNIONS c DIFF complex_boundary c` THEN
      UNDISCH_TAC `zz SUBSET std_triangle DIFF relative_frontier std_triangle` THEN
      UNDISCH_TAC `(x:real^2) IN zz` THEN SET_TAC[];
      UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
                   relative_frontier std_triangle` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `open:(real^2->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `n:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`(a:real^2) IN zz`; `(b:real^2) IN zz`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC
     `(if (a:real^2) IN zz then (g:real^2->real^N) a else f a) =
      (if (b:real^2) IN zz then g b else f b)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `DISJOINT (IMAGE (g:real^2->real^N) zz)
                     (IMAGE f (std_triangle DIFF zz))` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_DIFF; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^N) a`) THEN REWRITE_TAC[] THEN
      ASM_MESON_TAC[IN_INTER];
      UNDISCH_TAC `DISJOINT (IMAGE (g:real^2->real^N) zz)
                     (IMAGE f (std_triangle DIFF zz))` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_DIFF; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^N) b`) THEN REWRITE_TAC[] THEN
      ASM_MESON_TAC[IN_INTER];
      ASM_MESON_TAC[IN_INTER]];
    X_GEN_TAC `w:real^N` THEN
    ASM_CASES_TAC `(w:real^N) IN IMAGE (g:real^2->real^N) zz` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [IN_IMAGE]) THEN
      SUBGOAL_THEN `{x | x IN std_triangle /\
                         (if x IN zz then (g:real^2->real^N) x else f x) = w} SUBSET {x0}`
      ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `x:real^2` THEN
        COND_CASES_TAC THEN STRIP_TAC THENL
         [ASM_MESON_TAC[];
          UNDISCH_TAC `DISJOINT (IMAGE (g:real^2->real^N) zz)
                         (IMAGE f (std_triangle DIFF zz))` THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_DIFF; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x0:real^2}` THEN
        ASM_REWRITE_TAC[FINITE_SING];
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {x0:real^2}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_SING];
          REWRITE_TAC[CARD_SING] THEN ARITH_TAC]];
      SUBGOAL_THEN `{x | x IN std_triangle /\
                         (if x IN zz then (g:real^2->real^N) x else f x) = w} SUBSET
                    {x | x IN std_triangle /\ f x = w}`
      ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
        COND_CASES_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~((w:real^N) IN IMAGE (g:real^2->real^N) zz)` THEN
        REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `w:real^N` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `CARD:(real^2->bool)->num`))
                                    (concl th))) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x = w}` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC `CARD {x | x IN std_triangle /\ (f:real^2->real^N) x = w}` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]]]]);;

(* The double image of the new map. *)

let MOI_LA2_REPLACE_DOUBLE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^N) zz.
     moi_lt_singular_disk c f /\ zz SUBSET std_triangle /\
     (!x y. x IN zz /\ y IN zz /\ g x = g y ==> x = y) /\
     DISJOINT (IMAGE g zz) (IMAGE f (std_triangle DIFF zz))
     ==> moi_lt_double_image (\x. if x IN zz then g x else f x) =
         moi_lt_double_image f DIFF IMAGE f zz`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; moi_lt_double_image; IN_ELIM_THM; IN_DIFF; IN_IMAGE] THEN
  X_GEN_TAC `w:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~((a:real^2) IN zz) /\ ~((b:real^2) IN zz)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `DISJOINT (IMAGE (g:real^2->real^N) zz)
                     (IMAGE f (std_triangle DIFF zz))` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_DIFF; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN
      MAP_EVERY UNDISCH_TAC
       [`(if (a:real^2) IN zz then (g:real^2->real^N) a else f a) = w`;
        `(if (b:real^2) IN zz then (g:real^2->real^N) b else f b) = w`] THEN
      MAP_EVERY ASM_CASES_TAC [`(a:real^2) IN zz`; `(b:real^2) IN zz`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(if (a:real^2) IN zz then (g:real^2->real^N) a else f a) = w` THEN
    UNDISCH_TAC `(if (b:real^2) IN zz then (g:real^2->real^N) b else f b) = w` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real^2`; `b:real^2`] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `w:real^N`)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^2->real^N) x0` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `CARD:(real^2->bool)->num`))
                                    (concl th))) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `CARD {a:real^2,b,x0} <=
                    CARD {x | x IN std_triangle /\ (f:real^2->real^N) x = f x0}`
      MP_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
        ASM_MESON_TAC[SUBSET];
        ALL_TAC] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      SUBGOAL_THEN `~(x0:real^2 = a) /\ ~(x0 = b)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
      UNDISCH_TAC `CARD {x | x IN std_triangle /\ (f:real^2->real^N) x = f x0} <= 2` THEN
      ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`a:real^2`; `b:real^2`] THEN
    SUBGOAL_THEN `~((a:real^2) IN zz) /\ ~((b:real^2) IN zz)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]]);;

(* A component of the old double image is covered by f(zz) or misses it   *)
(* (its source misses the frontier of zz).                                 *)

let MOI_LA2_COMPONENT_CASES = prove
 (mk_imp(moi_la2_image_component,
  `!(c:(real^N->bool)->bool) (f:real^2->real^N) zz k k'.
     moi_lt_normal_disk c f /\ k IN components (moi_lt_double_image f) /\
     k' IN components (moi_lt_double_image f) /\ ~(k' = k) /\
     compact zz /\ zz SUBSET std_triangle /\
     (!x. x IN zz /\ f x IN moi_lt_double_image f /\ ~(f x IN k) ==> x IN interior zz)
     ==> k' SUBSET IMAGE f zz \/ DISJOINT k' (IMAGE f zz)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC) THEN
  ABBREV_TAC `pp = {x | x IN std_triangle /\ (f:real^2->real^N) x IN k'}` THEN
  ASM_CASES_TAC `pp INTER zz:real^2->bool = {}` THENL
   [DISJ2_TAC THEN UNDISCH_TAC `pp INTER zz:real^2->bool = {}` THEN EXPAND_TAC "pp" THEN
    UNDISCH_TAC `zz SUBSET std_triangle` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[SUBSET];
    DISJ1_TAC] THEN
  SUBGOAL_THEN `closed (pp:real^2->bool) /\ compact (pp:real^2->bool)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "pp" THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC];
      DISCH_TAC THEN ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      SIMP_TAC[COMPACT_IMP_BOUNDED; MOI_LTD_STD_TRIANGLE_BASIC] THEN
      EXPAND_TAC "pp" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pp INTER zz SUBSET interior (zz:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "pp" THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `k' SUBSET moi_lt_double_image (f:real^2->real^N) /\ k INTER k' = {}`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; COMPONENTS_NONOVERLAP];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) (pp INTER zz) = k'` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `closed:(real^2->bool)->bool`)) (concl th))) THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      ASM_MESON_TAC[COMPACT_INTER_CLOSED; INTER_COMM; COMPACT_IMP_CLOSED];
      SUBGOAL_THEN `pp DIFF pp INTER zz = pp INTER ((:real^2) DIFF interior zz)`
      SUBST1_TAC THENL
       [MP_TAC(ISPEC `zz:real^2->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `pp INTER zz SUBSET interior (zz:real^2->bool)` THEN SET_TAC[];
        MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR]]];
    SET_TAC[]]);;

(* A union of components of d has as components some components of d. *)

let MOI_LA2_UNION_COMPONENTS = prove
 (`!d d':real^N->bool.
     d' SUBSET d /\ (!k. k IN components d ==> k SUBSET d' \/ DISJOINT k d')
     ==> components d' SUBSET components d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_COMPONENTS] THEN
  X_GEN_TAC `cc:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^N` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `connected_component d (y:real^N) SUBSET d'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `connected_component d (y:real^N)`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_COMPONENTS] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN
    REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM SET_TAC[]]);;

(* The subcomplex of a 1-manifold over a union of its components. *)

let MOI_LA2_SUBCOMPLEX_MANIFOLD = prove
 (`!(c:(real^N->bool)->bool) (s:(real^N->bool)->bool) d'.
     FINITE s /\ combinatorial_manifold_with_boundary 1 s /\
     (!v. {v} IN s
          ==> (pl_ball 0 (UNIONS (simplicial_link s v)) <=> v IN complex_boundary c)) /\
     d' SUBSET UNIONS s /\
     (!k. k IN components (UNIONS s) ==> k SUBSET d' \/ DISJOINT k d')
     ==> ?s'. FINITE s' /\ combinatorial_manifold_with_boundary 1 s' /\
              UNIONS s' = d' /\
              !v. {v} IN s'
                  ==> (pl_ball 0 (UNIONS (simplicial_link s' v)) <=>
                       v IN complex_boundary c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [combinatorial_manifold_with_boundary]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN s /\ ~(t INTER d' = {}) ==> t SUBSET d'`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^N` (STRIP_ASSUME_TAC o REWRITE_RULE[IN_INTER]) o
      GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN `t SUBSET connected_component (UNIONS s) (y:real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `connected_component (UNIONS s) (y:real^N)` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `components:(real^N->bool)->(real^N->bool)->bool`))
          (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_COMPONENTS] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~b /\ (a ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM SET_TAC[];
      UNDISCH_TAC `t SUBSET connected_component (UNIONS s) (y:real^N)` THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `s' = {t:real^N->bool | t IN s /\ t SUBSET d'}` THEN
  SUBGOAL_THEN `!v:real^N. {v} IN s' ==> simplicial_link s' v = simplicial_link s v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN EXPAND_TAC "s'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN EQ_TAC THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `t':real^N->bool` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(t':real^N->bool) SUBSET d'` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v:real^N` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(t:real^N->bool) SUBSET t'` ASSUME_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[]; ASM SET_TAC[]; ASM_REWRITE_TAC[];
        EXISTS_TAC `t':real^N->bool` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `s':(real^N->bool)->bool` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "s'" THEN SET_TAC[];
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s'" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      EXPAND_TAC "s'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `t:real^N->bool`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `a:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(t:real^N->bool) SUBSET d'` THEN SET_TAC[];
      EXPAND_TAC "s'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `b:real^N->bool`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `FINITE:((real^N->bool)->bool)->bool`)) (concl th))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `(x:real^N) IN UNIONS s'` THEN
                      EXPAND_TAC "s'" THEN SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
      EXPAND_TAC "s'" THEN SET_TAC[];
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `{v:real^N} IN s'` THEN
      EXPAND_TAC "s'" THEN SET_TAC[]];
    EXPAND_TAC "s'" THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [SET_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?t:real^N->bool. t IN s /\ y IN t` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^N) IN d'` THEN
        UNDISCH_TAC `d' SUBSET UNIONS (s:(real^N->bool)->bool)` THEN SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `{v:real^N} IN s'` THEN
    EXPAND_TAC "s'" THEN SET_TAC[]]);;

(* The replacement lemma. *)

let MOI_LA2_REPLACE = prove
 (mk_imp(moi_la2_image_component,
  `!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^N) zz k.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_normal2_disk c f /\
     k IN components (moi_lt_double_image f) /\
     compact zz /\ zz SUBSET std_triangle DIFF relative_frontier std_triangle /\
     pl_map_on std_triangle (\x. if x IN zz then g x else f x) /\
     IMAGE g zz SUBSET UNIONS c DIFF complex_boundary c /\
     (!x y. x IN zz /\ y IN zz /\ g x = g y ==> x = y) /\
     DISJOINT (IMAGE g zz) (IMAGE f (std_triangle DIFF zz)) /\
     k SUBSET IMAGE f zz /\
     (!x. x IN zz /\ f x IN moi_lt_double_image f /\ ~(f x IN k) ==> x IN interior zz)
     ==> moi_lt_normal2_disk c (\x. if x IN zz then g x else f x) /\
         moi_lt_disk_complexity (\x. if x IN zz then g x else f x) <
         moi_lt_disk_complexity f /\
         !x. x IN relative_frontier std_triangle
             ==> (\x. if x IN zz then g x else f x) x = f x`),
  DISCH_THEN(LABEL_TAC "ic") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_normal_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LT2D_NORMAL2_IMP]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_NORMAL_BASIC) THEN
  SUBGOAL_THEN `(zz:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
   [UNDISCH_TAC `zz SUBSET std_triangle DIFF relative_frontier std_triangle` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the new map is singular, with the expected double image *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^N`;
                 `zz:real^2->bool`] MOI_LA2_REPLACE_SINGULAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `g:real^2->real^N`;
                 `zz:real^2->bool`] MOI_LA2_REPLACE_DOUBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `dd = moi_lt_double_image (\x. if x IN zz then (g:real^2->real^N) x else f x)` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  (* every old component is all in or all out *)
  SUBGOAL_THEN `!k'. k' IN components (moi_lt_double_image (f:real^2->real^N))
                     ==> k' SUBSET dd \/ DISJOINT k' dd`
  ASSUME_TAC THENL
   [X_GEN_TAC `k':real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k' SUBSET moi_lt_double_image (f:real^2->real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `k':real^N->bool = k` THENL
     [DISJ2_TAC THEN UNDISCH_TAC `(k:real^N->bool) SUBSET IMAGE (f:real^2->real^N) zz` THEN
      UNDISCH_TAC `moi_lt_double_image (f:real^2->real^N) DIFF IMAGE f zz = dd` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "ic" (fun ic -> MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
      `zz:real^2->bool`; `k:real^N->bool`; `k':real^N->bool`]
      (MP MOI_LA2_COMPONENT_CASES ic))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_lt_double_image (f:real^2->real^N) DIFF IMAGE f zz = dd` THEN
    UNDISCH_TAC `k' SUBSET moi_lt_double_image (f:real^2->real^N)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dd SUBSET moi_lt_double_image (f:real^2->real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_double_image (f:real^2->real^N) DIFF IMAGE f zz = dd` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `components dd SUBSET
                components (moi_lt_double_image (f:real^2->real^N)) DELETE k`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_lt_double_image (f:real^2->real^N)`; `dd:real^N->bool`]
      MOI_LA2_UNION_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((k:real^N->bool) IN components dd)` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `~(k:real^N->bool = {}) /\ k SUBSET dd` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC IN_COMPONENTS_NONEMPTY THEN
          EXISTS_TAC `dd:real^N->bool` THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      UNDISCH_TAC `(k:real^N->bool) SUBSET IMAGE (f:real^2->real^N) zz` THEN
      UNDISCH_TAC `moi_lt_double_image (f:real^2->real^N) DIFF IMAGE f zz = dd` THEN
      MAP_EVERY UNDISCH_TAC [`~(k:real^N->bool = {})`; `(k:real^N->bool) SUBSET dd`] THEN
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* normal2 *)
    SUBGOAL_THEN `!y. y IN dd
                      ==> moi_lt_crossing2_at c
                            (\x. if x IN zz then (g:real^2->real^N) x else f x) y`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^2->real^N) continuous_on zz` ASSUME_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC `\x. if x IN zz then (g:real^2->real^N) x else f x` THEN
        SIMP_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `std_triangle` THEN ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
        ALL_TAC] THEN
      SUBGOAL_THEN `compact (IMAGE (f:real^2->real^N) zz) /\
                    compact (IMAGE (g:real^2->real^N) zz)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_LA2_CROSSING2_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`f:real^2->real^N`;
        `(:real^N) DIFF (IMAGE (f:real^2->real^N) zz UNION IMAGE (g:real^2->real^N) zz)`] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
        REWRITE_TAC[moi_lt_normal2_disk] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        UNDISCH_TAC `(y:real^N) IN dd` THEN
        UNDISCH_TAC `dd SUBSET moi_lt_double_image (f:real^2->real^N)` THEN SET_TAC[];
        REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNION THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        SUBGOAL_THEN `?x. x IN std_triangle /\ (f:real^2->real^N) x = y`
        STRIP_ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall (concl th) &&
            can (find_term (fun t -> t = `IMAGE (f:real^2->real^N) std_triangle`)) (concl th))) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC `(y:real^N) IN dd` THEN
            UNDISCH_TAC `dd SUBSET moi_lt_double_image (f:real^2->real^N)` THEN SET_TAC[];
            REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
          ALL_TAC] THEN
        SUBGOAL_THEN `~((x:real^2) IN zz)` ASSUME_TAC THENL
         [UNDISCH_TAC `(y:real^N) IN dd` THEN
          UNDISCH_TAC `moi_lt_double_image (f:real^2->real^N) DIFF IMAGE f zz = dd` THEN
          UNDISCH_TAC `(f:real^2->real^N) x = y` THEN SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `DISJOINT (IMAGE (g:real^2->real^N) zz) (IMAGE f (std_triangle DIFF zz))` THEN
        UNDISCH_TAC `moi_lt_double_image (f:real^2->real^N) DIFF IMAGE f zz = dd` THEN
        UNDISCH_TAC `(y:real^N) IN dd` THEN
        MAP_EVERY UNDISCH_TAC [`(x:real^2) IN std_triangle`; `~((x:real^2) IN zz)`;
                               `(f:real^2->real^N) x = y`] THEN
        SET_TAC[];
        X_GEN_TAC `x:real^2` THEN BETA_TAC THEN STRIP_TAC THEN
        SUBGOAL_THEN `~((x:real^2) IN zz)` (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `(f:real^2->real^N) x IN
                     (:real^N) DIFF (IMAGE f zz UNION IMAGE (g:real^2->real^N) zz)` THEN
        SET_TAC[];
        X_GEN_TAC `x:real^2` THEN BETA_TAC THEN STRIP_TAC THEN
        ASM_CASES_TAC `(x:real^2) IN zz` THENL
         [UNDISCH_TAC `(if (x:real^2) IN zz then (g:real^2->real^N) x else f x) IN
                       (:real^N) DIFF (IMAGE f zz UNION IMAGE g zz)` THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^2) IN zz` THEN SET_TAC[];
          UNDISCH_TAC `(if (x:real^2) IN zz then (g:real^2->real^N) x else f x) IN
                       (:real^N) DIFF (IMAGE f zz UNION IMAGE g zz)` THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `moi_lt_double_image (f:real^2->real^N) DIFF IMAGE f zz = dd` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_lt_normal2_disk; moi_lt_normal_disk] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_lt_normal_disk c (f:real^2->real^N)` THEN
      REWRITE_TAC[moi_lt_normal_disk] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `s:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      MATCH_MP_TAC MOI_LA2_SUBCOMPLEX_MANIFOLD THEN
      EXISTS_TAC `s:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_LT2D_CROSSING2_IMP THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    (* the complexity drops *)
    REWRITE_TAC[moi_lt_disk_complexity] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `CARD (components (moi_lt_double_image (f:real^2->real^N)) DELETE k) + 1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `a <= b ==> a < b + 1`) THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_DELETE; MOI_LT2D_NORMAL2_FINITE] THEN
      ASM_MESON_TAC[MOI_LT2D_NORMAL2_FINITE];
      SUBGOAL_THEN `FINITE (components (moi_lt_double_image (f:real^2->real^N)))`
      ASSUME_TAC THENL [ASM_MESON_TAC[MOI_LT2D_NORMAL2_FINITE]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_DELETE] THEN
      SUBGOAL_THEN `~(CARD (components (moi_lt_double_image (f:real^2->real^N))) = 0)`
      MP_TAC THENL
       [ASM_SIMP_TAC[CARD_EQ_0] THEN
        UNDISCH_TAC `(k:real^N->bool) IN components (moi_lt_double_image (f:real^2->real^N))` THEN
        SET_TAC[];
        ARITH_TAC]];
    (* the boundary values *)
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((x:real^2) IN zz)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `zz SUBSET std_triangle DIFF relative_frontier std_triangle` THEN
    UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 4. PL tools for the swap.  The closure of the complement of a            *)
(* polyhedron in the interior of another is a polyhedron; pasting the new  *)
(* map along the frontier of zz; a PL homeomorphism between the rims of two *)
(* PL 2-cells extends to the cells (the cone construction of pc_moi_cone).  *)
(* ------------------------------------------------------------------------- *)

let MOI_LA2_COMPL_POLY = prove
 (`!q s:real^N->bool.
     pl_polyhedron q /\ pl_polyhedron s /\ s SUBSET interior q
     ==> pl_polyhedron (q DIFF interior s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?t:(real^N->bool)->bool.
                  simplicial_complex t /\ UNIONS t = q /\
                  !z. z IN s ==> ?r. r IN t /\ r SUBSET s /\ z IN r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_polyhedron (q:real^N->bool)` THEN
    REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `pl_polyhedron (s:real^N->bool)` THEN REWRITE_TAC[pl_polyhedron] THEN
    DISCH_THEN(X_CHOOSE_THEN `cs:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `s = UNIONS cs:real^N->bool` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `cs:(real^N->bool)->bool`]
      SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[] THEN MP_TAC(ISPEC `q:real^N->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET interior q` THEN
      UNDISCH_TAC `UNIONS cs = s:real^N->bool` THEN
      UNDISCH_TAC `(k:real^N->bool) IN cs` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?k:real^N->bool. k IN cs /\ z IN k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^N) IN s` THEN UNDISCH_TAC `UNIONS cs = s:real^N->bool` THEN
      SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `cs:(real^N->bool)->bool`))
                                  (concl th) &&
      can (find_term (fun t -> t = `t:(real^N->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ff:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?r:real^N->bool. r IN ff /\ z IN r` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^N) IN k` THEN UNDISCH_TAC `k = UNIONS ff:real^N->bool` THEN
      SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ff SUBSET (t:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(r:real^N->bool) IN ff` THEN SET_TAC[];
      UNDISCH_TAC `(r:real^N->bool) IN ff` THEN UNDISCH_TAC `k = UNIONS ff:real^N->bool` THEN
      UNDISCH_TAC `(k:real^N->bool) IN cs` THEN UNDISCH_TAC `UNIONS cs = s:real^N->bool` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `q DIFF interior s = UNIONS {r:real^N->bool | r IN t /\ ~(r SUBSET s)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [(* points of q outside the interior of s *)
      SUBGOAL_THEN `closed (UNIONS {r:real^N->bool | r IN t /\ ~(r SUBSET s)})`
      ASSUME_TAC THENL
       [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
          SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
            ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `q DIFF s SUBSET UNIONS {r:real^N->bool | r IN t /\ ~(r SUBSET s)}`
      ASSUME_TAC THENL
       [UNDISCH_TAC `UNIONS t = (q:real^N->bool)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      ASM_CASES_TAC `(x:real^N) IN s` THENL [ALL_TAC; ASM SET_TAC[]] THEN
      SUBGOAL_THEN `(x:real^N) IN closure (q DIFF s)` MP_TAC THENL
       [REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(x:real^N) IN interior q` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_INTERIOR] THEN
        DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `~((x:real^N) IN interior s)` THEN
        REWRITE_TAC[IN_INTERIOR; NOT_EXISTS_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `min e e1`) THEN
        ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET; IN_BALL; NOT_FORALL_THM; NOT_IMP] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
        CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]] THEN
        UNDISCH_TAC `ball(x:real^N,e1) SUBSET q` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`q DIFF s:real^N->bool`;
                     `UNIONS {r:real^N->bool | r IN t /\ ~(r SUBSET s)}`] CLOSURE_MINIMAL) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      (* a simplex not inside s misses the interior of s *)
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_DIFF] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `relative_interior r INTER (s:real^N->bool) = {}` ASSUME_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^N` THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `?r'. r' IN t /\ r' SUBSET (s:real^N->bool) /\ (z:real^N) IN r'`
        STRIP_ASSUME_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `(r INTER r') face_of (r:real^N->bool)` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPECL [`r:real^N->bool`; `r':real^N->bool`] o check
            (fun th -> is_forall (concl th) &&
               can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of"))
                   (concl th) &&
               can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER"))
                   (concl th))) THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`r INTER r':real^N->bool`; `r:real^N->bool`]
          FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
        ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `r INTER r':real^N->bool = r` THENL
         [UNDISCH_TAC `~(r SUBSET (s:real^N->bool))` THEN
          UNDISCH_TAC `(r':real^N->bool) SUBSET s` THEN
          UNDISCH_TAC `r INTER r':real^N->bool = r` THEN SET_TAC[];
          ASM_REWRITE_TAC[] THEN
          MAP_EVERY UNDISCH_TAC [`(z:real^N) IN relative_interior r`; `(z:real^N) IN r'`] THEN
          MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(r:real^N->bool) SUBSET closure (q DIFF s)` MP_TAC THENL
       [SUBGOAL_THEN `r = closure (relative_interior r:real^N->bool)` SUBST1_TAC THENL
         [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; SIMPLEX_IMP_CONVEX] THEN
          ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED];
          MATCH_MP_TAC SUBSET_CLOSURE THEN
          MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
          UNDISCH_TAC `relative_interior r INTER (s:real^N->bool) = {}` THEN
          SUBGOAL_THEN `(r:real^N->bool) SUBSET q` MP_TAC THENL
           [UNDISCH_TAC `UNIONS t = (q:real^N->bool)` THEN
            UNDISCH_TAC `(r:real^N->bool) IN t` THEN SET_TAC[];
            SET_TAC[]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `closure (q DIFF s) SUBSET q DIFF interior (s:real^N->bool)` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
         [MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
          MATCH_MP_TAC CLOSED_DIFF THEN
          ASM_SIMP_TAC[OPEN_INTERIOR; PL_POLYHEDRON_IMP_COMPACT; COMPACT_IMP_CLOSED]];
        UNDISCH_TAC `(x:real^N) IN r` THEN SET_TAC[]]];
    REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `{r:real^N->bool | r IN t /\ ~(r SUBSET s)}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]]]]);;

(* The open triangle is the interior of the triangle. *)

let MOI_LA2_OPEN_TRIANGLE = prove
 (`std_triangle DIFF relative_frontier std_triangle = interior std_triangle`,
  SUBGOAL_THEN `~(interior std_triangle = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `std_triangle` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[DIMINDEX_2] THEN MATCH_MP_TAC AFF_DIM_SIMPLEX THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[relative_frontier; GSYM RELATIVE_INTERIOR_NONEMPTY_INTERIOR] THEN
  SIMP_TAC[CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC] THEN
  MP_TAC(ISPEC `std_triangle` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

(* Pasting the new map along the frontier of zz. *)

let MOI_LA2_PASTE = prove
 (`!(f:real^2->real^N) g zz.
     pl_map_on std_triangle f /\ pl_map_on zz g /\ pl_polyhedron zz /\
     zz SUBSET std_triangle DIFF relative_frontier std_triangle /\
     (!x. x IN zz /\ ~(x IN interior zz) ==> g x = f x)
     ==> pl_map_on std_triangle (\x. if x IN zz then g x else f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_LA2_OPEN_TRIANGLE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (std_triangle DIFF interior zz)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LA2_COMPL_POLY THEN ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC];
    ALL_TAC] THEN
  SUBGOAL_THEN `std_triangle = (std_triangle DIFF interior zz) UNION (zz:real^2->bool)`
  (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
   [MP_TAC(ISPEC `zz:real^2->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `std_triangle` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(zz:real^2->bool) SUBSET interior std_triangle` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `f:real^2->real^N` THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN SET_TAC[]];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `g:real^2->real^N` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[SUBSET_UNION] THEN
    ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT; COMPACT_IMP_CLOSED];
    MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[SUBSET_UNION] THEN
    ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT; COMPACT_IMP_CLOSED]]);;

(* A PL homeomorphism between the rims of two PL 2-cells extends to a PL   *)
(* homeomorphism of the cells (cone extension on the model simplices).      *)

let MOI_LA2_CELL_EXTENSION = prove
 (`!(d:real^2->bool) j (e:real^N->bool) b (p:real^2->real^N) p'.
     pl_cell_with_boundary 2 d j /\ pl_cell_with_boundary 2 e b /\
     pl_homeomorphism (j,b) (p,p')
     ==> ?g g'. pl_homeomorphism (d,e) (g,g') /\ !x. x IN j ==> g x = p x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k1:real^2->bool` (X_CHOOSE_THEN `a:real^2->real^2`
      (X_CHOOSE_THEN `a':real^2->real^2` STRIP_ASSUME_TAC)))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `k2:real^N->bool` (X_CHOOSE_THEN `b0:real^N->real^N`
        (X_CHOOSE_THEN `b0':real^N->real^N` STRIP_ASSUME_TAC)))
      ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "relative_frontier")) (rhs (concl th))))) THEN
  SUBGOAL_THEN `relative_frontier k1 SUBSET (k1:real^2->bool) /\
                relative_frontier k2 SUBSET (k2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED; SUBSET_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (relative_frontier k1:real^2->bool) /\
                pl_polyhedron (relative_frontier k2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k1,relative_frontier k2)
      ((b0':real^N->real^N) o ((p:real^2->real^N) o (a:real^2->real^2)),
       ((a':real^2->real^2) o (p':real^N->real^2)) o (b0:real^N->real^N))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k1:real^2->bool`; `d:real^2->bool`; `a:real^2->real^2`;
                   `a':real^2->real^2`; `relative_frontier k1:real^2->bool`]
      MOI_FMB_PLH_RESTRICT) THEN
    MP_TAC(ISPECL [`k2:real^N->bool`; `e:real^N->bool`; `b0:real^N->real^N`;
                   `b0':real^N->real^N`; `relative_frontier k2:real^N->bool`]
      MOI_FMB_PLH_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (b0:real^N->real^N) (relative_frontier k2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `IMAGE (a:real^2->real^2) (relative_frontier k1)` THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:real^2->bool`; `k2:real^N->bool`; `2`;
                 `(b0':real^N->real^N) o ((p:real^2->real^N) o (a:real^2->real^2))`;
                 `((a':real^2->real^2) o (p':real^N->real^2)) o (b0:real^N->real^N)`]
    PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hh:real^2->real^N` (X_CHOOSE_THEN `hh':real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(b0:real^N->real^N) o ((hh:real^2->real^N) o (a':real^2->real^2))`;
                        `((a:real^2->real^2) o (hh':real^N->real^2)) o (b0':real^N->real^N)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k1:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  UNDISCH_TAC `pl_homeomorphism (k1,d) ((a:real^2->real^2),(a':real^2->real^2))` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a':real^2->real^2) ((a:real^2->real^2) z) = z` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `relative_frontier k1 SUBSET (k1:real^2->bool)` THEN
    UNDISCH_TAC `(z:real^2) IN relative_frontier k1` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM] THEN
  SUBGOAL_THEN `(p:real^2->real^N) ((a:real^2->real^2) z) IN
                IMAGE (b0:real^N->real^N) (relative_frontier k2)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (IMAGE (a:real^2->real^2) (relative_frontier k1),
                   IMAGE (b0:real^N->real^N) (relative_frontier k2))
                   ((p:real^2->real^N),(p':real^N->real^2))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (p:real^2->real^N) (IMAGE (a:real^2->real^2) (relative_frontier k1)) =
                 IMAGE (b0:real^N->real^N) (relative_frontier k2)` THEN
    UNDISCH_TAC `(z:real^2) IN relative_frontier k1` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism (k2,e) ((b0:real^N->real^N),(b0':real^N->real^N))` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `IMAGE (b0:real^N->real^N) k2 = e` THEN
  UNDISCH_TAC `relative_frontier k2 SUBSET (k2:real^N->bool)` THEN
  UNDISCH_TAC `(p:real^2->real^N) ((a:real^2->real^2) z) IN
               IMAGE (b0:real^N->real^N) (relative_frontier k2)` THEN
  SET_TAC[]);;

(* PL cells and their rims are polyhedra. *)

let MOI_LA2_CELL_POLY = prove
 (`!n (d:real^N->bool) j.
     pl_cell_with_boundary n d j
     ==> pl_polyhedron d /\ pl_polyhedron j /\ compact d /\ compact j /\ j SUBSET d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^N`
    (X_CHOOSE_THEN `q:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool) /\
                pl_polyhedron (k:real^N->bool) /\ pl_polyhedron (relative_frontier k)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[relative_frontier] THEN
      ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED; SUBSET_DIFF];
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_PL_POLYHEDRON];
      MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (IMAGE (p:real^N->real^N) k) /\
                pl_polyhedron (IMAGE (p:real^N->real^N) (relative_frontier k))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (p:real^N->real^N) k = d` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. The common facts of the swap and the nested case.  D1 =               *)
(* j1 UNION inside j1 (innermost) and D2 = j2 UNION inside j2.  In the     *)
(* nested case D1 lies inside j2: the new map is f o phi on D2, phi : D2 -> *)
(* D1 a PL homeomorphism that matches the two sheets on j2 (the cone        *)
(* extension of (f|j1)^-1 o f|j2); its image f(D1) misses f(T DIFF D2).     *)
(* ------------------------------------------------------------------------- *)

(* The statement of MOI_LA1_CASE2_BIJ (pc_moi_lt_cuta1). *)

let moi_la2_case2_bij =
 `!c (f:real^2->real^N) k j1 j2.
     moi_lt_singular_disk c f /\ k IN components (moi_lt_double_image f) /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\ DISJOINT j1 j2 /\
     compact j1 /\ compact j2 /\ connected j1 /\ connected j2 /\
     ~(j1 = {}) /\ ~(j2 = {})
     ==> IMAGE f j1 = k /\ IMAGE f j2 = k /\
         (!x y. x IN j1 /\ y IN j1 /\ f x = f y ==> x = y) /\
         (!x y. x IN j2 /\ y IN j2 /\ f x = f y ==> x = y)`;;

let MOI_LA2_SWAP_FACTS = prove
 (mk_imp(moi_la2_case2_bij,
  `!(c:(real^N->bool)->bool) (f:real^2->real^N) k (j1:real^2->bool) j2.
     moi_lt_normal2_disk c f /\
     k IN components (moi_lt_double_image f) /\
     pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ DISJOINT j1 j2 /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\
     j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     {x | x IN inside j1 /\ f x IN moi_lt_double_image f} = {}
     ==> IMAGE f j1 = k /\ IMAGE f j2 = k /\
         (!x y. x IN j1 /\ y IN j1 /\ f x = f y ==> x = y) /\
         (!x y. x IN j2 /\ y IN j2 /\ f x = f y ==> x = y) /\
         (!x. x IN j1 UNION inside j1 /\ f x IN moi_lt_double_image f ==> x IN j1) /\
         (!x y. x IN j1 UNION inside j1 /\ y IN j1 UNION inside j1 /\ f x = f y
                ==> x = y) /\
         IMAGE f (j1 UNION inside j1) SUBSET UNIONS c DIFF complex_boundary c`),
  DISCH_THEN(LABEL_TAC "bij") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LT2D_NORMAL2_IMP; moi_lt_normal_disk]; ALL_TAC] THEN
  MP_TAC(ISPEC `j1:real^2->bool` MOI_LA2_JORDAN_DISK) THEN
  MP_TAC(ISPEC `j2:real^2->bool` MOI_LA2_JORDAN_DISK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  USE_THEN "bij" (MP_TAC o SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `k:real^N->bool`; `j1:real^2->bool`; `j2:real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!x. x IN j1 UNION inside j1 /\ (f:real^2->real^N) x IN moi_lt_double_image f
                    ==> x IN j1`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    UNDISCH_TAC `{x | x IN inside j1 /\ (f:real^2->real^N) x IN moi_lt_double_image f} = {}` THEN
    UNDISCH_TAC `(f:real^2->real^N) x IN moi_lt_double_image f` THEN
    UNDISCH_TAC `(x:real^2) IN j1 UNION inside j1` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^N) x IN moi_lt_double_image f` ASSUME_TAC THENL
     [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `y:real^2`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle` THEN
      MAP_EVERY UNDISCH_TAC [`(x:real^2) IN j1 UNION inside j1`;
                             `(y:real^2) IN j1 UNION inside j1`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN j1 /\ (y:real^2) IN j1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(x:real^2 = y)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `j1:real^2->bool`)) (concl th) &&
      not (can (find_term (fun t -> t = `inside:(real^2->bool)->real^2->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
                 relative_frontier std_triangle` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) std_triangle SUBSET UNIONS c` THEN
    UNDISCH_TAC `j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle` THEN
    REWRITE_TAC[EXTENSION; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[]]);;

(* The restrictions of f to j1 and j2 are PL homeomorphisms onto k. *)

let MOI_LA2_RIM_PLH = prove
 (`!(f:real^2->real^N) j k.
     pl_map_on std_triangle f /\ pl_sphere 1 j /\ j SUBSET std_triangle /\
     IMAGE f j = k /\ (!x y. x IN j /\ y IN j /\ f x = f y ==> x = y)
     ==> ?h. pl_homeomorphism (j,k) (f,h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `j:real^2->bool` MOI_LA2_JORDAN_DISK) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LA2_CELL_POLY) THEN
  SUBGOAL_THEN `pl_map_on j (f:real^2->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `f:real^2->real^N`; `k:real^N->bool`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `h:real^N->real^2`)] THEN
  EXISTS_TAC `h:real^N->real^2` THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[]);;

(* The nested case. *)

let MOI_LA2_NESTED = prove
 (mk_imp(mk_conj(moi_la2_image_component,moi_la2_case2_bij),
  `!(c:(real^N->bool)->bool) (f:real^2->real^N) k (j1:real^2->bool) j2.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_normal2_disk c f /\
     k IN components (moi_lt_double_image f) /\
     pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ DISJOINT j1 j2 /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\
     j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     j2 UNION inside j2 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     {x | x IN inside j1 /\ f x IN moi_lt_double_image f} = {} /\
     j1 UNION inside j1 SUBSET inside j2
     ==> ?f'. moi_lt_normal2_disk c f' /\
              moi_lt_disk_complexity f' < moi_lt_disk_complexity f /\
              !x. x IN relative_frontier std_triangle ==> f' x = f x`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ic") (LABEL_TAC "bij")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "bij" (fun bij -> MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `k:real^N->bool`; `j1:real^2->bool`; `j2:real^2->bool`]
    (MP MOI_LA2_SWAP_FACTS bij))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N) /\
                pl_map_on std_triangle (f:real^2->real^N)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LT2D_NORMAL2_IMP; moi_lt_normal_disk; moi_lt_singular_disk];
    ALL_TAC] THEN
  MP_TAC(ISPEC `j1:real^2->bool` MOI_LA2_JORDAN_DISK) THEN
  MP_TAC(ISPEC `j2:real^2->bool` MOI_LA2_JORDAN_DISK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`2`; `j1 UNION inside j1:real^2->bool`; `j1:real^2->bool`]
    MOI_LA2_CELL_POLY) THEN
  MP_TAC(ISPECL [`2`; `j2 UNION inside j2:real^2->bool`; `j2:real^2->bool`]
    MOI_LA2_CELL_POLY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  (* the rims are PL homeomorphic to k *)
  MP_TAC(ISPECL [`f:real^2->real^N`; `j1:real^2->bool`; `k:real^N->bool`]
    MOI_LA2_RIM_PLH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle` THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `h1:real^N->real^2`)] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `j2:real^2->bool`; `k:real^N->bool`]
    MOI_LA2_RIM_PLH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j2 UNION inside j2 SUBSET std_triangle DIFF relative_frontier std_triangle` THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `h2:real^N->real^2`)] THEN
  SUBGOAL_THEN `!y. y IN k ==> (f:real^2->real^N) ((h1:real^N->real^2) y) = y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (j1,k) ((f:real^2->real^N),(h1:real^N->real^2))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  (* the disk map phi : D2 -> D1 *)
  MP_TAC(ISPECL [`j2 UNION inside j2:real^2->bool`; `j2:real^2->bool`;
                 `j1 UNION inside j1:real^2->bool`; `j1:real^2->bool`;
                 `(h1:real^N->real^2) o (f:real^2->real^N)`;
                 `(h2:real^N->real^2) o (f:real^2->real^N)`] MOI_LA2_CELL_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^2->real^2` (X_CHOOSE_THEN `phi':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    can (find_term (fun t -> t = `phi:real^2->real^2`)) (concl th) &&
    is_comb (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_homeomorphism"))
        (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (find_term (fun t -> t = `phi:real^2->real^2`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "homeomorphism"))
        (concl th))) THEN
  (* the replacement *)
  USE_THEN "ic" (fun ic -> MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `(f:real^2->real^N) o (phi:real^2->real^2)`; `j2 UNION inside j2:real^2->bool`;
    `k:real^N->bool`] (MP MOI_LA2_REPLACE ic))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(* PL *)
      MATCH_MP_TAC MOI_LA2_PASTE THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
        EXISTS_TAC `j1 UNION inside j1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
          ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
          UNDISCH_TAC `j1 UNION inside j1 SUBSET
                       std_triangle DIFF relative_frontier std_triangle` THEN SET_TAC[];
          UNDISCH_TAC `IMAGE (phi:real^2->real^2) (j2 UNION inside j2) = j1 UNION inside j1` THEN
          SET_TAC[]];
        X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(x:real^2) IN j2` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`(x:real^2) IN j2 UNION inside j2`;
                                 `~((x:real^2) IN inside j2)`] THEN SET_TAC[];
          ALL_TAC] THEN
        ASM_SIMP_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `IMAGE (f:real^2->real^N) j2 = k` THEN
        UNDISCH_TAC `(x:real^2) IN j2` THEN SET_TAC[]];
      (* image in the interior of c *)
      REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
      (* injective *)
      REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(phi:real^2->real^2) x = phi y` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `inside:(real^2->bool)->real^2->bool`)) (concl th) &&
          can (find_term (fun t -> t = `j1:real^2->bool`)) (concl th) &&
          not (can (find_term (fun t -> t = `moi_lt_double_image:(real^2->real^N)->real^N->bool`))
                (concl th)))) THEN
        REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `IMAGE (phi:real^2->real^2) (j2 UNION inside j2) = j1 UNION inside j1` THEN
          UNDISCH_TAC `(x:real^2) IN j2 UNION inside j2` THEN SET_TAC[];
          UNDISCH_TAC `IMAGE (phi:real^2->real^2) (j2 UNION inside j2) = j1 UNION inside j1` THEN
          UNDISCH_TAC `(y:real^2) IN j2 UNION inside j2` THEN SET_TAC[];
          FIRST_ASSUM ACCEPT_TAC];
        DISCH_TAC THEN
        SUBGOAL_THEN `(phi':real^2->real^2) (phi x) = x /\ phi' (phi y) = (y:real^2)`
        MP_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN MESON_TAC[]]];
      (* the new disk misses the rest of the image *)
      REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; IN_DIFF] THEN
      X_GEN_TAC `w:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(f:real^2->real^N) b = f a` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`w = (f:real^2->real^N) a`; `w = (f:real^2->real^N) b`] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(a:real^2 = b)` ASSUME_TAC THENL
       [UNDISCH_TAC `j1 UNION inside j1 SUBSET inside (j2:real^2->bool)` THEN
        MAP_EVERY UNDISCH_TAC [`(a:real^2) IN j1 UNION inside j1`;
                               `~((b:real^2) IN j2 UNION inside j2)`] THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:real^2->real^N) a IN moi_lt_double_image f` ASSUME_TAC THENL
       [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`a:real^2`; `b:real^2`] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `j1 UNION inside j1 SUBSET
                     std_triangle DIFF relative_frontier std_triangle` THEN
        UNDISCH_TAC `(a:real^2) IN j1 UNION inside j1` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(a:real^2) IN j1` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(b:real^2) IN j1 UNION j2` MP_TAC THENL
       [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} = j1 UNION j2` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (f:real^2->real^N) j1 = k` THEN
        UNDISCH_TAC `(a:real^2) IN j1` THEN UNDISCH_TAC `(f:real^2->real^N) b = f a` THEN
        SET_TAC[];
        UNDISCH_TAC `j1 UNION inside j1 SUBSET inside (j2:real^2->bool)` THEN
        UNDISCH_TAC `~((b:real^2) IN j2 UNION inside j2)` THEN SET_TAC[]];
      (* k is covered *)
      UNDISCH_TAC `IMAGE (f:real^2->real^N) j2 = k` THEN SET_TAC[];
      (* source double points outside k are interior to D2 *)
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((x:real^2) IN j2)` MP_TAC THENL
       [UNDISCH_TAC `~((f:real^2->real^N) x IN k)` THEN
        UNDISCH_TAC `IMAGE (f:real^2->real^N) j2 = k` THEN SET_TAC[];
        UNDISCH_TAC `(x:real^2) IN j2 UNION inside j2` THEN SET_TAC[]]];
    STRIP_TAC THEN
    EXISTS_TAC `\x. if x IN j2 UNION inside j2
                    then ((f:real^2->real^N) o (phi:real^2->real^2)) x else f x` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 6. The separate case from the clean cap, and the swap.  In the           *)
(* separate case the cap gives a polygon j around D2 (no source double      *)
(* points between j and j2) and a PL disk d with rim f(j) meeting the image *)
(* only in f(j); the new map sends j UNION inside j onto d, matching f on j *)
(* (cone extension).  Both cases are instances of MOI_LA2_REPLACE.          *)
(* ------------------------------------------------------------------------- *)

let MOI_LA2_SEPARATE = prove
 (mk_imp(list_mk_conj [moi_la2_image_component; moi_la2_case2_bij; MOI_LT3_CLEAN_CAP],
  `!(c:(real^N->bool)->bool) (f:real^2->real^N) k (j1:real^2->bool) j2.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_normal2_disk c f /\
     k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {} /\
     pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ DISJOINT j1 j2 /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\
     j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     j2 UNION inside j2 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     {x | x IN inside j1 /\ f x IN moi_lt_double_image f} = {} /\
     DISJOINT (j1 UNION inside j1) (j2 UNION inside j2)
     ==> ?f'. moi_lt_normal2_disk c f' /\
              moi_lt_disk_complexity f' < moi_lt_disk_complexity f /\
              !x. x IN relative_frontier std_triangle ==> f' x = f x`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ic") (CONJUNCTS_THEN2 (LABEL_TAC "bij")
    (LABEL_TAC "cap"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "cap" (MP_TAC o SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `k:real^N->bool`; `j1:real^2->bool`; `j2:real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^2->bool` (X_CHOOSE_THEN `d:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "bij" (fun bij -> MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `k:real^N->bool`; `j1:real^2->bool`; `j2:real^2->bool`]
    (MP MOI_LA2_SWAP_FACTS bij))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_map_on std_triangle (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LT2D_NORMAL2_IMP; moi_lt_normal_disk; moi_lt_singular_disk];
    ALL_TAC] THEN
  MP_TAC(ISPEC `j:real^2->bool` MOI_LA2_JORDAN_DISK) THEN
  MP_TAC(ISPEC `j2:real^2->bool` MOI_LA2_JORDAN_DISK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`2`; `j UNION inside j:real^2->bool`; `j:real^2->bool`]
    MOI_LA2_CELL_POLY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  (* j misses D2, so it carries no source double point *)
  SUBGOAL_THEN `!x. x IN j ==> ~((f:real^2->real^N) x IN moi_lt_double_image f)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `{x | x IN (j UNION inside j) DIFF (j2 UNION inside j2) /\
                      (f:real^2->real^N) x IN moi_lt_double_image f} = {}` THEN
    UNDISCH_TAC `j2 UNION inside j2 SUBSET inside (j:real^2->bool)` THEN
    UNDISCH_TAC `inside j INTER j:real^2->bool = {}` THEN
    UNDISCH_TAC `(x:real^2) IN j` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN j /\ y IN j /\ (f:real^2->real^N) x = f y ==> x = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^N) x IN moi_lt_double_image f` MP_TAC THENL
     [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `y:real^2`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `j UNION inside j SUBSET std_triangle DIFF relative_frontier std_triangle` THEN
      MAP_EVERY UNDISCH_TAC [`(x:real^2) IN j`; `(y:real^2) IN j`] THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the rim map and the disk map *)
  MP_TAC(ISPECL [`f:real^2->real^N`; `j:real^2->bool`; `IMAGE (f:real^2->real^N) j`]
    MOI_LA2_RIM_PLH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j UNION inside j SUBSET std_triangle DIFF relative_frontier std_triangle` THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `hj:real^N->real^2`)] THEN
  MP_TAC(ISPECL [`j UNION inside j:real^2->bool`; `j:real^2->bool`; `d:real^N->bool`;
                 `IMAGE (f:real^2->real^N) j`; `f:real^2->real^N`; `hj:real^N->real^2`]
    MOI_LA2_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^N` (X_CHOOSE_THEN `g':real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    can (find_term (fun t -> t = `g:real^2->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_homeomorphism"))
        (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (find_term (fun t -> t = `g:real^2->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "homeomorphism"))
        (concl th))) THEN
  (* the replacement *)
  USE_THEN "ic" (fun ic -> MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `g:real^2->real^N`; `j UNION inside j:real^2->bool`; `k:real^N->bool`]
    (MP MOI_LA2_REPLACE ic))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(* PL *)
      MATCH_MP_TAC MOI_LA2_PASTE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(x:real^2) IN j UNION inside j`;
                             `~((x:real^2) IN inside j)`] THEN SET_TAC[];
      (* injective *)
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(g':real^N->real^2) (g x) = x /\ g' (g y) = (y:real^2)` MP_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN MESON_TAC[]];
      (* the disk misses the rest of the image *)
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; IN_DIFF] THEN
      X_GEN_TAC `w:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `b:real^2` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(w:real^N) IN d INTER IMAGE f std_triangle` MP_TAC THENL
       [REWRITE_TAC[IN_INTER; IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `b:real^2` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `d INTER IMAGE (f:real^2->real^N) std_triangle = IMAGE f j` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(f:real^2->real^N) x0 IN moi_lt_double_image f` MP_TAC THENL
       [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`x0:real^2`; `b:real^2`] THEN
        SUBGOAL_THEN `(f:real^2->real^N) b = f x0` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`w = (f:real^2->real^N) x0`; `w = (f:real^2->real^N) b`] THEN
          MESON_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `j UNION inside j SUBSET std_triangle DIFF relative_frontier std_triangle` THEN
        UNDISCH_TAC `~((b:real^2) IN j UNION inside j)` THEN
        UNDISCH_TAC `(x0:real^2) IN j` THEN SET_TAC[];
        ASM_SIMP_TAC[]];
      (* k is covered *)
      UNDISCH_TAC `IMAGE (f:real^2->real^N) j2 = k` THEN
      UNDISCH_TAC `j2 UNION inside j2 SUBSET inside (j:real^2->bool)` THEN SET_TAC[];
      (* source double points outside k are interior to zz *)
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      UNDISCH_TAC `{x | x IN (j UNION inside j) DIFF (j2 UNION inside j2) /\
                        (f:real^2->real^N) x IN moi_lt_double_image f} = {}` THEN
      UNDISCH_TAC `j2 UNION inside j2 SUBSET inside (j:real^2->bool)` THEN
      MAP_EVERY UNDISCH_TAC [`(x:real^2) IN j UNION inside j`;
                             `(f:real^2->real^N) x IN moi_lt_double_image f`] THEN
      SET_TAC[]];
    STRIP_TAC THEN
    EXISTS_TAC `\x. if x IN j UNION inside j then (g:real^2->real^N) x else f x` THEN
    ASM_REWRITE_TAC[]]);;

(* The swap, conditional on the statements of the two lemmas of           *)
(* pc_moi_lt_cuta1.                                                         *)

let MOI_LA2_SWAP_COND = prove
 (mk_imp(mk_conj(moi_la2_image_component,moi_la2_case2_bij), MOI_LT3_SWAP_FROM_CAP),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ic") (LABEL_TAC "bij")) THEN
  DISCH_THEN(LABEL_TAC "cap") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`j1:real^2->bool`; `j2:real^2->bool`] MOI_LA2_NEST_CASES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [USE_THEN "ic" (fun ic -> USE_THEN "bij" (fun bij ->
      MATCH_MP_TAC(MP MOI_LA2_NESTED (CONJ ic bij)))) THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `j1:real^2->bool`; `j2:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "ic" (fun ic -> USE_THEN "bij" (fun bij -> USE_THEN "cap" (fun cap ->
      MATCH_MP_TAC(MP MOI_LA2_SEPARATE (CONJ ic (CONJ bij cap)))))) THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `j1:real^2->bool`; `j2:real^2->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. The main theorem. The two antecedents of MOI_LA2_SWAP_COND are         *)
(* MOI_LA1_IMAGE_COMPONENT and MOI_LA1_CASE2_BIJ (pc_moi_lt_cuta1).          *)
(* ------------------------------------------------------------------------- *)

let SWAP_FROM_CAP = prove
 (MOI_LT3_SWAP_FROM_CAP,
  ACCEPT_TAC(MP MOI_LA2_SWAP_COND (CONJ MOI_LA1_IMAGE_COMPONENT MOI_LA1_CASE2_BIJ)));;

