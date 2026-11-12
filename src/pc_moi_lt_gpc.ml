needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_lt_cutc.ml";;
needs "src/pc_moi_ptri.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_lt_gpc: CROSSINGS_NORMAL, a step of the loop theorem (Moise        *)
(* GTM 47, p.184): a singular disk whose double points are all crossings is  *)
(* normal.  Main theorem CROSSINGS_NORMAL : |- MOI_LT_CROSSINGS_NORMAL       *)
(* (pc_moi_loop_stmt.ml).  Route: the double image D is compact (local       *)
(* injectivity keeps the pairs off the diagonal) and locally polyhedral      *)
(* (near each point it is the PL image of an axis segment of the crossing    *)
(* chart), so a polyhedron, triangulated by a finite complex s; the crossing *)
(* charts give one or two unit ray directions of D at each point             *)
(* (moi_lcc_dirs of pc_moi_lt_cutc), one exactly at the points of            *)
(* complex_boundary c; and a finite complex with one or two ray directions   *)
(* at every point is a combinatorial 1-manifold with boundary whose boundary *)
(* vertices are the one-direction points.                                    *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* The double image of a singular disk is compact.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LGC_DOUBLE_COMPACT = prove
 (`!c (f:real^2->real^N).
     moi_lt_singular_disk c f ==> compact (moi_lt_double_image f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM] o
    check (fun th -> can (term_match []
      `!x:real^2. x IN std_triangle ==> ?n. open n /\ x IN n /\ P n x`) (concl th))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:real^2->real^2->bool` (LABEL_TAC "inj")) THEN
  ABBREV_TAC `G = UNIONS {(nn:real^2->real^2->bool) x PCROSS nn x | x IN std_triangle}` THEN
  SUBGOAL_THEN `open (G:real^(2,2)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC OPEN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC OPEN_PCROSS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `Q = {z | z IN std_triangle PCROSS std_triangle /\
             (\z:real^(2,2)finite_sum. (f:real^2->real^N)(fstcart z) - f(sndcart z)) z =
             vec 0}` THEN
  SUBGOAL_THEN `compact (Q:real^(2,2)finite_sum->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `(std_triangle:real^2->bool) PCROSS std_triangle` THEN
      SIMP_TAC[BOUNDED_PCROSS; COMPACT_IMP_BOUNDED; MOI_LTD_STD_TRIANGLE_BASIC] THEN
      EXPAND_TAC "Q" THEN SET_TAC[];
      EXPAND_TAC "Q" THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
      SIMP_TAC[CLOSED_PCROSS; MOI_LTD_STD_TRIANGLE_BASIC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_lt_double_image (f:real^2->real^N) =
    IMAGE ((f:real^2->real^N) o fstcart) (Q DIFF G:real^(2,2)finite_sum->bool)`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_lt_double_image] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; o_THM] THEN
    EXPAND_TAC "Q" THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART; IN_UNIONS; EXISTS_IN_GSPEC;
                VECTOR_SUB_EQ] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `x':real^2`] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NOT_EXISTS_THM; PASTECART_IN_PCROSS] THEN
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      USE_THEN "inj" (MP_TAC o C MATCH_MP (ASSUME `(z:real^2) IN std_triangle`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^2`; `x':real^2`] o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[IN_INTER];
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `x':real^2`] THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
        is_exists (rand (concl th)))) THEN
      REWRITE_TAC[] THEN EXISTS_TAC `x:real^2` THEN
      USE_THEN "inj" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN std_triangle`)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(x:real^2) = x'`)) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[COMPACT_DIFF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle:real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "Q" THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_ELIM_THM; FORALL_PASTECART;
              PASTECART_IN_PCROSS; FSTCART_PASTECART] THEN
  SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Sets with axis charts are locally polyhedral; the double image of a      *)
(* singular disk with crossings is a polyhedron.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_LGC_AXIS_NORM = prove
 (`!z:real^3. z$1 = &0 /\ z$2 = &0 ==> norm z = abs(z$3)`,
  GEN_TAC THEN REWRITE_TAC[vector_norm; dot; DIMINDEX_3; SUM_3] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

(* A compact polytope piece of the axis inside the model ball or half ball,  *)
(* containing the axis points of norm less than 1/2.                         *)

let MOI_LGC_AXIS_PIECE = prove
 (`!B:real^3->bool.
     B = ball(vec 0,&1) \/ B = ball(vec 0,&1) INTER {z | &0 <= z$3}
     ==> ?P. polytope P /\ P SUBSET B INTER {z | z$1 = &0 /\ z$2 = &0} /\
             B INTER {z | z$1 = &0 /\ z$2 = &0} INTER ball(vec 0,inv(&2)) SUBSET P`,
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `interval[vector[&0;&0;--inv(&2)]:real^3,vector[&0;&0;inv(&2)]]`;
    EXISTS_TAC `interval[vec 0:real^3,vector[&0;&0;inv(&2)]]`] THEN
  REWRITE_TAC[POLYTOPE_INTERVAL; SUBSET; IN_INTER; IN_ELIM_THM; IN_BALL_0; IN_INTERVAL;
              DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
  CONJ_TAC THEN X_GEN_TAC `z:real^3` THEN
  ASM_CASES_TAC `(z:real^3)$1 = &0 /\ (z:real^3)$2 = &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOI_LGC_AXIS_NORM] THEN ASM_REAL_ARITH_TAC);;

(* A set X inside a polyhedron Y with an axis chart at each point (a PL     *)
(* homeomorphism of an open set of Y onto the unit ball or half ball,        *)
(* carrying X onto the z3-axis) is locally polyhedral.                       *)

let MOI_LGC_CHART_LOCALLY_POLYHEDRAL = prove
 (`!(Y:real^N->bool) X.
     X SUBSET Y /\
     (!w. w IN X
          ==> ?u (h:real^N->real^3) h'.
                open_in (subtopology euclidean Y) u /\ w IN u /\
                pl_homeomorphism (u,IMAGE h u) (h,h') /\ h w = vec 0 /\
                (IMAGE h u = ball(vec 0,&1) \/
                 IMAGE h u = ball(vec 0,&1) INTER {z | &0 <= z$3}) /\
                IMAGE h (X INTER u) = IMAGE h u INTER {z | z$1 = &0 /\ z$2 = &0})
     ==> locally_polyhedral X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[locally_polyhedral] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^N) IN X`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPEC `IMAGE (h:real^N->real^3) u` MOI_LGC_AXIS_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_polyhedron (IMAGE (h':real^3->real^N) P)` MP_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (h:real^N->real^3) u` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (h':real^3->real^N) P SUBSET X` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (h:real^N->real^3) (X INTER u)` MP_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN P` THEN
      UNDISCH_TAC `P SUBSET IMAGE (h:real^N->real^3) u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}` THEN
      UNDISCH_TAC `IMAGE (h:real^N->real^3) (X INTER u) =
                   IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean Y)
            {y | y IN u /\ (h:real^N->real^3) y IN ball(vec 0,inv(&2))}`
  MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:(real^N->bool)->bool`; `v:real^N->bool`] THEN
  SUBGOAL_THEN `(w:real^N) IN v` ASSUME_TAC THENL
   [SUBGOAL_THEN `(w:real^N) IN {y | y IN u /\ (h:real^N->real^3) y IN ball(vec 0,inv(&2))}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL; REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH];
      UNDISCH_TAC `{y | y IN u /\ (h:real^N->real^3) y IN ball(vec 0,inv(&2))} = Y INTER v` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `X INTER v SUBSET UNIONS (k:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN u /\ (h:real^N->real^3) y IN ball(vec 0,inv(&2))`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^N) IN Y INTER v` MP_TAC THENL
       [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(X:real^N->bool) SUBSET Y` THEN UNDISCH_TAC `(y:real^N) IN X` THEN
        SET_TAC[];
        UNDISCH_TAC `{y | y IN u /\ (h:real^N->real^3) y IN ball(vec 0,inv(&2))} = Y INTER v` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^3) y IN IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}`
    ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        lhand (concl th) = `IMAGE (h:real^N->real^3) (X INTER u)`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^3) y IN P` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^N->real^3) u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} INTER
                   ball(vec 0,inv(&2)) SUBSET P` THEN
      UNDISCH_TAC `(h:real^N->real^3) y IN IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}` THEN
      UNDISCH_TAC `(h:real^N->real^3) y IN ball(vec 0,inv(&2))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) = (h':real^3->real^N) (h y)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rand (concl th) = `UNIONS (k:(real^N->bool)->bool)`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k':real^N->bool` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (k:(real^N->bool)->bool)` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    rand (concl th) = `UNIONS (k:(real^N->bool)->bool)`)) THEN
  ASM_REWRITE_TAC[]);;

(* The axis chart of a crossing (dropping the sheets).                       *)

let MOI_LGC_CROSSING_CHART = prove
 (`!c (f:real^2->real^N) y.
     moi_lt_crossing_at c f y
     ==> ?u (h:real^N->real^3) h'.
           open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
           pl_homeomorphism (u,IMAGE h u) (h,h') /\ h y = vec 0 /\
           ((~(y IN complex_boundary c) /\ IMAGE h u = ball(vec 0,&1)) \/
            (y IN complex_boundary c /\
             IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3})) /\
           IMAGE h (moi_lt_double_image f INTER u) =
           IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_crossing_at] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGC_DOUBLE_SUBSET = prove
 (`!c (f:real^2->real^N).
     moi_lt_singular_disk c f ==> moi_lt_double_image f SUBSET UNIONS c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_singular_disk; moi_lt_double_image] THEN
  STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]);;

let MOI_LGC_DOUBLE_PL = prove
 (`!c (f:real^2->real^N).
     moi_lt_singular_disk c f /\
     (!y. y IN moi_lt_double_image f ==> moi_lt_crossing_at c f y)
     ==> pl_polyhedron (moi_lt_double_image f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PTR_COMPACT_LOCALLY_POLYHEDRAL THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_LGC_DOUBLE_COMPACT]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGC_CHART_LOCALLY_POLYHEDRAL THEN
  EXISTS_TAC `UNIONS c:real^N->bool` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_LGC_DOUBLE_SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N`]
    MOI_LGC_CROSSING_CHART) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* A PL map is affine on an initial piece of any ray germ in its domain.    *)

let MOI_LGC_PL_RAY = prove
 (`!(S:real^M->bool) (g:real^M->real^N) x d e.
     pl_map_on S g /\ x IN S /\ &0 < e /\
     (!t. &0 < t /\ t < e ==> x + t % d IN S)
     ==> ?t0 a. &0 < t0 /\ t0 < e /\
                !t. &0 <= t /\ t <= t0 ==> g(x + t % d) = g x + t % a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o GEN_REWRITE_RULE I [pl_map_on]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` (X_CHOOSE_THEN `u:real^M->bool`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `open(u:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`d:real^M`; `r:real`] MOI_LCC_SMALL_MUL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `x:real^M`; `d:real^M`; `min e e1`]
    MOI_LCC_GERM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[POLYTOPE_IMP_CLOSED]; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `x + t % d IN (S:real^M->bool) INTER u` MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `ball(x:real^M,r) SUBSET u` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL; NORM_ARITH
        `dist(x:real^M,x + y) = norm y`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `t1:real`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool` o check (fun th -> can (term_match []
    `!k:real^M->bool. k IN c ==> polytope k /\ P k`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`t1:real`; `(l:real^M->real^N) d`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `x + t % d IN (k:real^M->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^M->bool` POLYTOPE_IMP_CONVEX) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONVEX_ALT] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `x + t1 % d:real^M`; `t / t1`]) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % x + u % (x + v % d):real^M = x + (u * v) % d`] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < t1` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  VECTOR_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Ray directions at the centre of an axis chart: the two half-axes are     *)
(* mapped affinely near the centre (MOI_LGC_PL_RAY), and every ray direction *)
(* of X passes through one of them (MOI_LGC_CHART_POINT).                    *)
(* ------------------------------------------------------------------------- *)

(* One side of an axis chart: h' is affine on an initial piece of the       *)
(* half-axis through sg, and its direction is a ray direction of X at w.     *)

let MOI_LGC_CHART_SIDE = prove
 (`!(X:real^N->bool) u (h:real^N->real^3) h' w (sg:real^3).
     pl_homeomorphism (u,IMAGE h u) (h,h') /\ w IN u /\ h w = vec 0 /\
     IMAGE h (X INTER u) = IMAGE h u INTER {z | z$1 = &0 /\ z$2 = &0} /\
     sg$1 = &0 /\ sg$2 = &0 /\ ~(sg = vec 0) /\
     (!t. &0 <= t /\ t < &1 ==> t % sg IN IMAGE h u)
     ==> ?t0 a. &0 < t0 /\ t0 < &1 /\ ~(a = vec 0) /\
                (!t. &0 <= t /\ t <= t0 ==> h'(t % sg) = w + t % a) /\
                inv(norm a) % a IN moi_lcc_dirs X w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(h':real^3->real^N) (vec 0) = w /\ vec 0 IN IMAGE (h:real^N->real^3) u`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(h:real^N->real^3) w = vec 0`)) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) u`; `h':real^3->real^N`; `vec 0:real^3`;
                 `sg:real^3`; `&1`] MOI_LGC_PL_RAY) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LID; REAL_LT_01] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= t0 ==> t % sg IN IMAGE (h:real^N->real^3) u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t. &0 <= t /\ t < &1 ==> t % sg IN IMAGE (h:real^N->real^3) u`) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(h':real^3->real^N) (t0 % sg) = h' (vec 0)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL; VECTOR_MUL_RZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `h:real^N->real^3`) THEN
    SUBGOAL_THEN `(h:real^N->real^3) ((h':real^3->real^N) (t0 % sg)) = t0 % sg /\
                  (h:real^N->real^3) ((h':real^3->real^N) (vec 0)) = vec 0`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!y:real^3. y IN IMAGE (h:real^N->real^3) u ==> h(h' y) = y`) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t0:real`; `a:real^N`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `t0 * norm(a:real^N)` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; NORM_POS_LT] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t / norm(a:real^N) /\ t / norm a <= t0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; NORM_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `w + t % inv(norm a) % a = (h':real^3->real^N) ((t / norm(a:real^N)) % sg)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t / norm(a:real^N)) % sg IN IMAGE (h:real^N->real^3) (X INTER u)` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_MUL_COMPONENT; REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

(* A ray direction at w gives points of X INTER u near w with small chart    *)
(* image.                                                                     *)

let MOI_LGC_CHART_NEAR = prove
 (`!(Y:real^N->bool) X u (h:real^N->real^3) w d ee.
     X SUBSET Y /\ open_in (subtopology euclidean Y) u /\ w IN u /\
     h continuous_on u /\ d IN moi_lcc_dirs X w /\ &0 < ee
     ==> ?t. &0 < t /\ w + t % d IN X /\ w + t % d IN u /\
             norm(h(w + t % d) - h w) < ee`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC))))) THEN
  UNDISCH_TAC `open_in (subtopology euclidean Y) (u:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N) IN o1` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `open(o1:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(h:real^N->real^3) continuous_on u` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `ee:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e (min r dl) / &2` THEN
  SUBGOAL_THEN `&0 < min e (min r dl) / &2 /\ min e (min r dl) / &2 < e /\
                min e (min r dl) / &2 < r /\ min e (min r dl) / &2 < dl`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = min e (min r dl) / &2` THEN
  SUBGOAL_THEN `dist(w + t % d:real^N,w) = t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_ARITH `dist(w + y:real^N,w) = norm y`; NORM_MUL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `w + t % d IN (X:real^N->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `w + t % d IN (u:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `w + t % d IN ball(w:real^N,r)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `ball(w:real^N,r) SUBSET o1` THEN
    UNDISCH_TAC `(u:real^N->bool) = Y INTER o1` THEN
    UNDISCH_TAC `(X:real^N->bool) SUBSET Y` THEN
    UNDISCH_TAC `w + t % d IN (X:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w + t % d IN Y INTER (o1:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `w + t % d IN (u:real^N->bool)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM dist] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* A ray direction at w passes through an axis point of the chart of small *)
(* nonzero height.                                                          *)

let MOI_LGC_CHART_POINT = prove
 (`!(Y:real^N->bool) X u (h:real^N->real^3) h' w d ee.
     X SUBSET Y /\ open_in (subtopology euclidean Y) u /\ w IN u /\
     pl_homeomorphism (u,IMAGE h u) (h,h') /\ h w = vec 0 /\
     IMAGE h (X INTER u) = IMAGE h u INTER {z | z$1 = &0 /\ z$2 = &0} /\
     d IN moi_lcc_dirs X w /\ &0 < ee
     ==> ?t tau. &0 < t /\ ~(tau = &0) /\ abs tau < ee /\
                 tau % basis 3 IN IMAGE h u /\
                 w + t % d = h'(tau % basis 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`Y:real^N->bool`; `X:real^N->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `w:real^N`; `d:real^N`; `ee:real`] MOI_LGC_CHART_NEAR) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `z = (h:real^N->real^3) (w + t % d)` THEN
  SUBGOAL_THEN `(z:real^3) IN IMAGE (h:real^N->real^3) u INTER {z | z$1 = &0 /\ z$2 = &0}`
  MP_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `IMAGE (h:real^N->real^3) (X INTER u)`)) THEN
    EXPAND_TAC "z" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `z = ((z:real^3)$3) % basis 3` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(norm(d:real^N) = &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^N) IN moi_lcc_dirs X w` THEN
    REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `(z:real^3)$3`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `z:real^3 = vec 0` ASSUME_TAC THENL
     [FIRST_X_ASSUM((fun th -> ONCE_REWRITE_TAC[th]) o check (fun th ->
        concl th = `z = ((z:real^3)$3) % basis 3`)) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `w + t % d = (w:real^N)` MP_TAC THENL
     [SUBGOAL_THEN `w + t % d = (h':real^3->real^N) z /\ w = h' (vec 0)`
      (fun th -> ONCE_REWRITE_TAC[th]) THENL
       [CONJ_TAC THENL
         [EXPAND_TAC "z" THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
            concl th = `(h:real^N->real^3) w = vec 0`)) THEN
          CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[VECTOR_ARITH `w + t % d:real^N = w <=> t % d = vec 0`] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ; GSYM NORM_EQ_0] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(z:real^3)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`z:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `z = ((z:real^3)$3) % basis 3`)) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `z = ((z:real^3)$3) % basis 3`)) THEN
    EXPAND_TAC "z" THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LGC_E3 = prove
 (`(basis 3:real^3)$1 = &0 /\ (basis 3:real^3)$2 = &0 /\ (basis 3:real^3)$3 = &1 /\
   ~(basis 3:real^3 = vec 0) /\ norm(basis 3:real^3) = &1 /\
   (--basis 3:real^3)$1 = &0 /\ (--basis 3:real^3)$2 = &0 /\
   ~(--basis 3:real^3 = vec 0)`,
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; VECTOR_NEG_COMPONENT; REAL_NEG_0;
           VECTOR_NEG_EQ_0; BASIS_NONZERO; NORM_BASIS]);;

(* Ray directions at the centre of an axis chart: two for the ball, one for *)
(* the half ball.                                                            *)

let MOI_LGC_CHART_DIRS_BALL = prove
 (`!(Y:real^N->bool) X u (h:real^N->real^3) h' w.
     X SUBSET Y /\ open_in (subtopology euclidean Y) u /\ w IN u /\
     pl_homeomorphism (u,IMAGE h u) (h,h') /\ h w = vec 0 /\
     IMAGE h (X INTER u) = IMAGE h u INTER {z | z$1 = &0 /\ z$2 = &0} /\
     IMAGE h u = ball(vec 0,&1)
     ==> moi_lcc_dirs X w HAS_SIZE 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    MP_TAC(ISPECL [`X:real^N->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                   `h':real^3->real^N`; `w:real^N`; `basis 3:real^3`] MOI_LGC_CHART_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MOI_LGC_E3; IN_BALL_0; NORM_MUL; REAL_MUL_RID] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`X:real^N->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                   `h':real^3->real^N`; `w:real^N`; `--basis 3:real^3`] MOI_LGC_CHART_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MOI_LGC_E3; IN_BALL_0; NORM_MUL; NORM_NEG; REAL_MUL_RID] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `moi_lcc_dirs X (w:real^N) = {inv(norm a) % a, inv(norm b) % b}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]] THEN
      REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `d:real^N` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `norm(d:real^N) = &1` ASSUME_TAC THENL
       [UNDISCH_TAC `(d:real^N) IN moi_lcc_dirs X w` THEN
        REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`Y:real^N->bool`; `X:real^N->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `w:real^N`; `d:real^N`;
                     `min t0 t1`] MOI_LGC_CHART_POINT) THEN
      ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC)) THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (REAL_ARITH `tau = &0 \/ &0 < tau \/ tau < &0`) THENL
       [UNDISCH_TAC `~(tau = &0)` THEN ASM_REWRITE_TAC[];
        DISJ1_TAC THEN MATCH_MP_TAC MOI_LCC_DIR_SCALE THEN
        MAP_EVERY EXISTS_TAC [`t:real`; `tau:real`] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(VECTOR_ARITH `!w x y:real^N. w + x = w + y ==> x = y`) THEN
        EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!t. &0 <= t /\ t <= t0 ==> (h':real^3->real^N) (t % basis 3) = w + t % a`)
          (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        DISJ2_TAC THEN MATCH_MP_TAC MOI_LCC_DIR_SCALE THEN
        MAP_EVERY EXISTS_TAC [`t:real`; `--tau:real`] THEN
        ASM_REWRITE_TAC[REAL_NEG_GT0] THEN
        MATCH_MP_TAC(VECTOR_ARITH `!w x y:real^N. w + x = w + y ==> x = y`) THEN
        EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `tau % basis 3:real^3 = (--tau) % --basis 3` SUBST1_TAC THENL
         [VECTOR_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!t. &0 <= t /\ t <= t1 ==> (h':real^3->real^N) (t % --basis 3) = w + t % b`)
          (concl th))) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE] THEN
    SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES; IN_INSERT; NOT_IN_EMPTY] THEN
    COND_CASES_TAC THENL [CONV_TAC NUM_REDUCE_CONV; CONV_TAC NUM_REDUCE_CONV] THEN
    (* the two directions differ *)
    ABBREV_TAC `s = min (t0 * norm(a:real^N)) (t1 * norm(b:real^N))` THEN
    SUBGOAL_THEN `&0 < s /\ s / norm(a:real^N) <= t0 /\ s / norm(b:real^N) <= t1 /\
                  &0 < s / norm a /\ &0 < s / norm b`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
       [EXPAND_TAC "s" THEN ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_MUL; NORM_POS_LT];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_DIV; NORM_POS_LT] THEN
      EXPAND_TAC "s" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^N) ((s / norm(a:real^N)) % basis 3) =
                  h' ((s / norm(b:real^N)) % --basis 3)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THEN
      UNDISCH_TAC `inv(norm(a:real^N)) % a = inv(norm(b:real^N)) % b` THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s / norm(a:real^N)) % basis 3 IN IMAGE (h:real^N->real^3) u /\
                  (s / norm(b:real^N)) % --basis 3 IN IMAGE (h:real^N->real^3) u`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_BALL_0; NORM_MUL; NORM_NEG; MOI_LGC_E3; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(s / norm(a:real^N)) % basis 3 = (s / norm(b:real^N)) % --basis 3:real^3`
    MP_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(h:real^N->real^3) ((h':real^3->real^N) ((s / norm(a:real^N)) % basis 3))` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!y:real^3. y IN IMAGE (h:real^N->real^3) u ==> h(h' y) = y`) (concl th))) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq (concl th) &&
          lhand (concl th) = `(h':real^3->real^N) ((s / norm(a:real^N)) % basis 3)`)) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!y:real^3. y IN IMAGE (h:real^N->real^3) u ==> h(h' y) = y`) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\z:real^3. z$3`) THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT; MOI_LGC_E3] THEN
    ASM_REAL_ARITH_TAC);;

let MOI_LGC_CHART_DIRS_HALF = prove
 (`!(Y:real^N->bool) X u (h:real^N->real^3) h' w.
     X SUBSET Y /\ open_in (subtopology euclidean Y) u /\ w IN u /\
     pl_homeomorphism (u,IMAGE h u) (h,h') /\ h w = vec 0 /\
     IMAGE h (X INTER u) = IMAGE h u INTER {z | z$1 = &0 /\ z$2 = &0} /\
     IMAGE h u = ball(vec 0,&1) INTER {z | &0 <= z$3}
     ==> moi_lcc_dirs X w HAS_SIZE 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    MP_TAC(ISPECL [`X:real^N->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                   `h':real^3->real^N`; `w:real^N`; `basis 3:real^3`] MOI_LGC_CHART_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MOI_LGC_E3; IN_INTER; IN_ELIM_THM; IN_BALL_0; NORM_MUL;
                      REAL_MUL_RID; VECTOR_MUL_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `moi_lcc_dirs X (w:real^N) = {inv(norm a) % a}` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REWRITE_TAC[SING_SUBSET]] THEN
      REWRITE_TAC[SUBSET; IN_SING] THEN X_GEN_TAC `d:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm(d:real^N) = &1` ASSUME_TAC THENL
       [UNDISCH_TAC `(d:real^N) IN moi_lcc_dirs X w` THEN
        REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`Y:real^N->bool`; `X:real^N->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `w:real^N`; `d:real^N`;
                     `t0:real`] MOI_LGC_CHART_POINT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 <= tau` MP_TAC THENL
         [SUBGOAL_THEN `tau % basis 3 IN ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3}`
          MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
          SIMP_TAC[VECTOR_MUL_COMPONENT; MOI_LGC_E3; REAL_MUL_RID];
          UNDISCH_TAC `~(tau = &0)` THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_LCC_DIR_SCALE THEN
      MAP_EVERY EXISTS_TAC [`t:real`; `tau:real`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(VECTOR_ARITH `!w x y:real^N. w + x = w + y ==> x = y`) THEN
      EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. &0 <= t /\ t <= t0 ==> (h':real^3->real^N) (t % basis 3) = w + t % a`)
        (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[HAS_SIZE; FINITE_SING; CARD_SING]]);;

let MOI_LGC_CHART_DIRS = prove
 (`!(Y:real^N->bool) X u (h:real^N->real^3) h' w.
     X SUBSET Y /\ open_in (subtopology euclidean Y) u /\ w IN u /\
     pl_homeomorphism (u,IMAGE h u) (h,h') /\ h w = vec 0 /\
     IMAGE h (X INTER u) = IMAGE h u INTER {z | z$1 = &0 /\ z$2 = &0}
     ==> (IMAGE h u = ball(vec 0,&1) ==> moi_lcc_dirs X w HAS_SIZE 2) /\
         (IMAGE h u = ball(vec 0,&1) INTER {z | &0 <= z$3}
          ==> moi_lcc_dirs X w HAS_SIZE 1)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_LGC_CHART_DIRS_BALL; MATCH_MP_TAC MOI_LGC_CHART_DIRS_HALF] THEN
  MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                        `h':real^3->real^N`] THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Finite complexes with one or two ray directions everywhere.               *)
(* ------------------------------------------------------------------------- *)

(* The unit direction of a segment from w is a ray direction of any set     *)
(* containing the segment.                                                   *)

let MOI_LGC_SEG_DIR = prove
 (`!(X:real^N->bool) w a.
     ~(a = w) /\ segment[w,a] SUBSET X
     ==> inv(norm(a - w)) % (a - w) IN moi_lcc_dirs X w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(a - w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  EXISTS_TAC `norm(a - w:real^N)` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  MATCH_MP_TAC MOI_LCC_RAY_IN_SEGMENT THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
  VECTOR_ARITH_TAC);;

(* Parallel unit directions from w give collinear points.                    *)

let MOI_LGC_DIR_COLLINEAR = prove
 (`!(w:real^N) a b k.
     ~(a = w) /\ inv(norm(b - w)) % (b - w) = k % inv(norm(a - w)) % (a - w)
     ==> collinear {w,a,b}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `{w,a,b} = {a,w,b}:real^N->bool`] THEN
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
  ASM_CASES_TAC `b:real^N = w` THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN
  EXISTS_TAC `norm(b - w:real^N) * k * inv(norm(a - w:real^N))` THEN
  SUBGOAL_THEN `~(norm(b - w:real^N) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `((%):real->real^N->real^N) (norm(b - w:real^N))`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

(* A convex set of dimension >= 2 has three distinct ray directions at a     *)
(* relative interior point.                                                  *)

let MOI_LGC_THREE_DIRS = prove
 (`!(X:real^N->bool) t.
     convex t /\ t SUBSET X /\ &2 <= aff_dim t
     ==> ?w d1 d2 d3. w IN t /\ d1 IN moi_lcc_dirs X w /\ d2 IN moi_lcc_dirs X w /\
                      d3 IN moi_lcc_dirs X w /\
                      ~(d1 = d2) /\ ~(d1 = d3) /\ ~(d2 = d3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(relative_interior t:real^N->bool = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `&2 <= aff_dim(t:real^N->bool)` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real^N`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?a:real^N. a IN t /\ ~(a = w)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    SUBGOAL_THEN `t = {w:real^N}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&2 <= aff_dim{w:real^N}` THEN REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w:real^N = a)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?b:real^N. b IN t /\ ~collinear {w,a,b}` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    SUBGOAL_THEN `t SUBSET affine hull {w:real^N,a}` MP_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`w:real^N`; `a:real^N`; `b:real^N`] COLLINEAR_3_AFFINE_HULL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_2] THEN
      UNDISCH_TAC `&2 <= aff_dim(t:real^N->bool)` THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b:real^N = w)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear {w:real^N,a,b}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `{w,a,w} = {w,a}:real^N->bool`; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(a - w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ABBREV_TAC `l = (e / &2) / norm(a - w:real^N)` THEN
  SUBGOAL_THEN `&0 < l /\ l * norm(a - w:real^N) = e / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; REAL_DIV_RMUL;
                                      REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ABBREV_TAC `a' = w - l % (a - w:real^N)` THEN
  SUBGOAL_THEN `(a':real^N) IN t` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> can (term_match []
      `ball(w:real^N,e) INTER affine hull t SUBSET t`) (concl th))) THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
     [EXPAND_TAC "a'" THEN
      REWRITE_TAC[NORM_ARITH `dist(w:real^N,w - x) = norm x`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `{w:real^N,a}`; `t:real^N->bool`]
        HULL_MONO) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`&1 + l`; `--l:real`] THEN EXPAND_TAC "a'" THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a':real^N = w)` ASSUME_TAC THENL
   [EXPAND_TAC "a'" THEN
    REWRITE_TAC[VECTOR_ARITH `w - x:real^N = w <=> x = vec 0`; VECTOR_MUL_EQ_0;
                VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm(a' - w)) % (a' - w) = --(inv(norm(a - w)) % (a - w:real^N))`
  ASSUME_TAC THENL
   [EXPAND_TAC "a'" THEN
    REWRITE_TAC[VECTOR_ARITH `(w - x) - w:real^N = --x`; NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`; REAL_INV_MUL; VECTOR_MUL_ASSOC;
                 VECTOR_MUL_RNEG] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < l` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`w:real^N`; `inv(norm(a - w)) % (a - w:real^N)`;
    `inv(norm(a' - w)) % (a' - w:real^N)`; `inv(norm(b - w)) % (b - w:real^N)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LGC_SEG_DIR THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `inv(norm(a' - w)) % (a' - w:real^N)`)) THEN
    MATCH_MP_TAC MOI_LGC_SEG_DIR THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT];
    MATCH_MP_TAC MOI_LGC_SEG_DIR THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT];
    REWRITE_TAC[VECTOR_ARITH `x:real^N = --x <=> x = vec 0`; VECTOR_MUL_EQ_0;
                REAL_INV_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `~collinear {w:real^N,a,b}` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LGC_DIR_COLLINEAR THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID];
    DISCH_TAC THEN UNDISCH_TAC `~collinear {w:real^N,a,b}` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LGC_DIR_COLLINEAR THEN EXISTS_TAC `--(&1)` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID]]);;

(* At most two ray directions everywhere: all simplices have dimension at   *)
(* most 1.                                                                   *)

let MOI_LGC_DIM_DIRS = prove
 (`!s:(real^N->bool)->bool.
     simplicial_complex s /\
     (!w. w IN UNIONS s
          ==> moi_lcc_dirs (UNIONS s) w HAS_SIZE 1 \/
              moi_lcc_dirs (UNIONS s) w HAS_SIZE 2)
     ==> !t. t IN s ==> aff_dim t <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `t:real^N->bool`] MOI_LGC_THREE_DIRS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM SET_TAC[];
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` (X_CHOOSE_THEN `d1:real^N`
    (X_CHOOSE_THEN `d2:real^N` (X_CHOOSE_THEN `d3:real^N` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(w:real^N) IN UNIONS s` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (moi_lcc_dirs (UNIONS s) (w:real^N)) /\
                CARD (moi_lcc_dirs (UNIONS s) w) <= 2`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^N) IN UNIONS s`) o
      check (fun th -> can (term_match []
        `!w:real^N. w IN UNIONS s ==> P w \/ Q w`) (concl th))) THEN
    REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_lcc_dirs (UNIONS s) (w:real^N)`; `d1:real^N`; `d2:real^N`;
                 `d3:real^N`] MOI_LCC_CARD_LE2) THEN
  ASM_REWRITE_TAC[]);;

(* Vertex degrees are direction counts.                                     *)

let MOI_LGC_VERTEX_SIZE = prove
 (`!s (v:real^N).
     simplicial_complex s /\ (!t. t IN s ==> aff_dim t <= &1) /\ {v} IN s
     ==> !n. UNIONS (simplicial_link s v) HAS_SIZE n <=>
             moi_lcc_dirs (UNIONS s) v HAS_SIZE n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ASM_SIMP_TAC[MOI_LCC_LINK_1; MOI_LCC_DIRS_VERTEX] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_LCC_DIRS_INJ THEN
  EXISTS_TAC `s:(real^N->bool)->bool` THEN EXISTS_TAC `v:real^N` THEN
  ASM_REWRITE_TAC[]);;

(* A finite complex with one or two ray directions at each point is a       *)
(* combinatorial 1-manifold with boundary; its boundary vertices are the    *)
(* points with one direction.                                                *)

let MOI_LGC_DIRS_CMWB1 = prove
 (`!s:(real^N->bool)->bool.
     simplicial_complex s /\
     (!w. w IN UNIONS s
          ==> moi_lcc_dirs (UNIONS s) w HAS_SIZE 1 \/
              moi_lcc_dirs (UNIONS s) w HAS_SIZE 2)
     ==> combinatorial_manifold_with_boundary 1 s /\
         (!v. {v} IN s
              ==> (pl_ball 0 (UNIONS (simplicial_link s v)) <=>
                   moi_lcc_dirs (UNIONS s) v HAS_SIZE 1))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN s ==> aff_dim t <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGC_DIM_DIRS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. {v} IN s
               ==> (UNIONS (simplicial_link s v) HAS_SIZE 1 \/
                    UNIONS (simplicial_link s v) HAS_SIZE 2) /\
                   (UNIONS (simplicial_link s v) HAS_SIZE 1 <=>
                    moi_lcc_dirs (UNIONS s) v HAS_SIZE 1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `v:real^N`] MOI_LGC_VERTEX_SIZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOI_LCC_SC_LF; MOI_LCC_PL_SPHERE_0; MOI_LCC_PL_BALL_0] THEN
  CONJ_TAC THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN s`)) THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The main theorem CROSSINGS_NORMAL.                                         *)
(* ------------------------------------------------------------------------- *)

(* Ray directions of the double image: one at the boundary of c, two        *)
(* elsewhere.                                                                *)

let MOI_LGC_DOUBLE_DIRS = prove
 (`!c (f:real^2->real^N) w.
     moi_lt_singular_disk c f /\
     (!y. y IN moi_lt_double_image f ==> moi_lt_crossing_at c f y) /\
     w IN moi_lt_double_image f
     ==> (moi_lcc_dirs (moi_lt_double_image f) w HAS_SIZE 1 \/
          moi_lcc_dirs (moi_lt_double_image f) w HAS_SIZE 2) /\
         (moi_lcc_dirs (moi_lt_double_image f) w HAS_SIZE 1 <=>
          w IN complex_boundary c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N`]
    MOI_LGC_CROSSING_CHART) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `moi_lt_double_image (f:real^2->real^N)`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `w:real^N`]
    MOI_LGC_CHART_DIRS) THEN
  ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[MOI_LGC_DOUBLE_SUBSET]; ALL_TAC]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `(s:real^N->bool) HAS_SIZE 2`) (concl th))) THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let CROSSINGS_NORMAL = prove
 (MOI_LT_CROSSINGS_NORMAL,
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[moi_lt_normal_disk] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`] MOI_LGC_DOUBLE_PL) THEN
  ASM_REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:(real^N->bool)->bool` THEN
  MP_TAC(ISPEC `s:(real^N->bool)->bool` MOI_LGC_DIRS_CMWB1) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N`]
      MOI_LGC_DOUBLE_DIRS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `v:real^N`]
    MOI_LGC_DOUBLE_DIRS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rand (concl th) = `moi_lt_double_image (f:real^2->real^N)`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    SIMP_TAC[]]);;

