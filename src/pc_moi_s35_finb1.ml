(* ========================================================================= *)
(* pc_moi_s35_finb1: the Sec 35 unit s35_fin_b, part 1 (general lemmas for  *)
(* FINAL_R2 of pc_moi_s35_stmt_r2.ml).  A PL 3-ball is split by a properly  *)
(* embedded PL 2-cell into two PL 3-balls (MOI_S5N_SPLIT_BALL, given PL     *)
(* Schoenflies): the two disks of the frontier sphere cut out by the circle *)
(* together with the cell bound balls, and the three disks form a theta     *)
(* complex whose complement has exactly three components, as for a model    *)
(* theta (the number of components of the complement of a closed set in     *)
(* euclidean space is a topological invariant,                              *)
(* CARD_EQ_CONNECTED_COMPONENTS_EUCLIDEAN_COMPLEMENTS of homology.ml).      *)
(* ========================================================================= *)

needs "src/pc_moi_s35_fina.ml";;
needs "src/pc_moi_s35_stmt_r2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. The number of components of the complement of a closed set in real^N  *)
(* is a topological invariant (transfer from euclidean_space).               *)
(* ------------------------------------------------------------------------- *)

let MOI_S5N_BRIDGE = prove
 (`!u:real^N->bool.
     closed u
     ==> closed_in (euclidean_space(dimindex(:N)))
           (IMAGE (\x:real^N i. if 1 <= i /\ i <= dimindex(:N) then x$i else &0) u) /\
         (subtopology euclidean u) homeomorphic_space
         (subtopology (euclidean_space(dimindex(:N)))
           (IMAGE (\x:real^N i. if 1 <= i /\ i <= dimindex(:N) then x$i else &0) u)) /\
         components((:real^N) DIFF u) =_c
         connected_components_of
          (subtopology (euclidean_space(dimindex(:N)))
            (topspace(euclidean_space(dimindex(:N))) DIFF
             IMAGE (\x:real^N i. if 1 <= i /\ i <= dimindex(:N) then x$i else &0) u))`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `g = \x:real^N i. if 1 <= i /\ i <= dimindex(:N) then x$i else &0` THEN
  ABBREV_TAC `ee = euclidean_space(dimindex(:N))` THEN
  SUBGOAL_THEN `homeomorphic_map (euclidean:(real^N)topology,ee) (g:real^N->num->real)`
  ASSUME_TAC THENL
   [MP_TAC HOMEOMORPHIC_MAPS_EUCLIDEAN_SPACE_EUCLIDEAN THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[HOMEOMORPHIC_MAPS_MAP];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_EUCLIDEAN; IN_UNIV]) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `u:real^N->bool` o MATCH_MP HOMEOMORPHIC_MAP_CLOSEDNESS_EQ) THEN
    ASM_REWRITE_TAC[GSYM CLOSED_IN; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    MATCH_MP_TAC HOMEOMORPHIC_MAP_IMP_HOMEOMORPHIC_SPACE THEN
    EXISTS_TAC `g:real^N->num->real` THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    UNDISCH_TAC `IMAGE (g:real^N->num->real) (:real^N) = topspace ee` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM EUCLIDEAN_CONNECTED_COMPONENTS_OF] THEN
  SUBGOAL_THEN
   `connected_components_of (subtopology ee (topspace ee DIFF IMAGE g u)) =
    IMAGE (IMAGE (g:real^N->num->real))
          (connected_components_of (subtopology euclidean ((:real^N) DIFF u)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_MAP_CONNECTED_COMPONENTS_OF THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (g:real^N->num->real) (:real^N) = topspace ee`;
      `!x y. (g:real^N->num->real) x = g y <=> x = y`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN MATCH_MP_TAC CARD_EQ_IMAGE THEN
  MAP_EVERY X_GEN_TAC [`c1:real^N->bool`; `c2:real^N->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^N->num->real` INJECTIVE_IMAGE) THEN
  ASM_MESON_TAC[]);;

let MOI_S5N_COMPONENTS_HOMEOMORPHIC = prove
 (`!s t:real^N->bool.
     closed s /\ closed t /\ s homeomorphic t
     ==> components((:real^N) DIFF s) =_c components((:real^N) DIFF t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` MOI_S5N_BRIDGE) THEN
  MP_TAC(ISPEC `t:real^N->bool` MOI_S5N_BRIDGE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g = \x:real^N i. if 1 <= i /\ i <= dimindex(:N) then x$i else &0` THEN
  ABBREV_TAC `ee = euclidean_space(dimindex(:N))` THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:(num->real)->bool`,`:B`] CARD_EQ_TRANS) THEN
  EXISTS_TAC `connected_components_of
               (subtopology ee (topspace ee DIFF IMAGE (g:real^N->num->real) s))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INST_TYPE [`:(num->real)->bool`,`:B`] CARD_EQ_TRANS) THEN
  EXISTS_TAC `connected_components_of
               (subtopology ee (topspace ee DIFF IMAGE (g:real^N->num->real) t))` THEN
  CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN ASM_REWRITE_TAC[]] THEN
  EXPAND_TAC "ee" THEN MATCH_MP_TAC CARD_EQ_CONNECTED_COMPONENTS_EUCLIDEAN_COMPLEMENTS THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INST_TYPE [`:real^N`,`:B`] HOMEOMORPHIC_SPACE_TRANS) THEN
  EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:real^N`,`:B`] HOMEOMORPHIC_SPACE_TRANS) THEN
  EXISTS_TAC `subtopology euclidean (t:real^N->bool)` THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_SPACE_EUCLIDEAN]);;

(* ------------------------------------------------------------------------- *)
(* 2. The model theta: the frontiers of the two halves of the model cube     *)
(* (moi_s35_upper, moi_s35_lower), which meet in the middle square; its      *)
(* three disks (the two cups and the square) are PL 2-cells with the common *)
(* boundary circle, and its complement has exactly three components.        *)
(* ------------------------------------------------------------------------- *)

(* A copy of the first MOI_S5C_SPHERE_PLH of pc_moi_s35_minc (that name is  *)
(* rebound later in the same unit, so the first statement is not reachable). *)

let MOI_S5N_SPHERE_PLH = prove
 (`!n (s:real^M->bool) (t:real^N->bool).
     pl_sphere n s /\ pl_sphere n t ==> ?f g. pl_homeomorphism (s,t) (f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^M->bool` (X_CHOOSE_THEN `f1:real^M->real^M`
     (X_CHOOSE_THEN `g1:real^M->real^M` STRIP_ASSUME_TAC)))
   (X_CHOOSE_THEN `k2:real^N->bool` (X_CHOOSE_THEN `f2:real^N->real^N`
     (X_CHOOSE_THEN `g2:real^N->real^N` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k1:real^M->bool`; `k2:real^N->bool`; `&(n + 1):int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^M->real^N` (X_CHOOSE_THEN `q:real^N->real^M`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(f2:real^N->real^N) o ((p:real^M->real^N) o (g1:real^M->real^M))` THEN
  EXISTS_TAC `((f1:real^M->real^M) o (q:real^N->real^M)) o (g2:real^N->real^N)` THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier(k2:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier(k1:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_S5N_HALVES = prove
 (`moi_s35_upper = interval[vector[-- &1;-- &1;&0],vector[&1;&1;&1]] /\
   moi_s35_lower = interval[vector[-- &1;-- &1;-- &1],vector[&1;&1;&0]] /\
   moi_s35_cube = interval[vector[-- &1;-- &1;-- &1],vector[&1;&1;&1]]`,
  REWRITE_TAC[EXTENSION; moi_s35_upper; moi_s35_lower; moi_s35_cube; IN_ELIM_THM;
              IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT;
              VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S5N_BOX_RF = prove
 (`!a b:real^3.
     (!i. 1 <= i /\ i <= 3 ==> a$i < b$i)
     ==> relative_frontier(interval[a,b]) = interval[a,b] DIFF interval(a,b) /\
         interior(interval[a,b]) = interval(a,b) /\
         ~(interval(a,b) = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interval(a:real^3,b) = {})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_3]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INTERIOR_INTERVAL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_FRONTIER_NONEMPTY_INTERIOR o
    lhand o snd) THEN
  ASM_REWRITE_TAC[INTERIOR_INTERVAL] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FRONTIER_CLOSED_INTERVAL]);;

let MOI_S5N_BOX_CELL = prove
 (`!a b:real^3.
     (!i. 1 <= i /\ i <= 3 ==> a$i < b$i)
     ==> pl_cell_with_boundary 3 (interval[a,b]) (relative_frontier(interval[a,b])) /\
         pl_sphere 2 (relative_frontier(interval[a,b]))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 3 (interval[a:real^3,b])
                                      (relative_frontier(interval[a,b]))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4A_POLY_CELL_3 THEN REWRITE_TAC[POLYTOPE_INTERVAL] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM DIMINDEX_3] THEN
    MATCH_MP_TAC AFF_DIM_NONEMPTY_INTERIOR THEN
    ASM_SIMP_TAC[MOI_S5N_BOX_RF; DIMINDEX_3];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_cell_with_boundary 3 (interval[a:real^3,b])
                                      (relative_frontier(interval[a,b]))` THEN
  REWRITE_TAC[pl_cell_with_boundary; pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `interval[a:real^3,b]`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SIMPLEX_IMP_CLOSED];
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `2` THEN
    MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 + 1 = 3`]]);;

let MOI_S5N_SQ = prove
 (`pl_cell_with_boundary 2
     (IMAGE (moi_s35_lift (&0)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
     (IMAGE (moi_s35_lift (&0))
            (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) /\
   (!x. x IN IMAGE (moi_s35_lift (&0))
               (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) <=>
        x$3 = &0 /\ abs(x$1) <= &1 /\ abs(x$2) <= &1) /\
   (!x. x IN IMAGE (moi_s35_lift (&0))
               (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) <=>
        x$3 = &0 /\ abs(x$1) <= &1 /\ abs(x$2) <= &1 /\
        (abs(x$1) = &1 \/ abs(x$2) = &1))`,
  SUBGOAL_THEN
   `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) =
    interval[--vector[&1;&1],vector[&1;&1]] DIFF interval(--vector[&1;&1],vector[&1;&1])`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_FRONTIER_NONEMPTY_INTERIOR o
      lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FRONTIER_CLOSED_INTERVAL]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5C_LIFT_CELL THEN MATCH_MP_TAC MOI_S5C_POLYTOPE_CELL THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[MOI_S5C_IN_LIFT; moi_s5c_proj; IN_INTERVAL] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN ASM_REWRITE_TAC[MOI_S5C_IN_LIFT; moi_s5c_proj; IN_INTERVAL; IN_DIFF] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC]);;

(* The model theta and its three disks.  Set facts about the half cubes   *)
(* (small coordinate computations), then set algebra.                       *)

let MOI_S5N_HALF_FACTS = prove
 (`pl_sphere 2 (relative_frontier moi_s35_upper) /\
   pl_sphere 2 (relative_frontier moi_s35_lower) /\
   relative_frontier moi_s35_upper = moi_s35_upper DIFF interior moi_s35_upper /\
   relative_frontier moi_s35_lower = moi_s35_lower DIFF interior moi_s35_lower /\
   convex moi_s35_upper /\ convex moi_s35_lower /\
   ~(interior moi_s35_upper = {}) /\ ~(interior moi_s35_lower = {}) /\
   interior moi_s35_upper SUBSET moi_s35_upper /\
   interior moi_s35_lower SUBSET moi_s35_lower /\
   moi_s35_upper UNION moi_s35_lower = moi_s35_cube /\
   moi_s35_upper INTER moi_s35_lower = moi_s35_mid /\
   interior moi_s35_upper INTER moi_s35_lower = {} /\
   interior moi_s35_lower INTER moi_s35_upper = {}`,
  SUBGOAL_THEN
   `(!i. 1 <= i /\ i <= 3
         ==> (vector[-- &1;-- &1;&0]:real^3)$i < (vector[&1;&1;&1]:real^3)$i) /\
    (!i. 1 <= i /\ i <= 3
         ==> (vector[-- &1;-- &1;-- &1]:real^3)$i < (vector[&1;&1;&0]:real^3)$i)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INTERIOR_SUBSET] THEN REWRITE_TAC[MOI_S5N_HALVES] THEN
  ASM_SIMP_TAC[MOI_S5N_BOX_CELL; MOI_S5N_BOX_RF; CONVEX_INTERVAL] THEN
  REWRITE_TAC[moi_s35_mid; MOI_S5N_HALVES] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY;
              IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5N_MID_SQ = prove
 (`IMAGE (moi_s35_lift (&0)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) =
   moi_s35_mid`,
  REWRITE_TAC[EXTENSION; MOI_S5N_SQ] THEN
  REWRITE_TAC[moi_s35_mid; MOI_S5N_HALVES; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3;
              FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5N_MODEL = prove
 (`?d1 d2 m j0:real^3->bool.
     pl_cell_with_boundary 2 d1 j0 /\ pl_cell_with_boundary 2 d2 j0 /\
     pl_cell_with_boundary 2 m j0 /\
     d1 INTER d2 = j0 /\ d1 INTER m = j0 /\ d2 INTER m = j0 /\
     closed d1 /\ closed d2 /\ closed m /\
     d1 UNION d2 UNION m =
     relative_frontier moi_s35_upper UNION relative_frontier moi_s35_lower`,
  MP_TAC MOI_S5N_HALF_FACTS THEN STRIP_TAC THEN
  MP_TAC(CONJUNCT1 MOI_S5N_SQ) THEN REWRITE_TAC[MOI_S5N_MID_SQ] THEN
  ABBREV_TAC `j0 = IMAGE (moi_s35_lift (&0))
                    (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(j0:real^3->bool) SUBSET moi_s35_mid /\ closed moi_s35_mid`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S5C_CELL_COMPACT; MOI_S5C_CELL_COMPACT2; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_mid SUBSET relative_frontier moi_s35_upper /\
                moi_s35_mid SUBSET relative_frontier moi_s35_lower`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`moi_s35_upper INTER moi_s35_lower = moi_s35_mid`;
      `interior moi_s35_upper INTER moi_s35_lower = {}`;
      `interior moi_s35_lower INTER moi_s35_upper = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2
      ((relative_frontier moi_s35_upper DIFF moi_s35_mid) UNION (j0:real^3->bool)) j0 /\
    pl_cell_with_boundary 2
      ((relative_frontier moi_s35_lower DIFF moi_s35_mid) UNION (j0:real^3->bool)) j0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DISK_COMPLEMENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier moi_s35_upper INTER relative_frontier moi_s35_lower =
                moi_s35_mid` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`moi_s35_mid SUBSET relative_frontier moi_s35_upper`;
      `moi_s35_mid SUBSET relative_frontier moi_s35_lower`;
      `relative_frontier moi_s35_upper = moi_s35_upper DIFF interior moi_s35_upper`;
      `relative_frontier moi_s35_lower = moi_s35_lower DIFF interior moi_s35_lower`;
      `moi_s35_upper INTER moi_s35_lower = moi_s35_mid`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(relative_frontier moi_s35_upper DIFF moi_s35_mid) UNION (j0:real^3->bool)`;
    `(relative_frontier moi_s35_lower DIFF moi_s35_mid) UNION (j0:real^3->bool)`;
    `moi_s35_mid`; `j0:real^3->bool`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC
     [`relative_frontier moi_s35_upper INTER relative_frontier moi_s35_lower =
       moi_s35_mid`; `(j0:real^3->bool) SUBSET moi_s35_mid`;
      `moi_s35_mid SUBSET relative_frontier moi_s35_upper`;
      `moi_s35_mid SUBSET relative_frontier moi_s35_lower`] THEN SET_TAC[];
    UNDISCH_TAC `(j0:real^3->bool) SUBSET moi_s35_mid` THEN SET_TAC[];
    UNDISCH_TAC `(j0:real^3->bool) SUBSET moi_s35_mid` THEN SET_TAC[];
    MP_TAC(MATCH_MP MOI_S5C_CELL_COMPACT (ASSUME
      `pl_cell_with_boundary 2
         ((relative_frontier moi_s35_upper DIFF moi_s35_mid) UNION (j0:real^3->bool)) j0`)) THEN
    SIMP_TAC[COMPACT_IMP_CLOSED];
    MP_TAC(MATCH_MP MOI_S5C_CELL_COMPACT (ASSUME
      `pl_cell_with_boundary 2
         ((relative_frontier moi_s35_lower DIFF moi_s35_mid) UNION (j0:real^3->bool)) j0`)) THEN
    SIMP_TAC[COMPACT_IMP_CLOSED];
    FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC
     [`(j0:real^3->bool) SUBSET moi_s35_mid`;
      `moi_s35_mid SUBSET relative_frontier moi_s35_upper`] THEN SET_TAC[]]);;

(* The complement of the model theta has three components. *)

let MOI_S5N_MODEL_COMPONENTS = prove
 (`components((:real^3) DIFF
              (relative_frontier moi_s35_upper UNION relative_frontier moi_s35_lower))
   HAS_SIZE 3`,
  MP_TAC MOI_S5N_HALF_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `components((:real^3) DIFF
               (relative_frontier moi_s35_upper UNION relative_frontier moi_s35_lower)) =
    {interior moi_s35_upper, interior moi_s35_lower, (:real^3) DIFF moi_s35_cube}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC COMPONENTS_OPEN_UNIQUE THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; PAIRWISE_INSERT; PAIRWISE_EMPTY;
                UNIONS_INSERT; UNIONS_0; IN_INSERT] THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN
    SUBGOAL_THEN `open((:real^3) DIFF moi_s35_cube) /\
                  connected((:real^3) DIFF moi_s35_cube)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM closed; moi_s35_cube; CLOSED_INTERVAL] THEN
      MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
      REWRITE_TAC[DIMINDEX_3; ARITH_RULE `2 <= 3`; BOUNDED_INTERVAL; CONVEX_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((:real^3) DIFF moi_s35_cube = {})` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!x:real^3. ~(x IN s) ==> ~(UNIV DIFF s = {})`) THEN
      EXISTS_TAC `vector[&2;&0;&0]:real^3` THEN
      REWRITE_TAC[moi_s35_cube; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERIOR] THEN
    MAP_EVERY UNDISCH_TAC
     [`relative_frontier moi_s35_upper = moi_s35_upper DIFF interior moi_s35_upper`;
      `relative_frontier moi_s35_lower = moi_s35_lower DIFF interior moi_s35_lower`;
      `interior moi_s35_upper SUBSET moi_s35_upper`;
      `interior moi_s35_lower SUBSET moi_s35_lower`;
      `moi_s35_upper UNION moi_s35_lower = moi_s35_cube`;
      `interior moi_s35_upper INTER moi_s35_lower = {}`;
      `interior moi_s35_lower INTER moi_s35_upper = {}`] THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(interior moi_s35_upper = interior moi_s35_lower) /\
    ~(interior moi_s35_upper = (:real^3) DIFF moi_s35_cube) /\
    ~(interior moi_s35_lower = (:real^3) DIFF moi_s35_cube)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(interior moi_s35_upper = {})`; `~(interior moi_s35_lower = {})`;
      `interior moi_s35_upper SUBSET moi_s35_upper`;
      `interior moi_s35_lower SUBSET moi_s35_lower`;
      `moi_s35_upper UNION moi_s35_lower = moi_s35_cube`;
      `interior moi_s35_upper INTER moi_s35_lower = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE] THEN SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* 3. A theta complex: three PL 2-cells with a common boundary circle,      *)
(* pairwise meeting only in it.  It is homeomorphic to the model theta, so  *)
(* its complement has exactly three components.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S5N_THETA_HOMEO = prove
 (`!s1 s2 e j:real^3->bool.
     pl_cell_with_boundary 2 s1 j /\ pl_cell_with_boundary 2 s2 j /\
     pl_cell_with_boundary 2 e j /\
     s1 INTER s2 = j /\ s1 INTER e = j /\ s2 INTER e = j
     ==> (s1 UNION s2 UNION e) homeomorphic
         (relative_frontier moi_s35_upper UNION relative_frontier moi_s35_lower)`,
  REPEAT STRIP_TAC THEN
  MP_TAC MOI_S5N_MODEL THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
    (X_CHOOSE_THEN `m:real^3->bool` (X_CHOOSE_THEN `j0:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    can (find_term ((=) `relative_frontier moi_s35_upper`)) (concl th))) THEN
  SUBGOAL_THEN `?h h'. pl_homeomorphism (j:real^3->bool,j0:real^3->bool) ((h:real^3->real^3),(h':real^3->real^3))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5N_SPHERE_PLH THEN EXISTS_TAC `1` THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_S5E_CELL_SPHERE1 THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) j = j0` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (j:real^3->bool,j0:real^3->bool) ((h:real^3->real^3),(h':real^3->real^3))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (s1:real^3->bool) /\ closed (s2:real^3->bool) /\
                closed (e:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S5C_CELL_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `s1:real^3->bool`; `j:real^3->bool`; `d1:real^3->bool`;
                 `j0:real^3->bool`; `h:real^3->real^3`; `h':real^3->real^3`]
    MOI_S5C_CELL_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^3->real^3` (X_CHOOSE_THEN `g1:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`2`; `s2:real^3->bool`; `j:real^3->bool`; `d2:real^3->bool`;
                 `j0:real^3->bool`; `h:real^3->real^3`; `h':real^3->real^3`]
    MOI_S5C_CELL_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^3->real^3` (X_CHOOSE_THEN `g2:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`2`; `e:real^3->bool`; `j:real^3->bool`; `m:real^3->bool`;
                 `j0:real^3->bool`; `h:real^3->real^3`; `h':real^3->real^3`]
    MOI_S5C_CELL_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f3:real^3->real^3` (X_CHOOSE_THEN `g3:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s1:real^3->bool`; `s2:real^3->bool`; `d1:real^3->bool`;
                 `d2:real^3->bool`; `f1:real^3->real^3`; `g1:real^3->real^3`;
                 `f2:real^3->real^3`; `g2:real^3->real^3`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) j = j0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (u:real^3->real^3) x = v x)
                           ==> IMAGE u s = IMAGE v s`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`s1 UNION s2:real^3->bool`; `e:real^3->bool`;
                 `d1 UNION d2:real^3->bool`; `m:real^3->bool`;
                 `\x:real^3. if x IN s1 then (f1:real^3->real^3) x else f2 x`;
                 `\y:real^3. if y IN d1 then (g1:real^3->real^3) y else g2 y`;
                 `f3:real^3->real^3`; `g3:real^3->real^3`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ASM_SIMP_TAC[CLOSED_UNION] THEN
  SUBGOAL_THEN `(s1 UNION s2) INTER e:real^3->bool = j /\
                (d1 UNION d2) INTER m:real^3->bool = j0` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN s1` (fun th -> REWRITE_TAC[th]) THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]];
      UNDISCH_TAC `IMAGE (h:real^3->real^3) j = j0` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (u:real^3->real^3) x = v x)
                             ==> IMAGE u s = IMAGE v s`) THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN s1` (fun th -> REWRITE_TAC[th]) THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_ASSOC] THEN DISCH_TAC THEN
  REWRITE_TAC[homeomorphic] THEN
  FIRST_X_ASSUM(fun th -> MAP_EVERY EXISTS_TAC
    [lhand(rand(concl th)); rand(rand(concl th))] THEN
    MP_TAC th) THEN
  SIMP_TAC[pl_homeomorphism]);;

let MOI_S5N_THETA_COMPONENTS = prove
 (`!s1 s2 e j:real^3->bool.
     pl_cell_with_boundary 2 s1 j /\ pl_cell_with_boundary 2 s2 j /\
     pl_cell_with_boundary 2 e j /\
     s1 INTER s2 = j /\ s1 INTER e = j /\ s2 INTER e = j
     ==> components((:real^3) DIFF (s1 UNION s2 UNION e)) HAS_SIZE 3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s1 UNION s2 UNION e:real^3->bool`;
                 `relative_frontier moi_s35_upper UNION relative_frontier moi_s35_lower`]
    MOI_S5N_COMPONENTS_HOMEOMORPHIC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
      ASM_MESON_TAC[MOI_S5C_CELL_COMPACT; COMPACT_IMP_CLOSED];
      MATCH_MP_TAC CLOSED_UNION THEN REWRITE_TAC[CLOSED_RELATIVE_FRONTIER];
      MATCH_MP_TAC MOI_S5N_THETA_HOMEO THEN EXISTS_TAC `j:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `3` o MATCH_MP CARD_HAS_SIZE_CONG) THEN
  REWRITE_TAC[MOI_S5N_MODEL_COMPONENTS]);;

(* ------------------------------------------------------------------------- *)
(* 4. A PL 3-ball is split by a properly embedded PL 2-cell into two PL      *)
(* 3-balls.  The circle splits the frontier sphere into two disks s1, s2;   *)
(* s_i UNION e are spheres bounding balls (Schoenflies); the theta s1 UNION *)
(* s2 UNION e has three complement components (inside of each sphere and    *)
(* the outside of the frontier), so the two balls cover the ball and meet   *)
(* only in e.                                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S5N_CLOPEN_COMPONENT = prove
 (`!s c:real^N->bool.
     connected c /\ ~(c = {}) /\ c SUBSET s /\ s INTER frontier c = {}
     ==> c IN components s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `x:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `x:real^N` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`connected_component s (x:real^N)`; `c:real^N->bool`]
    CONNECTED_INTER_FRONTIER) THEN
  REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`] CONNECTED_COMPONENT_SUBSET) THEN
  SUBGOAL_THEN `(x:real^N) IN connected_component s x` MP_TAC THENL
   [REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(y:real^N) IN connected_component s x`; `~((y:real^N) IN c)`;
    `(x:real^N) IN c`; `s INTER frontier c:real^N->bool = {}`] THEN
  SET_TAC[]);;

let MOI_S5N_FILL_FRONTIER = prove
 (`!s:real^3->bool.
     pl_sphere 2 s
     ==> frontier(s UNION inside s) = s /\ interior(s UNION inside s) = inside s /\
         closed(s UNION inside s) /\ s UNION inside s = (:real^3) DIFF outside s`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_PLSPH_JB) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_JB_CLOSURE) THEN
  SUBGOAL_THEN `s UNION inside s = (:real^3) DIFF outside s` ASSUME_TAC THENL
   [REWRITE_TAC[UNION_WITH_INSIDE]; ALL_TAC] THEN
  SUBGOAL_THEN `closed(s UNION inside s:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `interior(s UNION inside s:real^3->bool) = inside s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[SUBSET_UNION] THEN
      ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN s` ASSUME_TAC THENL
     [MP_TAC(ISPEC `s UNION inside s:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^3) IN interior(s UNION inside s)` THEN
      UNDISCH_TAC `~((y:real^3) IN inside s)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN closure(outside s)` MP_TAC THENL
     [UNDISCH_TAC `(s:real^3->bool) SUBSET closure(outside s)` THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    UNDISCH_TAC `(y:real^3) IN interior(s UNION inside s)` THEN
    REWRITE_TAC[IN_INTERIOR] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN s UNION inside s` MP_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,r) SUBSET s UNION inside s` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) IN outside s` THEN
    UNDISCH_TAC `s UNION inside s = (:real^3) DIFF outside s` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[frontier] THEN
  SUBGOAL_THEN `closure(s UNION inside s:real^3->bool) = s UNION inside s` SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th ->
    concl th = `interior(s UNION inside s:real^3->bool) = inside s`)) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  UNDISCH_TAC `DISJOINT (s:real^3->bool) (inside s)` THEN SET_TAC[]);;

let MOI_S5N_SIDE = prove
 (`!s a b e j:real^3->bool.
     pl_sphere 2 s /\ outside s SUBSET outside(b UNION e) /\
     pl_cell_with_boundary 2 a j /\ a SUBSET s /\
     (b DIFF j) INTER (a DIFF j) = {} /\ e INTER (a DIFF j) = {} /\
     j SUBSET b /\ pl_sphere 2 (b UNION e)
     ==> (a DIFF j) SUBSET outside(b UNION e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `b UNION e:real^3->bool` MOI_S5C_PLSPH_JB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET closure(outside s)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^3->bool` MOI_S5C_JB_CLOSURE) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected(a DIFF j:real^3->bool) /\ ~(a DIFF j:real^3->bool = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S4D_PL_CELL_OPEN_CONNECTED];
      MP_TAC(ISPECL [`a:real^3->bool`; `j:real^3->bool`] MOI_S5F_CELL_NOT_BOUNDARY) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a DIFF j) INTER (b UNION e:real^3->bool) = {}` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(b DIFF j) INTER (a DIFF j):real^3->bool = {}`;
      `e INTER (a DIFF j):real^3->bool = {}`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a DIFF j) SUBSET inside(b UNION e:real^3->bool) \/
                (a DIFF j) SUBSET outside(b UNION e:real^3->bool)` MP_TAC THENL
   [MP_TAC(ISPECL [`a DIFF j:real^3->bool`; `inside(b UNION e:real^3->bool)`]
      CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(a DIFF j) INTER (b UNION e:real^3->bool) = {}`;
      `inside(b UNION e) UNION outside(b UNION e) = (:real^3) DIFF (b UNION e)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(a DIFF j:real^3->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `p:real^3`) THEN
  SUBGOAL_THEN `(p:real^3) IN closure(outside s) /\ (p:real^3) IN inside(b UNION e)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(p:real^3) IN a DIFF j`; `(a:real^3->bool) SUBSET s`;
      `(s:real^3->bool) SUBSET closure(outside s)`;
      `(a DIFF j) SUBSET inside(b UNION e:real^3->bool)`] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`inside(b UNION e:real^3->bool)`; `outside s:real^3->bool`]
    OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~p /\ q ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(p:real^3) IN closure(outside s)`; `(p:real^3) IN inside(b UNION e)`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`outside s SUBSET outside(b UNION e:real^3->bool)`;
      `inside(b UNION e) INTER outside(b UNION e:real^3->bool) = {}`] THEN
    SET_TAC[]]);;

let MOI_S5N_SPLIT_BALL = prove
 (`!x e j:real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ pl_ball 3 x /\ pl_cell_with_boundary 2 e j /\
     e SUBSET x /\ e INTER frontier x = j
     ==> ?x1 x2 s1 s2.
           pl_ball 3 x1 /\ pl_ball 3 x2 /\ x1 UNION x2 = x /\ x1 INTER x2 = e /\
           pl_cell_with_boundary 2 s1 j /\ pl_cell_with_boundary 2 s2 j /\
           s1 UNION s2 = frontier x /\ s1 INTER s2 = j /\
           frontier x1 = s1 UNION e /\ frontier x2 = s2 UNION e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_sphere 2 (frontier x:real^3->bool) /\
    frontier x UNION inside(frontier x) = (x:real^3->bool) /\
    (:real^3) DIFF x = outside(frontier x) /\
    connected(outside(frontier x:real^3->bool)) /\
    ~bounded(outside(frontier x:real^3->bool))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `x:real^3->bool` MOI_S5F_BALL_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s = frontier x:real^3->bool` THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET e /\ (j:real^3->bool) SUBSET s /\ pl_sphere 1 j`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S5C_CELL_COMPACT2];
      UNDISCH_TAC `e INTER s:real^3->bool = j` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S5E_CELL_SPHERE1 THEN EXISTS_TAC `e:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `j:real^3->bool`] SPHERE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^3->bool` (X_CHOOSE_THEN `s2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `s1 INTER e:real^3->bool = j /\ s2 INTER e:real^3->bool = j /\
                (j:real^3->bool) SUBSET s1 /\ (j:real^3->bool) SUBSET s2 /\
                (s1:real^3->bool) SUBSET s /\ (s2:real^3->bool) SUBSET s /\
                (s2 DIFF j) INTER (s1 DIFF j):real^3->bool = {} /\
                (s1 DIFF j) INTER (s2 DIFF j):real^3->bool = {} /\
                e INTER (s1 DIFF j):real^3->bool = {} /\
                e INTER (s2 DIFF j):real^3->bool = {}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`s1 UNION s2:real^3->bool = s`; `s1 INTER s2:real^3->bool = j`;
      `e INTER s:real^3->bool = j`; `(j:real^3->bool) SUBSET e`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (s1 UNION e:real^3->bool) /\
                pl_sphere 2 (s2 UNION e:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DISK_UNION THEN EXISTS_TAC `j:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `outside s SUBSET outside(s1 UNION e:real^3->bool) /\
                outside s SUBSET outside(s2 UNION e:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5F_SUBSET_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(s1:real^3->bool) SUBSET s`; `(s2:real^3->bool) SUBSET s`;
      `(e:real^3->bool) SUBSET x`; `(:real^3) DIFF x = outside s`;
      `s UNION inside s:real^3->bool = x`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s2 DIFF j) SUBSET outside(s1 UNION e:real^3->bool) /\
                (s1 DIFF j) SUBSET outside(s2 UNION e:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5N_SIDE THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t1 = s1 UNION e:real^3->bool` THEN
  ABBREV_TAC `t2 = s2 UNION e:real^3->bool` THEN
  MP_TAC(MATCH_MP MOI_S5C_PLSPH_JB (ASSUME `pl_sphere 2 (t1:real^3->bool)`)) THEN
  MP_TAC(MATCH_MP MOI_S5C_PLSPH_JB (ASSUME `pl_sphere 2 (t2:real^3->bool)`)) THEN
  MP_TAC(MATCH_MP MOI_S5C_PLSPH_JB (ASSUME `pl_sphere 2 (s:real^3->bool)`)) THEN
  REPEAT(DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  (* the theta and its three complement components *)
  ABBREV_TAC `th = s1 UNION s2 UNION e:real^3->bool` THEN
  SUBGOAL_THEN `components((:real^3) DIFF th) HAS_SIZE 3` ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN MATCH_MP_TAC MOI_S5N_THETA_COMPONENTS THEN
    EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 UNION (s2 DIFF j) = th /\ t2 UNION (s1 DIFF j) = th /\
                s UNION (e:real^3->bool) = th` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `s1 UNION s2 UNION e:real^3->bool = th`); SYM(ASSUME `s1 UNION e:real^3->bool = t1`); SYM(ASSUME `s2 UNION e:real^3->bool = t2`)] THEN
    MAP_EVERY UNDISCH_TAC
     [`s1 UNION s2:real^3->bool = s`; `(j:real^3->bool) SUBSET s1`;
      `(j:real^3->bool) SUBSET s2`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside t1 IN components((:real^3) DIFF th) /\
                inside t2 IN components((:real^3) DIFF th) /\
                outside s IN components((:real^3) DIFF th)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S5N_CLOPEN_COMPONENT THEN
    ASM_REWRITE_TAC[] THENL
     [MAP_EVERY UNDISCH_TAC
       [`t1 UNION (s2 DIFF j:real^3->bool) = th`;
        `(s2 DIFF j) SUBSET outside(t1:real^3->bool)`;
        `DISJOINT (t1:real^3->bool) (inside t1)`;
        `inside t1 INTER outside(t1:real^3->bool) = {}`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`t2 UNION (s1 DIFF j:real^3->bool) = th`;
        `(s1 DIFF j) SUBSET outside(t2:real^3->bool)`;
        `DISJOINT (t2:real^3->bool) (inside t2)`;
        `inside t2 INTER outside(t2:real^3->bool) = {}`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`s UNION (e:real^3->bool) = th`; `(e:real^3->bool) SUBSET x`;
        `(:real^3) DIFF x = outside s`;
        `DISJOINT (s:real^3->bool) (outside s)`] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(inside t1:real^3->bool = inside t2) /\
                ~(inside t1:real^3->bool = outside s) /\
                ~(inside t2:real^3->bool = outside s)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(t1:real^3->bool) = t2` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SYM(ASSUME `s1 UNION e:real^3->bool = t1`); SYM(ASSUME `s2 UNION e:real^3->bool = t2`)] THEN
      SUBGOAL_THEN `~(s1 DIFF j:real^3->bool = {})` MP_TAC THENL
       [MP_TAC(ISPECL [`s1:real^3->bool`; `j:real^3->bool`] MOI_S5F_CELL_NOT_BOUNDARY) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(s1 DIFF j) INTER (s2 DIFF j):real^3->bool = {}`;
        `e INTER (s1 DIFF j):real^3->bool = {}`] THEN SET_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `components((:real^3) DIFF th) = {inside t1, inside t2, outside s}`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    UNDISCH_TAC `components((:real^3) DIFF th) HAS_SIZE 3` THEN
    REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]; ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(:real^3) DIFF th = inside t1 UNION inside t2 UNION outside s /\
                inside t1 INTER inside t2:real^3->bool = {}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3) DIFF th` UNIONS_COMPONENTS) THEN
      ASM_REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY];
      MP_TAC(ISPEC `(:real^3) DIFF th` PAIRWISE_DISJOINT_COMPONENTS) THEN
      ASM_REWRITE_TAC[pairwise; IN_INSERT; NOT_IN_EMPTY; DISJOINT] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_ball 3 (t1 UNION inside t1:real^3->bool) /\
                pl_ball 3 (t2 UNION inside t2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `PL_SCHOENFLIES_3_STATEMENT` THEN
    REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t1 UNION inside t1) UNION (t2 UNION inside t2):real^3->bool = x`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(:real^3) DIFF th = inside t1 UNION inside t2 UNION outside s`;
      `s1 UNION s2 UNION e:real^3->bool = th`;
      `s1 UNION e:real^3->bool = t1`; `s2 UNION e:real^3->bool = t2`;
      `s1 UNION s2:real^3->bool = s`;
      `(:real^3) DIFF x = outside s`; `(e:real^3->bool) SUBSET x`;
      `s UNION inside s:real^3->bool = x`;
      `inside t1 INTER outside(t1:real^3->bool) = {}`;
      `inside t2 INTER outside(t2:real^3->bool) = {}`;
      `outside s SUBSET outside(t1:real^3->bool)`;
      `outside s SUBSET outside(t2:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t1 UNION inside t1) INTER (t2 UNION inside t2):real^3->bool = e`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`inside t1 INTER inside t2:real^3->bool = {}`;
      `(s2 DIFF j) SUBSET outside(t1:real^3->bool)`;
      `(s1 DIFF j) SUBSET outside(t2:real^3->bool)`;
      `inside t1 INTER outside(t1:real^3->bool) = {}`;
      `inside t2 INTER outside(t2:real^3->bool) = {}`;
      `DISJOINT (t1:real^3->bool) (inside t1)`;
      `DISJOINT (t2:real^3->bool) (inside t2)`;
      `s1 INTER s2:real^3->bool = j`; `(j:real^3->bool) SUBSET e`;
      `s1 UNION e:real^3->bool = t1`; `s2 UNION e:real^3->bool = t2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`t1 UNION inside t1:real^3->bool`; `t2 UNION inside t2:real^3->bool`;
    `s1:real^3->bool`; `s2:real^3->bool`] THEN
  ASM_SIMP_TAC[MOI_S5N_FILL_FRONTIER]);;

