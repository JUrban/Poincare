(* ========================================================================= *)
(* Sanity theorems for poincare_statement.ml.                                *)
(*  - the new notions agree with the library's for subsets of real^N;        *)
(*  - the 3-sphere satisfies all hypotheses of POINCARE_STATEMENT, so the    *)
(*    statement is not vacuous;                                              *)
(*  - teeth: the circle is not simply connected in the new sense;            *)
(*  - POINCARE_STATEMENT implies the embedded form.                          *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;

(* ------------------------------------------------------------------------- *)
(* Simple connectivity: the general notion agrees with the library's.        *)
(* ------------------------------------------------------------------------- *)

let PC_CONTINUOUS_MAP_LIFT_DROP_UNIT = prove
 (`continuous_map (subtopology euclideanreal (real_interval[&0,&1]),
                   subtopology euclidean (interval[vec 0:real^1,vec 1])) lift /\
   continuous_map (subtopology euclidean (interval[vec 0:real^1,vec 1]),
                   subtopology euclideanreal (real_interval[&0,&1])) drop`,
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_LIFT;
           CONTINUOUS_MAP_DROP] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; IMAGE_DROP_INTERVAL] THEN
  REWRITE_TAC[LIFT_NUM; DROP_VEC; SUBSET_REFL]);;

let SIMPLY_CONNECTED_SPACE_EUCLIDEAN = prove
 (`!s:real^N->bool.
        simply_connected_space (subtopology euclidean s) <=>
        simply_connected s`,
  GEN_TAC THEN REWRITE_TAC[simply_connected_space; simply_connected] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(p:real^1->real^N) o lift`; `(q:real^1->real^N) o lift`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
      ASM_MESON_TAC[pathstart; pathfinish];
      DISCH_TAC] THEN
    REWRITE_TAC[homotopic_loops] THEN
    SUBGOAL_THEN
     `p = ((p:real^1->real^N) o lift) o drop /\
      q = ((q:real^1->real^N) o lift) o drop`
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL
     [`\r:real->real^N. r(&1) = r(&0)`;
      `\r:real^1->real^N. pathfinish r = pathstart r`;
      `(p:real^1->real^N) o lift`; `(q:real^1->real^N) o lift`;
      `drop`;
      `subtopology euclidean (interval[vec 0:real^1,vec 1])`;
      `subtopology euclideanreal (real_interval[&0,&1])`;
      `subtopology euclidean (s:real^N->bool)`]
     HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_RIGHT) THEN
    ASM_REWRITE_TAC[PC_CONTINUOUS_MAP_LIFT_DROP_UNIT] THEN
    REWRITE_TAC[pathstart; pathfinish; o_THM; DROP_VEC] THEN
    MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`p:real->real^N`; `q:real->real^N`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(p:real->real^N) o drop`; `(q:real->real^N) o drop`]) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[PATH_IN_EUCLIDEAN]) THEN
      ASM_REWRITE_TAC[pathstart; pathfinish; o_THM; DROP_VEC];
      REWRITE_TAC[homotopic_loops] THEN DISCH_TAC] THEN
    SUBGOAL_THEN
     `p = ((p:real->real^N) o drop) o lift /\
      q = ((q:real->real^N) o drop) o lift`
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL
     [`\r:real^1->real^N. pathfinish r = pathstart r`;
      `\r:real->real^N. r(&1) = r(&0)`;
      `(p:real->real^N) o drop`; `(q:real->real^N) o drop`;
      `lift`;
      `subtopology euclideanreal (real_interval[&0,&1])`;
      `subtopology euclidean (interval[vec 0:real^1,vec 1])`;
      `subtopology euclidean (s:real^N->bool)`]
     HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_RIGHT) THEN
    ASM_REWRITE_TAC[PC_CONTINUOUS_MAP_LIFT_DROP_UNIT] THEN
    REWRITE_TAC[pathstart; pathfinish; o_THM; LIFT_NUM] THEN
    MESON_TAC[]]);;

let SIMPLY_CONNECTED_SPACE_SPHERE_3 = prove
 (`simply_connected_space
     (subtopology euclidean (sphere(vec 0:real^4,&1)))`,
  REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EUCLIDEAN] THEN
  MATCH_MP_TAC SIMPLY_CONNECTED_SPHERE THEN
  REWRITE_TAC[DIMINDEX_4] THEN ARITH_TAC);;

let NOT_SIMPLY_CONNECTED_SPACE_CIRCLE = prove
 (`~simply_connected_space
      (subtopology euclidean (sphere(vec 0:real^2,&1)))`,
  REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EUCLIDEAN; SIMPLY_CONNECTED_SPHERE_EQ] THEN
  REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC(DEPTH_CONV NUM_LE_CONV) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Local Euclideanness of subspaces of real^N, and of the 3-sphere.          *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN = prove
 (`!s:real^N->bool.
        locally_euclidean_space (:M) (subtopology euclidean s) <=>
        !x. x IN s
            ==> ?U. open_in (subtopology euclidean s) U /\ x IN U /\
                    U homeomorphic (:real^M)`,
  GEN_TAC THEN
  REWRITE_TAC[locally_euclidean_space; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN
   `!U:real^N->bool.
        open_in (subtopology euclidean (s:real^N->bool)) U
        ==> (subtopology (subtopology euclidean s) U homeomorphic_space
             (euclidean:(real^M)topology) <=>
             U homeomorphic (:real^M))`
   (fun th -> MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[SUBTOPOLOGY_SUBTOPOLOGY;
               SET_RULE `(u:A->bool) SUBSET s ==> s INTER u = u`] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM SUBTOPOLOGY_UNIV] THEN
  REWRITE_TAC[HOMEOMORPHIC_SPACE_EUCLIDEAN]);;

let LOCALLY_EUCLIDEAN_SPACE_SPHERE_3 = prove
 (`locally_euclidean_space (:3)
     (subtopology euclidean (sphere(vec 0:real^4,&1)))`,
  REWRITE_TAC[LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN] THEN
  X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
  EXISTS_TAC `sphere(vec 0:real^4,&1) DELETE (--x)` THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE
     `s DELETE (a:real^4) = s INTER ((:real^4) DELETE a)`] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
    ASM_REWRITE_TAC[IN_DELETE] THEN
    REWRITE_TAC[VECTOR_ARITH `x:real^4 = --x <=> x = vec 0`] THEN
    DISCH_TAC THEN UNDISCH_TAC `x IN sphere(vec 0:real^4,&1)` THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_SPHERE_0]) THEN
    ASM_REWRITE_TAC[REAL_LT_01; IN_SPHERE_0; NORM_NEG;
                    DIMINDEX_3; DIMINDEX_4] THEN
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The 3-sphere satisfies every hypothesis of POINCARE_STATEMENT.            *)
(* ------------------------------------------------------------------------- *)

let POINCARE_HYPOTHESES_SPHERE_3 = prove
 (`hausdorff_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   locally_euclidean_space (:3)
     (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   compact_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   ~(topspace (subtopology euclidean (sphere(vec 0:real^4,&1))) = {}) /\
   simply_connected_space (subtopology euclidean (sphere(vec 0:real^4,&1)))`,
  REWRITE_TAC[LOCALLY_EUCLIDEAN_SPACE_SPHERE_3;
              SIMPLY_CONNECTED_SPACE_SPHERE_3] THEN
  SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN] THEN
  SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SPHERE_EQ_EMPTY] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The embedded form follows from the abstract topological form.            *)
(* ------------------------------------------------------------------------- *)

let POINCARE_STATEMENT_IMP_EMBEDDED = prove
 (`POINCARE_STATEMENT (:real^N) ==> POINCARE_EMBEDDED_STATEMENT (:N)`,
  REWRITE_TAC[POINCARE_STATEMENT; POINCARE_EMBEDDED_STATEMENT] THEN
  DISCH_TAC THEN X_GEN_TAC `M:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `subtopology euclidean (M:real^N->bool)`) THEN
  REWRITE_TAC[HOMEOMORPHIC_SPACE_EUCLIDEAN] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  SIMPLY_CONNECTED_SPACE_EUCLIDEAN;
                  LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN] THEN
  SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN] THEN
  ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN]);;
