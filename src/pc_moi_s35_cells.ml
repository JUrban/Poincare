(* ========================================================================= *)
(* pc_moi_s35_cells: the Sec 35 unit s35_cells, main theorem SOURCE =       *)
(* MOI_S35_SOURCE (pc_moi_s35_stmt.ml, sections 4 and 7.6): for edge charts *)
(* as in moi_s35_charts, the pierced source cells C'_v (A-side edges cut at *)
(* small levels, B-side edges with finger and rim retraction), the 34.1     *)
(* domains C''_v and the bigger cells are PL 3-cells, and compact cores of  *)
(* the graph lie inside the pierced cells and off the tubes.  Construction: *)
(* the pierced cells by finitely many chart moves psi_e o phi_e o psi_e^-1  *)
(* (phi_e the identity off the slab: a vertical PL map on the A side, a     *)
(* vertical PL shear by a soft-thresholded gauge on the B side); the 34.1   *)
(* domains and the bigger cells by gluing boxes and fingers along squares;  *)
(* the cores by local finiteness of the dual cells and small chart balls.   *)
(* Moise GTM 47, pp.248-249.                                                *)
(* ========================================================================= *)

needs "src/pc_moi_s35_charts.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. The model pieces: the half slabs, the slab and the small square as    *)
(* intervals; the finger bcell INTER lower as a polytope cut out by the     *)
(* halfspaces +-x_i - 8 x3 <= 1/4.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_BOXES = prove
 (`moi_s35_slab INTER moi_s35_upper =
     interval[vector[-- &1;-- &1;&0]:real^3,vector[&1;&1;&1 / &8]] /\
   moi_s35_slab INTER moi_s35_lower =
     interval[vector[-- &1;-- &1;--(&1 / &8)]:real^3,vector[&1;&1;&0]] /\
   moi_s35_slab =
     interval[vector[-- &1;-- &1;--(&1 / &8)]:real^3,vector[&1;&1;&1 / &8]] /\
   moi_s35_bcell INTER moi_s35_mid =
     interval[vector[--(&1 / &4);--(&1 / &4);&0]:real^3,
              vector[&1 / &4;&1 / &4;&0]]`,
  REWRITE_TAC[moi_s35_slab; moi_s35_upper; moi_s35_lower; moi_s35_mid; moi_s35_bcell;
              moi_s35_n; moi_s35_cube] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN
  REWRITE_TAC[VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5V_FINGER_EQ = prove
 (`moi_s35_bcell INTER moi_s35_lower =
   moi_s35_cube INTER
   ({x:real^3 | vector[&0;&0;&1] dot x <= &0} INTER
    {x | vector[&1;&0;-- &8] dot x <= &1 / &4} INTER
    {x | vector[-- &1;&0;-- &8] dot x <= &1 / &4} INTER
    {x | vector[&0;&1;-- &8] dot x <= &1 / &4} INTER
    {x | vector[&0;-- &1;-- &8] dot x <= &1 / &4})`,
  REWRITE_TAC[moi_s35_lower; moi_s35_bcell; moi_s35_n; moi_s35_cube] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN
  REWRITE_TAC[DOT_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5V_FINGER = prove
 (`polytope (moi_s35_bcell INTER moi_s35_lower) /\
   aff_dim (moi_s35_bcell INTER moi_s35_lower) = &3 /\
   moi_s35_bcell INTER moi_s35_lower SUBSET moi_s35_slab INTER moi_s35_lower /\
   (moi_s35_bcell INTER moi_s35_lower) INTER moi_s35_upper =
     moi_s35_bcell INTER moi_s35_mid /\
   moi_s35_bcell INTER moi_s35_mid SUBSET
     relative_frontier (moi_s35_bcell INTER moi_s35_lower)`,
  SUBGOAL_THEN
   `ball(vector[&0;&0;--(&1 / &64)]:real^3,&1 / &128) SUBSET
    moi_s35_bcell INTER moi_s35_lower`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; moi_s35_lower; moi_s35_bcell; moi_s35_n;
                moi_s35_cube; IN_INTER; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3;
                FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`vector[&0;&0;--(&1 / &64)] - z:real^3`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`vector[&0;&0;--(&1 / &64)] - z:real^3`; `2`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`vector[&0;&0;--(&1 / &64)] - z:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
    UNDISCH_TAC `dist(vector[&0;&0;--(&1 / &64)]:real^3,z) < &1 / &128` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_S5V_FINGER_EQ] THEN MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
    REWRITE_TAC[moi_s35_cube; POLYTOPE_INTERVAL] THEN
    REPEAT(MATCH_MP_TAC POLYHEDRON_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[POLYHEDRON_HALFSPACE_LE];
    MP_TAC(ISPEC `moi_s35_bcell INTER moi_s35_lower` AFF_DIM_NONEMPTY_INTERIOR) THEN
    REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!x:real^3. x IN s ==> ~(s = {})`) THEN
    EXISTS_TAC `vector[&0;&0;--(&1 / &64)]:real^3` THEN
    MATCH_MP_TAC(SET_RULE `!b:real^3->bool. x IN b /\ b SUBSET s ==> x IN s`) THEN
    EXISTS_TAC `ball(vector[&0;&0;--(&1 / &64)]:real^3,&1 / &128)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[OPEN_BALL]];
    REWRITE_TAC[moi_s35_slab; moi_s35_lower; moi_s35_bcell; moi_s35_n; SUBSET;
                IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s35_upper; moi_s35_lower; moi_s35_mid; moi_s35_bcell; EXTENSION;
                IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(moi_s35_bcell INTER moi_s35_lower)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5V_FINGER_EQ] THEN MATCH_MP_TAC CLOSED_INTER THEN
    REWRITE_TAC[moi_s35_cube; CLOSED_INTERVAL] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier (moi_s35_bcell INTER moi_s35_lower) =
    frontier (moi_s35_bcell INTER moi_s35_lower)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
    MATCH_MP_TAC(SET_RULE `!x:real^3. x IN s ==> ~(s = {})`) THEN
    EXISTS_TAC `vector[&0;&0;--(&1 / &64)]:real^3` THEN
    MATCH_MP_TAC(SET_RULE `!b:real^3->bool. x IN b /\ b SUBSET s ==> x IN s`) THEN
    EXISTS_TAC `ball(vector[&0;&0;--(&1 / &64)]:real^3,&1 / &128)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN moi_s35_bcell INTER moi_s35_mid` THEN
    REWRITE_TAC[moi_s35_bcell; moi_s35_lower; moi_s35_mid; IN_INTER; IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x + (r / &2) % basis 3:real^3) IN
                moi_s35_bcell INTER moi_s35_lower` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `x - (x + v):real^3 = --v`; NORM_NEG;
                NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(x:real^3) IN moi_s35_bcell INTER moi_s35_mid` THEN
    REWRITE_TAC[moi_s35_bcell; moi_s35_lower; moi_s35_mid; IN_INTER; IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3;
             ARITH] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S5V_HALVES = prove
 (`polytope (moi_s35_slab INTER moi_s35_upper) /\
   aff_dim (moi_s35_slab INTER moi_s35_upper) = &3 /\
   polytope (moi_s35_slab INTER moi_s35_lower) /\
   aff_dim (moi_s35_slab INTER moi_s35_lower) = &3 /\
   polytope (moi_s35_bcell INTER moi_s35_mid) /\
   aff_dim (moi_s35_bcell INTER moi_s35_mid) = &2 /\
   moi_s35_mid SUBSET relative_frontier (moi_s35_slab INTER moi_s35_upper) /\
   moi_s35_mid SUBSET relative_frontier (moi_s35_slab INTER moi_s35_lower) /\
   moi_s35_lower INTER (moi_s35_slab INTER moi_s35_upper) = moi_s35_mid /\
   moi_s35_upper INTER (moi_s35_slab INTER moi_s35_lower) = moi_s35_mid /\
   moi_s35_slab = (moi_s35_slab INTER moi_s35_upper) UNION
                  (moi_s35_slab INTER moi_s35_lower) /\
   moi_s35_mid SUBSET moi_s35_slab /\
   moi_s35_bcell INTER moi_s35_mid SUBSET moi_s35_mid`,
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MOI_S5V_BOXES; POLYTOPE_INTERVAL] THEN NO_TAC) THENL
   [MP_TAC(ISPEC `moi_s35_slab INTER moi_s35_upper` AFF_DIM_NONEMPTY_INTERIOR) THEN
    REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MOI_S5V_BOXES; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPEC `moi_s35_slab INTER moi_s35_lower` AFF_DIM_NONEMPTY_INTERIOR) THEN
    REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MOI_S5V_BOXES; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[MOI_S5V_BOXES; AFF_DIM_INTERVAL] THEN
    SUBGOAL_THEN
     `~(interval[vector[--(&1 / &4);--(&1 / &4);&0]:real^3,
                 vector[&1 / &4;&1 / &4;&0]] = {})`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^3` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN
    SUBGOAL_THEN
     `{i | 1 <= i /\ i <= 3 /\
           (vector[--(&1 / &4);--(&1 / &4);&0]:real^3)$i <
           (vector[&1 / &4;&1 / &4;&0]:real^3)$i} = {1,2}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC) THEN
      ASM_CASES_TAC `i = 2` THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC) THEN
      ASM_CASES_TAC `i = 3` THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC) THEN
      ASM_ARITH_TAC;
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV];
    SUBGOAL_THEN `relative_frontier (moi_s35_slab INTER moi_s35_upper) =
                  frontier (moi_s35_slab INTER moi_s35_upper)` SUBST1_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
      REWRITE_TAC[MOI_S5V_BOXES; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT;
                  VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MOI_S5V_BOXES; FRONTIER_CLOSED_INTERVAL; SUBSET; IN_DIFF;
                IN_INTERVAL] THEN
    REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `relative_frontier (moi_s35_slab INTER moi_s35_lower) =
                  frontier (moi_s35_slab INTER moi_s35_lower)` SUBST1_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
      REWRITE_TAC[MOI_S5V_BOXES; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT;
                  VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MOI_S5V_BOXES; FRONTIER_CLOSED_INTERVAL; SUBSET; IN_DIFF;
                IN_INTERVAL] THEN
    REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[moi_s35_slab; moi_s35_upper; moi_s35_lower; moi_s35_mid; EXTENSION;
                IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s35_slab; moi_s35_upper; moi_s35_lower; moi_s35_mid; EXTENSION;
                IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s35_slab; moi_s35_upper; moi_s35_lower; EXTENSION;
                IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s35_slab; moi_s35_mid; SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[] THEN REAL_ARITH_TAC;
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 2. Cells: simplices, images of model polytopes under a chart, and the    *)
(* union of two 3-cells glued along a 2-cell in both boundaries (by the     *)
(* base chart MOI_S5H_BASE).                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_SIMPLEX_CELL = prove
 (`!n (k:real^N->bool).
     &n simplex k ==> pl_cell_with_boundary n k (relative_frontier k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `\x:real^N. x`; `\x:real^N. x`] THEN
  ASM_REWRITE_TAC[IMAGE_ID; pl_homeomorphism; HOMEOMORPHISM_ID;
                  GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_PL_POLYHEDRON]);;

let MOI_S5V_IMG_CELL = prove
 (`!n (psi:real^3->real^N) q z p (k:real^N->bool).
     pl_homeomorphism (moi_s35_cube,z) (psi,q) /\ p SUBSET moi_s35_cube /\
     pl_cell_with_boundary n p (relative_frontier p) /\ polytope p /\ &n simplex k
     ==> pl_cell_with_boundary n (IMAGE psi p) (IMAGE psi (relative_frontier p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `k:real^N->bool`; `relative_frontier k:real^N->bool`;
                 `p:real^3->bool`; `relative_frontier p:real^3->bool`]
    MOI_S5H_CELL_PLH) THEN
  ASM_SIMP_TAC[MOI_S5V_SIMPLEX_CELL] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real^N->real^3` (X_CHOOSE_THEN `be:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism (p,IMAGE (psi:real^3->real^N) p) (psi,q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_s35_cube`; `z:real^N->bool`] THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON];
    ALL_TAC] THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `(psi:real^3->real^N) o (al:real^N->real^3)`;
                        `(be:real^3->real^N) o (q:real^N->real^3)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `p:real^3->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5V_RF_MID = prove
 (`relative_frontier moi_s35_mid = {x | x IN moi_s35_mid /\ moi_s35_n x = &1}`,
  STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `x:real^3` MOI_S5H_RF_LATERAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN
      REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN SIMP_TAC[];
      UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN
      REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN SIMP_TAC[]]] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
  ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED; IN_DIFF] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs((x:real^3)$1) <= &1 /\ abs(x$2) <= &1 /\ x$3 = &0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN
    REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN
    REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `n <= &1 /\ ~(n < &1) ==> n = &1`) THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_s35_n] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN relative_interior moi_s35_mid)` THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `&1 - moi_s35_n x` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  SUBGOAL_THEN `affine hull moi_s35_mid SUBSET {z:real^3 | basis 3 dot z = &0}`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
    REWRITE_TAC[SUBSET; moi_s35_mid; IN_ELIM_THM] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`x - z:real^3`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`x - z:real^3`; `2`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT] THEN
  UNDISCH_TAC `dist(x:real^3,z) < &1 - moi_s35_n x` THEN
  UNDISCH_TAC `moi_s35_n x < &1` THEN
  REWRITE_TAC[dist; moi_s35_n; moi_s35_mid; IN_ELIM_THM] THEN
  REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; VECTOR_3;
              DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5V_RF_CUBE = prove
 (`relative_frontier moi_s35_cube =
   (relative_frontier moi_s35_lower UNION relative_frontier moi_s35_upper) DIFF
   (moi_s35_mid DIFF relative_frontier moi_s35_mid)`,
  SUBGOAL_THEN
   `~(interior moi_s35_cube = {}) /\ ~(interior moi_s35_lower = {}) /\
    ~(interior moi_s35_upper = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5H_BOXES; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; MOI_S5V_RF_MID] THEN
  REWRITE_TAC[MOI_S5H_BOXES; FRONTIER_CLOSED_INTERVAL; EXTENSION; IN_DIFF; IN_UNION;
              IN_INTERVAL; IN_ELIM_THM; moi_s35_n] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5V_CELL_UNION = prove
 (`!(x:real^N->bool) bx y by d jd.
     pl_cell_with_boundary 3 x bx /\ pl_cell_with_boundary 3 y by /\
     x INTER y = d /\ pl_cell_with_boundary 2 d jd /\ d SUBSET bx /\ d SUBSET by
     ==> pl_cell_with_boundary 3 (x UNION y) ((bx UNION by) DIFF (d DIFF jd))`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  SUBGOAL_THEN `?m:real^N. m IN d /\ ~(m IN jd)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^N->bool`; `jd:real^N->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:real^N->bool` (X_CHOOSE_THEN `f0:real^N->real^N`
      (X_CHOOSE_THEN `g0:real^N->real^N` (MP_TAC o last o CONJUNCTS)))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `bx:real^N->bool`; `y:real^N->bool`;
                 `by:real^N->bool`; `jd:real^N->bool`; `m:real^N`] MOI_S5H_BASE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^N` (X_CHOOSE_THEN `q:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!u v. u IN moi_s35_cube /\ v IN moi_s35_cube /\
                      (psi:real^3->real^N) u = psi v ==> u = v`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,x UNION y:real^N->bool)
                   ((psi:real^3->real^N),(q:real^N->real^3))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier moi_s35_lower SUBSET moi_s35_cube /\
    relative_frontier moi_s35_upper SUBSET moi_s35_cube /\
    moi_s35_mid SUBSET moi_s35_cube /\
    relative_frontier moi_s35_mid SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; POLYTOPE_IMP_CLOSED] THEN
    MAP_EVERY UNDISCH_TAC [`moi_s35_lower UNION moi_s35_upper = moi_s35_cube`;
                           `moi_s35_lower INTER moi_s35_upper = moi_s35_mid`] THEN
    MP_TAC(ISPEC `moi_s35_mid` RELATIVE_FRONTIER_SUBSET) THEN
    MP_TAC(ISPEC `moi_s35_lower` RELATIVE_FRONTIER_SUBSET) THEN
    MP_TAC(ISPEC `moi_s35_upper` RELATIVE_FRONTIER_SUBSET) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(bx UNION by) DIFF (d DIFF jd) =
                IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_cube)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MOI_S5V_RF_CUBE] THEN
    UNDISCH_TAC `!u v. u IN moi_s35_cube /\ v IN moi_s35_cube /\
                       (psi:real^3->real^N) u = psi v ==> u = v` THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_lower) = bx`;
      `IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_upper) = by`;
      `IMAGE (psi:real^3->real^N) moi_s35_mid = d`;
      `IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_mid) = jd`;
      `x INTER y:real^N->bool = d`;
      `relative_frontier moi_s35_lower SUBSET moi_s35_cube`;
      `relative_frontier moi_s35_upper SUBSET moi_s35_cube`;
      `moi_s35_mid SUBSET moi_s35_cube`;
      `relative_frontier moi_s35_mid SUBSET moi_s35_cube`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `x UNION y:real^N->bool = IMAGE (psi:real^3->real^N) moi_s35_cube`
  SUBST1_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,x UNION y:real^N->bool)
                   ((psi:real^3->real^N),(q:real^N->real^3))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [pl_cell_with_boundary] o
    check (fun t -> concl t = `pl_cell_with_boundary 3 (x:real^N->bool) bx`)) THEN
  MATCH_MP_TAC MOI_S5V_IMG_CELL THEN
  MAP_EVERY EXISTS_TAC [`q:real^N->real^3`; `x UNION y:real^N->bool`;
                        `k:real^N->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  REWRITE_TAC[MOI_S5H_BOXES; POLYTOPE_INTERVAL] THEN
  MATCH_MP_TAC MOI_S4A_POLY_CELL_3 THEN REWRITE_TAC[POLYTOPE_INTERVAL] THEN
  MP_TAC(ISPEC `interval[--vec 1:real^3,vec 1]` AFF_DIM_NONEMPTY_INTERIOR) THEN
  REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 3. The A-side move: a vertical PL homeomorphism of the cube, the         *)
(* identity off the slab, taking the lower half slab to the part of the     *)
(* slab below the level c (four affine pieces in the height).               *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_PL_VERT4 = prove
 (`!f p1 p2 p3 a1 b1 a2 b2 a3 b3 a4 b4.
     -- &1 < p1 /\ p1 < p2 /\ p2 < p3 /\ p3 < &1 /\
     (!s. -- &1 <= s /\ s <= p1 ==> f s = a1 * s + b1) /\
     (!s. p1 <= s /\ s <= p2 ==> f s = a2 * s + b2) /\
     (!s. p2 <= s /\ s <= p3 ==> f s = a3 * s + b3) /\
     (!s. p3 <= s /\ s <= &1 ==> f s = a4 * s + b4)
     ==> pl_map_on moi_s35_cube (\x:real^3. vector[x$1; x$2; f(x$3)]:real^3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_map_on] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  EXISTS_TAC `{interval[--vec 1:real^3,vector[&1;&1;p1]],
               interval[vector[-- &1;-- &1;p1]:real^3,vector[&1;&1;p2]],
               interval[vector[-- &1;-- &1;p2]:real^3,vector[&1;&1;p3]],
               interval[vector[-- &1;-- &1;p3]:real^3,vec 1]}` THEN
  EXISTS_TAC `(:real^3)` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; OPEN_UNIV; IN_UNIV; INTER_UNIV] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; POLYTOPE_INTERVAL] THEN
  REWRITE_TAC[MOI_S5H_BOXES; SUBSET; UNIONS_INSERT; UNIONS_0;
              UNION_EMPTY; IN_UNION; IN_INTERVAL] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  SUBGOAL_THEN
   `!c d:real. linear (\y:real^3. vector[y$1; y$2; c * y$3]:real^3) /\
               !z:real^3. vector[z$1; z$2; c * z$3 + d] =
                          (\y:real^3. vector[y$1; y$2; c * y$3]:real^3) z +
                          vector[&0; &0; d]`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(GEN_TAC THEN
      MAP_EVERY UNDISCH_TAC [`-- &1 < p1`; `p1 < p2`; `p2 < p3`; `p3 < &1`] THEN
      REAL_ARITH_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`\y:real^3. vector[y$1; y$2; a1 * y$3]:real^3`;
                          `vector[&0; &0; b1]:real^3`];
    MAP_EVERY EXISTS_TAC [`\y:real^3. vector[y$1; y$2; a2 * y$3]:real^3`;
                          `vector[&0; &0; b2]:real^3`];
    MAP_EVERY EXISTS_TAC [`\y:real^3. vector[y$1; y$2; a3 * y$3]:real^3`;
                          `vector[&0; &0; b3]:real^3`];
    MAP_EVERY EXISTS_TAC [`\y:real^3. vector[y$1; y$2; a4 * y$3]:real^3`;
                          `vector[&0; &0; b4]:real^3`]] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let moi_s5v_va = new_definition
 `moi_s5v_va (c:real) (s:real) =
    if s <= --(&1 / &8) then s
    else if s <= &0 then (&8 * c + &1) * s + c
    else if s <= &1 / &8 then (&1 - &8 * c) * s + c
    else s`;;

let MOI_S5V_VA = prove
 (`!c. abs c < &1 / &8
       ==> (!s. -- &1 <= s /\ s <= --(&1 / &8) ==> moi_s5v_va c s = s) /\
           (!s. --(&1 / &8) <= s /\ s <= &0 ==> moi_s5v_va c s = (&8 * c + &1) * s + c) /\
           (!s. &0 <= s /\ s <= &1 / &8 ==> moi_s5v_va c s = (&1 - &8 * c) * s + c) /\
           (!s. &1 / &8 <= s ==> moi_s5v_va c s = s) /\
           (!s. --(&1 / &8) <= s /\ s <= &0
                ==> --(&1 / &8) <= moi_s5v_va c s /\ moi_s5v_va c s <= c) /\
           (!s. &0 <= s /\ s <= &1 / &8
                ==> c <= moi_s5v_va c s /\ moi_s5v_va c s <= &1 / &8) /\
           (!t. --(&1 / &8) <= t /\ t <= c
                ==> ?s. --(&1 / &8) <= s /\ s <= &0 /\ moi_s5v_va c s = t) /\
           (!t. c <= t /\ t <= &1 / &8
                ==> ?s. &0 <= s /\ s <= &1 / &8 /\ moi_s5v_va c s = t)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &8 * c + &1 /\ &0 < &1 - &8 * c` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a /\ b /\ c /\ d) /\ (a /\ b /\ c /\ d ==> e /\ f /\ g /\ h)
                     ==> a /\ b /\ c /\ d /\ e /\ f /\ g /\ h`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_s5v_va] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    REPEAT COND_CASES_TAC THEN
    TRY(FIRST_ASSUM(fun th -> if is_eq(concl th) then NO_TAC else ALL_TAC) THEN
        ASM_REAL_ARITH_TAC) THEN
    TRY(SUBGOAL_THEN `s = --(&1 / &8)` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC] THEN NO_TAC) THEN
    TRY(SUBGOAL_THEN `s = &0` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC] THEN NO_TAC) THEN
    TRY(SUBGOAL_THEN `s = &1 / &8` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC] THEN NO_TAC) THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`&8 * c + &1`; `s:real`; `&0`] REAL_LE_LMUL) THEN
    MP_TAC(ISPECL [`&8 * c + &1`; `--(&1 / &8)`; `s:real`] REAL_LE_LMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`&1 - &8 * c`; `&0`; `s:real`] REAL_LE_LMUL) THEN
    MP_TAC(ISPECL [`&1 - &8 * c`; `s:real`; `&1 / &8`] REAL_LE_LMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    EXISTS_TAC `(t - c) / (&8 * c + &1)` THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `--(&1 / &8) <= (t - c) / (&8 * c + &1) /\
                  (t - c) / (&8 * c + &1) <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    EXISTS_TAC `(t - c) / (&1 - &8 * c)` THEN
    SUBGOAL_THEN `&0 <= (t - c) / (&1 - &8 * c) /\
                  (t - c) / (&1 - &8 * c) <= &1 / &8` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC]);;

let MOI_S5V_VA_INJ = prove
 (`!c s t. abs c < &1 / &8 /\ moi_s5v_va c s = moi_s5v_va c t ==> s = t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `tent = \r:real. if r <= --(&1 / &8) then &0
                              else if r <= &0 then &8 * r + &1
                              else if r <= &1 / &8 then &1 - &8 * r else &0` THEN
  SUBGOAL_THEN `!r. moi_s5v_va c r = r + c * tent r` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "tent" THEN REWRITE_TAC[moi_s5v_va] THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r u. abs((tent:real->real) r - tent u) <= &8 * abs(r - u)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "tent" THEN REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(s - t) = abs c * abs((tent:real->real) t - tent s)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `moi_s5v_va c s = moi_s5v_va c t` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs c * abs((tent:real->real) t - tent s) <= abs c * (&8 * abs(t - s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(s - t) = &0 ==> s = t`) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  REWRITE_TAC[REAL_ABS_POS] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&8 * abs c) * abs(s - t) < &1 * abs(s - t)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_SUB] THEN
  UNDISCH_TAC `abs c * abs((tent:real->real) t - tent s) <= abs c * (&8 * abs(t - s))` THEN
  UNDISCH_TAC `abs(s - t) = abs c * abs((tent:real->real) t - tent s)` THEN
  REWRITE_TAC[REAL_ABS_SUB] THEN REAL_ARITH_TAC);;

let MOI_S5V_PHIA = prove
 (`!c. abs c < &1 / &8
       ==> ?f g. pl_homeomorphism (moi_s35_cube,moi_s35_cube) (f,g) /\
                 (!x. x IN moi_s35_cube /\ ~(x IN moi_s35_slab) ==> f x = x) /\
                 IMAGE f (moi_s35_slab INTER moi_s35_lower) =
                 {x | x IN moi_s35_slab /\ x$3 <= c}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5V_VA) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "p1") (CONJUNCTS_THEN2 (LABEL_TAC "p2")
    (CONJUNCTS_THEN2 (LABEL_TAC "p3") (CONJUNCTS_THEN2 (LABEL_TAC "p4")
    (CONJUNCTS_THEN2 (LABEL_TAC "r2") (CONJUNCTS_THEN2 (LABEL_TAC "r3")
    (CONJUNCTS_THEN2 (LABEL_TAC "s2") (LABEL_TAC "s3")))))))) THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_cube <=>
                           abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ abs(x$3) <= &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!s. abs s <= &1 ==> abs(moi_s5v_va c s) <= &1) /\
    (!s. abs s <= &1 /\ ~(abs s <= &1 / &8) ==> moi_s5v_va c s = s) /\
    (!t. abs t <= &1 ==> ?s. abs s <= &1 /\ moi_s5v_va c s = t)`
  (CONJUNCTS_THEN2 (LABEL_TAC "rng") (CONJUNCTS_THEN2 (LABEL_TAC "off")
    (LABEL_TAC "sur"))) THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MAP_EVERY (fun l -> USE_THEN l (MP_TAC o SPEC `s:real`))
        ["p1"; "p2"; "p3"; "p4"; "r2"; "r3"] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MAP_EVERY (fun l -> USE_THEN l (MP_TAC o SPEC `s:real`)) ["p1"; "p4"] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      ASM_CASES_TAC `t <= --(&1 / &8)` THENL
       [EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "p1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `t <= c` THENL
       [USE_THEN "s2" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; MESON_TAC[REAL_ARITH
            `--(&1 / &8) <= s /\ s <= &0 ==> abs s <= &1`]];
        ALL_TAC] THEN
      ASM_CASES_TAC `t <= &1 / &8` THENL
       [USE_THEN "s3" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; MESON_TAC[REAL_ARITH
            `&0 <= s /\ s <= &1 / &8 ==> abs s <= &1`]];
        ALL_TAC] THEN
      EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "p4" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `f = \x:real^3. vector[x$1; x$2; moi_s5v_va c (x$3)]:real^3` THEN
  SUBGOAL_THEN
   `!x:real^3. ((f:real^3->real^3) x)$1 = x$1 /\ (f x)$2 = x$2 /\
               (f x)$3 = moi_s5v_va c (x$3)`
  ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on moi_s35_cube (f:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN MATCH_MP_TAC MOI_S5V_PL_VERT4 THEN
    MAP_EVERY EXISTS_TAC [`--(&1 / &8)`; `&0`; `&1 / &8`; `&1`; `&0`;
                          `&8 * c + &1`; `c:real`; `&1 - &8 * c`; `c:real`;
                          `&1`; `&0`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THENL
     [USE_THEN "p1" (MP_TAC o SPEC `s:real`);
      USE_THEN "p2" (MP_TAC o SPEC `s:real`);
      USE_THEN "p3" (MP_TAC o SPEC `s:real`);
      USE_THEN "p4" (MP_TAC o SPEC `s:real`)] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) moi_s35_cube = moi_s35_cube` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rng" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "sur" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `abs((y:real^3)$3) <= &1`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `vector[(y:real^3)$1; y$2; s]:real^3` THEN
    ASM_REWRITE_TAC[VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^3. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                             (f:real^3->real^3) x = f y ==> x = y` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S5V_VA_INJ THEN EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?g. homeomorphism (moi_s35_cube,moi_s35_cube)
                                   ((f:real^3->real^3),g)`
  (X_CHOOSE_TAC `g:real^3->real^3`) THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_S5H_BOXES; COMPACT_INTERVAL];
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    USE_THEN "off" MATCH_MP_TAC THEN
    UNDISCH_TAC `~((x:real^3) IN moi_s35_slab)` THEN
    UNDISCH_TAC `(x:real^3) IN moi_s35_cube` THEN
    ASM_REWRITE_TAC[moi_s35_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
  REWRITE_TAC[moi_s35_slab; moi_s35_lower; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    USE_THEN "r2" (MP_TAC o SPEC `(x:real^3)$3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  USE_THEN "s2" (MP_TAC o SPEC `(y:real^3)$3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `vector[(y:real^3)$1; y$2; s]:real^3` THEN
  ASM_REWRITE_TAC[VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3] THEN
  ASM_REAL_ARITH_TAC);;

(* B-side move: the PL shear x |-> x + phi(g(x'),x3) e3 with                *)
(* g(x') = (n(x') - 1/4)/8 and phi(g,s) = g soft-thresholded at 7|s|/8: on  *)
(* each vertical line it is a PL increasing bijection of [-1,1] (slopes     *)
(* 1/8, 1, 15/8) taking 0 to g and fixing |s| >= 1/8.                        *)

let moi_s5v_phi = new_definition
 `moi_s5v_phi (g:real) (s:real) =
    max (&0) (g - &7 / &8 * abs s) - max (&0) (--g - &7 / &8 * abs s)`;;

let moi_s5v_fb = new_definition
 `moi_s5v_fb (x:real^3) =
    x + moi_s5v_phi ((moi_s35_n x - &1 / &4) / &8) (x$3) % basis 3`;;

let MOI_S5V_PHI_MONO = prove
 (`!g s t. s < t ==> s + moi_s5v_phi g s < t + moi_s5v_phi g t`,
  REWRITE_TAC[moi_s5v_phi] THEN REAL_ARITH_TAC);;

let MOI_S5V_PHI_MONO_LE = prove
 (`!g s t. s <= t ==> s + moi_s5v_phi g s <= t + moi_s5v_phi g t`,
  MESON_TAC[MOI_S5V_PHI_MONO; REAL_LE_LT; REAL_LT_IMP_LE]);;

let MOI_S5V_PHI_ZERO = prove
 (`!g s. abs g <= &3 / &32 /\ &1 / &8 <= abs s ==> moi_s5v_phi g s = &0`,
  REWRITE_TAC[moi_s5v_phi] THEN REAL_ARITH_TAC);;

let MOI_S5V_PHI_AT0 = prove
 (`!g. moi_s5v_phi g (&0) = g`,
  REWRITE_TAC[moi_s5v_phi] THEN REAL_ARITH_TAC);;

let MOI_S5V_PHI_SURJ = prove
 (`!g t. abs g <= &3 / &32 /\ -- &1 <= t /\ t <= &1
         ==> ?s. -- &1 <= s /\ s <= &1 /\ s + moi_s5v_phi g s = t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s5v_phi] THEN
  ASM_CASES_TAC `&0 <= g` THENL
   [EXISTS_TAC `t - max (&0) (min (&8 * g - &7 * t) ((&8 * g + &7 * t) / &15))`;
    EXISTS_TAC `t + max (&0) (min (&7 * t - &8 * g) ((--(&8 * g) - &7 * t) / &15))`] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S5V_N_CUBE = prove
 (`!x. x IN moi_s35_cube ==> &0 <= moi_s35_n x /\ moi_s35_n x <= &1`,
  REWRITE_TAC[moi_s35_cube; moi_s35_n; IN_INTERVAL; DIMINDEX_3; FORALL_3;
              VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S5V_FB_COMPONENTS = prove
 (`!x. (moi_s5v_fb x)$1 = x$1 /\ (moi_s5v_fb x)$2 = x$2 /\
       (moi_s5v_fb x)$3 = x$3 + moi_s5v_phi ((moi_s35_n x - &1 / &4) / &8) (x$3) /\
       moi_s35_n (moi_s5v_fb x) = moi_s35_n x`,
  GEN_TAC THEN
  SUBGOAL_THEN `(moi_s5v_fb x)$1 = x$1 /\ (moi_s5v_fb x)$2 = x$2 /\
                (moi_s5v_fb x)$3 =
                x$3 + moi_s5v_phi ((moi_s35_n x - &1 / &4) / &8) (x$3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5v_fb; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[moi_s35_n]]);;

(* The real PL rules needed here (as in pc_moi_fnd_rn, outside this load   *)
(* closure).                                                                *)

let MOI_S5V_PL_LIFT_ADD = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(f x + g x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PL_MAP_ON_ADD) THEN
  REWRITE_TAC[LIFT_ADD]);;

let MOI_S5V_PL_LIFT_SUB = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(f x - g x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^N. lift(f x + -- &1 * g x)` THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_S5V_PL_LIFT_ADD THEN ASM_SIMP_TAC[MOI_PTR_PL_LIFT_CMUL]]);;

let MOI_S5V_PL_LIFT_ABS = prove
 (`!(s:real^N->bool) f.
     pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(abs(f x)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^N. lift(max (f x) (-- &1 * f x))` THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN ASM_SIMP_TAC[MOI_PTR_PL_LIFT_CMUL]]);;

let MOI_S5V_PL_LIFT_NEG = prove
 (`!(s:real^N->bool) f.
     pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(--(f x)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^N. lift(-- &1 * f x)` THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[MOI_PTR_PL_LIFT_CMUL]]);;

let MOI_S5V_PL_LIFT_DIV = prove
 (`!(s:real^N->bool) f c.
     pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(f x / c))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[MOI_PTR_PL_LIFT_CMUL]);;

let MOI_S5V_PL_LIFT_COMPONENT = prove
 (`!(s:real^N->bool) i. locally_polyhedral s ==> pl_map_on s (\x. lift(x$i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift(y$i)`; `vec 0:real^1`]
    PL_MAP_ON_AFFINE) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_RID; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              LIFT_ADD; LIFT_CMUL]);;

let MOI_S5V_FB_PL = prove
 (`pl_map_on moi_s35_cube moi_s5v_fb`,
  SUBGOAL_THEN `locally_polyhedral (:real^3)` ASSUME_TAC THENL
   [SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
    REWRITE_TAC[moi_s35_cube; POLYTOPE_INTERVAL]] THEN
  SUBGOAL_THEN
   `pl_map_on (:real^3)
      (\x. lift(moi_s5v_phi ((moi_s35_n x - &1 / &4) / &8) (x$3)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5v_phi; moi_s35_n] THEN
    REPEAT(MATCH_MP_TAC MOI_S5V_PL_LIFT_SUB ORELSE
           MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX ORELSE
           MATCH_MP_TAC MOI_S5V_PL_LIFT_DIV ORELSE
           MATCH_MP_TAC MOI_PTR_PL_LIFT_CMUL ORELSE
           MATCH_MP_TAC MOI_S5V_PL_LIFT_ABS ORELSE
           MATCH_MP_TAC MOI_S5V_PL_LIFT_NEG ORELSE CONJ_TAC) THEN
    ASM_SIMP_TAC[MOI_S5V_PL_LIFT_COMPONENT; MOI_PTR_PL_LIFT_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s5v_fb =
    (\x. x + moi_s5v_phi ((moi_s35_n x - &1 / &4) / &8) (x$3) % basis 3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s5v_fb]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_ADD THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. moi_s5v_phi ((moi_s35_n x - &1 / &4) / &8) (x$3) % basis 3:real^3) =
    (\z:real^1. drop z % basis 3) o
    (\x. lift(moi_s5v_phi ((moi_s35_n x - &1 / &4) / &8) (x$3)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\z:real^1. drop z % basis 3:real^3`;
                 `vec 0:real^3`] PL_MAP_ON_AFFINE) THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; VECTOR_ADD_RID; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
  VECTOR_ARITH_TAC);;

let MOI_S5V_FB_INJ = prove
 (`!x y. moi_s5v_fb x = moi_s5v_fb y ==> x = y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3)$1 = (y:real^3)$1 /\ x$2 = y$2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(AP_TERM `\v:real^3. v$1` (ASSUME `moi_s5v_fb x = moi_s5v_fb y`));
      MP_TAC(AP_TERM `\v:real^3. v$2` (ASSUME `moi_s5v_fb x = moi_s5v_fb y`))] THEN
    REWRITE_TAC[MOI_S5V_FB_COMPONENTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_n x = moi_s35_n (y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s35_n]; ALL_TAC] THEN
  MP_TAC(AP_TERM `\v:real^3. v$3` (ASSUME `moi_s5v_fb x = moi_s5v_fb y`)) THEN
  REWRITE_TAC[MOI_S5V_FB_COMPONENTS] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g = (moi_s35_n y - &1 / &4) / &8` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3)$3 = (y:real^3)$3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real`; `(x:real^3)$3`; `(y:real^3)$3`] MOI_S5V_PHI_MONO) THEN
    MP_TAC(ISPECL [`g:real`; `(y:real^3)$3`; `(x:real^3)$3`] MOI_S5V_PHI_MONO) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3]]);;

let MOI_S5V_FB_CUBE = prove
 (`!x. x IN moi_s35_cube ==> moi_s5v_fb x IN moi_s35_cube`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real^3` MOI_S5V_N_CUBE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `g = (moi_s35_n x - &1 / &4) / &8` THEN
  SUBGOAL_THEN `abs g <= &3 / &32` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN moi_s35_cube` THEN
  REWRITE_TAC[moi_s35_cube; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
              VECTOR_NEG_COMPONENT] THEN
  ASM_REWRITE_TAC[MOI_S5V_FB_COMPONENTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real`; `-- &1`; `(x:real^3)$3`] MOI_S5V_PHI_MONO_LE) THEN
  MP_TAC(ISPECL [`g:real`; `(x:real^3)$3`; `&1`] MOI_S5V_PHI_MONO_LE) THEN
  MP_TAC(ISPECL [`g:real`; `-- &1`] MOI_S5V_PHI_ZERO) THEN
  MP_TAC(ISPECL [`g:real`; `&1`] MOI_S5V_PHI_ZERO) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_S5V_FB_PRE = prove
 (`!y. y IN moi_s35_cube ==> ?x. x IN moi_s35_cube /\ moi_s5v_fb x = y`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `y:real^3` MOI_S5V_N_CUBE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `-- &1 <= (y:real^3)$3 /\ y$3 <= &1 /\ -- &1 <= y$1 /\ y$1 <= &1 /\
                -- &1 <= y$2 /\ y$2 <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN moi_s35_cube` THEN
    REWRITE_TAC[moi_s35_cube; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(moi_s35_n y - &1 / &4) / &8`; `(y:real^3)$3`] MOI_S5V_PHI_SURJ) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `vector[(y:real^3)$1; y$2; s]:real^3` THEN
  SUBGOAL_THEN `moi_s35_n (vector[(y:real^3)$1; y$2; s]:real^3) = moi_s35_n y`
  ASSUME_TAC THENL [REWRITE_TAC[moi_s35_n; VECTOR_3]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_s35_cube; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3;
                VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_S5V_FB_COMPONENTS] THEN
    ASM_REWRITE_TAC[VECTOR_3]]);;

let MOI_S5V_PHIB = prove
 (`?f g. pl_homeomorphism (moi_s35_cube,moi_s35_cube) (f,g) /\
         (!x. x IN moi_s35_cube /\ ~(x IN moi_s35_slab) ==> f x = x) /\
         IMAGE f (moi_s35_slab INTER moi_s35_upper) =
         moi_s35_bcell INTER moi_s35_slab`,
  MP_TAC(ISPECL [`moi_s35_cube`; `moi_s5v_fb`] PL_INJECTIVE_INVERSE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_S5V_FB_PL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      REWRITE_TAC[moi_s35_cube; POLYTOPE_INTERVAL];
      MESON_TAC[MOI_S5V_FB_INJ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE moi_s5v_fb moi_s35_cube = moi_s35_cube` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_S5V_FB_CUBE] THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[MOI_S5V_FB_PRE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `gb:real^3->real^3`) THEN
  MAP_EVERY EXISTS_TAC [`moi_s5v_fb`; `gb:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[moi_s5v_fb] THEN
    MATCH_MP_TAC(MESON[VECTOR_MUL_LZERO; VECTOR_ADD_RID]
      `c = &0 ==> x + c % b = x:real^3`) THEN
    MATCH_MP_TAC MOI_S5V_PHI_ZERO THEN
    MP_TAC(SPEC `x:real^3` MOI_S5V_N_CUBE) THEN
    UNDISCH_TAC `~((x:real^3) IN moi_s35_slab)` THEN
    ASM_REWRITE_TAC[moi_s35_slab; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s35_cube /\ &0 <= x$3 /\ x$3 <= &1 / &8`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN moi_s35_upper` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s35_slab` THEN
      REWRITE_TAC[moi_s35_slab; moi_s35_upper; IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `x:real^3` MOI_S5V_FB_CUBE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `x:real^3` MOI_S5V_N_CUBE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    ABBREV_TAC `g = (moi_s35_n x - &1 / &4) / &8` THEN
    SUBGOAL_THEN `abs g <= &3 / &32` ASSUME_TAC THENL
     [EXPAND_TAC "g" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_s35_bcell; moi_s35_slab; IN_ELIM_THM; MOI_S5V_FB_COMPONENTS] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g:real`; `&0`; `(x:real^3)$3`] MOI_S5V_PHI_MONO_LE) THEN
    MP_TAC(ISPECL [`g:real`; `(x:real^3)$3`; `&1 / &8`] MOI_S5V_PHI_MONO_LE) THEN
    MP_TAC(ISPECL [`g:real`; `&1 / &8`] MOI_S5V_PHI_ZERO) THEN
    REWRITE_TAC[MOI_S5V_PHI_AT0] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_bcell; moi_s35_slab; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPEC `y:real^3` MOI_S5V_FB_PRE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real^3` THEN
  ASM_REWRITE_TAC[moi_s35_upper; moi_s35_slab; IN_ELIM_THM] THEN
  MP_TAC(SPEC `x:real^3` MOI_S5V_N_CUBE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `moi_s5v_fb x = y`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_S5V_FB_COMPONENTS]) THEN
  ABBREV_TAC `g = (moi_s35_n x - &1 / &4) / &8` THEN
  SUBGOAL_THEN `abs g <= &3 / &32` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real`; `(x:real^3)$3`; `&0`] MOI_S5V_PHI_MONO) THEN
  MP_TAC(ISPECL [`g:real`; `&1 / &8`; `(x:real^3)$3`] MOI_S5V_PHI_MONO) THEN
  MP_TAC(ISPECL [`g:real`; `&1 / &8`] MOI_S5V_PHI_ZERO) THEN
  REWRITE_TAC[MOI_S5V_PHI_AT0] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. One chart move: a cell meeting a slab image as the image of a half    *)
(* slab is moved by psi o phi o psi^-1 (phi the identity off the slab); the *)
(* other parts of the cell outside the chart lie in a polyhedron missing    *)
(* the slab image.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_STEP = prove
 (`!(psi:real^3->real^N) q z phi phi' x bx h k.
     pl_homeomorphism (moi_s35_cube,z) (psi,q) /\
     pl_homeomorphism (moi_s35_cube,moi_s35_cube) (phi,phi') /\
     (!y. y IN moi_s35_cube /\ ~(y IN moi_s35_slab) ==> phi y = y) /\
     pl_cell_with_boundary 3 x bx /\
     x INTER IMAGE psi moi_s35_slab = IMAGE psi (moi_s35_slab INTER h) /\
     pl_polyhedron k /\ x DIFF IMAGE psi moi_s35_cube SUBSET k /\
     DISJOINT k (IMAGE psi moi_s35_slab)
     ==> ?bx'. pl_cell_with_boundary 3
                 ((x DIFF IMAGE psi moi_s35_slab) UNION
                  IMAGE psi (IMAGE phi (moi_s35_slab INTER h))) bx'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_slab SUBSET moi_s35_cube` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_slab] THEN SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun t -> concl t = `pl_homeomorphism (moi_s35_cube,z:real^N->bool)
                                 ((psi:real^3->real^N),(q:real^N->real^3))`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun t -> concl t = `pl_homeomorphism (moi_s35_cube,moi_s35_cube)
                                 ((phi:real^3->real^3),(phi':real^3->real^3))`)) THEN
  SUBGOAL_THEN `compact(x:real^N->bool) /\ pl_polyhedron x /\ pl_polyhedron(z:real^N->bool) /\
                compact z /\ compact(k:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_CEL_CELL_COMPACT];
      ASM_MESON_TAC[MOI_S5H_CELL_POLY];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
        concl t = `IMAGE (psi:real^3->real^N) moi_s35_cube = z`)) THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MOI_S5H_BOXES] THEN MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      REWRITE_TAC[POLYTOPE_INTERVAL];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
        concl t = `IMAGE (psi:real^3->real^N) moi_s35_cube = z`)) THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MOI_S5H_BOXES; COMPACT_INTERVAL];
      ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT]];
    ALL_TAC] THEN
  ABBREV_TAC `ps = \y:real^N. if y IN z then (psi:real^3->real^N) ((phi:real^3->real^3) ((q:real^N->real^3) y)) else y` THEN
  SUBGOAL_THEN `!w. w IN moi_s35_cube ==> (ps:real^N->real^N) (psi w) = psi (phi w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN EXPAND_TAC "ps" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^3->real^N) w IN z` (fun t -> REWRITE_TAC[t]) THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. ~(y IN IMAGE (psi:real^3->real^N) moi_s35_slab)
                    ==> (ps:real^N->real^N) y = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "ps" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(q:real^N->real^3) y IN moi_s35_cube /\ ~(q y IN moi_s35_slab)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(y IN IMAGE (psi:real^3->real^N) moi_s35_slab)` THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(q:real^N->real^3) y` THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ps:real^N->real^N) x =
                (x DIFF IMAGE psi moi_s35_slab) UNION
                IMAGE psi (IMAGE phi (moi_s35_slab INTER h))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_s35_slab INTER h SUBSET moi_s35_cube` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `y IN IMAGE (psi:real^3->real^N) moi_s35_slab` THENL
       [SUBGOAL_THEN `y IN IMAGE (psi:real^3->real^N) (moi_s35_slab INTER h)` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(phi:real^3->real^3) w` THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
          REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]];
        ASM_SIMP_TAC[IN_UNION; IN_DIFF]];
      REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN ASM_SIMP_TAC[];
        UNDISCH_TAC `y IN IMAGE (psi:real^3->real^N)
                            (IMAGE (phi:real^3->real^3) (moi_s35_slab INTER h))` THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
          (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC))) THEN
        EXISTS_TAC `(psi:real^3->real^N) w` THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun t ->
            can (find_term ((=) `ps:real^N->real^N`)) (concl t) &&
            can (find_term ((=) `phi:real^3->real^3`)) (concl t))) THEN
          ASM SET_TAC[];
          ASM SET_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (x:real^N->bool) (ps:real^N->real^N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `x = (x INTER z) UNION (x INTER k:real^N->bool)` SUBST1_TAC THENL
     [UNDISCH_TAC `x DIFF IMAGE (psi:real^3->real^N) moi_s35_cube SUBSET k` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `(psi:real^3->real^N) o (phi:real^3->real^3) o (q:real^N->real^3)` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER; o_THM] THEN STRIP_TAC THEN
        EXPAND_TAC "ps" THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `z:real^N->bool` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_s35_cube` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_s35_cube` THEN
          ASM_REWRITE_TAC[SUBSET_REFL];
          REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[SUBSET_REFL]];
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
        MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\y:real^N. y` THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `DISJOINT (k:real^N->bool) (IMAGE (psi:real^3->real^N) moi_s35_slab)` THEN
        UNDISCH_TAC `(y:real^N) IN k` THEN SET_TAC[];
        REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
        MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CLOSED_SUBSET THEN
      ASM_SIMP_TAC[COMPACT_INTER; COMPACT_IMP_CLOSED; SUBSET_UNION];
      MATCH_MP_TAC CLOSED_SUBSET THEN
      ASM_SIMP_TAC[COMPACT_INTER; COMPACT_IMP_CLOSED; SUBSET_UNION]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN z ==> (q:real^N->real^3) y IN moi_s35_cube /\
                                (phi:real^3->real^3) (q y) IN moi_s35_cube /\
                                (psi:real^3->real^N) (phi (q y)) IN z`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (q:real^N->real^3) z = moi_s35_cube`;
      `IMAGE (phi:real^3->real^3) moi_s35_cube = moi_s35_cube`;
      `IMAGE (psi:real^3->real^N) moi_s35_cube = z`; `(y:real^N) IN z`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. y1 IN x /\ y2 IN x /\ (ps:real^N->real^N) y1 = ps y2 ==> y1 = y2`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y1:real^N`; `y2:real^N`] THEN EXPAND_TAC "ps" THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `(y1:real^N) IN z` THEN ASM_CASES_TAC `(y2:real^N) IN z` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `y1:real^N` o check (fun t ->
        can (find_term ((=) `phi:real^3->real^3`)) (concl t) && is_forall (concl t) &&
        can (find_term ((=) `z:real^N->bool`)) (concl t))) THEN
      FIRST_ASSUM(MP_TAC o SPEC `y2:real^N` o check (fun t ->
        can (find_term ((=) `phi:real^3->real^3`)) (concl t) && is_forall (concl t) &&
        can (find_term ((=) `z:real^N->bool`)) (concl t))) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(phi:real^3->real^3) ((q:real^N->real^3) y1) = phi (q y2)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o AP_TERM `q:real^N->real^3` o check (fun t ->
          concl t = `(psi:real^3->real^N) ((phi:real^3->real^3) ((q:real^N->real^3) y1)) =
                    psi (phi (q y2))`)) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(q:real^N->real^3) y1 = q y2` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o AP_TERM `phi':real^3->real^3`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `psi:real^3->real^N`) THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `y1:real^N` o check (fun t ->
        can (find_term ((=) `phi:real^3->real^3`)) (concl t) && is_forall (concl t) &&
        can (find_term ((=) `z:real^N->bool`)) (concl t))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `~((y2:real^N) IN z)` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
        concl t = `(psi:real^3->real^N) ((phi:real^3->real^3) ((q:real^N->real^3) y1)) = y2`)) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `y2:real^N` o check (fun t ->
        can (find_term ((=) `phi:real^3->real^3`)) (concl t) && is_forall (concl t) &&
        can (find_term ((=) `z:real^N->bool`)) (concl t))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `~((y1:real^N) IN z)` THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun t ->
        concl t = `(y1:real^N) = (psi:real^3->real^N) ((phi:real^3->real^3) ((q:real^N->real^3) y2))`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?pinv. homeomorphism (x,IMAGE (ps:real^N->real^N) x) (ps,pinv)`
  (X_CHOOSE_TAC `pinv:real^N->real^N`) THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
      REFL_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (ps:real^N->real^N) bx` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
    concl t = `IMAGE (ps:real^N->real^N) x =
               (x DIFF IMAGE psi moi_s35_slab) UNION
               IMAGE psi (IMAGE (phi:real^3->real^3) (moi_s35_slab INTER h))`)) THEN
  MATCH_MP_TAC MOI_FTA_CELL_PLH THEN EXISTS_TAC `pinv:real^N->real^N` THEN
  ASM_SIMP_TAC[HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* 5. The pierced cells (part (A) of moi_s35_source_ok): finitely many      *)
(* chart moves at the edges of the vertex.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_POLY_UNIONS = prove
 (`!(f:A->real^N->bool) s.
     FINITE s /\ (!x. x IN s ==> pl_polyhedron (f x))
     ==> pl_polyhedron (UNIONS (IMAGE f s))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; UNIONS_0];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_SIMP_TAC[]]);;

let MOI_S5V_EDGES_FINITE = prove
 (`!(t:(real^N->bool)->bool) l (av:(real^N->bool)->real^N) bv v.
     graph_in_complex t l /\ {v} IN l /\
     (!e. moi_s35_edge l e ==> e = segment[av e,bv e])
     ==> FINITE {e | moi_s35_edge l e /\ (av e = v \/ bv e = v)}`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
  REWRITE_TAC[graph_in_complex; simplicial_subcomplex; lf_simplicial_complex] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `open:(real^N->bool)->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
    REWRITE_TAC[IN_SING] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{s:real^N->bool | s IN t /\ ~(s INTER u = {})}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `e:real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^N->bool) IN l /\ (v:real^N) IN e` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[moi_s35_edge];
      FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP th
        (ASSUME `moi_s35_edge l (e:real^N->bool)`)]) THEN
      ASM_MESON_TAC[ENDS_IN_SEGMENT]];
    ASM SET_TAC[]]);;

let MOI_S5V_CSRC_CELL = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     (!e. abs(cc e) <= &1 / &512) /\ {v} IN l
     ==> ?bs. pl_cell_with_boundary 3 (moi_s35_csrc t l av bv psi cc v) bs`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ed") (LABEL_TAC "dj")) THEN
  ABBREV_TAC `ee = {e | moi_s35_edge l e /\
                        ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}` THEN
  SUBGOAL_THEN `FINITE (ee:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN MATCH_MP_TAC MOI_S5V_EDGES_FINITE THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `mm = \e. if (bv:(real^N->bool)->real^N) e = v
             then IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                        (moi_s35_bcell INTER moi_s35_slab)
             else IMAGE (psi e)
                        {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e}` THEN
  SUBGOAL_THEN
   `!e. e IN ee ==> moi_s35_edge l e /\ ~((av:(real^N->bool)->real^N) e = bv e) /\
                    (av e = v \/ bv e = v) /\
                    (mm:(real^N->bool)->real^N->bool) e SUBSET
                    IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN EXPAND_TAC "ee" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "mm" THEN
    COND_CASES_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s35_csrc t l av bv psi cc v =
    (derived_dual_cell t l v DIFF
     UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab) ee))
    UNION UNIONS (IMAGE (mm:(real^N->bool)->real^N->bool) ee)`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_s35_csrc] THEN
    SUBGOAL_THEN
     `UNIONS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab | e |
              moi_s35_edge l e /\ ((av:(real^N->bool)->real^N) e = v \/ bv e = v)} =
      UNIONS (IMAGE (\e. IMAGE (psi e) moi_s35_slab) ee)`
    SUBST1_TAC THENL
     [AP_TERM_TAC THEN EXPAND_TAC "ee" THEN ONCE_REWRITE_TAC[EXTENSION] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[UNION_ASSOC] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `(!e. (bv:(real^N->bool)->real^N) e = v
           ==> (mm:(real^N->bool)->real^N->bool) e =
               IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     (moi_s35_bcell INTER moi_s35_slab)) /\
      (!e. ~((bv:(real^N->bool)->real^N) e = v)
           ==> (mm:(real^N->bool)->real^N->bool) e =
               IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e})`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "mm" THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!e. moi_s35_edge l e ==> ~((av:(real^N->bool)->real^N) e = bv e)`
    ASSUME_TAC THENL
     [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!e. e IN ee <=> moi_s35_edge l e /\
                                 ((av:(real^N->bool)->real^N) e = v \/ bv e = v)`
    ASSUME_TAC THENL
     [EXPAND_TAC "ee" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    MAP_EVERY UNDISCH_TAC
     [`!e. (bv:(real^N->bool)->real^N) e = v
           ==> (mm:(real^N->bool)->real^N->bool) e =
               IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     (moi_s35_bcell INTER moi_s35_slab)`;
      `!e. ~((bv:(real^N->bool)->real^N) e = v)
           ==> (mm:(real^N->bool)->real^N->bool) e =
               IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e}`;
      `!e. moi_s35_edge l e ==> ~((av:(real^N->bool)->real^N) e = bv e)`;
      `!e. e IN ee <=> moi_s35_edge l e /\
                      ((av:(real^N->bool)->real^N) e = v \/ bv e = v)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ff. FINITE ff
         ==> ff SUBSET ee
             ==> ?bs. pl_cell_with_boundary 3
                        ((derived_dual_cell t l v DIFF
                          UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                                   moi_s35_slab) ff)) UNION
                         UNIONS (IMAGE (mm:(real^N->bool)->real^N->bool) ff)) bs`
  (fun th -> ASM_MESON_TAC[th; SUBSET_REFL]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; DIFF_EMPTY; UNION_EMPTY] THEN DISCH_TAC THEN
    USE_THEN "tube" (MP_TAC o C MATCH_MP
      (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`) o CONJUNCT1 o CONJUNCT2) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `ff:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  USE_THEN "ih" (MP_TAC o C MATCH_MP (ASSUME `ff SUBSET (ee:(real^N->bool)->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `bs:real^N->bool`) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(e:real^N->bool) IN ee`) o check (fun t ->
    is_forall(concl t) && can (find_term ((=) `mm:(real^N->bool)->real^N->bool`)) (concl t)
    && can (find_term ((=) `ee:(real^N->bool)->bool`)) (concl t))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^N->real^3`) STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `?phi phi' h. pl_homeomorphism (moi_s35_cube,moi_s35_cube) (phi,phi') /\
                 (!y. y IN moi_s35_cube /\ ~(y IN moi_s35_slab) ==> phi y = y) /\
                 derived_dual_cell t l v = IMAGE ((psi:(real^N->bool)->real^3->real^N) e) h /\
                 h SUBSET moi_s35_cube /\
                 IMAGE (psi e) (IMAGE phi (moi_s35_slab INTER h)) =
                 (mm:(real^N->bool)->real^N->bool) e`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(bv:(real^N->bool)->real^N) e = v` THENL
     [MP_TAC MOI_S5V_PHIB THEN
      DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^3` (X_CHOOSE_THEN `phi':real^3->real^3`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `phi':real^3->real^3`;
                            `moi_s35_upper`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o check (fun t ->
          concl t = `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                     derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)`)) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[moi_s35_upper] THEN SET_TAC[];
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "mm" THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(av:(real^N->bool)->real^N) e = v` ASSUME_TAC THENL
       [UNDISCH_TAC `(av:(real^N->bool)->real^N) e = v \/ bv e = v` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPEC `(cc:(real^N->bool)->real) e` MOI_S5V_PHIA) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x <= &1 / &512 ==> x < &1 / &8`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^3` (X_CHOOSE_THEN `phi':real^3->real^3`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `phi':real^3->real^3`;
                            `moi_s35_lower`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o check (fun t ->
          concl t = `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower =
                     derived_dual_cell t l ((av:(real^N->bool)->real^N) e)`)) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[moi_s35_lower] THEN SET_TAC[];
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "mm" THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e'. e' IN ff
         ==> (mm:(real^N->bool)->real^N->bool) e' SUBSET
             IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab /\
             DISJOINT (IMAGE (psi e') moi_s35_slab) (IMAGE (psi e) moi_s35_slab) /\
             pl_polyhedron (IMAGE (psi e') moi_s35_slab)`
  ASSUME_TAC THENL
   [X_GEN_TAC `e':real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e':real^N->bool) IN ee /\ ~(e' = e)` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`ff SUBSET (ee:(real^N->bool)->bool)`;
                             `~((e:real^N->bool) IN ff)`; `(e':real^N->bool) IN ff`] THEN
      MESON_TAC[SUBSET];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(e':real^N->bool) IN ee`) o check (fun t ->
      is_forall(concl t) && can (find_term ((=) `mm:(real^N->bool)->real^N->bool`)) (concl t)
      && can (find_term ((=) `ee:(real^N->bool)->bool`)) (concl t))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e':real^N->bool)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `q':real^N->real^3` MP_TAC) THEN
    REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_S5V_BOXES] THEN MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      REWRITE_TAC[POLYTOPE_INTERVAL];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_s35_slab] THEN SET_TAC[];
        REWRITE_TAC[MOI_S5V_BOXES] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
        MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_INTERVAL]]];
    ALL_TAC] THEN
  ABBREV_TAC `uu = UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                         moi_s35_slab) ff)` THEN
  ABBREV_TAC `ww = UNIONS (IMAGE (mm:(real^N->bool)->real^N->bool) ff)` THEN
  SUBGOAL_THEN `(ww:real^N->bool) SUBSET uu /\
                DISJOINT (uu:real^N->bool)
                         (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab) /\
                pl_polyhedron uu`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["uu"; "ww"] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `e':real^N->bool` THEN
      DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(e':real^N->bool) IN ff`) o
          check (fun t -> is_forall (concl t) &&
            can (find_term ((=) `ff:(real^N->bool)->bool`)) (concl t) &&
            can (find_term ((=) `mm:(real^N->bool)->real^N->bool`)) (concl t))) THEN
        SIMP_TAC[];
        MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `e':real^N->bool` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[SET_RULE `DISJOINT (UNIONS s) (t:real^N->bool) <=>
                            !u. u IN s ==> DISJOINT u t`] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_S5V_POLY_UNIONS THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w1 w2. w1 IN moi_s35_cube /\ w2 IN moi_s35_cube /\
                        (psi:(real^N->bool)->real^3->real^N) e w1 = psi e w2 ==> w1 = w2`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,
                   derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                   derived_dual_cell t l ((bv:(real^N->bool)->real^N) e))
                   ((psi:(real^N->bool)->real^3->real^N) e,(q:real^N->real^3))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(psi:(real^N->bool)->real^3->real^N) e`; `q:real^N->real^3`;
    `derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
     derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)`;
    `phi:real^3->real^3`; `phi':real^3->real^3`;
    `(derived_dual_cell t l v DIFF uu) UNION (ww:real^N->bool)`;
    `bs:real^N->bool`; `h:real^3->bool`; `uu:real^N->bool`] MOI_S5V_STEP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_slab INTER h) =
                    IMAGE (psi e) h INTER IMAGE (psi e) moi_s35_slab` SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!c. (!x y. x IN c /\ y IN c /\ (f:real^3->real^N) x = f y ==> x = y) /\
              s SUBSET c /\ t SUBSET c ==> IMAGE f (s INTER t) = IMAGE f t INTER IMAGE f s`) THEN
        EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[moi_s35_slab] THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(ww:real^N->bool) SUBSET uu`;
        `DISJOINT (uu:real^N->bool)
                  (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)`] THEN
      SET_TAC[];
      MP_TAC(ISPECL [`(psi:(real^N->bool)->real^3->real^N) e`; `h:real^3->bool`;
                     `moi_s35_cube`] IMAGE_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(ww:real^N->bool) SUBSET uu` THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b':real^N->bool` THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`(ww:real^N->bool) SUBSET uu`;
    `DISJOINT (uu:real^N->bool)
              (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. The 34.1 domains and the bigger cells (part (B)): gluing finitely     *)
(* many cells to a cell along disks in its boundary, inside disjoint slabs. *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_GLUE = prove
 (`!(x0:real^N->bool) b0 (ee:A->bool) y by d jd sl.
     FINITE ee /\ pl_cell_with_boundary 3 x0 b0 /\
     (!e. e IN ee
          ==> pl_cell_with_boundary 3 (y e) (by e) /\
              pl_cell_with_boundary 2 (d e) (jd e) /\
              x0 INTER y e = d e /\ d e SUBSET b0 /\ d e SUBSET by e /\
              y e SUBSET sl e) /\
     (!e e'. e IN ee /\ e' IN ee /\ ~(e = e') ==> DISJOINT (sl e) (sl e'))
     ==> ?b. pl_cell_with_boundary 3 (x0 UNION UNIONS (IMAGE y ee)) b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pe") (LABEL_TAC "dsj")))) THEN
  SUBGOAL_THEN
   `!ff. FINITE ff
         ==> ff SUBSET ee
             ==> ?b. pl_cell_with_boundary 3 (x0 UNION UNIONS (IMAGE y ff)) b /\
                     !e. e IN ee /\ ~(e IN ff) ==> (d:A->real^N->bool) e SUBSET b`
  (fun th -> MP_TAC(SPEC `ee:A->bool` th) THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
             MESON_TAC[]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `b0:real^N->bool` THEN
    ASM_SIMP_TAC[IMAGE_CLAUSES; UNIONS_0; UNION_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e:A`; `ff:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  USE_THEN "ih" (MP_TAC o C MATCH_MP (ASSUME `ff SUBSET (ee:A->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(e:A) IN ee`) o check (fun t ->
    is_forall(concl t) && can (find_term ((=) `jd:A->real^N->bool`)) (concl t))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!e'. e' IN ff ==> DISJOINT ((sl:A->real^N->bool) e') (sl e)`
  ASSUME_TAC THENL
   [X_GEN_TAC `e':A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`ff SUBSET (ee:A->bool)`; `~((e:A) IN ff)`;
                           `(e':A) IN ff`; `(e:A) IN ee`] THEN
    MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e'. e' IN ff ==> (y:A->real^N->bool) e' SUBSET sl e'` ASSUME_TAC THENL
   [X_GEN_TAC `e':A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e':A` o check (fun t ->
      is_forall(concl t) && can (find_term ((=) `jd:A->real^N->bool`)) (concl t))) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`ff SUBSET (ee:A->bool)`; `(e':A) IN ff`] THEN
      MESON_TAC[SUBSET];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (UNIONS (IMAGE (y:A->real^N->bool) ff)) ((sl:A->real^N->bool) e)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `DISJOINT (UNIONS s) (t:real^N->bool) <=>
                          !u. u IN s ==> DISJOINT u t`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `e':A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!t:real^N->bool. s SUBSET t /\ DISJOINT t u ==> DISJOINT s u`) THEN
    EXISTS_TAC `(sl:A->real^N->bool) e'` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x0 UNION UNIONS (IMAGE (y:A->real^N->bool) ff)`; `b:real^N->bool`;
                 `(y:A->real^N->bool) e`; `(by:A->real^N->bool) e`;
                 `(d:A->real^N->bool) e`; `(jd:A->real^N->bool) e`] MOI_S5V_CELL_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`x0 INTER (y:A->real^N->bool) e = d e`; `(y:A->real^N->bool) e SUBSET sl e`;
        `DISJOINT (UNIONS (IMAGE (y:A->real^N->bool) ff)) ((sl:A->real^N->bool) e)`] THEN
      SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "un") THEN
  EXISTS_TAC `(b UNION (by:A->real^N->bool) e) DIFF (d e DIFF (jd:A->real^N->bool) e)` THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN CONJ_TAC THENL
   [USE_THEN "un" MP_TAC THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e':A` THEN REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d:A->real^N->bool) e' SUBSET b /\ d e' SUBSET sl e' /\
                (d:A->real^N->bool) e SUBSET sl e /\ DISJOINT ((sl:A->real^N->bool) e') (sl e)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `e':A` o check (fun t ->
        is_forall(concl t) && can (find_term ((=) `jd:A->real^N->bool`)) (concl t))) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`x0 INTER (y:A->real^N->bool) e = d e`;
                             `(y:A->real^N->bool) e SUBSET sl e`] THEN SET_TAC[];
      USE_THEN "dsj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY UNDISCH_TAC
     [`(d:A->real^N->bool) e' SUBSET b`; `(d:A->real^N->bool) e' SUBSET sl e'`;
      `(d:A->real^N->bool) e SUBSET sl e`;
      `DISJOINT ((sl:A->real^N->bool) e') (sl e)`] THEN
    SET_TAC[]]);;

let MOI_S5V_PIECE = prove
 (`!(psi:real^3->real^N) q z h p m (k3:real^N->bool) (k2:real^N->bool) x bx.
     pl_homeomorphism (moi_s35_cube,z) (psi,q) /\ &3 simplex k3 /\ &2 simplex k2 /\
     polytope p /\ aff_dim p = &3 /\ polytope m /\ aff_dim m = &2 /\
     p SUBSET moi_s35_slab /\ m SUBSET relative_frontier p /\ h SUBSET moi_s35_cube /\
     h INTER p = m /\ x = IMAGE psi h /\ IMAGE psi moi_s35_mid SUBSET bx /\
     m SUBSET moi_s35_mid
     ==> pl_cell_with_boundary 3 (IMAGE psi p) (IMAGE psi (relative_frontier p)) /\
         pl_cell_with_boundary 2 (IMAGE psi m) (IMAGE psi (relative_frontier m)) /\
         x INTER IMAGE psi p = IMAGE psi m /\ IMAGE psi m SUBSET bx /\
         IMAGE psi m SUBSET IMAGE psi (relative_frontier p) /\
         IMAGE psi p SUBSET IMAGE psi moi_s35_slab`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_slab SUBSET moi_s35_cube /\ moi_s35_mid SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_slab; moi_s35_mid] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w1 w2. w1 IN moi_s35_cube /\ w2 IN moi_s35_cube /\
                        (psi:real^3->real^N) w1 = psi w2 ==> w1 = w2` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,z:real^N->bool)
                   ((psi:real^3->real^N),(q:real^N->real^3))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5V_IMG_CELL THEN
    MAP_EVERY EXISTS_TAC [`q:real^N->real^3`; `z:real^N->bool`; `k3:real^N->bool`] THEN
    ASM_SIMP_TAC[MOI_S4A_POLY_CELL_3] THEN ASM SET_TAC[];
    MATCH_MP_TAC MOI_S5V_IMG_CELL THEN
    MAP_EVERY EXISTS_TAC [`q:real^N->real^3`; `z:real^N->bool`; `k2:real^N->bool`] THEN
    ASM_SIMP_TAC[MOI_S4A_POLY_CELL_2] THEN ASM SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun t -> is_eq(concl t) &&
      lhs(concl t) = `x:real^N->bool`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t -> is_eq(concl t) &&
      rhs(concl t) = `m:real^3->bool`)) THEN
    MATCH_MP_TAC(SET_RULE
     `!c. (!x y. x IN c /\ y IN c /\ (f:real^3->real^N) x = f y ==> x = y) /\
          s SUBSET c /\ t SUBSET c ==> IMAGE f s INTER IMAGE f t = IMAGE f (s INTER t)`) THEN
    EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (psi:real^3->real^N) moi_s35_mid` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ASM_SIMP_TAC[IMAGE_SUBSET]]);;

let MOI_S5V_GLUE_MODEL = prove
 (`!(x0:real^N->bool) b0 ee (psi:(real^N->bool)->real^3->real^N) hh pp mq
    (k3:real^N->bool) (k2:real^N->bool).
     FINITE ee /\ pl_cell_with_boundary 3 x0 b0 /\ &3 simplex k3 /\ &2 simplex k2 /\
     (!e. e IN ee
          ==> (?q z. pl_homeomorphism (moi_s35_cube,z) (psi e,q)) /\
              x0 = IMAGE (psi e) (hh e) /\ hh e SUBSET moi_s35_cube /\
              IMAGE (psi e) moi_s35_mid SUBSET b0 /\
              polytope (pp e) /\ aff_dim (pp e) = &3 /\
              polytope (mq e) /\ aff_dim (mq e) = &2 /\
              pp e SUBSET moi_s35_slab /\ mq e SUBSET relative_frontier (pp e) /\
              hh e INTER pp e = mq e /\ mq e SUBSET moi_s35_mid) /\
     (!e e'. e IN ee /\ e' IN ee /\ ~(e = e')
             ==> DISJOINT (IMAGE (psi e) moi_s35_slab) (IMAGE (psi e') moi_s35_slab))
     ==> ?b. pl_cell_with_boundary 3
               (x0 UNION UNIONS (IMAGE (\e. IMAGE (psi e) (pp e)) ee)) b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S5V_GLUE THEN
  MAP_EVERY EXISTS_TAC
   [`b0:real^N->bool`;
    `\e:real^N->bool. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                            (relative_frontier ((pp:(real^N->bool)->real^3->bool) e))`;
    `\e:real^N->bool. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                            ((mq:(real^N->bool)->real^3->bool) e)`;
    `\e:real^N->bool. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                            (relative_frontier ((mq:(real^N->bool)->real^3->bool) e))`;
    `\e:real^N->bool. IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(e:real^N->bool) IN ee`) o check (fun t ->
    is_forall(concl t) && can (find_term ((=) `mq:(real^N->bool)->real^3->bool`)) (concl t))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^N->real^3`
    (X_CHOOSE_TAC `z:real^N->bool`)) STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S5V_PIECE THEN
  MAP_EVERY EXISTS_TAC [`q:real^N->real^3`; `z:real^N->bool`;
                        `(hh:(real^N->bool)->real^3->bool) e`;
                        `k3:real^N->bool`; `k2:real^N->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5V_PLUS_CELLS = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ {v} IN l
     ==> (?bs. pl_cell_with_boundary 3 (moi_s35_cplus t l av bv psi v) bs) /\
         (?bs. pl_cell_with_boundary 3 (moi_s35_cbig t l av bv psi v) bs)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ed") (LABEL_TAC "dj")) THEN
  USE_THEN "tube" (MP_TAC o C MATCH_MP
    (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`) o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))) THEN
  ABBREV_TAC `bd = (derived_dual_cell t l v INTER derived_frontier t l) UNION
                   UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w | w |
                           ~(w = v) /\ segment[v:real^N,w] IN l}` THEN
  SUBGOAL_THEN `?k3:real^N->bool. &3 simplex k3` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 3 (derived_dual_cell t l (v:real^N)) bd` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k2:real^N->bool. &2 simplex k2` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC CHOOSE_SIMPLEX THEN
    MP_TAC(ISPEC `k3:real^N->bool` AFF_DIM_LE_UNIV) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP AFF_DIM_SIMPLEX th]) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ee = {e | moi_s35_edge l e /\
                        ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}` THEN
  SUBGOAL_THEN `FINITE (ee:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN MATCH_MP_TAC MOI_S5V_EDGES_FINITE THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN ee
        ==> moi_s35_edge l e /\ ((av:(real^N->bool)->real^N) e = v \/ bv e = v) /\
            ~(av e = bv e) /\
            (?q. pl_homeomorphism
                   (moi_s35_cube,derived_dual_cell t l (av e) UNION
                                 derived_dual_cell t l (bv e))
                   ((psi:(real^N->bool)->real^3->real^N) e,q)) /\
            (av e = v ==> derived_dual_cell t l v = IMAGE (psi e) moi_s35_lower) /\
            (bv e = v ==> derived_dual_cell t l v = IMAGE (psi e) moi_s35_upper) /\
            IMAGE (psi e) moi_s35_mid SUBSET bd`
  (LABEL_TAC "pe") THENL
   [X_GEN_TAC `e:real^N->bool` THEN EXPAND_TAC "ee" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^N->real^3`) STRIP_ASSUME_TAC))))) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXISTS_TAC `q:real^N->real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
        concl t = `(av:(real^N->bool)->real^N) e = v`)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
        concl t = `(bv:(real^N->bool)->real^N) e = v`)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_mid =
                  derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e)`
    SUBST1_TAC THENL
     [MP_TAC MOI_S5H_MODEL THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
        concl t = `moi_s35_lower INTER moi_s35_upper = moi_s35_mid`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
        concl t = `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower =
                   derived_dual_cell t l ((av:(real^N->bool)->real^N) e)`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
        concl t = `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                   derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)`)) THEN
      MATCH_MP_TAC(SET_RULE
       `!c. (!x y. x IN c /\ y IN c /\ (f:real^3->real^N) x = f y ==> x = y) /\
            s SUBSET c /\ t SUBSET c ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`) THEN
      EXISTS_TAC `moi_s35_cube` THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,
                       derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                       derived_dual_cell t l ((bv:(real^N->bool)->real^N) e))
                       ((psi:(real^N->bool)->real^3->real^N) e,(q:real^N->real^3))` THEN
        REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
        REWRITE_TAC[moi_s35_lower] THEN SET_TAC[];
        REWRITE_TAC[moi_s35_upper] THEN SET_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "bd" THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN DISJ2_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun t ->
      concl t = `(av:(real^N->bool)->real^N) e = v \/ bv e = v`)) THENL
     [EXISTS_TAC `derived_dual_cell t l (av e) INTER
                  derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `(bv:(real^N->bool)->real^N) e` THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun t ->
        concl t = `(av:(real^N->bool)->real^N) e = v`)) THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t -> is_eq(concl t) &&
        lhs(concl t) = `e:real^N->bool`)) THEN
      UNDISCH_TAC `moi_s35_edge l (e:real^N->bool)` THEN SIMP_TAC[moi_s35_edge];
      EXISTS_TAC `derived_dual_cell t l (bv e) INTER
                  derived_dual_cell t l ((av:(real^N->bool)->real^N) e)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      EXISTS_TAC `(av:(real^N->bool)->real^N) e` THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun t ->
        concl t = `(bv:(real^N->bool)->real^N) e = v`)) THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t -> is_eq(concl t) &&
        lhs(concl t) = `e:real^N->bool`)) THEN
      UNDISCH_TAC `moi_s35_edge l (e:real^N->bool)` THEN SIMP_TAC[moi_s35_edge]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e e'. e IN ee /\ e' IN ee /\ ~(e = e')
           ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                        (IMAGE (psi e') moi_s35_slab)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `e':real^N->bool`] THEN STRIP_TAC THEN
    USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pe" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
      (ASSUME `(e:real^N->bool) IN ee`))) THEN MP_TAC(CONJUNCT1(MATCH_MP th
      (ASSUME `(e':real^N->bool) IN ee`)))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN ee
        ==> (?q z. pl_homeomorphism (moi_s35_cube,z)
                     ((psi:(real^N->bool)->real^3->real^N) e,q)) /\
            derived_dual_cell t l v =
            IMAGE (psi e) (if (bv:(real^N->bool)->real^N) e = v then moi_s35_upper
                           else moi_s35_lower) /\
            (if bv e = v then moi_s35_upper else moi_s35_lower) SUBSET moi_s35_cube /\
            IMAGE (psi e) moi_s35_mid SUBSET bd`
  (LABEL_TAC "pf") THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "pe" (MP_TAC o C MATCH_MP (ASSUME `(e:real^N->bool) IN ee`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^N->real^3`)
      (CONJUNCTS_THEN2 (LABEL_TAC "lo") (CONJUNCTS_THEN2 (LABEL_TAC "up")
       ASSUME_TAC)))))) THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`q:real^N->real^3`;
        `derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
         derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)`] THEN ASM_REWRITE_TAC[];
      COND_CASES_TAC THENL
       [USE_THEN "up" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "lo" MATCH_MP_TAC THEN
        UNDISCH_TAC `(av:(real^N->bool)->real^N) e = v \/ bv e = v` THEN
        ASM_REWRITE_TAC[]];
      COND_CASES_TAC THEN REWRITE_TAC[moi_s35_upper; moi_s35_lower] THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  STRIP_ASSUME_TAC MOI_S5V_FINGER THEN STRIP_ASSUME_TAC MOI_S5V_HALVES THEN
  STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  SUBGOAL_THEN
   `?b. pl_cell_with_boundary 3
          (derived_dual_cell t l v UNION
           UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                   (if (bv:(real^N->bool)->real^N) e = v
                                    then moi_s35_bcell INTER moi_s35_lower
                                    else moi_s35_slab INTER moi_s35_upper)) ee)) b`
  (X_CHOOSE_TAC `b1:real^N->bool`) THENL
   [MATCH_MP_TAC MOI_S5V_GLUE_MODEL THEN
    MAP_EVERY EXISTS_TAC
     [`bd:real^N->bool`;
      `\e. if (bv:(real^N->bool)->real^N) e = v then moi_s35_upper else moi_s35_lower`;
      `\e. if (bv:(real^N->bool)->real^N) e = v then moi_s35_bcell INTER moi_s35_mid
            else moi_s35_mid`;
      `k3:real^N->bool`; `k2:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "pf" (MP_TAC o C MATCH_MP (ASSUME `(e:real^N->bool) IN ee`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [`q:real^N->real^3`; `z:real^N->bool`] THEN
                    ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `(moi_s35_bcell INTER moi_s35_lower) INTER moi_s35_upper =
                     moi_s35_bcell INTER moi_s35_mid` THEN SET_TAC[]];
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [SET_TAC[]; SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?b. pl_cell_with_boundary 3
          (derived_dual_cell t l v UNION
           UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                   (if (bv:(real^N->bool)->real^N) e = v
                                    then moi_s35_slab INTER moi_s35_lower
                                    else moi_s35_slab INTER moi_s35_upper)) ee)) b`
  (X_CHOOSE_TAC `b2:real^N->bool`) THENL
   [MATCH_MP_TAC MOI_S5V_GLUE_MODEL THEN
    MAP_EVERY EXISTS_TAC
     [`bd:real^N->bool`;
      `\e. if (bv:(real^N->bool)->real^N) e = v then moi_s35_upper else moi_s35_lower`;
      `\e:real^N->bool. moi_s35_mid`; `k3:real^N->bool`; `k2:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "pf" (MP_TAC o C MATCH_MP (ASSUME `(e:real^N->bool) IN ee`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [`q:real^N->real^3`; `z:real^N->bool`] THEN
                    ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. (bv:(real^N->bool)->real^N) e = v /\ moi_s35_edge l e ==> e IN ee`
  (LABEL_TAC "s1") THENL
   [GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "ee" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. (av:(real^N->bool)->real^N) e = v /\ moi_s35_edge l e
                    ==> e IN ee /\ ~(bv e = v)`
  (LABEL_TAC "s2") THENL
   [GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "ee" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      UNDISCH_TAC `(av:(real^N->bool)->real^N) e = v` THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. e IN ee /\ (bv:(real^N->bool)->real^N) e = v
                    ==> derived_dual_cell t l v =
                        IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper`
  (LABEL_TAC "s3") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "pf" (MP_TAC o C MATCH_MP (ASSUME `(e:real^N->bool) IN ee`)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. e IN ee /\ ~((bv:(real^N->bool)->real^N) e = v)
                    ==> moi_s35_edge l e /\ (av:(real^N->bool)->real^N) e = v`
  (LABEL_TAC "s4") THENL
   [GEN_TAC THEN EXPAND_TAC "ee" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `b1:real^N->bool` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun t -> concl t =
      `pl_cell_with_boundary 3
          (derived_dual_cell t l v UNION
           UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                   (if (bv:(real^N->bool)->real^N) e = v
                                    then moi_s35_bcell INTER moi_s35_lower
                                    else moi_s35_slab INTER moi_s35_upper)) ee)) b1`)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[moi_s35_cplus; UNION_ASSOC] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THENL
     [ASM_CASES_TAC `(bv:(real^N->bool)->real^N) e = v` THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s UNION u`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "pe" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
          (ASSUME `(e:real^N->bool) IN ee`)))) THEN SIMP_TAC[];
        MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET u UNION UNIONS s`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^N->bool` THEN
        USE_THEN "s4" (MP_TAC o SPEC `e:real^N->bool`) THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `e:real^N->bool` THEN
      SUBGOAL_THEN `(e:real^N->bool) IN ee` ASSUME_TAC THENL
       [USE_THEN "s1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `e:real^N->bool` THEN
      SUBGOAL_THEN `(e:real^N->bool) IN ee /\ ~((bv:(real^N->bool)->real^N) e = v)`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "s2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    EXISTS_TAC `b2:real^N->bool` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun t -> concl t =
      `pl_cell_with_boundary 3
          (derived_dual_cell t l v UNION
           UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                   (if (bv:(real^N->bool)->real^N) e = v
                                    then moi_s35_slab INTER moi_s35_lower
                                    else moi_s35_slab INTER moi_s35_upper)) ee)) b2`)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[moi_s35_cbig; moi_s35_cplus] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REPEAT CONJ_TAC THENL
     [SET_TAC[];
      X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(bv:(real^N->bool)->real^N) e = v` THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC(SET_RULE `!s'. (x:real^N->bool) SUBSET s' /\ s' IN s
                                    ==> x SUBSET u UNION UNIONS s`) THEN
        EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
          REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^N->bool` THEN
          ASM_REWRITE_TAC[] THEN
          USE_THEN "pe" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
            (ASSUME `(e:real^N->bool) IN ee`)))) THEN SIMP_TAC[]];
        MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s
                               ==> x SUBSET ((d UNION b) UNION UNIONS s) UNION u`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^N->bool` THEN
        USE_THEN "s4" (MP_TAC o SPEC `e:real^N->bool`) THEN ASM_SIMP_TAC[]];
      SET_TAC[];
      X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s'. (x:real^N->bool) SUBSET s' /\ s' IN s
                                  ==> x SUBSET d UNION UNIONS s`) THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                        (moi_s35_slab INTER moi_s35_lower)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `e:real^N->bool` THEN
        SUBGOAL_THEN `(e:real^N->bool) IN ee` ASSUME_TAC THENL
         [USE_THEN "s1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
      X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET d UNION UNIONS s`) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `e:real^N->bool` THEN
      SUBGOAL_THEN `(e:real^N->bool) IN ee /\ ~((bv:(real^N->bool)->real^N) e = v)`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "s2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(e:real^N->bool) IN ee` ASSUME_TAC THENL
       [USE_THEN "s1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab =
        IMAGE (psi e) (moi_s35_slab INTER moi_s35_upper) UNION
        IMAGE (psi e) (moi_s35_slab INTER moi_s35_lower)`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `(a:real^N->bool) SUBSET d /\ (b:real^N->bool) IN s
                             ==> a UNION b SUBSET d UNION UNIONS s`) THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `derived_dual_cell t l v =
                      IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper`
        SUBST1_TAC THENL
         [USE_THEN "s3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `e:real^N->bool` THEN
        ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* 7. The pierced cells lie in the 34.1 domains.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_CSRC_SUB = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc v.
     moi_s35_charts t l g av bv psi
     ==> moi_s35_csrc t l av bv psi cc v SUBSET moi_s35_cplus t l av bv psi v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ed") (K ALL_TAC)) THEN
  REWRITE_TAC[moi_s35_csrc; moi_s35_cplus] THEN
  REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `moi_s35_bcell INTER moi_s35_slab =
                  (moi_s35_bcell INTER moi_s35_slab INTER moi_s35_upper) UNION
                  (moi_s35_bcell INTER moi_s35_slab INTER moi_s35_lower)`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_s35_upper; moi_s35_lower; moi_s35_slab; EXTENSION; IN_INTER;
                  IN_UNION; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
      ASM_CASES_TAC `(x:real^3) IN moi_s35_bcell` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNION; UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(x:real^N->bool) SUBSET d ==> x SUBSET (d UNION b) UNION a`) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t -> concl t =
        `(bv:(real^N->bool)->real^N) e = v`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t -> concl t =
        `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
         derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)`)) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s'. (x:real^N->bool) SUBSET s' /\ s' IN s
                                  ==> x SUBSET (d UNION UNIONS s) UNION a`) THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                        (moi_s35_bcell INTER moi_s35_lower)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^N->bool` THEN
        ASM_REWRITE_TAC[]]];
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^3 | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e} SUBSET
                  (moi_s35_slab INTER moi_s35_lower) UNION (moi_s35_slab INTER moi_s35_upper)`
    ASSUME_TAC THENL
     [REWRITE_TAC[moi_s35_upper; moi_s35_lower; moi_s35_slab; SUBSET; IN_INTER;
                  IN_UNION; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                      ((moi_s35_slab INTER moi_s35_lower) UNION
                       (moi_s35_slab INTER moi_s35_upper))` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN REWRITE_TAC[IMAGE_UNION; UNION_SUBSET] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(x:real^N->bool) SUBSET d ==> x SUBSET (d UNION b) UNION a`) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t -> concl t =
        `(av:(real^N->bool)->real^N) e = v`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t -> concl t =
        `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower =
         derived_dual_cell t l ((av:(real^N->bool)->real^N) e)`)) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET (d UNION b) UNION UNIONS s`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 8. Near a point of the graph only the dual cells containing it matter    *)
(* (local finiteness of the dual cells, the graph in the interior of N).    *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_IN_INTERIOR_OF = prove
 (`!s t (y:real^N).
     y IN (subtopology euclidean s) interior_of t <=>
     ?u. open u /\ y IN u /\ y IN s /\ s INTER u SUBSET t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s INTER u:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S5V_SIMPLEX_EXT_FINITE = prove
 (`!s:real^N->bool. (?n. n simplex s) ==> FINITE {x | x extreme_point_of s}`,
  GEN_TAC THEN REWRITE_TAC[SIMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:real^N->bool` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[EXTREME_POINT_OF_CONVEX_HULL]);;

let MOI_S5V_LF_DUAL = prove
 (`!(t:(real^N->bool)->bool) l y.
     graph_in_complex t l /\ y IN UNIONS t /\
     (!w. {w} IN l ==> derived_dual_cell t l w SUBSET UNIONS {s | s IN t /\ w IN s})
     ==> ?u. open u /\ y IN u /\
             FINITE {w | {w} IN l /\ ~(derived_dual_cell t l w INTER u = {})}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  REWRITE_TAC[graph_in_complex; simplicial_subcomplex; lf_simplicial_complex] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `open:(real^N->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS {{x:real^N | x extreme_point_of s} | s |
                      s IN t /\ ~(s INTER u = {})}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MOI_S5V_SIMPLEX_EXT_FINITE THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN X_GEN_TAC `w:real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN t /\ w IN s /\ ~(s INTER u = {})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(derived_dual_cell t l (w:real^N) INTER u = {})` THEN
    USE_THEN "st" (MP_TAC o C MATCH_MP (ASSUME `{w:real^N} IN l`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{x:real^N | x extreme_point_of s}` THEN
  CONJ_TAC THENL
   [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM FACE_OF_SING] THEN
  SUBGOAL_THEN `{w:real^N} = {w} INTER s` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{w:real^N}`; `s:real^N->bool`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `(face_of):(real^N->bool)->(real^N->bool)->bool`))
    (concl th) && can (find_term ((=) `(INTER):(real^N->bool)->(real^N->bool)->real^N->bool`))
    (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

let MOI_S5V_LOCAL_UNION = prove
 (`!(t:(real^N->bool)->bool) l y.
     graph_in_complex t l /\
     derived_nbhd t l = UNIONS {derived_dual_cell t l w | w | {w} IN l} /\
     (!w. {w} IN l ==> derived_dual_cell t l w SUBSET UNIONS {s | s IN t /\ w IN s} /\
                       compact (derived_dual_cell t l w)) /\
     y IN UNIONS l
     ==> ?u. open u /\ y IN u /\
             UNIONS t INTER u SUBSET
             UNIONS {derived_dual_cell t l w | w | {w} IN l /\
                                                   y IN derived_dual_cell t l w}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dw") ASSUME_TAC))) THEN
  SUBGOAL_THEN `?u1. open u1 /\ (y:real^N) IN u1 /\ y IN UNIONS t /\
                     UNIONS t INTER u1 SUBSET derived_nbhd t l`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_S5V_IN_INTERIOR_OF] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      DERIVED_NBHD_BASIC) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
      SIMP_TAC[graph_in_complex];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`]
    MOI_S5V_LF_DUAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "dw" (MP_TAC o C MATCH_MP (ASSUME `{w:real^N} IN l`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `cc = UNIONS {derived_dual_cell t l (w:real^N) | w |
                           {w} IN l /\ ~(derived_dual_cell t l w INTER u2 = {}) /\
                           ~(y IN derived_dual_cell t l w)}` THEN
  SUBGOAL_THEN `closed (cc:real^N->bool) /\ ~((y:real^N) IN cc)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{w | {w} IN l /\
                         ~(derived_dual_cell t l (w:real^N) INTER u2 = {})}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
        USE_THEN "dw" (MP_TAC o C MATCH_MP (ASSUME `{w:real^N} IN l`)) THEN SIMP_TAC[]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `u1 INTER u2 INTER ((:real^N) DIFF cc)` THEN
  ASM_SIMP_TAC[OPEN_INTER; GSYM closed; IN_INTER; IN_DIFF; IN_UNIV] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `z:real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?w. {w} IN l /\ (z:real^N) IN derived_dual_cell t l w`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^N) IN derived_nbhd t l` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `derived_dual_cell t l (w:real^N)` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~((z:real^N) IN cc)` THEN EXPAND_TAC "cc" THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `derived_dual_cell t l (w:real^N)` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S5V_MIDPOINT_PAIR = prove
 (`!a b c d:real^N. {a,b} = {c,d} ==> midpoint(a,b) = midpoint(c,d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th) THEN
                       MP_TAC(SPEC `c:real^N` th) THEN MP_TAC(SPEC `d:real^N` th)) THEN
  MESON_TAC[MIDPOINT_SYM]);;

let MOI_S5V_CHART_NBHD = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e x r.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\
     x IN moi_s35_slab /\ psi e x IN UNIONS l /\ &0 < r
     ==> ?u. open u /\ psi e x IN u /\
             UNIONS t INTER u SUBSET IMAGE (psi e) (moi_s35_cube INTER ball(x,r))`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ed") (LABEL_TAC "dj")) THEN
  USE_THEN "tube" (MP_TAC o C MATCH_MP
    (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vtx")
    (CONJUNCTS_THEN2 (LABEL_TAC "edg") (LABEL_TAC "non")))) THEN
  USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^N->real^3`) STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `y = (psi:(real^N->bool)->real^3->real^N) e x` THEN
  ABBREV_TAC `a = (av:(real^N->bool)->real^N) e` THEN
  ABBREV_TAC `b = (bv:(real^N->bool)->real^N) e` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> can (find_term ((=) `q:real^N->real^3`)) (concl th))) THEN
  SUBGOAL_THEN `moi_s35_slab SUBSET moi_s35_cube` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_slab] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN moi_s35_cube /\ (q:real^N->real^3) y = x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "y" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. {w} IN l /\ (y:real^N) IN derived_dual_cell t l w ==> w = a \/ w = b`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `?c:real^N. (c = a \/ c = b) /\ y IN derived_dual_cell t l c`
    (X_CHOOSE_THEN `c:real^N` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
     [SUBGOAL_THEN `(y:real^N) IN derived_dual_cell t l a UNION derived_dual_cell t l b`
      MP_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_UNION] THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `{c:real^N} IN l /\ ~(c = w)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]; ALL_TAC] THEN
    ASM_CASES_TAC `segment[c:real^N,w] IN l` THENL
     [ALL_TAC;
      USE_THEN "non" (MP_TAC o SPECL [`c:real^N`; `w:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^N) IN derived_dual_cell t l c` THEN
      UNDISCH_TAC `(y:real^N) IN derived_dual_cell t l w` THEN SET_TAC[]] THEN
    USE_THEN "edg" (MP_TAC o C MATCH_MP (CONJ (ASSUME `~(c:real^N = w)`)
      (ASSUME `segment[c:real^N,w] IN l`))) THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `y = midpoint(c:real^N,w)` ASSUME_TAC THENL
     [MP_TAC(SPEC `y:real^N` (MATCH_MP (SET_RULE
        `!s t u m. s INTER t INTER u = {m}
                   ==> !x:real^N. x IN s /\ x IN t /\ x IN u ==> x = m`)
        (ASSUME `derived_dual_cell t l c INTER derived_dual_cell t l w INTER UNIONS l =
                 {midpoint(c:real^N,w)}`))) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "y" THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s35_edge l (segment[c:real^N,w])` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_s35_edge; AFF_DIM_SEGMENT]; ALL_TAC] THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP
      (ASSUME `moi_s35_edge l (segment[c:real^N,w])`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(segment[c:real^N,w] = e)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `{c:real^N,w} = {a,b}` MP_TAC THENL
       [REWRITE_TAC[GSYM SEGMENT_EQ] THEN
        UNDISCH_TAC `e = segment[a:real^N,b]` THEN
        UNDISCH_TAC `segment[c:real^N,w] = e` THEN MESON_TAC[];
        UNDISCH_TAC `~(w:real^N = a)` THEN UNDISCH_TAC `~(w:real^N = b)` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                           (IMAGE (psi (segment[c:real^N,w])) moi_s35_slab)` MP_TAC THENL
     [USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(segment[c:real^N,w] = e)` THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o
      REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `(psi:(real^N->bool)->real^3->real^N) (segment[c,w]) (vec 0)`)) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5V_MIDPOINT_PAIR THEN
        REWRITE_TAC[GSYM SEGMENT_EQ] THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[moi_s35_slab; IN_ELIM_THM; VEC_COMPONENT] THEN
        REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `e:real^N->bool`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`]
    MOI_S5V_LOCAL_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{w:real^N} IN l`)) THEN
    MESON_TAC[MOI_CEL_CELL_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !y'. y' IN derived_dual_cell t l a UNION derived_dual_cell t l b /\
             dist(y',y) < d ==> dist((q:real^N->real^3) y',x) < r`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `(q:real^N->real^3) continuous_on
       derived_dual_cell t l (a:real^N) UNION derived_dual_cell t l b`)) THEN
    REWRITE_TAC[continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ANTS_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `u1 INTER ball(y:real^N,d)` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN derived_dual_cell t l a UNION derived_dual_cell t l b`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^N) IN UNIONS {derived_dual_cell t l w | w |
                                      {w} IN l /\ y IN derived_dual_cell t l w}`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (CONJ (ASSUME `{w:real^N} IN l`)
      (ASSUME `(y:real^N) IN derived_dual_cell t l w`)) o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `a:real^N`)) (concl th) &&
        can (find_term ((=) `b:real^N`)) (concl th) &&
        can (find_term ((=) `(\/)`)) (concl th))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL] THEN
  EXISTS_TAC `(q:real^N->real^3) z` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 9. The cores (part (C)): the graph in the dual cell, minus the A-side    *)
(* caps above height -1/64, plus the B-side parts of the graph between      *)
(* heights -1/64 and 0 (inside the fingers).                                 *)
(* ------------------------------------------------------------------------- *)

let moi_s5v_core = new_definition
 `moi_s5v_core (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
               (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
               (psi:(real^N->bool)->real^3->real^N) (v:real^N) =
    ((derived_dual_cell t l v INTER UNIONS l) DIFF
     UNIONS {IMAGE (psi e) {x | x IN moi_s35_cube /\ --(&1 / &64) < x$3} | e |
             moi_s35_edge l e /\ av e = v}) UNION
    UNIONS {IMAGE (psi e) {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0}
            INTER UNIONS l | e | moi_s35_edge l e /\ bv e = v}`;;

let MOI_S5V_GRAPH_CELL_COMPACT = prove
 (`!(t:(real^N->bool)->bool) l w.
     graph_in_complex t l /\ {w} IN l /\
     derived_dual_cell t l w INTER UNIONS l =
     w INSERT UNIONS {segment[w,midpoint(w,z)] | z | ~(z = w) /\ segment[w,z] IN l}
     ==> compact(derived_dual_cell t l w INTER UNIONS l)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPACT_INSERT THEN MATCH_MP_TAC COMPACT_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; COMPACT_SEGMENT] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC MOI_S5H_NBRS_FINITE THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S5V_DIST_COMPONENTS = prove
 (`!x x':real^3. dist(x,x') < r
                 ==> abs(x'$1 - x$1) < r /\ abs(x'$2 - x$2) < r /\ abs(x'$3 - x$3) < r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x - x':real^3`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`x - x':real^3`; `2`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`x - x':real^3`; `3`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5V_BALL_A = prove
 (`!x x':real^3 cc.
     x$3 <= --(&1 / &64) /\ abs cc <= &1 / &512 /\ dist(x,x') < &1 / &1024
     ==> x'$3 <= &0 /\ x'$3 <= cc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S5V_DIST_COMPONENTS) THEN ASM_REAL_ARITH_TAC);;

let MOI_S5V_BALL_B = prove
 (`!x x':real^3.
     --(&1 / &64) <= x$3 /\ moi_s35_n x < &1 / &16 /\ dist(x,x') < &1 / &1024 /\
     x' IN moi_s35_cube
     ==> x' IN moi_s35_bcell /\ (~(x' IN moi_s35_slab) ==> x' IN moi_s35_upper) /\
         (x$3 <= &0 ==> x' IN moi_s35_slab)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S5V_DIST_COMPONENTS) THEN
  UNDISCH_TAC `moi_s35_n x < &1 / &16` THEN
  ASM_REWRITE_TAC[moi_s35_bcell; moi_s35_slab; moi_s35_upper; moi_s35_n; IN_ELIM_THM] THEN
  UNDISCH_TAC `--(&1 / &64) <= (x:real^3)$3` THEN REAL_ARITH_TAC);;

let MOI_S5V_CORE_GRAPH = prove
 (`!(t:(real^N->bool)->bool) l av bv psi v.
     moi_s5v_core t l av bv psi v SUBSET UNIONS l`,
  REWRITE_TAC[moi_s5v_core] THEN SET_TAC[]);;

let MOI_S5V_CORE_STUBE = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi v e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> DISJOINT (moi_s5v_core t l av bv psi v) (IMAGE (psi e) moi_s35_stube)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "ed") (K ALL_TAC))
    ASSUME_TAC) THEN
  MATCH_MP_TAC(SET_RULE `!u:real^N->bool. k SUBSET u /\ DISJOINT u s ==> DISJOINT k s`) THEN
  EXISTS_TAC `UNIONS l:real^N->bool` THEN REWRITE_TAC[MOI_S5V_CORE_GRAPH] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
  USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN moi_s35_stube` THEN
      REWRITE_TAC[moi_s35_stube; moi_s35_slab; IN_ELIM_THM; moi_s35_n] THEN
      REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                  VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `y:real^N`)) THEN ASM_REWRITE_TAC[]];
    UNDISCH_TAC `(x:real^3) IN moi_s35_stube` THEN
    REWRITE_TAC[moi_s35_stube; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let MOI_S5V_DIFF_UNIONS_CONG = prove
 (`!(k:real^N->bool) (f:A->real^N->bool) g P.
     (!e. P e ==> k INTER f e = k INTER g e)
     ==> k DIFF UNIONS {f e | e | P e} = k DIFF UNIONS {g e | e | P e}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let MOI_S5V_CORE_COMPACT = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ {v} IN l
     ==> compact (moi_s5v_core t l av bv psi v)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ed") (LABEL_TAC "dj")) THEN
  USE_THEN "tube" (MP_TAC o C MATCH_MP
    (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vtx")
    (CONJUNCTS_THEN2 (LABEL_TAC "edg") (LABEL_TAC "non")))) THEN
  SUBGOAL_THEN `!w. {w} IN l ==> compact(derived_dual_cell t l (w:real^N) INTER UNIONS l)`
  (LABEL_TAC "gc") THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S5V_GRAPH_CELL_COMPACT THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{w:real^N} IN l`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s5v_core] THEN MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `?ww. !e. moi_s35_edge l e /\ (av:(real^N->bool)->real^N) e = v
               ==> open (ww e) /\
                   IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                         {x | x IN moi_s35_cube /\ --(&1 / &64) < x$3} =
                   (derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e)) INTER
                   ww e`
    (X_CHOOSE_TAC `ww:(real^N->bool)->real^N->bool`) THENL
     [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `e:real^N->bool` THEN
      ASM_CASES_TAC `moi_s35_edge l (e:real^N->bool) /\ (av:(real^N->bool)->real^N) e = v`
      THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->real^3` MP_TAC) THEN
      ASM_REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM OPEN_IN_OPEN] THEN
      MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`q:real^N->real^3`; `moi_s35_cube`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `{x | x IN moi_s35_cube /\ --(&1 / &64) < (x:real^3)$3} =
                    moi_s35_cube INTER {x | x$3 > --(&1 / &64)}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(derived_dual_cell t l v INTER UNIONS l) DIFF
      UNIONS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                    {x | x IN moi_s35_cube /\ --(&1 / &64) < x$3} | e |
              moi_s35_edge l e /\ (av:(real^N->bool)->real^N) e = v} =
      (derived_dual_cell t l v INTER UNIONS l) DIFF
      UNIONS {(ww:(real^N->bool)->real^N->bool) e | e |
              moi_s35_edge l e /\ (av:(real^N->bool)->real^N) e = v}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_S5V_DIFF_UNIONS_CONG THEN X_GEN_TAC `e:real^N->bool` THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
        can (find_term ((=) `ww:(real^N->bool)->real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_DIFF THEN CONJ_TAC THENL
     [USE_THEN "gc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{e | moi_s35_edge l e /\
                     ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5V_EDGES_FINITE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      MESON_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^N->real^3`) STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> can (find_term ((=) `q:real^N->real^3`)) (concl th))) THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
          {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0} INTER UNIONS l =
    IMAGE (psi e) {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0} INTER
    ((derived_dual_cell t l (av e) INTER UNIONS l) UNION
     (derived_dual_cell t l ((bv:(real^N->bool)->real^N) e) INTER UNIONS l))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!c:real^N->bool. s SUBSET c /\ c = a UNION b
                               ==> s INTER u = s INTER (a INTER u UNION b INTER u)`) THEN
    EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_INTER_CLOSED THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `{x | x IN moi_s35_cube /\ --(&1 / &64) <= (x:real^3)$3 /\ x$3 <= &0} =
                    interval[vector[-- &1;-- &1;--(&1 / &64)],vector[&1;&1;&0]]`
      SUBST1_TAC THENL
       [REWRITE_TAC[MOI_S5H_BOXES; EXTENSION; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3;
                    FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
        GEN_TAC THEN REAL_ARITH_TAC;
        REWRITE_TAC[COMPACT_INTERVAL]]];
    MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    USE_THEN "gc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 10. The cores lie in the interiors of the pierced cells.  Small facts on *)
(* the charts and the source cells first.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_PSI_INJ = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e x y.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\
     x IN moi_s35_cube /\ y IN moi_s35_cube /\ psi e x = psi e y ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1)
    STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let MOI_S5V_SLAB_COMPACT = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> compact (IMAGE (psi e) moi_s35_slab)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1)
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s35_slab] THEN SET_TAC[];
    REWRITE_TAC[MOI_S5V_BOXES; COMPACT_INTERVAL]]);;

let MOI_S5V_VEC0_SLAB = prove
 (`(vec 0:real^3) IN moi_s35_slab`,
  REWRITE_TAC[moi_s35_slab; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3;
              FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S5V_LOWCAP_SLAB = prove
 (`!f:real^3->real^N.
     IMAGE f {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0}
     SUBSET IMAGE f moi_s35_slab`,
  GEN_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  REWRITE_TAC[moi_s35_slab; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Points of the source cell: off the slabs of the edges at v, in an A-side *)
(* slab below the level, in a B-side slab inside the finger region.         *)

let MOI_S5V_CSRC_OFF = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc v e x.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\
     x IN moi_s35_cube /\ ~(x IN moi_s35_slab) /\
     psi e x IN derived_dual_cell t l v /\
     (!e'. moi_s35_edge l e' /\ (av e' = v \/ bv e' = v) /\ ~(e' = e)
           ==> ~(psi e x IN IMAGE (psi e') moi_s35_slab))
     ==> psi e x IN moi_s35_csrc t l av bv psi cc v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s35_csrc; IN_UNION; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISJ1_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `e':real^N->bool` THEN
  ASM_CASES_TAC `e':real^N->bool = e` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC(TAUT `~b ==> ~(a /\ b)`) THEN
    REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) = y` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_S5V_PSI_INJ THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
        `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
        `e:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN
      REWRITE_TAC[moi_s35_slab] THEN SET_TAC[];
      UNDISCH_TAC `~((y:real^3) IN moi_s35_slab)` THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[]]);;

let MOI_S5V_CSRC_A = prove
 (`!(t:(real^N->bool)->bool) l av bv (psi:(real^N->bool)->real^3->real^N) cc v e x.
     moi_s35_edge l e /\ (av:(real^N->bool)->real^N) e = v /\ x IN moi_s35_slab /\
     x$3 <= cc e
     ==> psi e x IN moi_s35_csrc t l av bv psi cc v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s35_csrc; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM]);;

let MOI_S5V_CSRC_B = prove
 (`!(t:(real^N->bool)->bool) l av bv (psi:(real^N->bool)->real^3->real^N)
    (cc:(real^N->bool)->real) v e x.
     moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v /\ x IN moi_s35_slab /\
     x IN moi_s35_bcell
     ==> psi e x IN moi_s35_csrc t l av bv psi cc v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s35_csrc; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISJ1_TAC THEN DISJ2_TAC THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]);;

(* A core point off the slabs of the edges at v (k contains those slabs): *)
(* it lies in the dual cell of v only, and near it the complex lies in the  *)
(* dual cell of v off k, which is part of the source cell.                  *)

let MOI_S5V_CORE_INT_OFF = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc v z k.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ {v} IN l /\
     z IN moi_s5v_core t l av bv psi v /\ closed k /\ ~(z IN k) /\
     (!e. moi_s35_edge l e /\ (av e = v \/ bv e = v)
          ==> IMAGE (psi e) moi_s35_slab SUBSET k)
     ==> ?u. open u /\ z IN u /\
             UNIONS t INTER u SUBSET moi_s35_csrc t l av bv psi cc v`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "chs")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl"))))))) THEN
  USE_THEN "chs" (MP_TAC o REWRITE_RULE[moi_s35_charts]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ed") (LABEL_TAC "dj")) THEN
  USE_THEN "tube" (MP_TAC o C MATCH_MP
    (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vtx")
    (CONJUNCTS_THEN2 (LABEL_TAC "edg") (LABEL_TAC "non")))) THEN
  SUBGOAL_THEN
   `derived_dual_cell t l v DIFF k SUBSET moi_s35_csrc t l av bv psi cc (v:real^N)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_csrc; SUBSET; IN_DIFF; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN DISJ1_TAC THEN DISJ1_TAC THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `e:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab SUBSET k`
    MP_TAC THENL [USE_THEN "sl" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~((y:real^N) IN k)` THEN
    UNDISCH_TAC `(y:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN derived_dual_cell t l v /\ z IN UNIONS l`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^N) IN moi_s5v_core t l av bv psi v` THEN
    REWRITE_TAC[moi_s5v_core; IN_UNION; IN_DIFF; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `~b ==> (a /\ c) /\ d \/ b ==> a /\ c`) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab SUBSET k`
    MP_TAC THENL [USE_THEN "sl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `(psi:(real^N->bool)->real^3->real^N) e` MOI_S5V_LOWCAP_SLAB) THEN
    UNDISCH_TAC `~((z:real^N) IN k)` THEN
    UNDISCH_TAC `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                   {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. {w} IN l /\ (z:real^N) IN derived_dual_cell t l w ==> w = v`
  (LABEL_TAC "wz") THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    ASM_CASES_TAC `w:real^N = v` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(v:real^N = w)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(w:real^N = v)` THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `segment[v:real^N,w] IN l` THENL
     [ALL_TAC;
      USE_THEN "non" (MP_TAC o SPECL [`v:real^N`; `w:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^N) IN derived_dual_cell t l v` THEN
      UNDISCH_TAC `(z:real^N) IN derived_dual_cell t l w` THEN SET_TAC[]] THEN
    USE_THEN "edg" (MP_TAC o SPECL [`v:real^N`; `w:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) = midpoint(v,w)` ASSUME_TAC THENL
     [UNDISCH_TAC `derived_dual_cell t l v INTER derived_dual_cell t l w INTER UNIONS l =
                   {midpoint(v:real^N,w)}` THEN
      UNDISCH_TAC `(z:real^N) IN derived_dual_cell t l v` THEN
      UNDISCH_TAC `(z:real^N) IN derived_dual_cell t l w` THEN
      UNDISCH_TAC `(z:real^N) IN UNIONS l` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s35_edge l (segment[v:real^N,w])` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_s35_edge; AFF_DIM_SEGMENT]; ALL_TAC] THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (segment[v:real^N,w])`)) THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT1(funpow 3 CONJUNCT2 th)) THEN
                         MP_TAC(CONJUNCT1(funpow 7 CONJUNCT2 th))) THEN
    DISCH_TAC THEN DISCH_THEN(ASSUME_TAC o REWRITE_RULE[SEGMENT_EQ]) THEN
    SUBGOAL_THEN `(av:(real^N->bool)->real^N) (segment[v,w]) = v \/
                  bv (segment[v:real^N,w]) = v` ASSUME_TAC THENL
     [UNDISCH_TAC `{v:real^N,w} = {(av:(real^N->bool)->real^N) (segment[v,w]),
                                   bv (segment[v:real^N,w])}` THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `midpoint(v:real^N,w) =
                  midpoint((av:(real^N->bool)->real^N) (segment[v,w]),
                           bv (segment[v:real^N,w]))` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S5V_MIDPOINT_PAIR THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE ((psi:(real^N->bool)->real^3->real^N) (segment[v,w])) moi_s35_slab
                  SUBSET k` MP_TAC THENL
     [USE_THEN "sl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) (segment[v,w]))
                                moi_s35_slab` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN
      ASM_REWRITE_TAC[MOI_S5V_VEC0_SLAB];
      UNDISCH_TAC `~((z:real^N) IN k)` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `z:real^N`]
    MOI_S5V_LOCAL_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{w:real^N} IN l`)) THEN
    MESON_TAC[MOI_CEL_CELL_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u1 INTER ((:real^N) DIFF k)` THEN
  REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `derived_dual_cell t l v DIFF (k:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `UNIONS {derived_dual_cell t l w | w | {w} IN l /\
                                                     (z:real^N) IN derived_dual_cell t l w}
                SUBSET derived_dual_cell t l v` MP_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `w:real^N` THEN
    DISCH_TAC THEN SUBGOAL_THEN `w:real^N = v` (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN
    USE_THEN "wz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `UNIONS t INTER u1 SUBSET
               UNIONS {derived_dual_cell t l w | w | {w} IN l /\
                                                    (z:real^N) IN derived_dual_cell t l w}` THEN
  SET_TAC[]);;

(* A core point in the slab of an edge e at v (k contains the slabs of the *)
(* other edges at v and misses the point): near it the complex lies in the  *)
(* chart image of a small ball, which the cut levels and the finger region  *)
(* place inside the source cell.                                            *)

let MOI_S5V_CORE_INT_SLAB = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc v e z k.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     (!e. abs(cc e) <= &1 / &512) /\
     moi_s35_edge l e /\ (av e = v \/ bv e = v) /\
     z IN moi_s5v_core t l av bv psi v /\ z IN IMAGE (psi e) moi_s35_slab /\
     closed k /\ ~(z IN k) /\
     (!e'. moi_s35_edge l e' /\ (av e' = v \/ bv e' = v) /\ ~(e' = e)
           ==> IMAGE (psi e') moi_s35_slab SUBSET k)
     ==> ?u. open u /\ z IN u /\
             UNIONS t INTER u SUBSET moi_s35_csrc t l av bv psi cc v`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "chs")
    (CONJUNCTS_THEN2 (LABEL_TAC "cc") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "side") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "oth")))))))))) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^3) IN moi_s35_cube` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN moi_s35_slab` THEN REWRITE_TAC[moi_s35_slab] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e x IN UNIONS l` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `v:real^N`]
      MOI_S5V_CORE_GRAPH) THEN
    UNDISCH_TAC `(psi:(real^N->bool)->real^3->real^N) e x IN
                 moi_s5v_core t l av bv psi v` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "chs" (MP_TAC o REWRITE_RULE[moi_s35_charts]) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> MP_TAC(MATCH_MP th (ASSUME `moi_s35_edge l (e:real^N->bool)`)))
    (LABEL_TAC "dj")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (LABEL_TAC "axis"))))))))))) THEN
  (* the chart neighbourhood of radius 1/1024 *)
  USE_THEN "tube" (fun tb -> MP_TAC(ISPECL
    [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`;
     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
     `psi:(real^N->bool)->real^3->real^N`; `e:real^N->bool`; `x:real^3`;
     `&1 / &1024`] (MATCH_MP MOI_S5V_CHART_NBHD tb))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u0 INTER ((:real^N) DIFF k)` THEN
  REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNIV] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                              (moi_s35_cube INTER ball(x,&1 / &1024))` MP_TAC THENL
   [UNDISCH_TAC `UNIONS t INTER u0 SUBSET
                 IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                       (moi_s35_cube INTER ball(x,&1 / &1024))` THEN
    UNDISCH_TAC `(y:real^N) IN UNIONS t` THEN UNDISCH_TAC `(y:real^N) IN u0` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!e'. moi_s35_edge l e' /\ ((av:(real^N->bool)->real^N) e' = v \/ bv e' = v) /\
         ~(e' = e)
         ==> ~((psi:(real^N->bool)->real^3->real^N) e x' IN IMAGE (psi e') moi_s35_slab)`
  ASSUME_TAC THENL
   [X_GEN_TAC `e':real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab SUBSET k`
    MP_TAC THENL [USE_THEN "oth" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~((psi:(real^N->bool)->real^3->real^N) e x' IN k)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the two sides *)
  USE_THEN "side" (DISJ_CASES_THEN ASSUME_TAC) THENL
   [(* A-side: below the cut *)
    SUBGOAL_THEN `(x:real^3)$3 <= --(&1 / &64)` ASSUME_TAC THENL
     [UNDISCH_TAC `(psi:(real^N->bool)->real^3->real^N) e x IN
                   moi_s5v_core t l av bv psi v` THEN
      REWRITE_TAC[moi_s5v_core; IN_UNION; IN_DIFF; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o REWRITE_RULE[NOT_EXISTS_THM] o
          CONJUNCT2) THEN
        ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `~(e':real^N->bool = e)` ASSUME_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `~(e:real^N->bool = e')` ASSUME_TAC THENL
         [UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        USE_THEN "dj" (MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `(psi:(real^N->bool)->real^3->real^N) e'` MOI_S5V_LOWCAP_SLAB) THEN
        MP_TAC(ISPECL [`(psi:(real^N->bool)->real^3->real^N) e`; `moi_s35_slab`; `x:real^3`]
          FUN_IN_IMAGE) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(psi:(real^N->bool)->real^3->real^N) e x IN IMAGE (psi e')
                       {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0}` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`x:real^3`; `x':real^3`; `(cc:(real^N->bool)->real) e`]
      MOI_S5V_BALL_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x':real^3) IN moi_s35_slab` THENL
     [MATCH_MP_TAC MOI_S5V_CSRC_A THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5V_CSRC_OFF THEN EXISTS_TAC `g:real^N->real^N->bool` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower =
                   derived_dual_cell t l (av e)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[moi_s35_lower; IN_ELIM_THM]];
    (* B-side: inside the finger region *)
    SUBGOAL_THEN `--(&1 / &64) <= (x:real^3)$3` ASSUME_TAC THENL
     [UNDISCH_TAC `(psi:(real^N->bool)->real^3->real^N) e x IN
                   moi_s5v_core t l av bv psi v` THEN
      REWRITE_TAC[moi_s5v_core; IN_UNION; IN_DIFF; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT1) THEN
        UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                     derived_dual_cell t l (bv e)` THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `x'':real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(x:real^3) = x''` SUBST_ALL_TAC THENL
         [MATCH_MP_TAC MOI_S5V_PSI_INJ THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
          `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
          `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
          `e:real^N->bool`] THEN
        ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(x'':real^3) IN moi_s35_upper` THEN
          REWRITE_TAC[moi_s35_upper] THEN SET_TAC[];
          UNDISCH_TAC `(x'':real^3) IN moi_s35_upper` THEN
          REWRITE_TAC[moi_s35_upper; IN_ELIM_THM] THEN REAL_ARITH_TAC];
        DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `e':real^N->bool = e` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN
          UNDISCH_TAC `(psi:(real^N->bool)->real^3->real^N) e x IN IMAGE (psi e)
                         {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0}` THEN
          REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
          DISCH_THEN(X_CHOOSE_THEN `x'':real^3` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `(x:real^3) = x''` SUBST_ALL_TAC THENL
           [MATCH_MP_TAC MOI_S5V_PSI_INJ THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
          `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
          `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
          `e:real^N->bool`] THEN
        ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
          SUBGOAL_THEN `~(e:real^N->bool = e')` ASSUME_TAC THENL
         [UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        USE_THEN "dj" (MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `(psi:(real^N->bool)->real^3->real^N) e'` MOI_S5V_LOWCAP_SLAB) THEN
        MP_TAC(ISPECL [`(psi:(real^N->bool)->real^3->real^N) e`; `moi_s35_slab`; `x:real^3`]
          FUN_IN_IMAGE) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(psi:(real^N->bool)->real^3->real^N) e x IN IMAGE (psi e')
                       {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0}` THEN
        SET_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s35_n x < &1 / &16` ASSUME_TAC THENL
     [USE_THEN "axis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`x:real^3`; `x':real^3`] MOI_S5V_BALL_B) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x':real^3) IN moi_s35_slab` THENL
     [MATCH_MP_TAC MOI_S5V_CSRC_B THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5V_CSRC_OFF THEN EXISTS_TAC `g:real^N->real^N->bool` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                   derived_dual_cell t l (bv e)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `~((x':real^3) IN moi_s35_slab) ==> x' IN moi_s35_upper` THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_S5V_SLABS_CLOSED = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi s.
     moi_s35_charts t l g av bv psi /\ FINITE s /\ (!e. e IN s ==> moi_s35_edge l e)
     ==> closed (UNIONS (IMAGE (\e. IMAGE (psi e) moi_s35_slab) s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S5V_SLAB_COMPACT THEN
  MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                        `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                        `bv:(real^N->bool)->real^N`] THEN
  ASM_SIMP_TAC[]);;

let MOI_S5V_CORE_INTERIOR = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi v cc.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ {v} IN l /\
     (!e. abs(cc e) <= &1 / &512)
     ==> moi_s5v_core t l av bv psi v SUBSET
         (subtopology euclidean (UNIONS t)) interior_of
         (moi_s35_csrc t l av bv psi cc v)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "chs")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cc")))) THEN
  ABBREV_TAC `ee = {e | moi_s35_edge l e /\
                        ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}` THEN
  SUBGOAL_THEN `FINITE (ee:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN MATCH_MP_TAC MOI_S5V_EDGES_FINITE THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "chs" (MP_TAC o CONJUNCT1 o REWRITE_RULE[moi_s35_charts]) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. e IN ee <=> moi_s35_edge l e /\
                                  ((av:(real^N->bool)->real^N) e = v \/ bv e = v)`
  (LABEL_TAC "ee") THENL
   [EXPAND_TAC "ee" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[MOI_S5V_IN_INTERIOR_OF] THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `v:real^N`]
      MOI_S5V_CORE_GRAPH) THEN
    UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`] UNIONS_MONO) THEN
    UNDISCH_TAC `(z:real^N) IN moi_s5v_core t l av bv psi v` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?e. moi_s35_edge l e /\
                     ((av:(real^N->bool)->real^N) e = v \/ bv e = v) /\
                     (z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                     moi_s35_slab` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    USE_THEN "tube" (fun tb -> MP_TAC(ISPECL
      [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`;
       `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
       `psi:(real^N->bool)->real^3->real^N`; `cc:(real^N->bool)->real`; `v:real^N`;
       `e:real^N->bool`; `z:real^N`;
       `UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                      (ee DELETE (e:real^N->bool)))`]
      (MATCH_MP MOI_S5V_CORE_INT_SLAB tb))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5V_SLABS_CLOSED THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                              `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                              `bv:(real^N->bool)->real^N`] THEN
        ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN MESON_TAC[];
        REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_DELETE; NOT_EXISTS_THM] THEN
        BETA_TAC THEN X_GEN_TAC `e':real^N->bool` THEN STRIP_TAC THEN
        SUBGOAL_THEN `moi_s35_edge l (e':real^N->bool)` ASSUME_TAC THENL
         [UNDISCH_TAC `(e':real^N->bool) IN ee` THEN
          USE_THEN "ee" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
          ALL_TAC] THEN
        USE_THEN "chs" (MP_TAC o CONJUNCT2 o REWRITE_RULE[moi_s35_charts]) THEN
        DISCH_THEN(MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                                    moi_s35_slab` THEN
        UNDISCH_TAC `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                    moi_s35_slab` THEN
        SET_TAC[];
        X_GEN_TAC `e':real^N->bool` THEN STRIP_TAC THEN
        REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_DELETE] THEN BETA_TAC THEN
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `e':real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[]];
    USE_THEN "tube" (fun tb -> MP_TAC(ISPECL
      [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->real^N->bool`;
       `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
       `psi:(real^N->bool)->real^3->real^N`; `cc:(real^N->bool)->real`; `v:real^N`;
       `z:real^N`;
       `UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                      (ee:(real^N->bool)->bool))`]
      (MATCH_MP MOI_S5V_CORE_INT_OFF tb))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5V_SLABS_CLOSED THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                              `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                              `bv:(real^N->bool)->real^N`] THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN BETA_TAC THEN
        USE_THEN "ee" (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `~(?e. moi_s35_edge l e /\
                           ((av:(real^N->bool)->real^N) e = v \/ bv e = v) /\
                           (z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                           moi_s35_slab)` THEN
        MESON_TAC[];
        X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
        REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN BETA_TAC THEN
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 11. The cores cover the graph: a point of the graph in a B-side lower    *)
(* band lies in the core of the B-end; otherwise it lies in the core of a   *)
(* vertex whose dual cell contains it (an A-side cap point of that cell is  *)
(* in the lower half, hence in such a band).                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S5V_CORE_COVER = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi
     ==> UNIONS l SUBSET UNIONS {moi_s5v_core t l av bv psi v | v | {v} IN l}`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "chs")) THEN
  USE_THEN "chs" (MP_TAC o REWRITE_RULE[moi_s35_charts]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ed") (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `derived_nbhd t l = UNIONS {derived_dual_cell t l v | v | {v:real^N} IN l}`
  ASSUME_TAC THENL
   [USE_THEN "tube" (MP_TAC o C MATCH_MP
      (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS l SUBSET derived_nbhd t (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(subtopology euclidean (UNIONS t)) interior_of
                (derived_nbhd t (l:(real^N->bool)->bool))` THEN
    REWRITE_TAC[INTERIOR_OF_SUBSET] THEN MATCH_MP_TAC MOI_FDN_DERIVED_NBHD_INTERIOR THEN
    UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUBSET_UNIONS];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?v:real^N. {v} IN l /\ y IN derived_dual_cell t l v` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS l SUBSET derived_nbhd t (l:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  ASM_CASES_TAC
   `?e. moi_s35_edge l e /\
        (y:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                        {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0}` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(bv:(real^N->bool)->real^N) e` THEN CONJ_TAC THENL
     [USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s5v_core; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_s5v_core; IN_UNION; IN_DIFF; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISJ1_TAC THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `e:real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^3)$3 <= &0` ASSUME_TAC THENL
   [USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o funpow 5 CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(REWRITE_RULE[GSYM th]
      (ASSUME `(y:real^N) IN derived_dual_cell t l v`))) THEN
    ASM_REWRITE_TAC[IN_IMAGE; moi_s35_lower; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x'':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^3) = x''` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_S5V_PSI_INJ THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
      `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
      `e:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `~(?e. moi_s35_edge l e /\
          (y:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                          {x | x IN moi_s35_cube /\ --(&1 / &64) <= x$3 /\ x$3 <= &0})` THEN
  REWRITE_TAC[] THEN EXISTS_TAC `e:real^N->bool` THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `x:real^3` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 12. The main theorem SOURCE: the pierced cells are PL 3-cells inside the *)
(* enlarged cells, the enlarged and the big cells are PL 3-cells, and the   *)
(* cores (compact, in the relative interiors of all pierced cells, off the  *)
(* tubes) cover the graph.                                                   *)
(* ------------------------------------------------------------------------- *)

let SOURCE = prove
 (MOI_S35_SOURCE,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tube") (K ALL_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                       `bv:(real^N->bool)->real^N`;
                       `psi:(real^N->bool)->real^3->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[moi_s35_source_ok] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`cc:(real^N->bool)->real`; `v:real^N`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [USE_THEN "tube" (fun tb -> MATCH_MP_TAC(MATCH_MP MOI_S5V_CSRC_CELL tb)) THEN
      EXISTS_TAC `g:real^N->real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5V_CSRC_SUB THEN EXISTS_TAC `g:real^N->real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "tube" (fun tb -> MATCH_MP_TAC(MATCH_MP MOI_S5V_PLUS_CELLS tb)) THEN
    EXISTS_TAC `g:real^N->real^N->bool` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `moi_s5v_core (t:(real^N->bool)->bool) l av bv psi` THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [USE_THEN "tube" (fun tb -> MATCH_MP_TAC(MATCH_MP MOI_S5V_CORE_COMPACT tb)) THEN
        EXISTS_TAC `g:real^N->real^N->bool` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `cc:(real^N->bool)->real` THEN DISCH_TAC THEN
        USE_THEN "tube" (fun tb -> MATCH_MP_TAC(MATCH_MP MOI_S5V_CORE_INTERIOR tb)) THEN
        EXISTS_TAC `g:real^N->real^N->bool` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
        MATCH_MP_TAC MOI_S5V_CORE_STUBE THEN EXISTS_TAC `g:real^N->real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      USE_THEN "tube" (fun tb -> MATCH_MP_TAC(MATCH_MP MOI_S5V_CORE_COVER tb)) THEN
      EXISTS_TAC `g:real^N->real^N->bool` THEN ASM_REWRITE_TAC[]]]);;

