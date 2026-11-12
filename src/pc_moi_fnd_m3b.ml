(* ========================================================================= *)
(* pc_moi_fnd_m3b: foundations of the Moise PL core, second part (Moise,     *)
(* Geometric Topology in Dimensions 2 and 3, Sec 23, pp.165-170, 23.6-23.8;  *)
(* Rourke-Sanderson 2.21). Main theorems (proving the statement terms of     *)
(* pc_moi_fnd_stmt.ml and pc_moi_core_stmt.ml):                              *)
(*   COMBINATORIAL_WB_PL_INVARIANT = MOI_FND_COMPLEX_BOUNDARY_PL_INVARIANT   *)
(*   PL_BALL_TRIANGULATION_BOUNDARY = MOI_FND_PL_BALL_COMPLEX                *)
(*   INTERIOR_LINK_RETRIANGULATION = MOI_FND_INTERIOR_LINK_RETRIANGULATION   *)
(*   COMBINATORIAL_WB_BARYCENTRIC = MOI_FND_BARYCENTRIC_CM_WB                *)
(*   BALL_TRIANGULATION_IN_OPEN = MOI_FND_BALL_TRIANGULATION                 *)
(* Route (charts and invariance of domain, as pc_moi_comb and pc_moi_star   *)
(* for the closed case): every point of a combinatorial 3-manifold with     *)
(* boundary has a PL chart onto a relatively open subset of the closed      *)
(* half-space 0 <= y$3 of real^3, boundary points going to the plane; a     *)
(* vertex with such a chart has a PL 2-sphere link (open image) or a PL     *)
(* 2-ball link (boundary point), the latter by a pseudo-radial projection   *)
(* over a closed half-space of directions; the boundary is the set of      *)
(* points without a neighbourhood homeomorphic to an open subset of real^3 *)
(* (invariance of domain), which homeomorphisms preserve.                   *)
(* The first section: the l1 model in real^3: the octahedron, its upper      *)
(* boundary half (a PL 2-ball, the cone from basis 3 over the diamond        *)
(* curve), and the upper half of the open octahedron (the chart model at     *)
(* boundary points).                                                         *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_fnd_dn.ml";;
needs "src/pc_moi_ptri.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. The model sets.                                                        *)
(* ------------------------------------------------------------------------- *)

let moi_fmb_oct = new_definition
 `moi_fmb_oct = {y:real^3 | abs(y$1) + abs(y$2) + abs(y$3) <= &1}`;;

let moi_fmb_lam = new_definition
 `moi_fmb_lam = {y:real^3 | &0 <= y$3 /\ abs(y$1) + abs(y$2) + y$3 = &1}`;;

let moi_fmb_gam = new_definition
 `moi_fmb_gam = {y:real^3 | y$3 = &0 /\ abs(y$1) + abs(y$2) = &1}`;;

let MOI_FMB_PL_POLYHEDRON_INTER_POLYHEDRON = prove
 (`!s h:real^N->bool.
        pl_polyhedron s /\ polyhedron h ==> pl_polyhedron (s INTER h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:(real^N->bool)->bool`
    STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\k:real^N->bool. k INTER h) c` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; POLYTOPE_INTER_POLYHEDRON] THEN
  REWRITE_TAC[INTER_UNIONS; SIMPLE_IMAGE]);;

let MOI_FMB_L1_BOUND = prove
 (`!y:real^3. norm y <= abs(y$1) + abs(y$2) + abs(y$3)`,
  GEN_TAC THEN MP_TAC(ISPEC `y:real^3` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3]);;

let MOI_FMB_OCT_EQ = prove
 (`moi_fmb_oct =
      {y:real^3 | vector[&1;&1;&1] dot y <= &1} INTER
      {y:real^3 | vector[&1;&1;-- &1] dot y <= &1} INTER
      {y:real^3 | vector[&1;-- &1;&1] dot y <= &1} INTER
      {y:real^3 | vector[&1;-- &1;-- &1] dot y <= &1} INTER
      {y:real^3 | vector[-- &1;&1;&1] dot y <= &1} INTER
      {y:real^3 | vector[-- &1;&1;-- &1] dot y <= &1} INTER
      {y:real^3 | vector[-- &1;-- &1;&1] dot y <= &1} INTER
      {y:real^3 | vector[-- &1;-- &1;-- &1] dot y <= &1}`,
  REWRITE_TAC[moi_fmb_oct; EXTENSION; IN_INTER; IN_ELIM_THM; DOT_3;
              VECTOR_3] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_FMB_OPEN_OCT = prove
 (`open {y:real^3 | abs(y$1) + abs(y$2) + abs(y$3) < &1}`,
  SUBGOAL_THEN
   `{y:real^3 | abs(y$1) + abs(y$2) + abs(y$3) < &1} =
      {y:real^3 | vector[&1;&1;&1] dot y < &1} INTER
      {y:real^3 | vector[&1;&1;-- &1] dot y < &1} INTER
      {y:real^3 | vector[&1;-- &1;&1] dot y < &1} INTER
      {y:real^3 | vector[&1;-- &1;-- &1] dot y < &1} INTER
      {y:real^3 | vector[-- &1;&1;&1] dot y < &1} INTER
      {y:real^3 | vector[-- &1;&1;-- &1] dot y < &1} INTER
      {y:real^3 | vector[-- &1;-- &1;&1] dot y < &1} INTER
      {y:real^3 | vector[-- &1;-- &1;-- &1] dot y < &1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_3; VECTOR_3] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[OPEN_HALFSPACE_LT]]);;

let MOI_FMB_OCT_POLYTOPE = prove
 (`polytope moi_fmb_oct`,
  REWRITE_TAC[POLYTOPE_EQ_BOUNDED_POLYHEDRON] THEN CONJ_TAC THENL
   [REWRITE_TAC[MOI_FMB_OCT_EQ] THEN
    REPEAT(MATCH_MP_TAC POLYHEDRON_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[POLYHEDRON_HALFSPACE_LE];
    REWRITE_TAC[bounded; moi_fmb_oct; IN_ELIM_THM] THEN
    EXISTS_TAC `&1` THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPEC `y:real^3` MOI_FMB_L1_BOUND) THEN ASM_REAL_ARITH_TAC]);;

let MOI_FMB_OCT_INTERIOR = prove
 (`interior moi_fmb_oct =
   {y:real^3 | abs(y$1) + abs(y$2) + abs(y$3) < &1}`,
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERIOR; moi_fmb_oct; IN_ELIM_THM; IN_BALL] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `abs((y:real^3)$1) + abs(y$2) + abs(y$3) <= &1` ASSUME_TAC
    THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN
      ASM_REWRITE_TAC[DIST_REFL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(&1 + e / &2) % y:real^3`) THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(&1 + e / &2) = &1 + e / &2` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH
       `y - (&1 + e / &2) % y:real^3 = --(e / &2) % y`; NORM_MUL;
       REAL_ABS_NEG] THEN
      SUBGOAL_THEN `abs(e / &2) = e / &2` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `e / &2 * norm(y:real^3) <= e / &2 * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        MP_TAC(SPEC `y:real^3` MOI_FMB_L1_BOUND) THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `e / &2 * &1 <= e / &2 * (abs((y:real^3)$1) + abs(y$2) + abs(y$3))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `(&1 + e / &2) * abs((y:real^3)$1) + (&1 + e / &2) * abs(y$2) +
      (&1 + e / &2) * abs(y$3) <= &1` THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[MOI_FMB_OPEN_OCT] THEN
    REWRITE_TAC[SUBSET; moi_fmb_oct; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let MOI_FMB_OCT_FACTS = prove
 (`polytope moi_fmb_oct /\ convex moi_fmb_oct /\ bounded moi_fmb_oct /\
   compact moi_fmb_oct /\
   vec 0 IN relative_interior moi_fmb_oct /\
   affine hull moi_fmb_oct = (:real^3) /\
   relative_frontier moi_fmb_oct =
     {y:real^3 | abs(y$1) + abs(y$2) + abs(y$3) = &1}`,
  SUBGOAL_THEN `(vec 0:real^3) IN interior moi_fmb_oct` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FMB_OCT_INTERIOR; IN_ELIM_THM; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull moi_fmb_oct = (:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_HULL_NONEMPTY_INTERIOR THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FMB_OCT_POLYTOPE; POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED;
               POLYTOPE_IMP_COMPACT; RELATIVE_INTERIOR_INTERIOR] THEN
  REWRITE_TAC[relative_frontier] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED;
               POLYTOPE_IMP_COMPACT; MOI_FMB_OCT_POLYTOPE] THEN
  REWRITE_TAC[MOI_FMB_OCT_INTERIOR; moi_fmb_oct; EXTENSION; IN_DIFF;
              IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let MOI_FMB_LAM_RF = prove
 (`relative_frontier moi_fmb_oct INTER {y:real^3 | &0 <= y$3} = moi_fmb_lam`,
  REWRITE_TAC[MOI_FMB_OCT_FACTS; moi_fmb_lam; EXTENSION; IN_INTER;
              IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let MOI_FMB_GAM_RF = prove
 (`moi_fmb_gam =
   relative_frontier moi_fmb_oct INTER {y:real^3 | basis 3 dot y = &0}`,
  REWRITE_TAC[MOI_FMB_OCT_FACTS; moi_fmb_gam; EXTENSION; IN_INTER;
              IN_ELIM_THM] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let MOI_FMB_GAM_POLYHEDRON = prove
 (`pl_polyhedron moi_fmb_gam`,
  REWRITE_TAC[MOI_FMB_GAM_RF] THEN
  MATCH_MP_TAC MOI_FMB_PL_POLYHEDRON_INTER_POLYHEDRON THEN
  SIMP_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER; MOI_FMB_OCT_POLYTOPE;
           POLYHEDRON_HYPERPLANE]);;

let MOI_FMB_LAM_POLYHEDRON = prove
 (`pl_polyhedron moi_fmb_lam`,
  REWRITE_TAC[GSYM MOI_FMB_LAM_RF] THEN
  MATCH_MP_TAC MOI_FMB_PL_POLYHEDRON_INTER_POLYHEDRON THEN
  SIMP_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER; MOI_FMB_OCT_POLYTOPE] THEN
  SUBGOAL_THEN `{y:real^3 | &0 <= y$3} = {y | --(basis 3) dot y <= &0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_LNEG] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    REWRITE_TAC[POLYHEDRON_HALFSPACE_LE]]);;

let MOI_FMB_IN_UNIONS_SEGMENTS = prove
 (`!(a:real^N) s y.
        y IN UNIONS {segment[a,z] | z | z IN s} <=>
        ?z u. z IN s /\ &0 <= u /\ u <= &1 /\ y = a + u % (z - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN
    DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN
    MAP_EVERY EXISTS_TAC [`z:real^N`; `u:real`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` (X_CHOOSE_THEN `u:real`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `segment[a:real^N,z]` THEN CONJ_TAC THENL
     [EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN EXISTS_TAC `u:real` THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_FMB_GAM_SPHERE = prove
 (`pl_sphere 1 moi_fmb_gam`,
  SUBGOAL_THEN `linear (\z:real^2. vector[z$1; z$2; &0]:real^3)` ASSUME_TAC
  THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (\y:real^3. vector[y$1; y$2]:real^2)` ASSUME_TAC
  THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron {z:real^2 | abs(z$1) + abs(z$2) = &1}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{z:real^2 | abs(z$1) + abs(z$2) = &1} =
      IMAGE (\y:real^3. vector[y$1; y$2]:real^2) moi_fmb_gam`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; moi_fmb_gam] THEN
      X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
       [DISCH_TAC THEN EXISTS_TAC `vector[(z:real^2)$1; z$2; &0]:real^3` THEN
        ASM_REWRITE_TAC[VECTOR_3; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
        STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_2]];
      MATCH_MP_TAC PL_POLYHEDRON_LINEAR_IMAGE THEN
      ASM_REWRITE_TAC[MOI_FMB_GAM_POLYHEDRON]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fmb_gam =
    IMAGE (\z:real^2. vector[z$1; z$2; &0]:real^3)
          {z:real^2 | abs(z$1) + abs(z$2) = &1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; moi_fmb_gam] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `vector[(y:real^3)$1; y$2]:real^2` THEN
      ASM_REWRITE_TAC[VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_2];
      STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^2. vector[z$1; z$2; &0]:real^3`;
                 `{z:real^2 | abs(z$1) + abs(z$2) = &1}`; `1`]
    MOI_FM3_PL_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3;
                VECTOR_3] THEN
    MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPEC `{z:real^2 | abs(z$1) + abs(z$2) = &1}`
    MOI_CMB_STAR_SHAPED_PL_SPHERE_0) THEN
  REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < abs((u:real^2)$1) + abs(u$2)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(u:real^2 = vec 0)` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; VECTOR_MUL_COMPONENT; REAL_ABS_MUL] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `inv(abs((u:real^2)$1) + abs(u$2))` THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ABS_INV] THEN
    SUBGOAL_THEN `abs(abs((u:real^2)$1) + abs(u$2)) = abs(u$1) + abs(u$2)`
    SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < abs((u:real^2)$1) + abs(u$2)` THEN CONV_TAC REAL_FIELD;
    MAP_EVERY X_GEN_TAC [`r1:real`; `r2:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs r1 = r1 /\ abs r2 = r2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs r1 * abs ((u:real^2)$1) + abs r1 * abs (u$2) = &1` THEN
    UNDISCH_TAC `abs r2 * abs ((u:real^2)$1) + abs r2 * abs (u$2) = &1` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < abs((u:real^2)$1) + abs(u$2)` THEN
    CONV_TAC REAL_FIELD]);;

let MOI_FMB_LAM_CONE = prove
 (`moi_fmb_lam =
   UNIONS {segment[vector[&0;&0;&1],z] | z | z IN moi_fmb_gam}`,
  REWRITE_TAC[EXTENSION; MOI_FMB_IN_UNIONS_SEGMENTS] THEN
  X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[moi_fmb_lam; moi_fmb_gam; IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_CASES_TAC `(y:real^3)$3 = &1` THENL
     [MAP_EVERY EXISTS_TAC [`vector[&1;&0;&0]:real^3`; `&0`] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - (y:real^3)$3` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`vector[(y:real^3)$1 / (&1 - y$3); y$2 / (&1 - y$3); &0]:real^3`;
      `&1 - (y:real^3)$3`] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
    REWRITE_TAC[REAL_ABS_DIV] THEN
    SUBGOAL_THEN `abs(&1 - (y:real^3)$3) = &1 - y$3` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `abs((y:real^3)$1) + abs(y$2) + y$3 = &1` THEN
      UNDISCH_TAC `&0 < &1 - (y:real^3)$3` THEN CONV_TAC REAL_FIELD;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < &1 - (y:real^3)$3` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < &1 - (y:real^3)$3` THEN CONV_TAC REAL_FIELD;
      REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` (X_CHOOSE_THEN `u:real`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    VECTOR_SUB_COMPONENT; VECTOR_3] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_ADD_LID; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs u = u` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs((z:real^3)$1) + abs(z$2) = &1` THEN
    CONV_TAC REAL_RING]);;

let MOI_FMB_GAM_SEG = prove
 (`~(vector[&0;&0;&1] IN moi_fmb_gam) /\
   (!x y. x IN moi_fmb_gam /\ y IN moi_fmb_gam /\
          y IN segment[vector[&0;&0;&1],x] ==> y = x)`,
  REWRITE_TAC[moi_fmb_gam; IN_ELIM_THM; VECTOR_3; MOI_STA_SEGMENT_PARAM] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2
    STRIP_ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `u = &1` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `(y:real^3)$3 = &0` THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    VECTOR_SUB_COMPONENT; VECTOR_3] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

let MOI_FMB_LAM_BALL = prove
 (`pl_ball 2 moi_fmb_lam`,
  REWRITE_TAC[MOI_FMB_LAM_CONE] THEN
  MP_TAC(ISPECL [`1`; `moi_fmb_gam`; `vector[&0;&0;&1]:real^3`]
    PL_BALL_CONE) THEN
  REWRITE_TAC[MOI_FMB_GAM_SPHERE; MOI_FMB_GAM_SEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let MOI_FMB_LAM_DISK = prove
 (`?k:real^3->bool kap kap'.
        &2 simplex k /\ pl_homeomorphism (k,moi_fmb_lam) (kap,kap') /\
        IMAGE kap (relative_frontier k) = moi_fmb_gam`,
  MP_TAC MOI_FMB_GAM_SPHERE THEN REWRITE_TAC[pl_sphere] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`relative_frontier k:real^3->bool`; `moi_fmb_gam`;
    `simplex_barycentre (k:real^3->bool)`; `vector[&0;&0;&1]:real^3`;
    `f:real^3->real^3`; `g:real^3->real^3`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[MOI_FMB_GAM_SEG] THEN
  REWRITE_TAC[GSYM MOI_FMB_LAM_CONE] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^3->bool`;
    `moi_con_conemap (relative_frontier k) (simplex_barycentre k)
       (vector[&0;&0;&1]) (f:real^3->real^3)`;
    `moi_con_conemap moi_fmb_gam (vector[&0;&0;&1])
       (simplex_barycentre (k:real^3->bool)) (g:real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `IMAGE (f:real^3->real^3) (relative_frontier k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN s ==> (p:real^3->real^3) x = q x)
      ==> IMAGE p s = IMAGE q s`) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `pl_homeomorphism (relative_frontier k,moi_fmb_gam)
                   (f:real^3->real^3,g)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]]);;

let MOI_FMB_LAM_YCONE = prove
 (`~(vec 0 IN moi_fmb_lam) /\ ~(moi_fmb_lam = {}) /\
   (!x y. x IN moi_fmb_lam /\ y IN moi_fmb_lam /\ y IN segment[vec 0,x]
          ==> y = x) /\
   UNIONS {segment[vec 0,z] | z | z IN moi_fmb_lam} DIFF moi_fmb_lam =
   {y:real^3 | abs(y$1) + abs(y$2) + abs(y$3) < &1} INTER {y | &0 <= y$3}`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fmb_lam; IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `vector[&0;&0;&1]:real^3` THEN
    REWRITE_TAC[moi_fmb_lam; IN_ELIM_THM; VECTOR_3] THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_fmb_lam; IN_ELIM_THM; MOI_STA_SEGMENT_PARAM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2
      STRIP_ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `u = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `abs((y:real^3)$1) + abs(y$2) + y$3 = &1` THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                      VECTOR_SUB_COMPONENT; VEC_COMPONENT] THEN
      REWRITE_TAC[REAL_SUB_RZERO; REAL_ADD_LID; REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs u = u` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `abs((x:real^3)$1) + abs(x$2) + x$3 = &1` THEN
      CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; MOI_FMB_IN_UNIONS_SEGMENTS] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[moi_fmb_lam; IN_ELIM_THM] THEN
    REWRITE_TAC[VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` (X_CHOOSE_THEN
        `u:real` STRIP_ASSUME_TAC)) MP_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs u = u` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs((z:real^3)$3) = z$3` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `u * abs((z:real^3)$1) + u * abs(z$2) + u * z$3 = u`
      SUBST1_TAC THENL
       [UNDISCH_TAC `abs((z:real^3)$1) + abs(z$2) + z$3 = &1` THEN
        CONV_TAC REAL_RING;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= u * (z:real^3)$3` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN
      ABBREV_TAC `t = abs((y:real^3)$1) + abs(y$2) + abs(y$3)` THEN
      ASM_CASES_TAC `t = &0` THENL
       [SUBGOAL_THEN `y:real^3 = vec 0` SUBST_ALL_TAC THENL
         [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`vector[&0;&0;&1]:real^3`; `&0`] THEN
          REWRITE_TAC[VECTOR_3; VECTOR_MUL_LZERO] THEN REAL_ARITH_TAC;
          REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
       [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`inv t % y:real^3`; `t:real`] THEN
        REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_ABS_MUL; REAL_ABS_INV] THEN
        SUBGOAL_THEN `abs t = t` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `abs((y:real^3)$3) = y$3` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
          UNDISCH_TAC `abs((y:real^3)$1) + abs(y$2) + abs(y$3) = t` THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
          ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]];
        ASM_REAL_ARITH_TAC]]]);;

(* ========================================================================= *)
(* Pseudo-radial projection over a closed half-space of directions          *)
(* (the boundary analogue of Rourke-Sanderson Lemma 2.19, used in           *)
(* pc_moi_comb for full rays): a compact polyhedron in the closed upper     *)
(* half-space met exactly once by every ray from the origin with direction  *)
(* in the closed upper half-space is a PL 2-ball.  Proof: its union with    *)
(* its mirror image is met once by every ray; the fan triangulation of the  *)
(* octahedron boundary cut by the plane y$3 = 0 restricts to its upper half *)
(* (the model 2-ball above), on which the radial map is projective.         *)
(* ========================================================================= *)

(* A copy of MOI_LFO_SUBCOMPLEX (pc_moi_lfopen, not loaded here).           *)

let MOI_FMB_SC_SUBCOMPLEX = prove
 (`!(k:(real^N->bool)->bool) k'.
     simplicial_complex k /\ k' SUBSET k /\
     (!f s. s IN k' /\ f face_of s ==> f IN k')
     ==> simplicial_complex k'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET];
    ASM SET_TAC[];
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let moi_fmb_refl = new_definition
 `moi_fmb_refl (y:real^3) = vector[y$1; y$2; --(y$3)]:real^3`;;

let MOI_FMB_REFL = prove
 (`(!y:real^3. (moi_fmb_refl y)$1 = y$1 /\ (moi_fmb_refl y)$2 = y$2 /\
               (moi_fmb_refl y)$3 = --(y$3)) /\
   (!y:real^3. moi_fmb_refl (moi_fmb_refl y) = y) /\
   linear moi_fmb_refl /\
   (!r y:real^3. moi_fmb_refl (r % y) = r % moi_fmb_refl y) /\
   (!y:real^3. moi_fmb_refl y = vec 0 <=> y = vec 0) /\
   (!y:real^3. y$3 = &0 ==> moi_fmb_refl y = y)`,
  REWRITE_TAC[moi_fmb_refl; VECTOR_3; linear] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FMB_IN_IMAGE_REFL = prove
 (`!s x:real^3. x IN IMAGE moi_fmb_refl s <=> moi_fmb_refl x IN s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[MOI_FMB_REFL]);;

let MOI_FMB_EXISTS_UNIQUE_POS_EQ = prove
 (`!P Q. (!r. &0 < r ==> (P r <=> Q r))
         ==> ((?!r. &0 < r /\ P r) <=> (?!r. &0 < r /\ Q r))`,
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN MESON_TAC[]);;

let MOI_FMB_HEMI_EXT = prove
 (`!s:real^3->bool.
     pl_polyhedron s /\ ~(vec 0 IN s) /\ (!x. x IN s ==> &0 <= x$3) /\
     (!u. ~(u = vec 0) /\ &0 <= u$3 ==> ?!r. &0 < r /\ r % u IN s)
     ==> ?s'. pl_polyhedron s' /\ ~(vec 0 IN s') /\
              (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s') /\
              s' INTER {y:real^3 | &0 <= y$3} = s`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `s UNION IMAGE moi_fmb_refl (s:real^3->bool)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_POLYHEDRON_LINEAR_IMAGE THEN
    ASM_REWRITE_TAC[MOI_FMB_REFL];
    ASM_REWRITE_TAC[IN_UNION; MOI_FMB_IN_IMAGE_REFL] THEN
    SUBGOAL_THEN `moi_fmb_refl (vec 0) = vec 0` SUBST1_TAC THENL
     [REWRITE_TAC[MOI_FMB_REFL]; ASM_REWRITE_TAC[]];
    X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `&0 <= (u:real^3)$3` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `u:real^3`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MOI_FMB_EXISTS_UNIQUE_POS_EQ THEN
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_UNION; MOI_FMB_IN_IMAGE_REFL] THEN
      EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `moi_fmb_refl (r % u) = r % (u:real^3)`
        (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC(el 5 (CONJUNCTS MOI_FMB_REFL)) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (ASSUME
        `!x:real^3. x IN s ==> &0 <= x$3`) o check (fun th ->
        concl th = `moi_fmb_refl (r % u) IN (s:real^3->bool)`)) THEN
      REWRITE_TAC[MOI_FMB_REFL; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `&0 <= r * (u:real^3)$3` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REAL_ARITH_TAC];
      SUBGOAL_THEN `~(moi_fmb_refl u = vec 0) /\ &0 <= (moi_fmb_refl u)$3`
      MP_TAC THENL
       [ASM_REWRITE_TAC[MOI_FMB_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MOI_FMB_EXISTS_UNIQUE_POS_EQ THEN
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_UNION; MOI_FMB_IN_IMAGE_REFL; MOI_FMB_REFL] THEN
      MATCH_MP_TAC(TAUT `~p ==> (p \/ q <=> q)`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (ASSUME
         `!x:real^3. x IN s ==> &0 <= x$3`)) THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_NOT_LE] THEN
      SUBGOAL_THEN `&0 < r * --((u:real^3)$3)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; MOI_FMB_IN_IMAGE_REFL;
                IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `moi_fmb_refl y = (y:real^3)`
        (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC(el 5 (CONJUNCTS MOI_FMB_REFL)) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (ASSUME
        `!x:real^3. x IN s ==> &0 <= x$3`) o check (fun th ->
        concl th = `moi_fmb_refl y IN (s:real^3->bool)`)) THEN
      REWRITE_TAC[MOI_FMB_REFL] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[]]]);;

let MOI_FMB_POLYHEDRON_HALVES = prove
 (`polyhedron {y:real^3 | &0 <= y$3} /\ polyhedron {y:real^3 | y$3 <= &0}`,
  CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | &0 <= y$3} = {y | --(basis 3) dot y <= &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_LNEG] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      REWRITE_TAC[POLYHEDRON_HALFSPACE_LE]];
    SUBGOAL_THEN `{y:real^3 | y$3 <= &0} = {y | basis 3 dot y <= &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
      REWRITE_TAC[POLYHEDRON_HALFSPACE_LE]]]);;

(* The projective property on a piece of a fan polytope (as in the proof of *)
(* MOI_CMB_FAN_TRIANGULATION, pc_moi_comb).                                  *)

let MOI_FMB_FAN_PROJ = prove
 (`!(s:real^N->bool) K sx d0 e d.
        simplicial_complex K /\ UNIONS K = s /\ ~(vec 0 IN s) /\
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s) /\
        polytope sx /\ vec 0 IN relative_interior sx /\
        d0 IN K /\ e face_of sx /\ ~(e = sx) /\
        d SUBSET conic hull d0 INTER e
        ==> ?a m. !y. y IN d
                      ==> &0 < a dot y /\
                          moi_cmb_radial s y = inv(a dot y) % y /\
                          m dot y = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(d0:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `d0:real^N->bool` MOI_CMB_HYPERPLANE_FUNCTIONAL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_CMB_STAR_AFFINE_HULL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`)] THEN
  MP_TAC(ISPECL [`sx:real^N->bool`; `e:real^N->bool`] MOI_CMB_FACE_FUNCTIONAL) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:real^N`) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `m:real^N`] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN conic hull d0 /\ y IN e` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N) dot y = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(m:real^N) dot y = &1` THEN
    ASM_REWRITE_TAC[DOT_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CMB_CONE_RADIAL THEN
  EXISTS_TAC `d0:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FMB_UNIONS_CUT = prove
 (`!P (h1:A->bool) h2.
     h1 UNION h2 = UNIV
     ==> UNIONS (IMAGE (\k. k INTER h1) P UNION IMAGE (\k. k INTER h2) P) =
         UNIONS P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIV] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_UNIONS; IN_UNION; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2 MP_TAC
      ASSUME_TAC)) THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `k:A->bool`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `k:A->bool` THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `x:A`) THENL
     [EXISTS_TAC `t INTER (h1:A->bool)` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      DISJ1_TAC THEN EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t INTER (h2:A->bool)` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      DISJ2_TAC THEN EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[]]]);;

let MOI_FMB_FAN_HALF = prove
 (`!(s:real^3->bool) K sx.
        simplicial_complex K /\ UNIONS K = s /\ ~(vec 0 IN s) /\
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s) /\
        polytope sx /\ vec 0 IN relative_interior sx
        ==> ?L. simplicial_complex L /\
                UNIONS L = relative_frontier sx INTER {y:real^3 | &0 <= y$3} /\
                !d. d IN L /\ ~(d = {})
                    ==> ?a m. !y. y IN d
                                  ==> &0 < a dot y /\
                                      moi_cmb_radial s y = inv(a dot y) % y /\
                                      m dot y = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `K:(real^3->bool)->bool`; `sx:real^3->bool`]
    MOI_CMB_FAN_POLYTOPES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC
   `IMAGE (\k:real^3->bool. k INTER {y:real^3 | &0 <= y$3}) P UNION
    IMAGE (\k:real^3->bool. k INTER {y:real^3 | y$3 <= &0}) P`
    POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FORALL_IN_UNION;
                 FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[POLYTOPE_INTER_POLYHEDRON; MOI_FMB_POLYHEDRON_HALVES];
    DISCH_THEN(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `UNIONS (IMAGE (\k:real^3->bool. k INTER {y:real^3 | &0 <= y$3}) P UNION
            IMAGE (\k:real^3->bool. k INTER {y:real^3 | y$3 <= &0}) P) =
    UNIONS P`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_UNIONS_CUT THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_UNIV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `{d:real^3->bool | d IN L /\ d SUBSET {y:real^3 | &0 <= y$3}}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FMB_SC_SUBCOMPLEX THEN
    EXISTS_TAC `L:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
    MAP_EVERY X_GEN_TAC [`f:real^3->bool`; `d:real^3->bool`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `z:real^3` THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      SUBGOAL_THEN `(z:real^3) IN UNIONS L` MP_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      GEN_REWRITE_TAC I [SUBSET] THEN
      REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `?k:real^3->bool. k IN P /\ z IN k` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN relative_frontier sx` THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `UNIONS P = relative_frontier (sx:real^3->bool)`)) THEN
        REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k INTER {y:real^3 | &0 <= y$3}` o
        check (fun th -> is_forall (concl th) &&
               can (term_match [] `!k:real^3->bool. k IN X ==> ?f. f SUBSET L /\ k = UNIONS f`) (concl th))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_UNION; IN_IMAGE] THEN DISJ1_TAC THEN
        EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^3) IN UNIONS f` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER] THEN
        ASM_REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `d:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `k INTER {y:real^3 | &0 <= y$3}` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; SET_TAC[]]];
    X_GEN_TAC `d:real^3->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `d:real^3->bool`;
     `IMAGE (\k:real^3->bool. k INTER {y:real^3 | &0 <= y$3}) P UNION
      IMAGE (\k:real^3->bool. k INTER {y:real^3 | y$3 <= &0}) P`]
      MOI_PLT_SIMPLEX_IN_COVER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN UNIONS L` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `d:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
        lhs (concl th) = `UNIONS L:real^3->bool`)) THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (term_match [] `!k:real^3->bool. k IN X ==> ?f. f SUBSET L /\ k = UNIONS f`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k':real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?k:real^3->bool. k IN P /\ d SUBSET k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(k':real^3->bool) IN
        IMAGE (\k:real^3->bool. k INTER {y:real^3 | &0 <= y$3}) P UNION
        IMAGE (\k:real^3->bool. k INTER {y:real^3 | y$3 <= &0}) P` THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
      STRIP_TAC THEN EXISTS_TAC `x:real^3->bool` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ASSUME `!k:real^3->bool. k IN P ==> ?d e. d IN K /\ e face_of sx /\
                    ~(e = sx) /\ k = conic hull d INTER e`) THEN
    DISCH_THEN(MP_TAC o SPEC `k:real^3->bool`) THEN
    REWRITE_TAC[ASSUME `(k:real^3->bool) IN P`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:real^3->bool` (X_CHOOSE_THEN `e:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_FMB_FAN_PROJ THEN
    MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `sx:real^3->bool`;
                          `d0:real^3->bool`; `e:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_FMB_RADIAL_HALF_IMAGE = prove
 (`!s':real^3->bool.
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s') /\ ~(vec 0 IN s')
        ==> IMAGE (moi_cmb_radial s') moi_fmb_lam =
            s' INTER {y:real^3 | &0 <= y$3}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (moi_cmb_radial s') (relative_frontier moi_fmb_oct) = s'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_RADIAL_IMAGE THEN ASM_REWRITE_TAC[MOI_FMB_OCT_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN relative_frontier moi_fmb_oct ==> ~(z = vec 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FMB_OCT_FACTS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    ASM_CASES_TAC `z:real^3 = vec 0` THEN ASM_REWRITE_TAC[VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MOI_FMB_LAM_RF; EXTENSION; IN_IMAGE; IN_INTER;
              IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s':real^3->bool`; `z:real^3`] MOI_CMB_RADIAL) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) (K ALL_TAC))) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (moi_cmb_radial s')
                                   (relative_frontier moi_fmb_oct)`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s':real^3->bool`; `z:real^3`] MOI_CMB_RADIAL) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) (K ALL_TAC))) THEN
    UNDISCH_TAC `&0 <= (y:real^3)$3` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ]]);;

let MOI_FMB_HEMI_PL_BALL = prove
 (`!s:real^3->bool.
     pl_polyhedron s /\ ~(vec 0 IN s) /\ (!x. x IN s ==> &0 <= x$3) /\
     (!u. ~(u = vec 0) /\ &0 <= u$3 ==> ?!r. &0 < r /\ r % u IN s)
     ==> pl_ball 2 s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_FMB_HEMI_EXT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX]
    o check (fun th -> concl th = `pl_polyhedron (s':real^3->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s':real^3->bool`; `K:(real^3->bool)->bool`; `moi_fmb_oct`]
    MOI_FMB_FAN_HALF) THEN
  ASM_REWRITE_TAC[MOI_FMB_OCT_FACTS; MOI_FMB_LAM_RF] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `moi_cmb_radial (s':real^3->bool)`]
    MOI_CMB_RADIAL_REALIZES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z1:real^3`; `z2:real^3`] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_CMB_RADIAL_INJECTIVE THEN
    MAP_EVERY EXISTS_TAC [`s':real^3->bool`; `moi_fmb_oct`] THEN
    ASM_REWRITE_TAC[MOI_FMB_OCT_FACTS] THEN
    UNDISCH_TAC `(z1:real^3) IN moi_fmb_lam` THEN
    UNDISCH_TAC `(z2:real^3) IN moi_fmb_lam` THEN
    REWRITE_TAC[GSYM MOI_FMB_LAM_RF; IN_INTER; MOI_FMB_OCT_FACTS] THEN
    SIMP_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `FINITE (L:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. x`; `moi_cmb_radial (s':real^3->bool)`;
                 `moi_real_vertex_sets (L:(real^3->bool)->bool)`]
    ABSTRACT_REALIZATIONS_PL_HOMEOMORPHIC) THEN
  ASM_SIMP_TAC[MOI_REAL_VERTEX_SETS_FINITE; MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX;
               MOI_REAL_VERTEX_SETS_REALIZES; MOI_REAL_VERTEX_SETS_UNIONS] THEN
  MP_TAC(ISPEC `s':real^3->bool` MOI_FMB_RADIAL_HALF_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MATCH_MP_TAC PL_BALL_PL_HOMEOMORPHIC THEN
  MAP_EVERY EXISTS_TAC [`moi_fmb_lam`; `h:real^3->real^3`;
                        `h':real^3->real^3`] THEN
  ASM_REWRITE_TAC[MOI_FMB_LAM_BALL]);;

(* ========================================================================= *)
(* Vertex links from PL charts.  A vertex w of a locally finite             *)
(* complex with a PL chart near w onto an open subset of real^3 has a PL    *)
(* 2-sphere link (pc_moi_comb, MOI_CMB_LOCAL_LINK_SPHERE); with a chart     *)
(* onto a relatively open subset of the closed half-space 0 <= y$3 taking w *)
(* to the plane y$3 = 0 it has a PL 2-ball link (pseudo-radial projection   *)
(* over the half-space of directions, above).                               *)
(* ========================================================================= *)

let MOI_FMB_HOMEO_LOCAL_SURJ = prove
 (`!(W:real^N->bool) (h:real^N->real^M) h' w e.
        homeomorphism (W,IMAGE h W) (h,h') /\ w IN W /\ &0 < e
        ==> ?O. open O /\ h w IN O /\
                !q. q IN O /\ q IN IMAGE h W
                    ==> ?x. x IN W /\ dist(w,x) < e /\ h x = q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^N->real^M`; `h':real^M->real^N`; `W:real^N->bool`;
                 `IMAGE (h:real^N->real^M) W`; `W INTER ball(w:real^N,e)`]
    HOMEOMORPHISM_IMP_OPEN_MAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `O:real^M->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^M) w IN IMAGE h (W INTER ball(w,e))`
    MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      ASM SET_TAC[]];
    X_GEN_TAC `q:real^M` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(q:real^M) IN IMAGE h (W INTER ball(w:real^N,e))` MP_TAC
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL] THEN MESON_TAC[]]);;

let MOI_FMB_CHART_DIM3 = prove
 (`!(W:real^N->bool) (h:real^N->real^3) h' V.
        homeomorphism (W,IMAGE h W) (h,h') /\ open V /\ ~(V = {}) /\
        V SUBSET IMAGE h W
        ==> 3 <= dimindex(:N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h':real^3->real^N`; `V:real^3->bool`]
    INVARIANCE_OF_DIMENSION) THEN
  REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]);;

let MOI_FMB_LINK_SPHERE_CHART = prove
 (`!(d:(real^N->bool)->bool) w W (h:real^N->real^3) h'.
        lf_simplicial_complex d /\ {w} IN d /\
        open_in (subtopology euclidean (UNIONS d)) W /\ w IN W /\
        pl_map_on W h /\ homeomorphism (W,IMAGE h W) (h,h') /\
        open (IMAGE h W)
        ==> pl_sphere 2 (UNIONS (simplicial_link d w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CMB_LOCAL_LINK_SPHERE THEN
  MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `h:real^N->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FMB_CHART_DIM3 THEN
    MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `h:real^N->real^3`;
                          `h':real^3->real^N`; `IMAGE (h:real^N->real^3) W`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL; IMAGE_EQ_EMPTY] THEN ASM SET_TAC[];
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    MATCH_MP_TAC MOI_CMB_OPEN_IN_BALL THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`W:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                   `w:real^N`; `e:real`] MOI_FMB_HOMEO_LOCAL_SURJ) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `O INTER IMAGE (h:real^N->real^3) W` OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^3) w`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_INTER] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

let MOI_FMB_CHART_HALF_OPEN_MAP = prove
 (`!(W:real^N->bool) (h:real^N->real^3) h' w O.
        homeomorphism (W,IMAGE h W) (h,h') /\ w IN W /\ open O /\
        IMAGE h W = O INTER {y:real^3 | &0 <= y$3}
        ==> !e. &0 < e
                ==> ?d. &0 < d /\
                        !q. dist(h w,q) < d /\ &0 <= q$3
                            ==> ?x. x IN W /\ dist(w,x) < e /\ h x = q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `w:real^N`; `e:real`] MOI_FMB_HOMEO_LOCAL_SURJ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O':real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(h:real^N->real^3) w IN O` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^3) w IN IMAGE h W` MP_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `O INTER (O':real^3->bool)` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^3) w`) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_INTER] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM]);;

(* The ray property over the closed upper half-space of directions: a copy *)
(* of MOI_CMB_RAY_PROPERTY (pc_moi_comb) with the openness hypothesis       *)
(* restricted to the half-space 0 <= q$3 and g v on the plane.              *)

let MOI_FMB_RAY_HALF = prove
 (`!(c:(real^N->bool)->bool) v (W:real^N->bool) (g:real^N->real^3) e r d.
        lf_simplicial_complex c /\ {v} IN c /\ W SUBSET UNIONS c /\
        &0 < r /\ r <= &1 /\ &0 < d /\
        (!x. x IN UNIONS c /\ dist(v,x) < e ==> ?t. t IN c /\ v IN t /\ x IN t) /\
        (!x l. x IN W /\ dist(v,x) < e /\ &0 <= l /\ l <= &1
               ==> v + l % (x - v) IN W /\
                   g(v + l % (x - v)) = g v + l % (g x - g v)) /\
        (!y. y IN UNIONS (simplicial_link c v)
             ==> v + r % (y - v) IN W /\ dist(v,v + r % (y - v)) < e) /\
        (!x y. x IN W /\ y IN W /\ g x = g y ==> x = y) /\
        (g v)$3 = &0 /\
        (!q. dist(g v,q) < d /\ &0 <= q$3
             ==> ?x. x IN W /\ dist(v,x) < e /\ g x = q)
        ==> !u. ~(u = vec 0) /\ &0 <= u$3
                ==> ?!rho. &0 < rho /\
                           g v + rho % u IN
                           IMAGE g (IMAGE (\y. v + r % (y - v))
                                          (UNIONS (simplicial_link c v)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "star") (CONJUNCTS_THEN2 (LABEL_TAC "conic")
   (CONJUNCTS_THEN2 (LABEL_TAC "lr") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "gv3") (LABEL_TAC "open")))))))))))) THEN
  X_GEN_TAC `u:real^3` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "u3")) THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; MOI_CMB_IN_IMAGE_IMAGE] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < norm(u:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < d / (&2 * norm(u:real^3))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "open" (MP_TAC o SPEC
      `(g:real^N->real^3) v + (d / (&2 * norm(u:real^3))) % u`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[dist; VECTOR_ARITH `a - (a + b):real^N = --b`;
                    NORM_NEG; NORM_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
        SUBGOAL_THEN `d / (&2 * norm(u:real^3)) * norm u = d / &2`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < norm(u:real^3)` THEN CONV_TAC REAL_FIELD;
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        USE_THEN "gv3" SUBST1_TAC THEN REWRITE_TAC[REAL_ADD_LID] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        USE_THEN "u3" (fun th -> REWRITE_TAC[th]) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `~(x:real^N = v)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
       `(g:real^N->real^3) x = g v + (d / (&2 * norm(u:real^3))) % u` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `a = a + b <=> b = vec 0:real^N`;
                      VECTOR_MUL_EQ_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `?t:real^N->bool. t IN c /\ v IN t /\ x IN t`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "star" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                   `x:real^N`] MOI_CMB_STAR_CONE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `s:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))))) THEN
    USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `y IN UNIONS (simplicial_link c (v:real^N))`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(g:real^N->real^3)(v + r % (y - v)) =
      g v + (r / s) % (g(v + s % (y - v)) - g v)`
    ASSUME_TAC THENL
     [DISJ_CASES_TAC(REAL_ARITH `(s:real) <= r \/ r < s`) THENL
       [USE_THEN "conic" (MP_TAC o SPECL [`v + r % (y - v):real^N`; `s / r`]) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                       REAL_MUL_LID];
          ALL_TAC] THEN
        REWRITE_TAC[VECTOR_ARITH `(v + r % (y - v)) - v:real^N = r % (y - v)`;
                    VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`;
                        VECTOR_MUL_ASSOC] THEN
        SUBGOAL_THEN `r / s * s / r = &1` SUBST1_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`&0 < r`; `&0 < s`] THEN CONV_TAC REAL_FIELD;
          VECTOR_ARITH_TAC];
        USE_THEN "conic" (MP_TAC o SPECL [`v + s % (y - v):real^N`; `r / s`]) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                       REAL_MUL_LID];
          ALL_TAC] THEN
        REWRITE_TAC[VECTOR_ARITH `(v + r % (y - v)) - v:real^N = r % (y - v)`;
                    VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]];
      ALL_TAC] THEN
    EXISTS_TAC `r / s * d / (&2 * norm(u:real^3))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`; VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b y1 y2. &0 < a /\ a < b /\
                y1 IN UNIONS (simplicial_link c v) /\
                y2 IN UNIONS (simplicial_link c v) /\
                (g:real^N->real^3) v + a % u = g(v + r % (y1 - v)) /\
                g v + b % u = g(v + r % (y2 - v))
                ==> F`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `y2 IN UNIONS (simplicial_link c (v:real^N))`))) THEN
    STRIP_TAC THEN
    USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `y1 IN UNIONS (simplicial_link c (v:real^N))`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "conic" (MP_TAC o SPECL [`v + r % (y2 - v):real^N`; `a / b`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                   REAL_MUL_LID];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `(v + r % (y - v)) - v:real^N = r % (y - v)`;
                VECTOR_MUL_ASSOC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `v + (a / b * r) % (y2 - v):real^N = v + r % (y1 - v)`
    ASSUME_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(g:real^N->real^3) v + a % u = g(v + r % (y1 - v))`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(g:real^N->real^3) v + b % u = g(v + r % (y2 - v))`)) THEN
      REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y2:real^N`;
                   `y1:real^N`; `a / b * r`; `r:real`] MOI_CMB_CONE_UNIQUE) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `a / b * r < &1 * r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC))) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `(a:real) < b \/ a = b \/ b < a`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_FMB_IN_TRANSLATE = prove
 (`!(a:real^N) s y. y IN IMAGE (\x. --a + x) s <=> a + y IN s`,
  REWRITE_TAC[IN_IMAGE] THEN
  MESON_TAC[VECTOR_ARITH `a + --a + x:real^N = x`;
            VECTOR_ARITH `--a + a + y:real^N = y`]);;

(* The half-space version of MOI_CMB_LOCAL_LINK_SPHERE (pc_moi_comb), whose *)
(* proof is copied up to the last step, where the pseudo-radial projection  *)
(* over the half-space (MOI_FMB_HEMI_PL_BALL) replaces STAR_SHAPED_PL_SPHERE.*)

let MOI_FMB_LOCAL_LINK_BALL = prove
 (`!(c:(real^N->bool)->bool) (v:real^N) (W:real^N->bool) (g:real^N->real^3).
        3 <= dimindex(:N) /\
        lf_simplicial_complex c /\ {v} IN c /\
        W SUBSET UNIONS c /\ v IN W /\
        (?e. &0 < e /\ !x. x IN UNIONS c /\ dist(v,x) < e ==> x IN W) /\
        pl_map_on W g /\
        (!x y. x IN W /\ y IN W /\ g x = g y ==> x = y) /\
        (g v)$3 = &0 /\ (!x. x IN W ==> &0 <= (g x)$3) /\
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !q. dist(g v,q) < d /\ &0 <= q$3
                         ==> ?x. x IN W /\ dist(v,x) < e /\ g x = q)
        ==> pl_ball 2 (UNIONS (simplicial_link c v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
   (CONJUNCTS_THEN2 (LABEL_TAC "gv3") (CONJUNCTS_THEN2 (LABEL_TAC "half")
     (LABEL_TAC "open"))))))))))) THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS (simplicial_link c (v:real^N)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `simplicial_link c (v:real^N)` THEN
    ASM_SIMP_TAC[MOI_CMB_LINK_FINITE] THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `g:real^N->real^3`; `v:real^N`]
    MOI_CMB_PL_LOCALLY_CONIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?e. &0 < e /\ e <= e1 /\ e <= e2 /\ e <= e3`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min e1 (min e2 e3)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN UNIONS c /\ dist(v:real^N,x) < e
        ==> ?t. t IN c /\ v IN t /\ x IN t`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x l. x IN W /\ dist(v:real^N,x) < e /\ &0 <= l /\ l <= &1
          ==> v + l % (x - v) IN W /\
              (g:real^N->real^3)(v + l % (x - v)) = g v + l % (g x - g v)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (simplicial_link c (v:real^N))`; `v:real^N`; `e:real`]
    MOI_CMB_SMALL_SCALE) THEN
  ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT; COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. y IN UNIONS (simplicial_link c v)
        ==> v + r % (y - v) IN W /\ dist(v:real^N,v + r % (y - v)) < e`
  (LABEL_TAC "lr") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `dist(v:real^N,v + r % (y - v)) < e` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v + r % (y - v) IN UNIONS (c:(real^N->bool)->bool)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`]
        MOI_CMB_LINK_IN_STAR) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    ASM_MESON_TAC[REAL_LTE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\y. v + r % (y - v)) (UNIONS (simplicial_link c (v:real^N))) SUBSET W`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `y IN UNIONS (simplicial_link c (v:real^N))`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_SCALE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (IMAGE (\y. v + r % (y - v))
                     (UNIONS (simplicial_link c (v:real^N))))
              (g:real^N->real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  USE_THEN "open" (fun th -> MP_TAC(MATCH_MP th (ASSUME `&0 < e`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `W:real^N->bool`;
                 `g:real^N->real^3`; `e:real`; `r:real`; `d:real`]
    MOI_FMB_RAY_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `~((g:real^N->real^3) v IN IMAGE g (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N)))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_CMB_IN_IMAGE_IMAGE; NOT_EXISTS_THM] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
        `y IN UNIONS (simplicial_link c (v:real^N))`))) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `~(y:real^N = v)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`]
          MOI_CMB_LINK_IN_STAR) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `v:real^N = v + r % (y - v)` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(v:real^N) = v + r % (y - v) <=> r % (y - v) = vec 0`;
       VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (IMAGE (g:real^N->real^3) (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N)))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_ball 2 (IMAGE (g:real^N->real^3) (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N)))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_BALL_PL_HOMEOMORPHIC THEN
    EXISTS_TAC `IMAGE (\x:real^3. --((g:real^N->real^3) v) + x)
                 (IMAGE g (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N)))))` THEN
    MAP_EVERY EXISTS_TAC [`\x:real^3. (g:real^N->real^3) v + x`;
                          `\x:real^3. --((g:real^N->real^3) v) + x`] THEN
    ASM_SIMP_TAC[MOI_CMB_TRANSLATION_PL_HOMEOMORPHISM] THEN
    MATCH_MP_TAC MOI_FMB_HEMI_PL_BALL THEN
    REWRITE_TAC[MOI_FMB_IN_TRANSLATE; VECTOR_ADD_RID] THEN
    ASM_SIMP_TAC[PL_POLYHEDRON_TRANSLATION] THEN
    REWRITE_TAC[MOI_CMB_IN_IMAGE_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z:real^3 = g(v + r % (y - v:real^N)) - g v` SUBST1_TAC
    THENL
     [UNDISCH_TAC `(g:real^N->real^3) v + z = g (v + r % (y - v))` THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN USE_THEN "gv3" SUBST1_TAC THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN USE_THEN "half" MATCH_MP_TAC THEN
    USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `y IN UNIONS (simplicial_link c (v:real^N))`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\y. v + r % (y - v))
                        (UNIONS (simplicial_link c (v:real^N)))`;
                 `g:real^N->real^3`;
                 `IMAGE (g:real^N->real^3) (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N))))`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT];
      ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
      REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (\y. v + r % (y - v))
                     (UNIONS (simplicial_link c (v:real^N))) SUBSET W` THEN
      MAP_EVERY UNDISCH_TAC
       [`x1 IN IMAGE (\y. v + r % (y - v))
                     (UNIONS (simplicial_link c (v:real^N)))`;
        `x2 IN IMAGE (\y. v + r % (y - v))
                     (UNIONS (simplicial_link c (v:real^N)))`] THEN
      SET_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `g':real^3->real^N`)] THEN
  MATCH_MP_TAC(ISPECL
   [`IMAGE (g:real^N->real^3) (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N))))`;
    `UNIONS (simplicial_link c (v:real^N))`;
    `(\z:real^N. v + inv r % (z - v)) o (g':real^3->real^N)`;
    `(g:real^N->real^3) o (\y:real^N. v + r % (y - v))`; `2`]
   MOI_FM3_PL_BALL_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `IMAGE (\y. v + r % (y - v))
                    (UNIONS (simplicial_link c (v:real^N)))` THEN
  ASM_SIMP_TAC[MOI_CMB_SCALE_PL_HOMEOMORPHISM] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[]);;

let MOI_FMB_OPEN_UPPER_POINT = prove
 (`!(O:real^3->bool) a. open O /\ a IN O /\ &0 <= a$3
                        ==> ?y. y IN O /\ &0 < y$3`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3` o REWRITE_RULE[open_def]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `a + (e / &2) % basis 3:real^3` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[dist; VECTOR_ARITH `(a + x) - a:real^N = x`; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_FMB_OPEN_UPPER = prove
 (`open {y:real^3 | &0 < y$3}`,
  REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT]);;

let MOI_FMB_LINK_BALL_CHART = prove
 (`!(d:(real^N->bool)->bool) w W (h:real^N->real^3) h' O.
        lf_simplicial_complex d /\ {w} IN d /\
        open_in (subtopology euclidean (UNIONS d)) W /\ w IN W /\
        pl_map_on W h /\ homeomorphism (W,IMAGE h W) (h,h') /\
        open O /\ IMAGE h W = O INTER {y:real^3 | &0 <= y$3} /\
        (h w)$3 = &0
        ==> pl_ball 2 (UNIONS (simplicial_link d w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FMB_LOCAL_LINK_BALL THEN
  MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `h:real^N->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(h:real^N->real^3) w IN O` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^3) w IN IMAGE h W` MP_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FMB_CHART_DIM3 THEN
    MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `h:real^N->real^3`;
                          `h':real^3->real^N`;
                          `O INTER {y:real^3 | &0 < y$3}`] THEN
    ASM_SIMP_TAC[OPEN_INTER; MOI_FMB_OPEN_UPPER] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      MATCH_MP_TAC MOI_FMB_OPEN_UPPER_POINT THEN
      EXISTS_TAC `(h:real^N->real^3) w` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
      SIMP_TAC[REAL_LT_IMP_LE]];
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    MATCH_MP_TAC MOI_CMB_OPEN_IN_BALL THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^3) x IN IMAGE h W` MP_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
    MATCH_MP_TAC MOI_FMB_CHART_HALF_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `O:real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* PL charts at the points of a combinatorial 3-manifold with               *)
(* boundary.  The open star of an interior vertex maps onto the interior    *)
(* of a 3-simplex (pushed into the open upper half-space); the open star of *)
(* a boundary vertex maps onto the upper half of the open octahedron, the   *)
(* points of complex_boundary going exactly to the plane y$3 = 0 (cone      *)
(* coordinates: a point v + r % (z - v) of the open star is on the boundary *)
(* iff z is on the boundary circle of the link disk).                       *)
(* ========================================================================= *)

let MOI_FMB_CONE_PT_OPEN_STAR = prove
 (`!c (v:real^N) z r.
        lf_simplicial_complex c /\ {v} IN c /\
        z IN UNIONS (simplicial_link c v) /\ &0 <= r /\ r < &1
        ==> v + r % (z - v) IN moi_sta_open_star c v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_DIFF; MOI_FMB_IN_UNIONS_SEGMENTS] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`z:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `v + r % (z - v):real^N = z` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MOI_STA_SEGMENT_PARAM] THEN
      EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `v + r % (z - v):real^N = z <=>
                              (&1 - r) % (z - v) = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]]);;

let MOI_FMB_CB_CONE = prove
 (`!c (v:real^N) z r.
        lf_simplicial_complex c /\ {v} IN c /\
        z IN UNIONS (simplicial_link c v) /\ &0 < r /\ r < &1
        ==> (v + r % (z - v) IN complex_boundary c <=>
             z IN moi_fm3_bd2 (simplicial_link c v))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `z:real^N`; `r:real`]
      MOI_FMB_CONE_PT_OPEN_STAR) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; moi_sta_open_star; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `v + r % (z - v) IN complex_boundary (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
        is_forall (concl th) &&
        can (term_match [] `!t. t IN c /\ x IN t ==> (v:real^N) IN t`)
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
      MOI_FM3_BT_AT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `convex(e:real^N->bool) /\ ~(e = {})` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
        MOI_FM3_LINK_IN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
        DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `v + r % (z - v) IN (s:real^N->bool)` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN
    ASM_SIMP_TAC[CONVEX_HULL_EQ; MOI_FMB_IN_UNIONS_SEGMENTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `l:real`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^N) IN e` ASSUME_TAC THENL
     [SUBGOAL_THEN `convex hull e = (e:real^N->bool)`
        (fun th -> ASM_MESON_TAC[th]) THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN UNIONS (simplicial_link c v)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `z:real^N = y` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `z:real^N`;
                     `y:real^N`; `r:real`; `l:real`] MOI_CMB_CONE_UNIQUE) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < l` (fun th -> SIMP_TAC[th]) THEN
      ASM_CASES_TAC `l = &0` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      UNDISCH_TAC `v + r % (z - v):real^N = v + l % (y - v)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      REWRITE_TAC[VECTOR_ARITH `v + r % (z - v):real^N = v <=>
                                r % (z - v) = vec 0`] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fm3_bd2; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_fm3_bd2; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_FM3_BT_FROM_LINK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
    ASM_SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; IN_INSERT; REAL_LT_IMP_LE]]);;

let MOI_FMB_OPEN_STAR_CB = prove
 (`!c (v:real^N) x.
        x IN moi_sta_open_star c v /\ x IN complex_boundary c
        ==> v IN complex_boundary c`,
  REWRITE_TAC[moi_sta_open_star; complex_boundary; IN_ELIM_THM; IN_UNIONS] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)
    (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]);;

let MOI_FMB_OPEN_IN_LOCPOLY = prove
 (`!c W:real^N->bool.
        lf_simplicial_complex c /\ open_in (subtopology euclidean (UNIONS c)) W
        ==> locally_polyhedral W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `U:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_INTER_OPEN; LOCALLY_POLYHEDRAL_LF_COMPLEX]);;

let MOI_FMB_HOMEO_TRANSLATE = prove
 (`!(s:real^M->bool) t (f:real^M->real^N) g a.
        homeomorphism (s,t) (f,g)
        ==> homeomorphism (s,IMAGE (\x. a + f x) s)
                          ((\x. a + f x),(\y. g(--a + y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_IMAGE; VECTOR_ARITH `--a + a + x:real^N = x`] THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `(\y. g(--a + y)) = (g:real^N->real^M) o (\y. --a + y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`] THEN
    ASM_REWRITE_TAC[ETA_AX]]);;

let MOI_FMB_STAR_SPHERE_CHART = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_sphere 2 (UNIONS (simplicial_link c v))
        ==> ?p:real^N->real^3 p'.
              pl_map_on (moi_sta_open_star c v) p /\
              homeomorphism (moi_sta_open_star c v,
                             IMAGE p (moi_sta_open_star c v)) (p,p') /\
              open (IMAGE p (moi_sta_open_star c v)) /\
              (!y. y IN moi_sta_open_star c v ==> &0 < (p y)$3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_STAR_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `q:real^3->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `locally_polyhedral (moi_sta_open_star c (v:real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_OPEN_IN_LOCPOLY THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism] o
    check (fun th -> can (term_match []
      `pl_homeomorphism (A:real^N->bool,B:real^3->bool) (f,g)`) (concl th))) THEN
  SUBGOAL_THEN
   `IMAGE (p:real^N->real^3) (moi_sta_open_star c v) = interior S`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:real^N->real^3`; `q:real^3->real^N`;
      `UNIONS {segment[v:real^N,y] | y | y IN UNIONS(simplicial_link c v)}`;
      `S:real^3->bool`; `UNIONS (simplicial_link c (v:real^N))`]
      MOI_STA_IMAGE_DIFF) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
        check (fun th -> can (term_match []
          `homeomorphism (A:real^N->bool,B:real^3->bool) (f,g)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; MOI_FMB_IN_UNIONS_SEGMENTS] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`y:real^N`; `&1`] THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MOI_STA_SIMPLEX_INTERIOR]];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded(S:real^3->bool)` MP_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  REWRITE_TAC[bounded] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_sta_open_star c v SUBSET
                UNIONS {segment[v:real^N,y] | y | y IN UNIONS(simplicial_link c v)}`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `\x:real^N. (B + &1) % basis 3 + (p:real^N->real^3) x` THEN
  EXISTS_TAC `\y:real^3. (q:real^3->real^N) (--((B + &1) % basis 3) + y)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_ADD THEN ASM_SIMP_TAC[PL_MAP_ON_CONST] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `UNIONS {segment[v:real^N,y] | y | y IN UNIONS(simplicial_link c v)}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `locally_polyhedral (moi_sta_open_star c (v:real^N))` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FMB_HOMEO_TRANSLATE THEN
    EXISTS_TAC `IMAGE (p:real^N->real^3) (moi_sta_open_star c v)` THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC
     [`UNIONS {segment[v:real^N,y] | y | y IN UNIONS(simplicial_link c v)}`;
      `S:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    SUBGOAL_THEN
     `IMAGE (\x:real^N. (B + &1) % basis 3 + (p:real^N->real^3) x)
            (moi_sta_open_star c v) =
      IMAGE (\y. (B + &1) % basis 3 + y) (interior S)`
    SUBST1_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th ->
        concl th = `IMAGE (p:real^N->real^3) (moi_sta_open_star c v) =
                    interior S`)) THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF];
      MATCH_MP_TAC OPEN_TRANSLATION THEN REWRITE_TAC[OPEN_INTERIOR]];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^N->real^3) y IN S` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!t:real^3->bool. x IN t /\ t SUBSET S ==> x IN S`) THEN
      EXISTS_TAC `interior S:real^3->bool` THEN
      REWRITE_TAC[INTERIOR_SUBSET] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th ->
        concl th = `IMAGE (p:real^N->real^3) (moi_sta_open_star c v) =
                    interior S`)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    MP_TAC(ISPECL [`(p:real^N->real^3) y`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^N->real^3) y` o check (fun th ->
      is_forall (concl th) && can (term_match [] `!x:real^3. x IN S ==> norm x <= B`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_FMB_LAM_CHAR = prove
 (`!(L:real^N->bool) (psi:real^N->real^3) psi' B.
        homeomorphism (L,moi_fmb_lam) (psi,psi') /\ B SUBSET L /\
        IMAGE psi B = moi_fmb_gam
        ==> !z. z IN L ==> ((psi z)$3 = &0 <=> z IN B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(psi:real^N->real^3) z IN moi_fmb_lam` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_fmb_lam; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(psi:real^N->real^3) z$3 = &0 <=> psi z IN moi_fmb_gam`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_fmb_gam; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `IMAGE (psi:real^N->real^3) B = moi_fmb_gam`)) THEN
  REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z:real^N = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(y:real^N) IN L` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    DISCH_TAC THEN EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]]);;

let MOI_FMB_LINK_TO_LAM = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_ball 2 (UNIONS (simplicial_link c v))
        ==> ?psi:real^N->real^3 psi'.
              pl_homeomorphism (UNIONS (simplicial_link c v),moi_fmb_lam)
                               (psi,psi') /\
              ~(moi_fm3_bd2 (simplicial_link c v) = {}) /\
              !z. z IN UNIONS (simplicial_link c v)
                  ==> ((psi z)$3 = &0 <=>
                       z IN moi_fm3_bd2 (simplicial_link c v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `simplicial_link c (v:real^N)` MOI_FM3_DISK_PL) THEN
  ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC MOI_FMB_LAM_DISK THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:real^3->bool` (X_CHOOSE_THEN `kap:real^3->real^3`
    (X_CHOOSE_THEN `kap':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `k3:real^3->bool`; `&2:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^N->real^3` (X_CHOOSE_THEN `q0:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (UNIONS (simplicial_link c v),moi_fmb_lam)
     ((\z:real^N. (kap:real^3->real^3) ((p0:real^N->real^3) ((g:real^N->real^N) z))),
      (\y:real^3. (f:real^N->real^N) ((q0:real^3->real^N) ((kap':real^3->real^3) y))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS (simplicial_link c (v:real^N))`; `k:real^N->bool`;
                   `k3:real^3->bool`; `g:real^N->real^N`; `f:real^N->real^N`;
                   `p0:real^N->real^3`; `q0:real^3->real^N`]
      PL_HOMEOMORPHISM_COMPOSE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`UNIONS (simplicial_link c (v:real^N))`; `k3:real^3->bool`;
                   `moi_fmb_lam`; `(p0:real^N->real^3) o (g:real^N->real^N)`;
                   `(f:real^N->real^N) o (q0:real^3->real^N)`;
                   `kap:real^3->real^3`; `kap':real^3->real^3`]
      PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\z:real^N. (kap:real^3->real^3) ((p0:real^N->real^3) ((g:real^N->real^N) z))`;
    `\y:real^3. (f:real^N->real^N) ((q0:real^3->real^N) ((kap':real^3->real^3) y))`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FMB_LAM_CHAR THEN
  EXISTS_TAC `\y:real^3. (f:real^N->real^N) ((q0:real^3->real^N) ((kap':real^3->real^3) y))` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ASSUME `pl_homeomorphism (k,UNIONS (simplicial_link c (v:real^N)))
                     (f:real^N->real^N,g)`) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `IMAGE (f:real^N->real^N) k = l /\ r SUBSET k ==> IMAGE f r SUBSET l`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[relative_frontier] THEN
    MATCH_MP_TAC(SET_RULE `closure (k:real^N->bool) = k ==> closure k DIFF s SUBSET k`) THEN
    ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[SYM(ASSUME
    `IMAGE (kap:real^3->real^3) (relative_frontier k3) = moi_fmb_gam`)] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    MATCH_MP_TAC(SET_RULE `closure (k:real^N->bool) = k ==> closure k DIFF s SUBSET k`) THEN
    ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ASSUME `pl_homeomorphism (k,UNIONS (simplicial_link c (v:real^N)))
                   (f:real^N->real^N,g)`) THEN
  MP_TAC(ASSUME `pl_homeomorphism (relative_frontier k,relative_frontier k3)
                   (p0:real^N->real^3,q0)`) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC(SET_RULE
   `IMAGE (p:real^N->real^3) r = r3 /\ (!x. x IN r ==> (g:real^N->real^N) (f x) = x)
    ==> IMAGE (\x. (kap:real^3->real^3) (p (g (f x)))) r = IMAGE kap r3`) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FMB_LINK_POLYHEDRON = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c
        ==> pl_polyhedron (UNIONS (simplicial_link c v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `simplicial_link c (v:real^N)` THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_FM3_LINK_SC; MOI_SCF_SC_FINITE; MOI_CON_SC_POLYTOPE]);;

let MOI_FMB_STAR_BALL_CHART = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_ball 2 (UNIONS (simplicial_link c v))
        ==> ?p:real^N->real^3 p'.
              pl_map_on (moi_sta_open_star c v) p /\
              homeomorphism (moi_sta_open_star c v,
                             IMAGE p (moi_sta_open_star c v)) (p,p') /\
              IMAGE p (moi_sta_open_star c v) =
                {y:real^3 | abs(y$1) + abs(y$2) + abs(y$3) < &1} INTER
                {y | &0 <= y$3} /\
              (!y. y IN moi_sta_open_star c v
                   ==> (y IN complex_boundary c <=> (p y)$3 = &0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FMB_LINK_TO_LAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^N->real^3` (X_CHOOSE_THEN
    `psi':real^3->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_fm3_bd2 (simplicial_link c (v:real^N)) SUBSET
                UNIONS (simplicial_link c v)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fm3_bd2] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link c (v:real^N)) = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FMB_LINK_POLYHEDRON) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_FMB_LAM_YCONE THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS (simplicial_link c (v:real^N))`; `moi_fmb_lam`;
                 `v:real^N`; `vec 0:real^3`; `psi:real^N->real^3`;
                 `psi':real^3->real^N`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `locally_polyhedral (moi_sta_open_star c (v:real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_OPEN_IN_LOCPOLY THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN complex_boundary c` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FM3_CB_VERTEX_BD2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ASSUME `pl_homeomorphism
         (UNIONS {segment[v,x] | x | x IN UNIONS (simplicial_link c (v:real^N))},
          UNIONS {segment[vec 0,y] | y IN moi_fmb_lam})
         (moi_con_conemap (UNIONS (simplicial_link c v)) v (vec 0)
            (psi:real^N->real^3),
          moi_con_conemap moi_fmb_lam (vec 0) v (psi':real^3->real^N))`) THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`moi_con_conemap (UNIONS (simplicial_link c v)) v (vec 0)
       (psi:real^N->real^3)`;
    `moi_con_conemap moi_fmb_lam (vec 0) v (psi':real^3->real^N)`] THEN
  SUBGOAL_THEN
   `IMAGE (moi_con_conemap (UNIONS (simplicial_link c v)) v (vec 0)
             (psi:real^N->real^3))
          (UNIONS {segment[v,x] | x | x IN UNIONS (simplicial_link c (v:real^N))}
           DIFF UNIONS (simplicial_link c v)) =
    {y:real^3 | abs(y$1) + abs(y$2) + abs(y$3) < &1} INTER {y | &0 <= y$3}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`moi_con_conemap (UNIONS (simplicial_link c v)) v (vec 0)
         (psi:real^N->real^3)`;
      `moi_con_conemap moi_fmb_lam (vec 0) v (psi':real^3->real^N)`;
      `UNIONS {segment[v,x] | x | x IN UNIONS (simplicial_link c (v:real^N))}`;
      `UNIONS {segment[vec 0,y] | y IN moi_fmb_lam}:real^3->bool`;
      `UNIONS (simplicial_link c (v:real^N))`] MOI_STA_IMAGE_DIFF) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
        check (fun th -> can (term_match []
          `homeomorphism (A:real^N->bool,B:real^3->bool) (f,g)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; MOI_FMB_IN_UNIONS_SEGMENTS] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`y:real^N`; `&1`] THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (moi_con_conemap (UNIONS (simplicial_link c v)) v (vec 0)
              (psi:real^N->real^3)) (UNIONS (simplicial_link c (v:real^N))) =
      moi_fmb_lam`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (psi:real^N->real^3) (UNIONS (simplicial_link c v))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `(!x:real^N. x IN s ==> (f:real^N->real^3) x = g x)
          ==> IMAGE f s = IMAGE g s`) THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[pl_homeomorphism; homeomorphism]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC
     `UNIONS {segment[v,x] | x | x IN UNIONS (simplicial_link c (v:real^N))}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC
     [`UNIONS {segment[v,x] | x | x IN UNIONS (simplicial_link c (v:real^N))}`;
      `UNIONS {segment[vec 0,y] | y IN moi_fmb_lam}:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
        `UNIONS {segment[vec 0,z] | z | z IN moi_fmb_lam} DIFF moi_fmb_lam = X`)
        (concl th))) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; MOI_FMB_IN_UNIONS_SEGMENTS] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` (X_CHOOSE_THEN `u:real`
    STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  SUBGOAL_THEN `~(u = &1)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((y:real^N) IN UNIONS (simplicial_link c v))` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `v + (z - v):real^N = z`];
    ALL_TAC] THEN
  ASM_CASES_TAC `u = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    MP_TAC(ISPECL [`UNIONS (simplicial_link c (v:real^N))`; `v:real^N`;
                   `vec 0:real^3`; `psi:real^N->real^3`] MOI_CON_CONEMAP_APEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VEC_COMPONENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`UNIONS (simplicial_link c (v:real^N))`; `v:real^N`;
                 `vec 0:real^3`; `psi:real^N->real^3`; `z:real^N`; `u:real`]
    MOI_CON_CONEMAP_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_SUB_RZERO; VECTOR_MUL_COMPONENT] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `z:real^N`; `u:real`]
    MOI_FMB_CB_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[REAL_ENTIRE]);;

let MOI_FMB_CHART = prove
 (`!(c:(real^N->bool)->bool) x.
     combinatorial_manifold_with_boundary 3 c /\ x IN UNIONS c
     ==> ?W (p:real^N->real^3) p' O.
           open_in (subtopology euclidean (UNIONS c)) W /\ x IN W /\
           pl_map_on W p /\ homeomorphism (W,IMAGE p W) (p,p') /\
           open O /\ IMAGE p W = O INTER {y:real^3 | &0 <= y$3} /\
           (!y. y IN W ==> (y IN complex_boundary c <=> (p y)$3 = &0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [combinatorial_manifold_with_boundary]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`]
    MOI_STA_OPEN_STAR_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `moi_sta_open_star c (v:real^N)` THEN
  ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`]
      MOI_FMB_STAR_SPHERE_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN
      `p':real^3->real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`p:real^N->real^3`; `p':real^3->real^N`;
                          `IMAGE (p:real^N->real^3) (moi_sta_open_star c v)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
      ASM_MESON_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((v:real^N) IN complex_boundary c)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_CB_VERTEX_CLASSIFY]; ALL_TAC] THEN
    SUBGOAL_THEN `~((y:real^N) IN complex_boundary c)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FMB_OPEN_STAR_CB]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      can (term_match [] `!y. y IN W ==> &0 < ((p:real^N->real^3) y)$3`)
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`]
      MOI_FMB_STAR_BALL_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN
      `p':real^3->real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`p:real^N->real^3`; `p':real^3->real^N`;
      `{y:real^3 | abs(y$1) + abs(y$2) + abs(y$3) < &1}`] THEN
    ASM_REWRITE_TAC[MOI_FMB_OPEN_OCT]]);;

(* ========================================================================= *)
(* The boundary is a topological invariant (invariance of domain): x in |c|  *)
(* is on complex_boundary c iff no neighbourhood of x in |c| is homeomorphic *)
(* to an open subset of real^3. PL invariance of the class of combinatorial  *)
(* 3-manifolds with boundary and of the boundary, for locally finite         *)
(* complexes in any dimensions, and the theorem                              *)
(* COMBINATORIAL_WB_PL_INVARIANT (Moise 23.6-23.7, RS 2.21).                 *)
(* ========================================================================= *)

let moi_fmb_mint = new_definition
 `moi_fmb_mint (X:real^N->bool) (x:real^N) <=>
    ?U (V:real^3->bool). open_in (subtopology euclidean X) U /\ x IN U /\
                         open V /\ U homeomorphic V`;;

let MOI_FMB_MINT_HOMEO_IMP = prove
 (`!(X:real^M->bool) (Y:real^N->bool) f g x.
        homeomorphism (X,Y) (f,g) /\ x IN X /\ moi_fmb_mint X x
        ==> moi_fmb_mint Y (f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fmb_mint] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `U:real^M->bool` (X_CHOOSE_THEN `V:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^M->real^N) U`; `V:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^M`; `X:real^M->bool`;
                   `Y:real^N->bool`; `U:real^M->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`IMAGE (f:real^M->real^N) U`; `U:real^M->bool`;
                         `V:real^3->bool`] HOMEOMORPHIC_TRANS) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`X:real^M->bool`; `Y:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(U:real^M->bool) SUBSET X` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
      check (fun th -> can (term_match []
        `homeomorphism (X:real^M->bool,Y:real^N->bool) (f,g)`) (concl th))) THEN
    ASM SET_TAC[]]);;

let MOI_FMB_MINT_HOMEO = prove
 (`!(X:real^M->bool) (Y:real^N->bool) f g x.
        homeomorphism (X,Y) (f,g) /\ x IN X
        ==> (moi_fmb_mint X x <=> moi_fmb_mint Y (f x))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MOI_FMB_MINT_HOMEO_IMP THEN
    MAP_EVERY EXISTS_TAC [`X:real^M->bool`; `g:real^N->real^M`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^N->real^M) ((f:real^M->real^N) x) = x`
      (fun th -> ONCE_REWRITE_TAC[SYM th]) THENL
     [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FMB_MINT_HOMEO_IMP THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `f:real^M->real^N`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[homeomorphism; FUN_IN_IMAGE]]]);;

let MOI_FMB_CHART_SHRINK = prove
 (`!(X:real^N->bool) W (p:real^N->real^3) p' O x.
        open_in (subtopology euclidean X) W /\ x IN W /\ pl_map_on W p /\
        homeomorphism (W,IMAGE p W) (p,p') /\ open O /\
        IMAGE p W = O INTER {y:real^3 | &0 <= y$3} /\ &0 < (p x)$3
        ==> ?W'. open_in (subtopology euclidean X) W' /\ x IN W' /\
                 W' SUBSET W /\ pl_map_on W' p /\
                 homeomorphism (W',IMAGE p W') (p,p') /\
                 open (IMAGE p W')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (term_match []
      `homeomorphism (W:real^N->bool,B:real^3->bool) (f,g)`) (concl th))) THEN
  EXISTS_TAC `{y:real^N | y IN W /\ (p:real^N->real^3) y IN {z:real^3 | &0 < z$3}}` THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean W)
      {y:real^N | y IN W /\ (p:real^N->real^3) y IN {z:real^3 | &0 < z$3}}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[MOI_FMB_OPEN_UPPER];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `open_in (subtopology euclidean W)
      {y:real^N | y IN W /\ (p:real^N->real^3) y IN {z:real^3 | &0 < z$3}}` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `Tt:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPECL [`W:real^N->bool`; `p:real^N->real^3`]
      PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `IMAGE (p:real^N->real^3) W`] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[]];
    SUBGOAL_THEN
     `IMAGE (p:real^N->real^3)
        {y:real^N | y IN W /\ (p:real^N->real^3) y IN {z:real^3 | &0 < z$3}} =
      O INTER {z:real^3 | &0 < z$3}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
        X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(p:real^N->real^3) y IN IMAGE p W` MP_TAC THENL
         [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
        REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
        X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(z:real^3) IN IMAGE p (W:real^N->bool)` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
          X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < (z:real^3)$3` THEN
          ASM_REWRITE_TAC[]]];
      MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[MOI_FMB_OPEN_UPPER]]]);;

let MOI_FMB_MINT_CB = prove
 (`!(c:(real^N->bool)->bool) x.
        combinatorial_manifold_with_boundary 3 c /\ x IN UNIONS c
        ==> (x IN complex_boundary c <=> ~moi_fmb_mint (UNIONS c) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `p':real^3->real^N` (X_CHOOSE_THEN `O:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `(x:real^N) IN complex_boundary c <=> ((p:real^N->real^3) x)$3 = &0`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((p:real^N->real^3) x)$3` ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:real^N->real^3) x IN IMAGE p W` MP_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[moi_fmb_mint; homeomorphic; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `V:real^3->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h:real^N->real^3`
        (X_CHOOSE_TAC `h':real^3->real^N`))))) THEN
    SUBGOAL_THEN `(U:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `open_in (subtopology euclidean U) (U INTER W:real^N->bool)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (W:real^N->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `Tt:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `Tt:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open (IMAGE (h:real^N->real^3) (U INTER W))` ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `V:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`h:real^N->real^3`; `h':real^3->real^N`; `U:real^N->bool`;
                     `V:real^3->bool`; `U INTER W:real^N->bool`]
        HOMEOMORPHISM_IMP_OPEN_MAP) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
      check (fun th -> can (term_match []
        `homeomorphism (U:real^N->bool,V:real^3->bool) (f,g)`) (concl th))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
      check (fun th -> can (term_match []
        `homeomorphism (W:real^N->bool,IMAGE (p:real^N->real^3) W) (f,g)`)
        (concl th))) THEN
    SUBGOAL_THEN
     `IMAGE (h':real^3->real^N) (IMAGE h (U INTER W)) = U INTER W`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(p:real^N->real^3) o (h':real^3->real^N)`;
                   `IMAGE (h:real^N->real^3) (U INTER W)`]
      INVARIANCE_OF_DOMAIN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
        REWRITE_TAC[o_THM] THEN
        MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `(h':real^3->real^N) y1 IN U INTER W /\
                      (h':real^3->real^N) y2 IN U INTER W`
        STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(h':real^3->real^N) y1 = h' y2` MP_TAC THENL
         [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o AP_TERM `h:real^N->real^3`) THEN
        SUBGOAL_THEN `(y1:real^3) IN V /\ (y2:real^3) IN V` STRIP_ASSUME_TAC
        THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^N->real^3) x` o
      GEN_REWRITE_RULE I [open_def]) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^N->real^3) x - (e / &2) % basis 3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH `(a - b) - a:real^N = --b`; NORM_NEG;
                  NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^N->real^3) x - (e / &2) % basis 3 IN IMAGE p W`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_SUB_COMPONENT;
                    VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    ASM_CASES_TAC `((p:real^N->real^3) x)$3 = &0` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~moi_fmb_mint (UNIONS c) (x:real^N)` THEN
    REWRITE_TAC[moi_fmb_mint] THEN
    MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `W:real^N->bool`;
                   `p:real^N->real^3`; `p':real^3->real^N`; `O:real^3->bool`;
                   `x:real^N`] MOI_FMB_CHART_SHRINK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `W':real^N->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`W':real^N->bool`; `IMAGE (p:real^N->real^3) W'`] THEN
    ASM_REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`p:real^N->real^3`; `p':real^3->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FMB_CB_SUBSET = prove
 (`!c:(real^N->bool)->bool. complex_boundary c SUBSET UNIONS c`,
  REWRITE_TAC[complex_boundary] THEN SET_TAC[]);;

let MOI_FMB_VERTEX_LINK_HOMEO = prove
 (`!(c:(real^M->bool)->bool) (d:(real^N->bool)->bool) f g w.
     combinatorial_manifold_with_boundary 3 c /\ lf_simplicial_complex d /\
     pl_homeomorphism (UNIONS c,UNIONS d) (f,g) /\ {w} IN d
     ==> pl_sphere 2 (UNIONS (simplicial_link d w)) \/
         pl_ball 2 (UNIONS (simplicial_link d w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism] o
    check (fun th -> can (term_match []
      `pl_homeomorphism (UNIONS (c:(real^M->bool)->bool),
                         UNIONS (d:(real^N->bool)->bool)) (f,g)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (term_match []
      `homeomorphism (UNIONS (c:(real^M->bool)->bool),
                      UNIONS (d:(real^N->bool)->bool)) (f,g)`) (concl th))) THEN
  SUBGOAL_THEN `(w:real^N) IN UNIONS d` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^M) w IN UNIONS c` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `(g:real^N->real^M) w`]
    MOI_FMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^M->bool` (X_CHOOSE_THEN `p:real^M->real^3`
    (X_CHOOSE_THEN `p':real^3->real^M` (X_CHOOSE_THEN `O:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `W SUBSET UNIONS (c:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (UNIONS d)) (IMAGE (f:real^M->real^N) W)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^M`;
                   `UNIONS c:real^M->bool`; `UNIONS d:real^N->bool`;
                   `W:real^M->bool`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN IMAGE (f:real^M->real^N) W` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^N->real^M) w` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^N->real^M) (IMAGE f W) = W` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (IMAGE (f:real^M->real^N) W)
              ((p:real^M->real^3) o (g:real^N->real^M))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `W:real^M->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `UNIONS d:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
      MATCH_MP_TAC MOI_FMB_OPEN_IN_LOCPOLY THEN
      EXISTS_TAC `d:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism (IMAGE (f:real^M->real^N) W,O INTER {y:real^3 | &0 <= y$3})
                  ((p:real^M->real^3) o (g:real^N->real^M),f o (p':real^3->real^M))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
      `IMAGE (p:real^M->real^3) W = O INTER {y:real^3 | &0 <= y$3}`)) THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `W:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`UNIONS d:real^N->bool`; `UNIONS c:real^M->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((p:real^M->real^3) o (g:real^N->real^M)) (IMAGE f W) = IMAGE p W`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((p:real^M->real^3) ((g:real^N->real^M) w))$3`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:real^M->real^3) ((g:real^N->real^M) w) IN IMAGE p W`
    MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `((p:real^M->real^3) ((g:real^N->real^M) w))$3 = &0` THENL
   [DISJ2_TAC THEN MATCH_MP_TAC MOI_FMB_LINK_BALL_CHART THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (f:real^M->real^N) W`; `(p:real^M->real^3) o (g:real^N->real^M)`;
      `(f:real^M->real^N) o (p':real^3->real^M)`; `O:real^3->bool`] THEN
    ASM_REWRITE_TAC[o_THM];
    DISJ1_TAC THEN
    MP_TAC(ISPECL [`UNIONS d:real^N->bool`; `IMAGE (f:real^M->real^N) W`;
                   `(p:real^M->real^3) o (g:real^N->real^M)`;
                   `(f:real^M->real^N) o (p':real^3->real^M)`; `O:real^3->bool`;
                   `w:real^N`] MOI_FMB_CHART_SHRINK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[o_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `W':real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FMB_LINK_SPHERE_CHART THEN
    MAP_EVERY EXISTS_TAC
     [`W':real^N->bool`; `(p:real^M->real^3) o (g:real^N->real^M)`;
      `(f:real^M->real^N) o (p':real^3->real^M)`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FMB_PL_INVARIANT_LF = prove
 (`!(c:(real^M->bool)->bool) (d:(real^N->bool)->bool) f g.
     combinatorial_manifold_with_boundary 3 c /\ lf_simplicial_complex d /\
     pl_homeomorphism (UNIONS c,UNIONS d) (f,g)
     ==> combinatorial_manifold_with_boundary 3 d /\
         IMAGE f (complex_boundary c) = complex_boundary d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (d:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FMB_VERTEX_LINK_HOMEO THEN
    MAP_EVERY EXISTS_TAC [`c:(real^M->bool)->bool`; `f:real^M->real^N`;
                          `g:real^N->real^M`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism] o
    check (fun th -> can (term_match []
      `pl_homeomorphism (UNIONS (c:(real^M->bool)->bool),
                         UNIONS (d:(real^N->bool)->bool)) (f,g)`) (concl th))) THEN
  SUBGOAL_THEN
   `!x:real^M. x IN UNIONS c
               ==> (x IN complex_boundary c <=>
                    (f:real^M->real^N) x IN complex_boundary d)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^N) x IN UNIONS d` ASSUME_TAC THENL
     [ASM_MESON_TAC[homeomorphism; FUN_IN_IMAGE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `(f:real^M->real^N) x`]
      MOI_FMB_MINT_CB) THEN
    MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `x:real^M`] MOI_FMB_MINT_CB) THEN
    MP_TAC(ISPECL [`UNIONS c:real^M->bool`; `UNIONS d:real^N->bool`;
                   `f:real^M->real^N`; `g:real^N->real^M`; `x:real^M`]
      MOI_FMB_MINT_HOMEO) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (term_match []
      `homeomorphism (UNIONS (c:(real^M->bool)->bool),
                      UNIONS (d:(real^N->bool)->bool)) (f,g)`) (concl th))) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN UNIONS c` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FMB_CB_SUBSET; SUBSET]; ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN UNIONS d` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FMB_CB_SUBSET; SUBSET]; ALL_TAC] THEN
    EXISTS_TAC `(g:real^N->real^M) y` THEN
    SUBGOAL_THEN `(g:real^N->real^M) y IN UNIONS c` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* The theorem COMBINATORIAL_WB_PL_INVARIANT (the statement term             *)
(* MOI_FND_COMPLEX_BOUNDARY_PL_INVARIANT): the finiteness hypotheses are not *)
(* needed.                                                                   *)

let COMBINATORIAL_WB_PL_INVARIANT = prove
 (`!(c:(real^M->bool)->bool) (d:(real^N->bool)->bool) f g.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE d /\ lf_simplicial_complex d /\
     pl_homeomorphism (UNIONS c,UNIONS d) (f,g)
     ==> combinatorial_manifold_with_boundary 3 d /\
         IMAGE f (complex_boundary c) = complex_boundary d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `d:(real^N->bool)->bool`;
                 `f:real^M->real^N`; `g:real^N->real^M`]
    MOI_FMB_PL_INVARIANT_LF) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The complex of faces of a 3-simplex is a combinatorial 3-manifold with    *)
(* boundary the relative frontier; the theorems                              *)
(* PL_BALL_TRIANGULATION_BOUNDARY (every finite triangulation of a PL 3-cell *)
(* is combinatorial, with boundary the cell boundary, a PL 2-sphere) and     *)
(* INTERIOR_LINK_RETRIANGULATION.                                            *)
(* ========================================================================= *)

let MOI_FMB_SC_LF = prove
 (`!c:(real^N->bool)->bool. simplicial_complex c ==> lf_simplicial_complex c`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT]);;

let MOI_FMB_FACE_COMPLEX = prove
 (`!n (k:real^N->bool).
        n simplex k
        ==> simplicial_complex {f | f face_of k} /\
            lf_simplicial_complex {f | f face_of k} /\
            UNIONS {f | f face_of k} = k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `simplicial_complex {f:real^N->bool | f face_of k}` ASSUME_TAC
  THENL
   [REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      UNDISCH_TAC `n simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(s:real^N->bool) face_of k` THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `&(CARD(c:real^N->bool)) - &1:int` THEN
      REWRITE_TAC[simplex] THEN EXISTS_TAC `c:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
        EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
        INT_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `s:real^N->bool`] THEN
      STRIP_TAC THEN MATCH_MP_TAC FACE_OF_TRANS THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(s INTER t:real^N->bool) face_of k` ASSUME_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`s INTER t:real^N->bool`; `k:real^N->bool`;
                       `s:real^N->bool`] FACE_OF_FACE);
        MP_TAC(ISPECL [`s INTER t:real^N->bool`; `k:real^N->bool`;
                       `t:real^N->bool`] FACE_OF_FACE)] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FMB_SC_LF] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t:real^N->bool) SUBSET k` MP_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ASM SET_TAC[]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]]);;

let MOI_FMB_FACE_COMPLEX_LINK = prove
 (`!(V:real^N->bool) v.
        ~affine_dependent V /\ v IN V
        ==> UNIONS (simplicial_link {f | f face_of convex hull V} v) =
            convex hull (V DELETE v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent(V DELETE (v:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN convex hull (V DELETE v))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) extreme_point_of convex hull (V DELETE v)`
    MP_TAC THENL
     [MP_TAC(ISPECL [`convex hull (V DELETE (v:real^N))`; `convex hull V:real^N->bool`;
                     `v:real^N`] EXTREME_POINT_OF_FACE) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
        EXISTS_TAC `V DELETE (v:real^N)` THEN REWRITE_TAC[DELETE_SUBSET];
        DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]];
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(s:real^N->bool) face_of convex hull V` THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(c:real^N->bool) SUBSET V DELETE v` ASSUME_TAC THENL
     [UNDISCH_TAC `~((v:real^N) IN s)` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `c:real^N->bool`]
        HULL_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET convex hull (V DELETE v)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    REWRITE_TAC[SUBSET; IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `convex hull (V DELETE (v:real^N))` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex hull (V DELETE (v:real^N)) face_of convex hull V`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `V DELETE (v:real^N)` THEN REWRITE_TAC[DELETE_SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `convex hull V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_REFL THEN REWRITE_TAC[CONVEX_CONVEX_HULL];
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]]]);;

let MOI_FMB_FACE_COMPLEX_CMWB = prove
 (`!k:real^N->bool.
        &3 simplex k ==> combinatorial_manifold_with_boundary 3 {f | f face_of k}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_FMB_FACE_COMPLEX]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_ELIM_THM; FACE_OF_SING] THEN
  UNDISCH_TAC `&3 simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOI_FMB_FACE_COMPLEX_LINK] THEN DISJ2_TAC THEN
  MATCH_MP_TAC PL_BALL_SIMPLEX THEN REWRITE_TAC[simplex] THEN
  EXISTS_TAC `V DELETE (v:real^N)` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE] THEN
  UNDISCH_TAC `&(CARD(V:real^N->bool)):int = &3 + &1` THEN
  SUBGOAL_THEN `1 <= CARD(V:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN INT_ARITH_TAC);;

let MOI_FMB_FACE_COMPLEX_CB = prove
 (`!k:real^N->bool.
        &3 simplex k ==> complex_boundary {f | f face_of k} = relative_frontier k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim (k:real^N->bool) = &3` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ polyhedron k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE;
                  POLYTOPE_IMP_POLYHEDRON];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON] THEN
  REWRITE_TAC[complex_boundary; IN_ELIM_THM; facet_of] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(s:real^N->bool) face_of k` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `CARD {r:real^N->bool | r face_of k /\ aff_dim r = &3 /\ s SUBSET r} = 1`
  (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN
     `{r:real^N->bool | r face_of k /\ aff_dim r = &3 /\ s SUBSET r} = {k}`
    (fun th -> REWRITE_TAC[th; CARD_SING]) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `r:real^N->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_CASES_TAC `r:real^N->bool = k` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `k:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FACE_OF_REFL] THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC);;

let MOI_FMB_PLH_RESTRICT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g s'.
        pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ pl_polyhedron s'
        ==> pl_homeomorphism (s',IMAGE f s') (f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_map_on s' (f:real^M->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[]]]);;

(* The theorem PL_BALL_TRIANGULATION_BOUNDARY (the statement term            *)
(* MOI_FND_PL_BALL_COMPLEX).                                                 *)

let PL_BALL_TRIANGULATION_BOUNDARY = prove
 (`!(d:(real^N->bool)->bool) b.
     FINITE d /\ lf_simplicial_complex d /\ pl_cell_with_boundary 3 (UNIONS d) b
     ==> combinatorial_manifold_with_boundary 3 d /\ complex_boundary d = b /\
         pl_sphere 2 b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`{s:real^N->bool | s face_of k}`; `d:(real^N->bool)->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`]
    MOI_FMB_PL_INVARIANT_LF) THEN
  MP_TAC(ISPECL [`&3:int`; `k:real^N->bool`] MOI_FMB_FACE_COMPLEX) THEN
  ASM_SIMP_TAC[MOI_FMB_FACE_COMPLEX_CMWB; MOI_FMB_FACE_COMPLEX_CB] THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
    `IMAGE (f:real^N->real^N) (relative_frontier k) =
     complex_boundary (d:(real^N->bool)->bool)`)) THEN
  MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
  MAP_EVERY EXISTS_TAC [`relative_frontier k:real^N->bool`; `f:real^N->real^N`;
                        `g:real^N->real^N`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `UNIONS d:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[relative_frontier] THEN
      MATCH_MP_TAC(SET_RULE `closure (k:real^N->bool) = k ==> closure k DIFF s SUBSET k`) THEN
      ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED];
      MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]]]);;

(* The closed star minus the link lies in the open star.                     *)

let MOI_FMB_CSTAR_DIFF_LINK = prove
 (`!t (v:real^N).
        lf_simplicial_complex t
        ==> UNIONS {s | s IN t /\ v IN s} DIFF UNIONS (simplicial_link t v)
            SUBSET moi_sta_open_star t v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM; moi_sta_open_star] THEN
  X_GEN_TAC `w:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s0:real^N->bool`
    STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  CONJ_TAC THENL [EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(v:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `~(?t'. t' IN simplicial_link t v /\ (w:real^N) IN t')` THEN
  REWRITE_TAC[] THEN EXISTS_TAC `s INTER s0:real^N->bool` THEN
  ASM_REWRITE_TAC[IN_INTER; simplicial_link; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`; `s0:real^N->bool`]
    MOI_FM3_LF_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The theorem INTERIOR_LINK_RETRIANGULATION (the statement term             *)
(* MOI_FND_INTERIOR_LINK_RETRIANGULATION).                                   *)

let INTERIOR_LINK_RETRIANGULATION = prove
 (`!(t:(real^N->bool)->bool) t' v w.
     lf_simplicial_complex t /\ lf_simplicial_complex t' /\ UNIONS t' = UNIONS t /\
     {v} IN t /\ pl_sphere 2 (UNIONS (simplicial_link t v)) /\
     {w} IN t' /\
     w IN UNIONS {s | s IN t /\ v IN s} DIFF UNIONS (simplicial_link t v)
     ==> pl_sphere 2 (UNIONS (simplicial_link t' w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N) IN moi_sta_open_star t v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`]
      MOI_FMB_CSTAR_DIFF_LINK) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`]
    MOI_FMB_STAR_SPHERE_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN
    `p':real^3->real^N` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_FMB_LINK_SPHERE_CHART THEN
  MAP_EVERY EXISTS_TAC [`moi_sta_open_star t (v:real^N)`; `p:real^N->real^3`;
                        `p':real^3->real^N`] THEN
  ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN]);;

(* ========================================================================= *)
(* Barycentric subdivision.  The class and the boundary are PL              *)
(* invariants (above); orientations pass to the barycentric subdivision     *)
(* (Moise p.170): a tetrahedron of the subdivision is spanned by the        *)
(* barycentres of a full flag S0 < S1 < S2 < S3 of faces of a tetrahedron   *)
(* S3 of c; its sign is the sign of the permutation sorting its vertices by *)
(* the dimension of their carriers times the sign of the vertex order       *)
(* (w0,w1,w2,w3) of S3 determined by the flag (w_k the vertex of S_k not in *)
(* S_(k-1)).  Changing one level j of the flag swaps w_j and w_(j+1)        *)
(* (j < 3) or changes the top tetrahedron across a common triangle (j = 3). *)
(* This gives COMBINATORIAL_WB_BARYCENTRIC = MOI_FND_BARYCENTRIC_CM_WB.     *)
(* ========================================================================= *)

let moi_fmb_car = new_definition
 `moi_fmb_car (c:(real^N->bool)->bool) (x:real^N) =
    @s. s IN c /\ ~(s = {}) /\ simplex_barycentre s = x`;;

let moi_fmb_lev = new_definition
 `moi_fmb_lev (c:(real^N->bool)->bool) (X:real^N->bool) (k:int) =
    moi_fmb_car c (@x. x IN X /\ aff_dim (moi_fmb_car c x) = k)`;;

let moi_fmb_new = new_definition
 `moi_fmb_new (s:real^N->bool) (t:real^N->bool) =
    @v. v extreme_point_of s /\ ~(v IN t)`;;

let moi_fmb_vx = new_definition
 `moi_fmb_vx (c:(real^N->bool)->bool) (X:real^N->bool) (k:int) =
    moi_fmb_new (moi_fmb_lev c X k)
                (if k = &0 then {} else moi_fmb_lev c X (k - &1))`;;

let moi_fmb_eps = new_definition
 `moi_fmb_eps (a:int) (b:int) (d:int) (e:int) =
    real_sgn((real_of_int b - real_of_int a) * (real_of_int d - real_of_int a) *
             (real_of_int e - real_of_int a) * (real_of_int d - real_of_int b) *
             (real_of_int e - real_of_int b) * (real_of_int e - real_of_int d))`;;

let MOI_FMB_EPS = prove
 (`(!a b d e. moi_fmb_eps b a d e = --(moi_fmb_eps a b d e)) /\
   (!a b d e. moi_fmb_eps a d b e = --(moi_fmb_eps a b d e)) /\
   (!a b d e. moi_fmb_eps a b e d = --(moi_fmb_eps a b d e)) /\
   (!a b d e. ~(a = b) /\ ~(a = d) /\ ~(a = e) /\ ~(b = d) /\ ~(b = e) /\
              ~(d = e)
              ==> moi_fmb_eps a b d e = &1 \/ moi_fmb_eps a b d e = -- &1)`,
  REWRITE_TAC[moi_fmb_eps] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[GSYM REAL_SGN_NEG] THEN AP_TERM_TAC THEN CONV_TAC REAL_RING;
    REWRITE_TAC[GSYM REAL_SGN_NEG] THEN AP_TERM_TAC THEN CONV_TAC REAL_RING;
    REWRITE_TAC[GSYM REAL_SGN_NEG] THEN AP_TERM_TAC THEN CONV_TAC REAL_RING;
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN STRIP_TAC THEN
    MP_TAC(SPEC
     `(real_of_int b - real_of_int a) * (real_of_int d - real_of_int a) *
      (real_of_int e - real_of_int a) * (real_of_int d - real_of_int b) *
      (real_of_int e - real_of_int b) * (real_of_int e - real_of_int d)`
      REAL_SGN_CASES) THEN
    REWRITE_TAC[REAL_SGN_EQ; REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC]);;

let MOI_FMB_CAR_BAR = prove
 (`!c s:real^N->bool.
        lf_simplicial_complex c /\ s IN c /\ ~(s = {})
        ==> moi_fmb_car c (simplex_barycentre s) = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fmb_car] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `t:real^N->bool` THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `simplex_barycentre (s:real^N->bool) IN relative_interior s /\
                simplex_barycentre (t:real^N->bool) IN relative_interior t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[MOI_FM3_LF_SIMPLEX];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THENL
   [EXISTS_TAC `c:(real^N->bool)->bool` THEN
    EXISTS_TAC `simplex_barycentre (t:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    EXISTS_TAC `simplex_barycentre (s:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]);;

let MOI_FMB_NEW_VERTEX = prove
 (`!(s:real^N->bool) t n.
        n simplex s /\ t face_of s /\ aff_dim s = aff_dim t + &1
        ==> moi_fmb_new s t extreme_point_of s /\ ~(moi_fmb_new s t IN t) /\
            (!v. v extreme_point_of s /\ ~(v IN t) ==> v = moi_fmb_new s t) /\
            {x | x extreme_point_of s} =
            moi_fmb_new s t INSERT {x | x extreme_point_of t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `s = convex hull (V:real^N->bool)`)) THEN
  UNDISCH_TAC `(t:real^N->bool) face_of convex hull V` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `t = convex hull (W:real^N->bool)`)) THEN
  SUBGOAL_THEN `~affine_dependent(W:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(V:real^N->bool) /\ FINITE(W:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = CARD(W:real^N->bool) + 1` ASSUME_TAC
  THENL
   [UNDISCH_TAC `aff_dim(convex hull V:real^N->bool) =
                 aff_dim(convex hull W:real^N->bool) + &1` THEN
    REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT;
             ASSUME `~affine_dependent (V:real^N->bool)`;
             ASSUME `~affine_dependent (W:real^N->bool)`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^N. V DIFF W = {u}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_FM3_CARD_EQ_1] THEN
    ASM_SIMP_TAC[FINITE_DIFF; CARD_DIFF] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN V ==> (x IN convex hull W <=> x IN W)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`convex hull W:real^N->bool`; `convex hull V:real^N->bool`;
                     `x:real^N`] EXTREME_POINT_OF_FACE) THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
                   EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `W:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MESON_TAC[HULL_INC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. v extreme_point_of convex hull V /\ ~(v IN convex hull W) <=>
               v = u`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    SUBGOAL_THEN `(u:real^N) IN V /\ ~(u IN W)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `V DIFF W = {u:real^N}` THEN SET_TAC[]; ALL_TAC] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `~((v:real^N) IN W)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `V DIFF W = {u:real^N}` THEN
      UNDISCH_TAC `(v:real^N) IN V` THEN UNDISCH_TAC `~((v:real^N) IN W)` THEN
      SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fmb_new (convex hull V) (convex hull W) = (u:real^N)`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_fmb_new] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
      can (term_match [] `!v:real^N. v extreme_point_of a /\ ~(v IN b) <=> v = u`)
      (concl th))) THEN
    SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
      can (term_match [] `!v:real^N. v extreme_point_of a /\ ~(v IN b) <=> v = u`)
      (concl th))) THEN
    SIMP_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[SET_RULE `!s:real^N->bool. {x | x IN s} = s`] THEN
    UNDISCH_TAC `V DIFF W = {u:real^N}` THEN
    UNDISCH_TAC `(W:real^N->bool) SUBSET V` THEN SET_TAC[]]);;

let MOI_FMB_AFF3_INDEP = prove
 (`!a b d e:real^N.
        aff_dim (convex hull {a,b,d,e}) = &3
        ==> ~affine_dependent {a,b,d,e} /\ CARD {a,b,d,e} = 4`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE {a:real^N,b,d,e}` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD {a:real^N,b,d,e} <= 4` ASSUME_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REPEAT COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `{a:real^N,b,d,e}` AFF_DIM_LE_CARD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `CARD {a:real^N,b,d,e} = 4` ASSUME_TAC THENL
   [UNDISCH_TAC `CARD {a:real^N,b,d,e} <= 4` THEN
    UNDISCH_TAC `&3 <= &(CARD {a:real^N,b,d,e}) - &1:int` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[AFFINE_INDEPENDENT_IFF_CARD] THEN INT_ARITH_TAC);;

let MOI_FMB_BS_TET = prove
 (`!c (a:real^N) b d e.
        lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &3) /\
        convex hull {a,b,d,e} IN barycentric_subdivision c /\
        aff_dim (convex hull {a,b,d,e}) = &3
        ==> ?S0 S1 S2 S3.
              S0 IN c /\ S1 IN c /\ S2 IN c /\ S3 IN c /\
              aff_dim S0 = &0 /\ aff_dim S1 = &1 /\ aff_dim S2 = &2 /\
              aff_dim S3 = &3 /\
              S0 SUBSET S1 /\ S1 SUBSET S2 /\ S2 SUBSET S3 /\
              {a,b,d,e} = {simplex_barycentre S0, simplex_barycentre S1,
                           simplex_barycentre S2, simplex_barycentre S3}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  UNDISCH_TAC `convex hull {a:real^N,b,d,e} IN barycentric_subdivision c` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`]
    MOI_FMB_AFF3_INDEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_AFFINE_INDEPENDENT]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,b,d,e} = IMAGE simplex_barycentre f` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPECL [`{a:real^N,b,d,e}`; `x:real^N`]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPECL [`IMAGE simplex_barycentre (f:(real^N->bool)->bool)`; `x:real^N`]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (f:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (f:(real^N->bool)->bool) = 4` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_CHAIN_BARYCENTRE_INJ];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN f ==> s IN c /\ ~(s = {}) /\ &0 <= aff_dim s /\
                                aff_dim s <= &3`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
    ASM_REWRITE_TAC[AFF_DIM_POS_LE] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t:real^N->bool. s IN f /\ t IN f /\ aff_dim s = aff_dim t ==> s = t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET t \/ t SUBSET s` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE aff_dim (f:(real^N->bool)->bool) = {&0,&1,&2,&3}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
        can (term_match [] `!s:real^N->bool. s IN f ==> s IN c /\ P s`)
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
               NOT_IN_EMPTY] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `CARD (f:(real^N->bool)->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[];
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k:int. k IN {&0,&1,&2,&3}
                        ==> ?s:real^N->bool. s IN f /\ aff_dim s = k`
  MP_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE aff_dim (f:(real^N->bool)->bool) = {&0,&1,&2,&3}`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    let sp k = REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY] (SPEC k th) in
    X_CHOOSE_THEN `S0:real^N->bool` STRIP_ASSUME_TAC (sp `&0:int`) THEN
    X_CHOOSE_THEN `S1:real^N->bool` STRIP_ASSUME_TAC (sp `&1:int`) THEN
    X_CHOOSE_THEN `S2:real^N->bool` STRIP_ASSUME_TAC (sp `&2:int`) THEN
    X_CHOOSE_THEN `S3:real^N->bool` STRIP_ASSUME_TAC (sp `&3:int`)) THEN
  MAP_EVERY EXISTS_TAC [`S0:real^N->bool`; `S1:real^N->bool`;
                        `S2:real^N->bool`; `S3:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s t:real^N->bool. s IN f /\ t IN f /\ aff_dim s < aff_dim t ==> s SUBSET t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET t \/ t SUBSET s` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `f = {S0:real^N->bool,S1,S2,S3}` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY] THEN
    SUBGOAL_THEN `~(S0:real^N->bool = S1) /\ ~(S0 = S2) /\ ~(S0 = S3) /\
                  ~(S1 = S2) /\ ~(S1 = S3) /\ ~(S2 = S3)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `aff_dim(S0:real^N->bool) = &0` THEN
      UNDISCH_TAC `aff_dim(S1:real^N->bool) = &1` THEN
      UNDISCH_TAC `aff_dim(S2:real^N->bool) = &2` THEN
      UNDISCH_TAC `aff_dim(S3:real^N->bool) = &3` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
    REWRITE_TAC[IMAGE_CLAUSES]]);;

let moi_fmb_flag = new_definition
 `moi_fmb_flag (c:(real^N->bool)->bool) S0 S1 S2 S3 <=>
    S0 IN c /\ S1 IN c /\ S2 IN c /\ S3 IN c /\
    aff_dim S0 = &0 /\ aff_dim S1 = &1 /\ aff_dim S2 = &2 /\ aff_dim S3 = &3 /\
    S0 SUBSET S1 /\ S1 SUBSET S2 /\ S2 SUBSET S3`;;

let MOI_FMB_FACE_STEP = prove
 (`!c (t:real^N->bool) s.
        lf_simplicial_complex c /\ s IN c /\ (t = {} \/ t IN c) /\ t SUBSET s /\
        aff_dim s = aff_dim t + &1
        ==> moi_fmb_new s t extreme_point_of s /\ ~(moi_fmb_new s t IN t) /\
            (!v. v extreme_point_of s /\ ~(v IN t) ==> v = moi_fmb_new s t) /\
            {x | x extreme_point_of s} =
            moi_fmb_new s t INSERT {x | x extreme_point_of t}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "tc") STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC MOI_FMB_NEW_VERTEX THEN
  EXISTS_TAC `aff_dim(s:real^N->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SIMPLEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  USE_THEN "tc" DISJ_CASES_TAC THENL
   [ASM_REWRITE_TAC[EMPTY_FACE_OF];
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_FMB_SIMPLEX_EXTREME = prove
 (`!c s:real^N->bool.
        lf_simplicial_complex c /\ s IN c
        ==> s = convex hull {x | x extreme_point_of s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FM3_LF_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]);;

let MOI_FMB_FLAG_VERTS = prove
 (`!c S0 S1 S2 (S3:real^N->bool).
        lf_simplicial_complex c /\ moi_fmb_flag c S0 S1 S2 S3
        ==> {x | x extreme_point_of S3} =
              {moi_fmb_new S0 {}, moi_fmb_new S1 S0, moi_fmb_new S2 S1,
               moi_fmb_new S3 S2} /\
            S3 = convex hull {moi_fmb_new S0 {}, moi_fmb_new S1 S0,
                              moi_fmb_new S2 S1, moi_fmb_new S3 S2} /\
            ~(moi_fmb_new S3 S2 IN S2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fmb_flag] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{}:real^N->bool`; `S0:real^N->bool`]
    MOI_FMB_FACE_STEP) THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET; AFF_DIM_EMPTY] THEN
  ANTS_TAC THENL [INT_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`]
    MOI_FMB_FACE_STEP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [INT_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S1:real^N->bool`; `S2:real^N->bool`]
    MOI_FMB_FACE_STEP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [INT_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S2:real^N->bool`; `S3:real^N->bool`]
    MOI_FMB_FACE_STEP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [INT_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `{x | x extreme_point_of S3} =
    {moi_fmb_new S0 {}, moi_fmb_new S1 S0, moi_fmb_new S2 S1,
     moi_fmb_new (S3:real^N->bool) S2}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; NOT_IN_EMPTY;
                EXTREME_POINT_OF_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_FMB_SIMPLEX_EXTREME THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_FMB_SWAP_HALF = prove
 (`!c (T0:real^N->bool) A A' T2.
        lf_simplicial_complex c /\ (T0 = {} \/ T0 IN c) /\
        A IN c /\ A' IN c /\ T2 IN c /\
        T0 SUBSET A /\ T0 SUBSET A' /\ A SUBSET T2 /\ A' SUBSET T2 /\
        aff_dim A = aff_dim T0 + &1 /\ aff_dim A' = aff_dim T0 + &1 /\
        aff_dim T2 = aff_dim A + &1 /\ ~(A = A')
        ==> moi_fmb_new A' T0 = moi_fmb_new T2 A`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "t0")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `T0:real^N->bool`; `A:real^N->bool`]
    MOI_FMB_FACE_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "vA")))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `T0:real^N->bool`; `A':real^N->bool`]
    MOI_FMB_FACE_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "eA'") (CONJUNCTS_THEN2
    (LABEL_TAC "nA'") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "vA'")))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `A:real^N->bool`; `T2:real^N->bool`]
    MOI_FMB_FACE_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "uT") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `(A:real^N->bool) face_of T2 /\ (A':real^N->bool) face_of T2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_fmb_new A T0 = moi_fmb_new (A':real^N->bool) T0)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(A:real^N->bool = A')` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `A:real^N->bool`]
      MOI_FMB_SIMPLEX_EXTREME) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `A':real^N->bool`]
      MOI_FMB_SIMPLEX_EXTREME) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
      ONCE_REWRITE_TAC[th1; th2])) THEN
    USE_THEN "vA" SUBST1_TAC THEN USE_THEN "vA'" SUBST1_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "uT" MATCH_MP_TAC THEN
  SUBGOAL_THEN `moi_fmb_new (A':real^N->bool) T0 extreme_point_of T2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A':real^N->bool`; `T2:real^N->bool`;
                   `moi_fmb_new (A':real^N->bool) T0`] EXTREME_POINT_OF_FACE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`A:real^N->bool`; `T2:real^N->bool`;
                 `moi_fmb_new (A':real^N->bool) T0`] EXTREME_POINT_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `moi_fmb_new (A':real^N->bool) T0 IN {x | x extreme_point_of A}`
  MP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  USE_THEN "vA" SUBST1_TAC THEN REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[];
    USE_THEN "nA'" MP_TAC THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[extreme_point_of]]);;

let MOI_FMB_FLAG_SWAP = prove
 (`!c (T0:real^N->bool) A A' T2.
        lf_simplicial_complex c /\ (T0 = {} \/ T0 IN c) /\
        A IN c /\ A' IN c /\ T2 IN c /\
        T0 SUBSET A /\ T0 SUBSET A' /\ A SUBSET T2 /\ A' SUBSET T2 /\
        aff_dim A = aff_dim T0 + &1 /\ aff_dim A' = aff_dim T0 + &1 /\
        aff_dim T2 = aff_dim A + &1 /\ ~(A = A')
        ==> moi_fmb_new A T0 = moi_fmb_new T2 A' /\
            moi_fmb_new A' T0 = moi_fmb_new T2 A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_FMB_SWAP_HALF THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_FMB_FLAG_VX = prove
 (`!c S0 S1 S2 (S3:real^N->bool).
        lf_simplicial_complex c /\ moi_fmb_flag c S0 S1 S2 S3
        ==> moi_fmb_car c (simplex_barycentre S0) = S0 /\
            moi_fmb_car c (simplex_barycentre S1) = S1 /\
            moi_fmb_car c (simplex_barycentre S2) = S2 /\
            moi_fmb_car c (simplex_barycentre S3) = S3 /\
            moi_fmb_vx c {simplex_barycentre S0, simplex_barycentre S1,
                          simplex_barycentre S2, simplex_barycentre S3} (&0) =
            moi_fmb_new S0 {} /\
            moi_fmb_vx c {simplex_barycentre S0, simplex_barycentre S1,
                          simplex_barycentre S2, simplex_barycentre S3} (&1) =
            moi_fmb_new S1 S0 /\
            moi_fmb_vx c {simplex_barycentre S0, simplex_barycentre S1,
                          simplex_barycentre S2, simplex_barycentre S3} (&2) =
            moi_fmb_new S2 S1 /\
            moi_fmb_vx c {simplex_barycentre S0, simplex_barycentre S1,
                          simplex_barycentre S2, simplex_barycentre S3} (&3) =
            moi_fmb_new S3 S2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fmb_flag] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_fmb_car c (simplex_barycentre S0) = S0 /\
    moi_fmb_car c (simplex_barycentre S1) = S1 /\
    moi_fmb_car c (simplex_barycentre S2) = S2 /\
    moi_fmb_car c (simplex_barycentre (S3:real^N->bool)) = S3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FMB_CAR_BAR THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!k:int y. y IN {simplex_barycentre S0, simplex_barycentre S1,
                    simplex_barycentre S2,
                    simplex_barycentre (S3:real^N->bool)} /\
              aff_dim (moi_fmb_car c y) = k
              ==> (k = &0 /\ y = simplex_barycentre S0) \/
                  (k = &1 /\ y = simplex_barycentre S1) \/
                  (k = &2 /\ y = simplex_barycentre S2) \/
                  (k = &3 /\ y = simplex_barycentre S3)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "y")) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `k:int`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. (k = &0 \/ k = &1 \/ k = &2 \/ k = &3)
        ==> moi_fmb_lev c {simplex_barycentre S0, simplex_barycentre S1,
                           simplex_barycentre S2,
                           simplex_barycentre (S3:real^N->bool)} k =
            (if k = &0 then S0 else if k = &1 then S1 else
             if k = &2 then S2 else S3)`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_fmb_lev] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `moi_fmb_car c
      (if (k:int) = &0 then simplex_barycentre S0 else
       if k = &1 then simplex_barycentre S1 else
       if k = &2 then simplex_barycentre S2 else
       simplex_barycentre (S3:real^N->bool))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
      X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
       [REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`k:int`; `y:real^N`] o
          check (fun th -> is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
          is_disj (concl th))) THEN
        CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN
        FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
          is_disj (concl th))) THEN
        CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[IN_INSERT]];
      FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
        is_disj (concl th))) THEN
      CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&0:int` th) THEN MP_TAC(SPEC `&1:int` th) THEN
    MP_TAC(SPEC `&2:int` th) THEN MP_TAC(SPEC `&3:int` th)) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[moi_fmb_vx] THEN
  CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let MOI_FMB_CARD4_DISTINCT = prove
 (`!a b d e:A. CARD {a,b,d,e} = 4
               ==> ~(a = b) /\ ~(a = d) /\ ~(a = e) /\ ~(b = d) /\ ~(b = e) /\
                   ~(d = e)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]);;

let MOI_FMB_LEVEL_TRANSFER = prove
 (`!c S0' S1' S2' S3' (Tq:real^N->bool).
        lf_simplicial_complex c /\ moi_fmb_flag c S0' S1' S2' S3' /\
        Tq IN c /\ ~(Tq = {}) /\
        simplex_barycentre Tq IN
          {simplex_barycentre S0', simplex_barycentre S1',
           simplex_barycentre S2', simplex_barycentre S3'}
        ==> (aff_dim Tq = &0 ==> S0' = Tq) /\ (aff_dim Tq = &1 ==> S1' = Tq) /\
            (aff_dim Tq = &2 ==> S2' = Tq) /\ (aff_dim Tq = &3 ==> S3' = Tq)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                 `S2':real^N->bool`; `S3':real^N->bool`] MOI_FMB_FLAG_VX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `Tq:real^N->bool`] MOI_FMB_CAR_BAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `simplex_barycentre (Tq:real^N->bool) IN
    {simplex_barycentre S0', simplex_barycentre S1',
     simplex_barycentre S2', simplex_barycentre S3'}` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  UNDISCH_TAC `moi_fmb_flag c S0' S1' S2' (S3':real^N->bool)` THEN
  REWRITE_TAC[moi_fmb_flag] THEN STRIP_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (fun th ->
    SUBGOAL_THEN `Tq:real^N->bool = moi_fmb_car c (simplex_barycentre Tq)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[th]])) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

(* Matching two flags whose barycentre tetrahedra share a triangle: the     *)
(* flags agree except at the level of the vertex opposite the triangle.     *)

let MOI_FMB_FLAG_MATCH = prove
 (`!c S0 S1 S2 S3 S0' S1' S2' S3' (a:real^N) b d e e'.
        lf_simplicial_complex c /\ moi_fmb_flag c S0 S1 S2 S3 /\
        moi_fmb_flag c S0' S1' S2' S3' /\
        {a,b,d,e} = {simplex_barycentre S0, simplex_barycentre S1,
                     simplex_barycentre S2, simplex_barycentre S3} /\
        {a,b,d,e'} = {simplex_barycentre S0', simplex_barycentre S1',
                      simplex_barycentre S2', simplex_barycentre S3'} /\
        ~(e = a) /\ ~(e = b) /\ ~(e = d) /\
        ~(e' = a) /\ ~(e' = b) /\ ~(e' = d) /\ ~(e = e')
        ==> (e = simplex_barycentre S0 /\ e' = simplex_barycentre S0' /\
             S1' = S1 /\ S2' = S2 /\ S3' = S3 /\ ~(S0' = S0)) \/
            (e = simplex_barycentre S1 /\ e' = simplex_barycentre S1' /\
             S0' = S0 /\ S2' = S2 /\ S3' = S3 /\ ~(S1' = S1)) \/
            (e = simplex_barycentre S2 /\ e' = simplex_barycentre S2' /\
             S0' = S0 /\ S1' = S1 /\ S3' = S3 /\ ~(S2' = S2)) \/
            (e = simplex_barycentre S3 /\ e' = simplex_barycentre S3' /\
             S0' = S0 /\ S1' = S1 /\ S2' = S2 /\ ~(S3' = S3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                 `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_FLAG_VX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fmb_flag] o
    check (fun th -> concl th = `moi_fmb_flag c S0 S1 S2 (S3:real^N->bool)`)) THEN
  SUBGOAL_THEN `~(S0:real^N->bool = {}) /\ ~(S1:real^N->bool = {}) /\
                ~(S2:real^N->bool = {}) /\ ~(S3:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim(S0:real^N->bool) = &0` THEN
    UNDISCH_TAC `aff_dim(S1:real^N->bool) = &1` THEN
    UNDISCH_TAC `aff_dim(S2:real^N->bool) = &2` THEN
    UNDISCH_TAC `aff_dim(S3:real^N->bool) = &3` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN {a,b,d,e} <=>
               x IN {simplex_barycentre S0, simplex_barycentre S1,
                     simplex_barycentre S2, simplex_barycentre S3}`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN {a,b,d,e'} <=>
               x IN {simplex_barycentre S0', simplex_barycentre S1',
                     simplex_barycentre S2', simplex_barycentre S3'}`
  (LABEL_TAC "X'") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S0 = (simplex_barycentre S1:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S0 = (simplex_barycentre S2:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S0 = (simplex_barycentre S3:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S1 = (simplex_barycentre S0:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S1 = (simplex_barycentre S2:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S1 = (simplex_barycentre S3:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S2 = (simplex_barycentre S0:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S2 = (simplex_barycentre S1:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S2 = (simplex_barycentre S3:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S3 = (simplex_barycentre S0:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S3 = (simplex_barycentre S1:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre S3 = (simplex_barycentre S2:real^N))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_fmb_car (c:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e = simplex_barycentre S0 \/ e = simplex_barycentre S1 \/ e = simplex_barycentre S2 \/ e = (simplex_barycentre S3:real^N)`
  MP_TAC THENL
   [MP_TAC(SPEC `e:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `S1' = (S1:real^N->bool) /\ S2' = (S2:real^N->bool) /\ S3' = (S3:real^N->bool)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S1:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S1:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S1 = (simplex_barycentre S0:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S2:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S2:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S2 = (simplex_barycentre S0:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S3:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S3:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S3 = (simplex_barycentre S0:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(S0' = (S0:real^N->bool))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(SPEC `simplex_barycentre S0':real^N` (ASSUME `!x:real^N. x IN {a,b,d,e'} <=> x IN {simplex_barycentre S0', simplex_barycentre S1', simplex_barycentre S2', simplex_barycentre S3'}`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `e = simplex_barycentre S0:real^N`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `e' = simplex_barycentre S0':real^N` ASSUME_TAC THENL
     [MP_TAC(SPEC `e':real^N` (ASSUME `!x:real^N. x IN {a,b,d,e'} <=> x IN {simplex_barycentre S0', simplex_barycentre S1', simplex_barycentre S2', simplex_barycentre S3'}`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `simplex_barycentre S1:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S1 = (simplex_barycentre S0:real^N))`) THEN
      MP_TAC(SPEC `simplex_barycentre S2:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S2 = (simplex_barycentre S0:real^N))`) THEN
      MP_TAC(SPEC `simplex_barycentre S3:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S3 = (simplex_barycentre S0:real^N))`) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `e = simplex_barycentre S0:real^N`)) THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
        [`~(e':real^N = a)`; `~(e':real^N = b)`; `~(e':real^N = d)`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `S0' = (S0:real^N->bool) /\ S2' = (S2:real^N->bool) /\ S3' = (S3:real^N->bool)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S0:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S0:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S0 = (simplex_barycentre S1:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S2:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S2:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S2 = (simplex_barycentre S1:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S3:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S3:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S3 = (simplex_barycentre S1:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(S1' = (S1:real^N->bool))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(SPEC `simplex_barycentre S1':real^N` (ASSUME `!x:real^N. x IN {a,b,d,e'} <=> x IN {simplex_barycentre S0', simplex_barycentre S1', simplex_barycentre S2', simplex_barycentre S3'}`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `e = simplex_barycentre S1:real^N`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `e' = simplex_barycentre S1':real^N` ASSUME_TAC THENL
     [MP_TAC(SPEC `e':real^N` (ASSUME `!x:real^N. x IN {a,b,d,e'} <=> x IN {simplex_barycentre S0', simplex_barycentre S1', simplex_barycentre S2', simplex_barycentre S3'}`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `simplex_barycentre S0:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S0 = (simplex_barycentre S1:real^N))`) THEN
      MP_TAC(SPEC `simplex_barycentre S2:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S2 = (simplex_barycentre S1:real^N))`) THEN
      MP_TAC(SPEC `simplex_barycentre S3:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S3 = (simplex_barycentre S1:real^N))`) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `e = simplex_barycentre S1:real^N`)) THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
        [`~(e':real^N = a)`; `~(e':real^N = b)`; `~(e':real^N = d)`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `S0' = (S0:real^N->bool) /\ S1' = (S1:real^N->bool) /\ S3' = (S3:real^N->bool)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S0:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S0:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S0 = (simplex_barycentre S2:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S1:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S1:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S1 = (simplex_barycentre S2:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S3:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S3:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S3 = (simplex_barycentre S2:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(S2' = (S2:real^N->bool))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(SPEC `simplex_barycentre S2':real^N` (ASSUME `!x:real^N. x IN {a,b,d,e'} <=> x IN {simplex_barycentre S0', simplex_barycentre S1', simplex_barycentre S2', simplex_barycentre S3'}`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `e = simplex_barycentre S2:real^N`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `e' = simplex_barycentre S2':real^N` ASSUME_TAC THENL
     [MP_TAC(SPEC `e':real^N` (ASSUME `!x:real^N. x IN {a,b,d,e'} <=> x IN {simplex_barycentre S0', simplex_barycentre S1', simplex_barycentre S2', simplex_barycentre S3'}`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `simplex_barycentre S0:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S0 = (simplex_barycentre S2:real^N))`) THEN
      MP_TAC(SPEC `simplex_barycentre S1:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S1 = (simplex_barycentre S2:real^N))`) THEN
      MP_TAC(SPEC `simplex_barycentre S3:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S3 = (simplex_barycentre S2:real^N))`) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `e = simplex_barycentre S2:real^N`)) THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
        [`~(e':real^N = a)`; `~(e':real^N = b)`; `~(e':real^N = d)`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN `S0' = (S0:real^N->bool) /\ S1' = (S1:real^N->bool) /\ S2' = (S2:real^N->bool)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S0:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S0:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S0 = (simplex_barycentre S3:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S1:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S1:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S1 = (simplex_barycentre S3:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                       `S2':real^N->bool`; `S3':real^N->bool`; `S2:real^N->bool`]
          MOI_FMB_LEVEL_TRANSFER) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [USE_THEN "X'" (fun th -> REWRITE_TAC[GSYM th]) THEN
          MP_TAC(SPEC `simplex_barycentre S2:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
          REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          MP_TAC(ASSUME `~(simplex_barycentre S2 = (simplex_barycentre S3:real^N))`) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[];
          CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(S3' = (S3:real^N->bool))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(SPEC `simplex_barycentre S3':real^N` (ASSUME `!x:real^N. x IN {a,b,d,e'} <=> x IN {simplex_barycentre S0', simplex_barycentre S1', simplex_barycentre S2', simplex_barycentre S3'}`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `e = simplex_barycentre S3:real^N`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `e' = simplex_barycentre S3':real^N` ASSUME_TAC THENL
     [MP_TAC(SPEC `e':real^N` (ASSUME `!x:real^N. x IN {a,b,d,e'} <=> x IN {simplex_barycentre S0', simplex_barycentre S1', simplex_barycentre S2', simplex_barycentre S3'}`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `simplex_barycentre S0:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S0 = (simplex_barycentre S3:real^N))`) THEN
      MP_TAC(SPEC `simplex_barycentre S1:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S1 = (simplex_barycentre S3:real^N))`) THEN
      MP_TAC(SPEC `simplex_barycentre S2:real^N` (ASSUME `!x:real^N. x IN {a,b,d,e} <=> x IN {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2, simplex_barycentre S3}`)) THEN
      MP_TAC(ASSUME `~(simplex_barycentre S2 = (simplex_barycentre S3:real^N))`) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `e = simplex_barycentre S3:real^N`)) THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
        [`~(e':real^N = a)`; `~(e':real^N = b)`; `~(e':real^N = d)`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FMB_DELTA_INJ = prove
 (`!c S0 S1 S2 (S3:real^N->bool).
        lf_simplicial_complex c /\ moi_fmb_flag c S0 S1 S2 S3
        ==> !x y. x IN {simplex_barycentre S0, simplex_barycentre S1,
                        simplex_barycentre S2, simplex_barycentre S3} /\
                  y IN {simplex_barycentre S0, simplex_barycentre S1,
                        simplex_barycentre S2, simplex_barycentre S3} /\
                  aff_dim (moi_fmb_car c x) = aff_dim (moi_fmb_car c y)
                  ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                 `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_FLAG_VX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fmb_flag] o
    check (fun th -> concl th = `moi_fmb_flag c S0 S1 S2 (S3:real^N->bool)`)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) &&
    (fst(dest_var(lhs(concl th))) = "x" || fst(dest_var(lhs(concl th))) = "y")))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (term_match [] `aff_dim (moi_fmb_car c (u:real^N)) = aff_dim (moi_fmb_car c v)`)
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let MOI_FMB_INSERT4 = prove
 (`!a b d e:A. {b,a,d,e} = {a,b,d,e} /\ {a,d,b,e} = {a,b,d,e} /\
               {a,b,e,d} = {a,b,d,e}`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN SET_TAC[]);;

(* Orientations pass to the barycentric subdivision.                         *)

let MOI_FMB_BARY_ORIENTABLE = prove
 (`!c:(real^N->bool)->bool.
        lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &3) /\
        orientable_complex c
        ==> orientable_complex (barycentric_subdivision c)`,
  GEN_TAC THEN REWRITE_TAC[orientable_complex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `sg:real^N->real^N->real^N->real^N->real`
      (CONJUNCTS_THEN2 (LABEL_TAC "O1") (LABEL_TAC "O2"))))) THEN
  EXISTS_TAC `\a b d e:real^N.
     moi_fmb_eps (aff_dim (moi_fmb_car c a)) (aff_dim (moi_fmb_car c b))
                 (aff_dim (moi_fmb_car c d)) (aff_dim (moi_fmb_car c e)) *
     sg (moi_fmb_vx c {a,b,d,e} (&0)) (moi_fmb_vx c {a,b,d,e} (&1))
        (moi_fmb_vx c {a,b,d,e} (&2)) (moi_fmb_vx c {a,b,d,e} (&3))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`]
      MOI_FMB_INSERT4) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
    MAP_EVERY (fun th -> MP_TAC(SPECL
      [`aff_dim (moi_fmb_car c (a:real^N))`; `aff_dim (moi_fmb_car c (b:real^N))`;
       `aff_dim (moi_fmb_car c (d:real^N))`; `aff_dim (moi_fmb_car c (e:real^N))`] th))
      (rev(butlast (CONJUNCTS MOI_FMB_EPS))) THEN
    REPEAT(DISCH_THEN(fun th -> ASSUME_TAC th)) THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REAL_RING `x' = --x ==> x' * s = --(x * s)`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC(REAL_RING `x' = --x ==> x' * s = --(x * s)`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC(REAL_RING `x' = --x ==> x' * s = --(x * s)`) THEN
      FIRST_ASSUM ACCEPT_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `d:real^N`;
                   `e:real^N`] MOI_FMB_BS_TET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `S0:real^N->bool` (X_CHOOSE_THEN `S1:real^N->bool`
      (X_CHOOSE_THEN `S2:real^N->bool` (X_CHOOSE_THEN `S3:real^N->bool`
        STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `moi_fmb_flag c S0 S1 S2 (S3:real^N->bool)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_fmb_flag]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`]
      MOI_FMB_AFF3_INDEP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`]
      MOI_FMB_CARD4_DISTINCT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                   `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_DELTA_INJ) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SYM(ASSUME `{a:real^N,b,d,e} =
      {simplex_barycentre S0, simplex_barycentre S1, simplex_barycentre S2,
       simplex_barycentre S3}`)] THEN
    DISCH_THEN(LABEL_TAC "inj") THEN
    SUBGOAL_THEN
     `moi_fmb_eps (aff_dim (moi_fmb_car c (a:real^N))) (aff_dim (moi_fmb_car c b))
                  (aff_dim (moi_fmb_car c d)) (aff_dim (moi_fmb_car c e)) = &1 \/
      moi_fmb_eps (aff_dim (moi_fmb_car c (a:real^N))) (aff_dim (moi_fmb_car c b))
                  (aff_dim (moi_fmb_car c d)) (aff_dim (moi_fmb_car c e)) = -- &1`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(last (CONJUNCTS MOI_FMB_EPS)) THEN
      REPEAT CONJ_TAC THEN DISCH_TAC THENL
       [USE_THEN "inj" (MP_TAC o SPECL [`a:real^N`; `b:real^N`]);
        USE_THEN "inj" (MP_TAC o SPECL [`a:real^N`; `d:real^N`]);
        USE_THEN "inj" (MP_TAC o SPECL [`a:real^N`; `e:real^N`]);
        USE_THEN "inj" (MP_TAC o SPECL [`b:real^N`; `d:real^N`]);
        USE_THEN "inj" (MP_TAC o SPECL [`b:real^N`; `e:real^N`]);
        USE_THEN "inj" (MP_TAC o SPECL [`d:real^N`; `e:real^N`])] THEN
      REWRITE_TAC[IN_INSERT] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                   `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_FLAG_VX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "O1" (MP_TAC o SPECL
        [`moi_fmb_new S0 {}:real^N`; `moi_fmb_new (S1:real^N->bool) S0`;
         `moi_fmb_new (S2:real^N->bool) S1`; `moi_fmb_new (S3:real^N->bool) S2`]) THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                       `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_FLAG_VERTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[SYM(CONJUNCT1(CONJUNCT2 th))]) THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj (concl th) &&
      can (term_match [] `moi_fmb_eps p q r s = &1 \/ moi_fmb_eps p q r s = -- &1`)
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `e':real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `d:real^N`;
                 `e:real^N`] MOI_FMB_BS_TET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S0:real^N->bool` (X_CHOOSE_THEN `S1:real^N->bool`
    (X_CHOOSE_THEN `S2:real^N->bool` (X_CHOOSE_THEN `S3:real^N->bool`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `d:real^N`;
                 `e':real^N`] MOI_FMB_BS_TET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S0':real^N->bool` (X_CHOOSE_THEN `S1':real^N->bool`
    (X_CHOOSE_THEN `S2':real^N->bool` (X_CHOOSE_THEN `S3':real^N->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `moi_fmb_flag c S0 S1 S2 (S3:real^N->bool) /\
                moi_fmb_flag c S0' S1' S2' (S3':real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[moi_fmb_flag]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`]
    MOI_FMB_AFF3_INDEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e':real^N`]
    MOI_FMB_AFF3_INDEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`]
    MOI_FMB_CARD4_DISTINCT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e':real^N`]
    MOI_FMB_CARD4_DISTINCT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                 `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_FLAG_VX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0':real^N->bool`; `S1':real^N->bool`;
                 `S2':real^N->bool`; `S3':real^N->bool`] MOI_FMB_FLAG_VX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                 `S2:real^N->bool`; `S3:real^N->bool`; `S0':real^N->bool`;
                 `S1':real^N->bool`; `S2':real^N->bool`; `S3':real^N->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `e':real^N`]
    MOI_FMB_FLAG_MATCH) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      is_var (lhs (concl th)) && is_var (rhs (concl th)) &&
      type_of (lhs (concl th)) = `:real^N->bool`))) THEN
    SUBGOAL_THEN `aff_dim (moi_fmb_car c (e':real^N)) = aff_dim (moi_fmb_car c e)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_RING `y' = --y ==> x * y' = --(x * y)`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{}:real^N->bool`; `S0:real^N->bool`; `S0':real^N->bool`; `S1:real^N->bool`]
      MOI_FMB_FLAG_SWAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET; AFF_DIM_EMPTY] THEN
      CONV_TAC INT_REDUCE_CONV;
      DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "O1" (MP_TAC o SPECL
        [`moi_fmb_new S0 {}:real^N`; `moi_fmb_new (S1:real^N->bool) S0`;
         `moi_fmb_new (S2:real^N->bool) S1`; `moi_fmb_new (S3:real^N->bool) S2`]) THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                       `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_FLAG_VERTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[SYM(CONJUNCT1(CONJUNCT2 th))]) THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      is_var (lhs (concl th)) && is_var (rhs (concl th)) &&
      type_of (lhs (concl th)) = `:real^N->bool`))) THEN
    SUBGOAL_THEN `aff_dim (moi_fmb_car c (e':real^N)) = aff_dim (moi_fmb_car c e)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_RING `y' = --y ==> x * y' = --(x * y)`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`; `S1':real^N->bool`; `S2:real^N->bool`]
      MOI_FMB_FLAG_SWAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET; AFF_DIM_EMPTY] THEN
      CONV_TAC INT_REDUCE_CONV;
      DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "O1" (MP_TAC o SPECL
        [`moi_fmb_new S0 {}:real^N`; `moi_fmb_new (S1:real^N->bool) S0`;
         `moi_fmb_new (S2:real^N->bool) S1`; `moi_fmb_new (S3:real^N->bool) S2`]) THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                       `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_FLAG_VERTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[SYM(CONJUNCT1(CONJUNCT2 th))]) THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      is_var (lhs (concl th)) && is_var (rhs (concl th)) &&
      type_of (lhs (concl th)) = `:real^N->bool`))) THEN
    SUBGOAL_THEN `aff_dim (moi_fmb_car c (e':real^N)) = aff_dim (moi_fmb_car c e)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_RING `y' = --y ==> x * y' = --(x * y)`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S1:real^N->bool`; `S2:real^N->bool`; `S2':real^N->bool`; `S3:real^N->bool`]
      MOI_FMB_FLAG_SWAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET; AFF_DIM_EMPTY] THEN
      CONV_TAC INT_REDUCE_CONV;
      DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "O1" (MP_TAC o SPECL
        [`moi_fmb_new S0 {}:real^N`; `moi_fmb_new (S1:real^N->bool) S0`;
         `moi_fmb_new (S2:real^N->bool) S1`; `moi_fmb_new (S3:real^N->bool) S2`]) THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                       `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_FLAG_VERTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[SYM(CONJUNCT1(CONJUNCT2 th))]) THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      is_var (lhs (concl th)) && is_var (rhs (concl th)) &&
      type_of (lhs (concl th)) = `:real^N->bool`))) THEN
    SUBGOAL_THEN `aff_dim (moi_fmb_car c (e':real^N)) = aff_dim (moi_fmb_car c e)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_RING `y' = --y ==> x * y' = --(x * y)`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                   `S2:real^N->bool`; `S3:real^N->bool`] MOI_FMB_FLAG_VERTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `S0:real^N->bool`; `S1:real^N->bool`;
                   `S2:real^N->bool`; `S3':real^N->bool`] MOI_FMB_FLAG_VERTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "O2" MATCH_MP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `S3:real^N->bool`)) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `S3':real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(S3' = (S3:real^N->bool))` THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `S3:real^N->bool`)) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `S3':real^N->bool`)) THEN
    ASM_REWRITE_TAC[]]);;

(* The theorem COMBINATORIAL_WB_BARYCENTRIC (the statement term              *)
(* MOI_FND_BARYCENTRIC_CM_WB).                                               *)

let COMBINATORIAL_WB_BARYCENTRIC = prove
 (`!c:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 c
     ==> combinatorial_manifold_with_boundary 3 (barycentric_subdivision c) /\
         complex_boundary (barycentric_subdivision c) = complex_boundary c /\
         (orientable_complex c ==> orientable_complex (barycentric_subdivision c))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (UNIONS c,UNIONS c) ((\x:real^N. x),(\x:real^N. x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
    REWRITE_TAC[HOMEOMORPHISM_ID; GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `barycentric_subdivision c:(real^N->bool)->bool`;
                 `\x:real^N. x`; `\x:real^N. x`] MOI_FMB_PL_INVARIANT_LF) THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION;
               IMAGE_ID] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FMB_BARY_ORIENTABLE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CM_WB_DIM THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* A PL 3-ball in an open subset u of real^3 is a combinatorial subcomplex   *)
(* of a finite triangulation inside u whose vertices on the ball are         *)
(* interior points of the triangulated set (PL 2-sphere links). This gives   *)
(* BALL_TRIANGULATION_IN_OPEN = MOI_FND_BALL_TRIANGULATION. Route: finitely  *)
(* many small cubes cover the ball with the ball in the interior of their   *)
(* union; a common simplicial refinement of the cubes and of the ball       *)
(* triangulates the union with the ball as a subcomplex.                    *)
(* ========================================================================= *)

let MOI_FMB_COMPACT_CUBE_NBHD = prove
 (`!(c:real^N->bool) u.
        compact c /\ open u /\ c SUBSET u
        ==> ?P. FINITE P /\ (!k. k IN P ==> polytope k /\ k SUBSET u) /\
                c SUBSET interior (UNIONS P)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^N->bool`; `(:real^N) DIFF u`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = d / (&2 * &(dimindex(:N)))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN c ==> interval[x - h % vec 1,x + h % vec 1] SUBSET u`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; REAL_NOT_LE] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((x - y:real^N)$i))` THEN
    CONJ_TAC THENL [REWRITE_TAC[dist; NORM_LE_L1]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&(CARD(1..dimindex(:N))) * h` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
      REWRITE_TAC[CARD_NUMSEG_1] THEN EXPAND_TAC "h" THEN
      SUBGOAL_THEN `&0 < &(dimindex(:N))` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN
        MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&(dimindex(:N)) * d / (&2 * &(dimindex(:N))) = d / &2`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &(dimindex(:N))` THEN CONV_TAC REAL_FIELD;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:real^N->bool` COMPACT_EQ_HEINE_BOREL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\x:real^N. interval(x - h % vec 1,x + h % vec 1)) c`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[IN_INTERVAL; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                    VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x:real^N. interval(x - h % vec 1,x + h % vec 1)`;
                 `c:real^N->bool`; `f':(real^N->bool)->bool`]
    FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. interval[x - h % vec 1,x + h % vec 1]) X` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; POLYTOPE_INTERVAL] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS (IMAGE (\x:real^N. interval(x - h % vec 1,x + h % vec 1)) X)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPECL [`x - h % vec 1:real^N`; `x + h % vec 1:real^N`]
      INTERVAL_OPEN_SUBSET_CLOSED) THEN
    SET_TAC[];
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE; OPEN_INTERVAL]]);;

let MOI_FMB_INTERIOR_VERTEX_SPHERE = prove
 (`!(t:(real^3->bool)->bool) v.
        lf_simplicial_complex t /\ {v} IN t /\ v IN interior (UNIONS t)
        ==> pl_sphere 2 (UNIONS (simplicial_link t v))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FMB_LINK_SPHERE_CHART THEN
  MAP_EVERY EXISTS_TAC [`interior (UNIONS t):real^3->bool`; `\x:real^3. x`;
                        `\x:real^3. x`] THEN
  ASM_REWRITE_TAC[IMAGE_ID; OPEN_INTERIOR; HOMEOMORPHISM_ID] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[OPEN_INTERIOR; INTERIOR_SUBSET];
    REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_INTERIOR]]);;

(* The theorem BALL_TRIANGULATION_IN_OPEN (the statement term                *)
(* MOI_FND_BALL_TRIANGULATION).                                              *)

let BALL_TRIANGULATION_IN_OPEN = prove
 (`!(c:real^3->bool) u.
     pl_ball 3 c /\ open u /\ c SUBSET u
     ==> ?t k. simplicial_complex t /\ UNIONS t SUBSET u /\
               simplicial_subcomplex k t /\ UNIONS k = c /\
               combinatorial_manifold_with_boundary 3 k /\
               (!v. {v} IN k ==> pl_sphere 2 (UNIONS (simplicial_link t v)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_ball]) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_polyhedron (c:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `c = IMAGE (f:real^3->real^3) S` SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `u:real^3->bool`] MOI_FMB_COMPACT_CUBE_NBHD) THEN
  ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME `pl_polyhedron (c:real^3->bool)`) THEN
  REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(real^3->bool)->bool` (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  MP_TAC(ISPEC `P UNION D:(real^3->bool)->bool`
    POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ASM_SIMP_TAC[FINITE_UNION; FORALL_IN_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `c SUBSET UNIONS (P:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS t = UNIONS (P:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNIONS_UNION] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `simplicial_subcomplex {s:real^3->bool | s IN t /\ s SUBSET c} t`
  ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET_RESTRICT; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `e:real^3->bool`] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {s:real^3->bool | s IN t /\ s SUBSET c} = c`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?d:real^3->bool. d IN D /\ x IN d` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN c` THEN
      REWRITE_TAC[SYM(ASSUME `UNIONS D = (c:real^3->bool)`)] THEN
      REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:real^3->bool` o check (fun th ->
      is_forall (concl th) && can (term_match []
        `!k:real^3->bool. k IN D ==> ?f. f SUBSET t /\ k = UNIONS f`)
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(d:real^3->bool) SUBSET c` ASSUME_TAC THENL
     [UNDISCH_TAC `(d:real^3->bool) IN D` THEN
      UNDISCH_TAC `UNIONS (D:(real^3->bool)->bool) = c` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:real^3->bool`; `t:(real^3->bool)->bool`;
                   `d:real^3->bool`; `e:(real^3->bool)->bool`; `x:real^3`]
      (SET_RULE `!(c:A->bool) t d e x.
         d SUBSET c /\ e SUBSET t /\ d = UNIONS e /\ x IN d
         ==> x IN UNIONS {s | s IN t /\ s SUBSET c}`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex {s:real^3->bool | s IN t /\ s SUBSET c}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_SC_SUBCOMPLEX THEN
    EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  EXISTS_TAC `t:(real^3->bool)->bool` THEN
  EXISTS_TAC `{s:real^3->bool | s IN t /\ s SUBSET c}` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_UNION; UNION_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET] THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`{s:real^3->bool | s IN t /\ s SUBSET c}`;
                   `IMAGE (f:real^3->real^3) (relative_frontier S)`]
      PL_BALL_TRIANGULATION_BOUNDARY) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MOI_FMB_SC_LF] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      REWRITE_TAC[pl_cell_with_boundary] THEN
      MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `f:real^3->real^3`;
                            `g:real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    X_GEN_TAC `v:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FMB_INTERIOR_VERTEX_SPHERE THEN
    ASM_SIMP_TAC[MOI_FMB_SC_LF] THEN
    SUBGOAL_THEN `(v:real^3) IN c` ASSUME_TAC THENL
     [UNDISCH_TAC `{v:real^3} SUBSET c` THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `interior (UNIONS (P:(real^3->bool)->bool)) SUBSET
                  interior (UNIONS (P UNION D))` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_INTERIOR THEN REWRITE_TAC[UNIONS_UNION] THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `c SUBSET interior (UNIONS (P:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `(v:real^3) IN c` THEN SET_TAC[]]);;

