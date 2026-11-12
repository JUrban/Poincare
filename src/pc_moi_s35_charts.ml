(* ========================================================================= *)
(* pc_moi_s35_charts: the second theorem of the Sec 35 unit s35_chart,      *)
(* CHARTS = MOI_S35_CHARTS (pc_moi_s35_stmt.ml, sections 3 and 7.6): edge   *)
(* charts of a graph tube.  For every edge e = uw of the graph, a PL        *)
(* homeomorphism psi e from the model double cube onto the union of the     *)
(* dual cells C(u), C(w) (lower half onto C(u), upper half onto C(w),       *)
(* centre to the midpoint), whose thin slab lies in the given open sets     *)
(* g u, g w, has its lateral band in the frontier of N, meets the graph     *)
(* only near the axis, and is disjoint from the slabs of the other edges.   *)
(* Construction: the two halves are PL 3-cells; a PL map of the middle      *)
(* square onto the splitting disk extends over the boundary spheres (disk   *)
(* complements in a model simplex of real^3, Alexander trick) and over the  *)
(* cells; the two extensions glue; a vertical PL squeeze makes the slab     *)
(* small.  Moise GTM 47, p.248 (Fig. 35.1).                                 *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt.ml";;
needs "src/pc_moi_s34_scella.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_cells.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. The model: the cube, its halves and the middle square as boxes.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S5H_BOXES = prove
 (`moi_s35_cube = interval[--vec 1:real^3,vec 1] /\
   moi_s35_lower = interval[--vec 1:real^3,vector[&1;&1;&0]] /\
   moi_s35_upper = interval[vector[-- &1;-- &1;&0]:real^3,vec 1] /\
   moi_s35_mid = interval[vector[-- &1;-- &1;&0]:real^3,vector[&1;&1;&0]]`,
  REWRITE_TAC[moi_s35_cube; moi_s35_lower; moi_s35_upper; moi_s35_mid] THEN
  REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_ELIM_THM; DIMINDEX_3; FORALL_3] THEN
  REWRITE_TAC[VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5H_MID_RELINT = prove
 (`vec 0 IN relative_interior moi_s35_mid /\ ~(vec 0 IN relative_frontier moi_s35_mid)`,
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s35_mid; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL] THEN
      REWRITE_TAC[DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    SUBGOAL_THEN `affine hull moi_s35_mid SUBSET {x:real^3 | basis 3 dot x = &0}`
    MP_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
      REWRITE_TAC[SUBSET; moi_s35_mid; IN_ELIM_THM] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL_0; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN DISCH_TAC THEN
    REWRITE_TAC[moi_s35_mid; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`x:real^3`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`x:real^3`; `2`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `norm(x:real^3) < &1` THEN REAL_ARITH_TAC;
    REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 2. The model facts and the vertical squeeze of the slab.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S5H_MODEL = prove
 (`polytope moi_s35_lower /\ aff_dim moi_s35_lower = &3 /\
   polytope moi_s35_upper /\ aff_dim moi_s35_upper = &3 /\
   polytope moi_s35_mid /\ aff_dim moi_s35_mid = &2 /\
   moi_s35_lower UNION moi_s35_upper = moi_s35_cube /\
   moi_s35_lower INTER moi_s35_upper = moi_s35_mid /\
   moi_s35_mid SUBSET relative_frontier moi_s35_lower /\
   moi_s35_mid SUBSET relative_frontier moi_s35_upper /\
   closed moi_s35_lower /\ closed moi_s35_upper /\ compact moi_s35_cube`,
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MOI_S5H_BOXES; POLYTOPE_INTERVAL; CLOSED_INTERVAL;
                  COMPACT_INTERVAL] THEN NO_TAC) THENL
   [MP_TAC(ISPEC `moi_s35_lower` AFF_DIM_NONEMPTY_INTERIOR) THEN
    REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MOI_S5H_BOXES; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPEC `moi_s35_upper` AFF_DIM_NONEMPTY_INTERIOR) THEN
    REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MOI_S5H_BOXES; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[MOI_S5H_BOXES; AFF_DIM_INTERVAL] THEN
    SUBGOAL_THEN `~(interval[vector[-- &1;-- &1;&0]:real^3,vector[&1;&1;&0]] = {})`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^3` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN
    SUBGOAL_THEN
     `{i | 1 <= i /\ i <= 3 /\
           (vector[-- &1;-- &1;&0]:real^3)$i < (vector[&1;&1;&0]:real^3)$i} = {1,2}`
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
    REWRITE_TAC[EXTENSION; moi_s35_lower; moi_s35_upper; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[EXTENSION; moi_s35_lower; moi_s35_upper; moi_s35_mid; IN_INTER;
                IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `relative_frontier moi_s35_lower = frontier moi_s35_lower`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
      REWRITE_TAC[MOI_S5H_BOXES; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT;
                  VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MOI_S5H_BOXES; FRONTIER_CLOSED_INTERVAL; SUBSET; IN_DIFF;
                IN_INTERVAL] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `relative_frontier moi_s35_upper = frontier moi_s35_upper`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
      REWRITE_TAC[MOI_S5H_BOXES; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT;
                  VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MOI_S5H_BOXES; FRONTIER_CLOSED_INTERVAL; SUBSET; IN_DIFF;
                IN_INTERVAL] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 3. A PL homeomorphism of the cube halving the slab, preserving the       *)
(* horizontal coordinates and the sign of the height; iterated, it squeezes *)
(* the slab into any thinner slab.                                          *)
(* ------------------------------------------------------------------------- *)

let moi_s5h_hl = new_definition
 `moi_s5h_hl (s:real) =
    if abs s <= &1 / &8 then s / &2
    else if &0 < s then &1 / &16 + (s - &1 / &8) * &15 / &14
    else -- (&1 / &16) + (s + &1 / &8) * &15 / &14`;;

let moi_s5h_hm = new_definition
 `moi_s5h_hm (r:real) =
    if abs r <= &1 / &16 then &2 * r
    else if &0 < r then &1 / &8 + (r - &1 / &16) * &14 / &15
    else -- (&1 / &8) + (r + &1 / &16) * &14 / &15`;;

let moi_s5h_h = new_definition
 `moi_s5h_h (x:real^3) = vector[x$1; x$2; moi_s5h_hl (x$3)]:real^3`;;

let moi_s5h_hi = new_definition
 `moi_s5h_hi (x:real^3) = vector[x$1; x$2; moi_s5h_hm (x$3)]:real^3`;;

let MOI_S5H_HL_FACTS = prove
 (`(!s. abs s <= &1 ==> abs(moi_s5h_hl s) <= &1 /\ moi_s5h_hm(moi_s5h_hl s) = s) /\
   (!r. abs r <= &1 ==> abs(moi_s5h_hm r) <= &1 /\ moi_s5h_hl(moi_s5h_hm r) = r) /\
   (!s c. abs s <= &1 /\ &0 < c /\ c <= &1 / &8
          ==> (abs(moi_s5h_hl s) <= c / &2 <=> abs s <= c)) /\
   (!s. moi_s5h_hl s <= &0 <=> s <= &0) /\
   (!s. &0 <= moi_s5h_hl s <=> &0 <= s) /\
   moi_s5h_hl (&0) = &0`,
  REWRITE_TAC[moi_s5h_hl; moi_s5h_hm] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S5H_PL_VERT = prove
 (`!f bb a1 b1 a2 b2 a3 b3.
     &0 < bb /\ bb < &1 /\
     (!s. -- &1 <= s /\ s <= --bb ==> f s = a1 * s + b1) /\
     (!s. --bb <= s /\ s <= bb ==> f s = a2 * s + b2) /\
     (!s. bb <= s /\ s <= &1 ==> f s = a3 * s + b3)
     ==> pl_map_on moi_s35_cube (\x:real^3. vector[x$1; x$2; f(x$3)]:real^3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_map_on] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  EXISTS_TAC `{interval[--vec 1:real^3,vector[&1;&1;--bb]],
               interval[vector[-- &1;-- &1;--bb]:real^3,vector[&1;&1;bb]],
               interval[vector[-- &1;-- &1;bb]:real^3,vec 1]}` THEN
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
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < bb`; `bb < &1`] THEN REAL_ARITH_TAC;
    GEN_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < bb`; `bb < &1`] THEN REAL_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`\y:real^3. vector[y$1; y$2; a1 * y$3]:real^3`;
                          `vector[&0; &0; b1]:real^3`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
    REWRITE_TAC[REAL_ADD_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`-- &1 <= (z:real^3)$3`; `(z:real^3)$3 <= --bb`] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < bb`; `bb < &1`] THEN REAL_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`\y:real^3. vector[y$1; y$2; a2 * y$3]:real^3`;
                          `vector[&0; &0; b2]:real^3`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
    REWRITE_TAC[REAL_ADD_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`--bb <= (z:real^3)$3`; `(z:real^3)$3 <= bb`] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < bb`; `bb < &1`] THEN REAL_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`\y:real^3. vector[y$1; y$2; a3 * y$3]:real^3`;
                          `vector[&0; &0; b3]:real^3`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
    REWRITE_TAC[REAL_ADD_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`bb <= (z:real^3)$3`; `(z:real^3)$3 <= &1`] THEN
    REAL_ARITH_TAC]);;

let MOI_S5H_H_EQ = prove
 (`moi_s5h_h = (\x:real^3. vector[x$1; x$2; moi_s5h_hl (x$3)]:real^3) /\
   moi_s5h_hi = (\x:real^3. vector[x$1; x$2; moi_s5h_hm (x$3)]:real^3)`,
  REWRITE_TAC[FUN_EQ_THM; moi_s5h_h; moi_s5h_hi]);;

let MOI_S5H_H_CUBE = prove
 (`(!x. x IN moi_s35_cube
        ==> moi_s5h_h x IN moi_s35_cube /\ moi_s5h_hi (moi_s5h_h x) = x) /\
   (!y. y IN moi_s35_cube
        ==> moi_s5h_hi y IN moi_s35_cube /\ moi_s5h_h (moi_s5h_hi y) = y)`,
  REWRITE_TAC[moi_s5h_h; moi_s5h_hi; MOI_S5H_BOXES; IN_INTERVAL; DIMINDEX_3; FORALL_3;
              VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT; CART_EQ] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
   [MP_TAC(SPEC `(x:real^3)$3` (CONJUNCT1 MOI_S5H_HL_FACTS));
    MP_TAC(SPEC `(x:real^3)$3` (CONJUNCT1(CONJUNCT2 MOI_S5H_HL_FACTS)))] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC));;

let MOI_S5H_H_PLH = prove
 (`pl_homeomorphism (moi_s35_cube,moi_s35_cube) (moi_s5h_h,moi_s5h_hi)`,
  SUBGOAL_THEN `pl_map_on moi_s35_cube moi_s5h_h /\ pl_map_on moi_s35_cube moi_s5h_hi`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5H_H_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5H_PL_VERT THEN
      MAP_EVERY EXISTS_TAC [`&1 / &8`; `&15 / &14`; `&1 / &14`; `&1 / &2`; `&0`;
                            `&15 / &14`; `-- (&1 / &14)`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[moi_s5h_hl] THEN
      REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN
      REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_S5H_PL_VERT THEN
      MAP_EVERY EXISTS_TAC [`&1 / &16`; `&14 / &15`; `-- (&1 / &15)`; `&2`; `&0`;
                            `&14 / &15`; `&1 / &15`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[moi_s5h_hm] THEN
      REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN
      REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  MP_TAC MOI_S5H_H_CUBE THEN SET_TAC[]);;

let MOI_S5H_H_FACTS = prove
 (`(!x. (moi_s5h_h x)$1 = x$1 /\ (moi_s5h_h x)$2 = x$2 /\
        (moi_s5h_h x)$3 = moi_s5h_hl (x$3)) /\
   IMAGE moi_s5h_h moi_s35_lower = moi_s35_lower /\
   IMAGE moi_s5h_h moi_s35_upper = moi_s35_upper /\
   IMAGE moi_s5h_h moi_s35_mid = moi_s35_mid /\
   moi_s5h_h (vec 0) = vec 0`,
  SUBGOAL_THEN `!x. (moi_s5h_h x)$1 = x$1 /\ (moi_s5h_h x)$2 = x$2 /\
                    (moi_s5h_h x)$3 = moi_s5h_hl (x$3) /\
                    (moi_s5h_hi x)$1 = x$1 /\ (moi_s5h_hi x)$2 = x$2 /\
                    (moi_s5h_hi x)$3 = moi_s5h_hm (x$3)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5h_h; moi_s5h_hi; VECTOR_3]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y:real^3. y IN moi_s35_cube ==> abs(y$3) <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC MOI_S5H_H_CUBE THEN MP_TAC MOI_S5H_HL_FACTS THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; moi_s35_lower; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[];
      STRIP_TAC THEN EXISTS_TAC `moi_s5h_hi y` THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; moi_s35_upper; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[];
      STRIP_TAC THEN EXISTS_TAC `moi_s5h_hi y` THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; moi_s35_mid; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[];
      STRIP_TAC THEN EXISTS_TAC `moi_s5h_hi y` THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[moi_s5h_h; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S5H_SQUEEZE = prove
 (`!c. &0 < c
       ==> ?f g. pl_homeomorphism (moi_s35_cube,moi_s35_cube) (f,g) /\
                 (!x. (f x)$1 = x$1 /\ (f x)$2 = x$2) /\
                 IMAGE f moi_s35_lower = moi_s35_lower /\
                 IMAGE f moi_s35_upper = moi_s35_upper /\
                 IMAGE f moi_s35_mid = moi_s35_mid /\ f (vec 0) = vec 0 /\
                 (!x. x IN moi_s35_slab ==> abs((f x)$3) <= c)`,
  SUBGOAL_THEN
   `!k. ?f g. pl_homeomorphism (moi_s35_cube,moi_s35_cube) (f,g) /\
              (!x. (f x)$1 = x$1 /\ (f x)$2 = x$2) /\
              IMAGE f moi_s35_lower = moi_s35_lower /\
              IMAGE f moi_s35_upper = moi_s35_upper /\
              IMAGE f moi_s35_mid = moi_s35_mid /\ f (vec 0) = vec 0 /\
              (!x. x IN moi_s35_slab ==> abs((f x)$3) <= &1 / &8 * inv(&2) pow k)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `\x:real^3. x`] THEN
      REWRITE_TAC[IMAGE_ID; real_pow; REAL_MUL_RID] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`\x:real^3. x`; `\x:real^3. x`; `moi_s35_cube`]
          MOI_SCD_PLH_RESTRICT) THEN
        REWRITE_TAC[MOI_SCD_PL_HOMEO_ID; IMAGE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
        REWRITE_TAC[MOI_S5H_BOXES; POLYTOPE_INTERVAL];
        REWRITE_TAC[moi_s35_slab; IN_ELIM_THM] THEN MESON_TAC[]];
      FIRST_X_ASSUM(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`moi_s5h_h o (f:real^3->real^3)`;
                            `(g:real^3->real^3) o moi_s5h_hi`] THEN
      REWRITE_TAC[o_THM; IMAGE_o] THEN ASM_REWRITE_TAC[MOI_S5H_H_FACTS] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s35_cube` THEN
        ASM_REWRITE_TAC[MOI_S5H_H_PLH];
        ALL_TAC] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^3->real^3) x IN moi_s35_cube` ASSUME_TAC THENL
       [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,moi_s35_cube)
                       ((f:real^3->real^3),(g:real^3->real^3))` THEN
        REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
        UNDISCH_TAC `(x:real^3) IN moi_s35_slab` THEN
        REWRITE_TAC[moi_s35_slab; IN_ELIM_THM] THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &1 / &8 * inv(&2) pow k /\ &1 / &8 * inv(&2) pow k <= &1 / &8`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          MATCH_MP_TAC REAL_POW_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
          MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &1 / &8 * x <= &1 / &8`) THEN
          MATCH_MP_TAC REAL_POW_1_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`((f:real^3->real^3) x)$3`; `&1 / &8 * inv(&2) pow k`]
        (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_S5H_HL_FACTS)))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(f:real^3->real^3) x IN moi_s35_cube` THEN
        REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                    VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[real_pow] THEN
      SUBGOAL_THEN `abs(((f:real^3->real^3) x)$3) <= &1 / &8 * inv(&2) pow k`
        (fun th -> REWRITE_TAC[th]) THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(&2)`; `&8 * c`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
      STRIP_ASSUME_TAC) o SPEC `k:num`) THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &8 * inv(&2) pow k` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `inv(&2) pow k < &8 * c` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 4. Cells: PL homeomorphisms between cells preserving boundaries, the     *)
(* extension of a disk map over two 3-cells of real^3, and a disk chart     *)
(* from the middle square with prescribed centre.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S5H_CELL_PLH = prove
 (`!n (s:real^M->bool) bs (t:real^N->bool) bt.
     pl_cell_with_boundary n s bs /\ pl_cell_with_boundary n t bt
     ==> ?f g. pl_homeomorphism (s,t) (f,g) /\ IMAGE f bs = bt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^M->bool` (X_CHOOSE_THEN `f1:real^M->real^M`
     (X_CHOOSE_THEN `g1:real^M->real^M` STRIP_ASSUME_TAC)))
   (X_CHOOSE_THEN `k2:real^N->bool` (X_CHOOSE_THEN `f2:real^N->real^N`
     (X_CHOOSE_THEN `g2:real^N->real^N` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k1:real^M->bool`; `k2:real^N->bool`; `&n:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^M->real^N` (X_CHOOSE_THEN `q:real^N->real^M`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(f2:real^N->real^N) o (p:real^M->real^N) o (g1:real^M->real^M)` THEN
  EXISTS_TAC `((f1:real^M->real^M) o (q:real^N->real^M)) o (g2:real^N->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k2:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k1:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `IMAGE (g1:real^M->real^M) (IMAGE f1 (relative_frontier k1)) =
                relative_frontier k1` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!z:real^M. z IN s ==> (g:real^M->real^M)((f:real^M->real^M) z) = z)
                           ==> IMAGE g (IMAGE f s) = s`) THEN
    X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    UNDISCH_TAC `pl_homeomorphism (k1:real^M->bool,s:real^M->bool)
                    ((f1:real^M->real^M),(g1:real^M->real^M))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:real^M) IN relative_frontier k1` THEN
    REWRITE_TAC[relative_frontier; IN_DIFF] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; CLOSURE_CLOSED];
    UNDISCH_TAC `pl_homeomorphism (relative_frontier k1:real^M->bool,
                                   relative_frontier k2:real^N->bool)
                    ((p:real^M->real^N),(q:real^N->real^M))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]]);;

(* A cell boundary is a sphere (as MOI_S4O_CELL_SPHERE of pc_moi_s34_outer,  *)
(* which is outside this load closure), and cells are polyhedra.            *)

let MOI_S5H_CELL_SPHERE = prove
 (`!n (c:real^N->bool) b.
     pl_cell_with_boundary (n + 1) c b ==> pl_sphere n b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_sphere] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CEL_PLH_SIMPLEX_RF THEN
  MAP_EVERY EXISTS_TAC [`n + 1`; `c:real^N->bool`] THEN ASM_REWRITE_TAC[]);;

let MOI_S5H_CELL_POLY = prove
 (`!n (s:real^N->bool) b.
     pl_cell_with_boundary n s b ==> pl_polyhedron s /\ pl_polyhedron b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `polytope(k:real^N->bool) /\ closed k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron(k:real^N->bool) /\ pl_polyhedron(relative_frontier k)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER; POLYTOPE_IMP_PL_POLYHEDRON];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
      concl t = `IMAGE (f:real^N->real^N) k = s`)) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; LOCALLY_POLYHEDRAL_PL_POLYHEDRON]]);;

(* Extension of a disk map in the boundary spheres of two 3-cells of real^3 *)
(* (complementary disks, DISK_COMPLEMENT; then the cells, CELL_EXTENSION).   *)

let MOI_S5H_EXT3 = prove
 (`!(x:real^3->bool) bx p jp (y:real^3->bool) by p' jp' th th'.
     pl_cell_with_boundary 3 x bx /\ pl_cell_with_boundary 3 y by /\
     pl_cell_with_boundary 2 p jp /\ p SUBSET bx /\
     pl_cell_with_boundary 2 p' jp' /\ p' SUBSET by /\
     pl_homeomorphism (p,p') (th,th') /\ IMAGE th jp = jp'
     ==> ?f g. pl_homeomorphism (x,y) (f,g) /\ (!z. z IN p ==> f z = th z) /\
               IMAGE f bx = by`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 2 (bx:real^3->bool) /\ pl_sphere 2 (by:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5H_CELL_SPHERE THEN
    REWRITE_TAC[ARITH_RULE `2 + 1 = 3`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 ((bx DIFF p) UNION jp) (jp:real^3->bool) /\
                pl_cell_with_boundary 2 ((by DIFF p') UNION jp') (jp':real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DISK_COMPLEMENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `p:real^3->bool`; `jp:real^3->bool`] MOI_CEL_CELL_COMPACT) THEN
  MP_TAC(ISPECL [`2`; `p':real^3->bool`; `jp':real^3->bool`] MOI_CEL_CELL_COMPACT) THEN
  MP_TAC(ISPECL [`2`; `(bx DIFF p) UNION jp:real^3->bool`; `jp:real^3->bool`]
    MOI_CEL_CELL_COMPACT) THEN
  MP_TAC(ISPECL [`2`; `(by DIFF p') UNION jp':real^3->bool`; `jp':real^3->bool`]
    MOI_CEL_CELL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (jp:real^3->bool,jp')
                  ((th:real^3->real^3),(th':real^3->real^3))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
      concl t = `IMAGE (th:real^3->real^3) jp = jp'`)) THEN
    MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`p:real^3->bool`; `p':real^3->bool`] THEN
    ASM_MESON_TAC[MOI_S5H_CELL_POLY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `(bx DIFF p) UNION jp:real^3->bool`; `jp:real^3->bool`;
                 `(by DIFF p') UNION jp':real^3->bool`; `jp':real^3->bool`;
                 `th:real^3->real^3`; `th':real^3->real^3`] MOI_CEL_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^3->real^3` (X_CHOOSE_THEN `g2:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`p:real^3->bool`; `(bx DIFF p) UNION jp:real^3->bool`;
                 `p':real^3->bool`; `(by DIFF p') UNION jp':real^3->bool`;
                 `th:real^3->real^3`; `th':real^3->real^3`;
                 `f2:real^3->real^3`; `g2:real^3->real^3`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN jp` (fun t -> ASM_MESON_TAC[t]) THEN
      UNDISCH_TAC `(z:real^3) IN p INTER ((bx DIFF p) UNION jp)` THEN SET_TAC[];
      SUBGOAL_THEN `(p:real^3->bool) INTER ((bx DIFF p) UNION jp) = jp /\
                    (p':real^3->bool) INTER ((by DIFF p') UNION jp') = jp'`
        (fun t -> ASM_REWRITE_TAC[t]) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p UNION ((bx DIFF p) UNION jp) = bx:real^3->bool /\
                p' UNION ((by DIFF p') UNION jp') = by:real^3->bool`
    (fun t -> REWRITE_TAC[t]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `x:real^3->bool`; `bx:real^3->bool`; `y:real^3->bool`;
                 `by:real^3->bool`;
                 `\z:real^3. if z IN p then (th:real^3->real^3) z else f2 z`;
                 `\z:real^3. if z IN p' then (th':real^3->real^3) z else g2 z`]
    MOI_CEL_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN bx` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) bx =
                IMAGE (\z:real^3. if z IN p then (th:real^3->real^3) z else f2 z) bx`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!z:real^3. z IN s ==> (f:real^3->real^3) z = g z) ==> IMAGE f s = IMAGE g s`) THEN
    ASM_SIMP_TAC[];
    UNDISCH_TAC `pl_homeomorphism (bx:real^3->bool,by)
                  ((\z:real^3. if z IN p then (th:real^3->real^3) z else f2 z),
                   (\z:real^3. if z IN p' then (th':real^3->real^3) z else g2 z))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]]);;

(* The same with the second cell in real^N: transport it to the first.       *)

let MOI_S5H_EXTN = prove
 (`!(x:real^3->bool) bx p jp (y:real^N->bool) by p' jp' th th'.
     pl_cell_with_boundary 3 x bx /\ pl_cell_with_boundary 3 y by /\
     pl_cell_with_boundary 2 p jp /\ p SUBSET bx /\
     pl_cell_with_boundary 2 p' jp' /\ p' SUBSET by /\
     pl_homeomorphism (p,p') (th,th') /\ IMAGE th jp = jp'
     ==> ?f g. pl_homeomorphism (x,y) (f,g) /\ (!z. z IN p ==> f z = th z) /\
               IMAGE f bx = by`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `y:real^N->bool`; `by:real^N->bool`; `x:real^3->bool`;
                 `bx:real^3->bool`] MOI_S5H_CELL_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `be:real^N->real^3` (X_CHOOSE_THEN `bi:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(by:real^N->bool) SUBSET y /\ (jp':real^N->bool) SUBSET p'`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CEL_CELL_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `(!z:real^N. z IN y ==> (bi:real^3->real^N) ((be:real^N->real^3) z) = z) /\
                IMAGE (be:real^N->real^3) y = x /\
                IMAGE (th:real^3->real^N) p = p'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (p:real^3->bool,p':real^N->bool)
                   ((th:real^3->real^N),(th':real^N->real^3))` THEN
    UNDISCH_TAC `pl_homeomorphism (y:real^N->bool,x:real^3->bool)
                   ((be:real^N->real^3),(bi:real^3->real^N))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (p':real^N->bool,IMAGE (be:real^N->real^3) p')
                  (be,(bi:real^3->real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`y:real^N->bool`; `x:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[MOI_S5H_CELL_POLY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (be:real^N->real^3) p') (IMAGE be jp')`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`y:real^N->bool`; `x:real^3->bool`; `bi:real^3->real^N`] THEN
    ASM_SIMP_TAC[MOI_SS2_FSA_OF_CELL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `bx:real^3->bool`; `p:real^3->bool`; `jp:real^3->bool`;
                 `x:real^3->bool`; `bx:real^3->bool`;
                 `IMAGE (be:real^N->real^3) p'`; `IMAGE (be:real^N->real^3) jp'`;
                 `(be:real^N->real^3) o (th:real^3->real^N)`;
                 `(th':real^N->real^3) o (bi:real^3->real^N)`] MOI_S5H_EXT3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (be:real^N->real^3) by = bx` THEN
      UNDISCH_TAC `(p':real^N->bool) SUBSET by` THEN SET_TAC[];
      MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `p':real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IMAGE_o]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^3->real^3` (X_CHOOSE_THEN `gg:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(bi:real^3->real^N) o (ff:real^3->real^3)`;
                        `(gg:real^3->real^3) o (be:real^N->real^3)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `x:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
      concl t = `IMAGE (be:real^N->real^3) by = bx`)) THEN
    MATCH_MP_TAC(SET_RULE
     `(!z:real^N. z IN s ==> (g:real^3->real^N) ((f:real^N->real^3) z) = z)
      ==> IMAGE g (IMAGE f s) = s`) THEN
    ASM SET_TAC[]]);;

(* A disk chart from the middle square with prescribed centre (cone map from *)
(* the centre of the square to the preimage of the given interior point).    *)

let MOI_S5H_DISK_CENTRE = prove
 (`!(d:real^N->bool) j m.
     pl_cell_with_boundary 2 d j /\ m IN d /\ ~(m IN j)
     ==> ?f g. pl_homeomorphism (moi_s35_mid,d) (f,g) /\
               IMAGE f (relative_frontier moi_s35_mid) = j /\ f (vec 0) = m`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 moi_s35_mid (relative_frontier moi_s35_mid)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4A_POLY_CELL_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `d:real^N->bool`; `j:real^N->bool`; `moi_s35_mid`;
                 `relative_frontier moi_s35_mid`] MOI_S5H_CELL_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^N->real^3` (X_CHOOSE_THEN `g1:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(j:real^N->bool) SUBSET d` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CEL_CELL_COMPACT]; ALL_TAC] THEN
  ABBREV_TAC `c0 = (f1:real^N->real^3) m` THEN
  SUBGOAL_THEN `(c0:real^3) IN moi_s35_mid /\ ~(c0 IN relative_frontier moi_s35_mid)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun t ->
      concl t = `IMAGE (f1:real^N->real^3) j = relative_frontier moi_s35_mid`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c0:real^3) IN relative_interior moi_s35_mid` ASSUME_TAC THENL
   [UNDISCH_TAC `~((c0:real^3) IN relative_frontier moi_s35_mid)` THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_frontier moi_s35_mid = {})` ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `moi_s35_mid` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_BOUNDED] THEN
    ASM_MESON_TAC[AFF_DIM_EMPTY; AFF_DIM_SING;
                  INT_ARITH `~(&2:int = -- &1) /\ ~(&2:int = &0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier moi_s35_mid,
                                  relative_frontier moi_s35_mid)
                                 ((\x:real^3. x),(\x:real^3. x))` ASSUME_TAC THENL
   [REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
                GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    ASM_SIMP_TAC[MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x y. x IN relative_frontier moi_s35_mid /\ y IN relative_frontier moi_s35_mid /\
           y IN segment[vec 0:real^3,x] ==> y = x) /\
    (!x y. x IN relative_frontier moi_s35_mid /\ y IN relative_frontier moi_s35_mid /\
           y IN segment[c0:real^3,x] ==> y = x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
    ASM_MESON_TAC[POLYTOPE_IMP_CONVEX; MOI_S5H_MID_RELINT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier moi_s35_mid`; `relative_frontier moi_s35_mid`;
                 `vec 0:real^3`; `c0:real^3`; `\x:real^3. x`; `\x:real^3. x`]
    MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER; MOI_S5H_MID_RELINT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {segment[vec 0:real^3,x] | x IN relative_frontier moi_s35_mid} =
    moi_s35_mid /\
    UNIONS {segment[c0:real^3,x] | x IN relative_frontier moi_s35_mid} = moi_s35_mid`
    (fun t -> REWRITE_TAC[t]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_CON_CONE_RF THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT; MOI_S5H_MID_RELINT];
    ALL_TAC] THEN
  ABBREV_TAC `cm = moi_con_conemap (relative_frontier moi_s35_mid) (vec 0:real^3) c0
                     (\x:real^3. x)` THEN
  ABBREV_TAC `cm' = moi_con_conemap (relative_frontier moi_s35_mid) (c0:real^3) (vec 0)
                      (\x:real^3. x)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(cm:real^3->real^3) (vec 0) = c0` ASSUME_TAC THENL
   [EXPAND_TAC "cm" THEN MATCH_MP_TAC MOI_CON_CONEMAP_APEX THEN
    ASM_REWRITE_TAC[MOI_S5H_MID_RELINT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(g1:real^3->real^N) o (cm:real^3->real^3)`;
                        `(cm':real^3->real^3) o (f1:real^N->real^3)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s35_mid` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (cm:real^3->real^3) (relative_frontier moi_s35_mid) =
                  relative_frontier moi_s35_mid` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x:real^3. x IN s ==> (f:real^3->real^3) x = x) ==> IMAGE f s = s`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun t ->
      concl t = `IMAGE (f1:real^N->real^3) j = relative_frontier moi_s35_mid`)) THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^N. x IN s ==> (g:real^3->real^N) ((f:real^N->real^3) x) = x)
      ==> IMAGE g (IMAGE f s) = s`) THEN
    ASM_MESON_TAC[SUBSET];
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 5. The base chart of an edge: the middle square onto the splitting disk  *)
(* (centre to the midpoint), extended over the two halves and glued; and    *)
(* the lateral faces of the model.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S5H_BASE = prove
 (`!(du:real^N->bool) bdu dv bdv jp m.
     pl_cell_with_boundary 3 du bdu /\ pl_cell_with_boundary 3 dv bdv /\
     pl_cell_with_boundary 2 (du INTER dv) jp /\
     du INTER dv SUBSET bdu /\ du INTER dv SUBSET bdv /\
     m IN du INTER dv /\ ~(m IN jp)
     ==> ?psi q. pl_homeomorphism (moi_s35_cube,du UNION dv) (psi,q) /\
                 IMAGE psi moi_s35_lower = du /\ IMAGE psi moi_s35_upper = dv /\
                 IMAGE psi moi_s35_mid = du INTER dv /\
                 IMAGE psi (relative_frontier moi_s35_lower) = bdu /\
                 IMAGE psi (relative_frontier moi_s35_upper) = bdv /\
                 IMAGE psi (relative_frontier moi_s35_mid) = jp /\
                 psi (vec 0) = m`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 3 moi_s35_lower (relative_frontier moi_s35_lower) /\
    pl_cell_with_boundary 3 moi_s35_upper (relative_frontier moi_s35_upper) /\
    pl_cell_with_boundary 2 moi_s35_mid (relative_frontier moi_s35_mid)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S4A_POLY_CELL_3; MOI_S4A_POLY_CELL_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier moi_s35_lower SUBSET moi_s35_lower /\
    relative_frontier moi_s35_upper SUBSET moi_s35_upper /\
    relative_frontier moi_s35_mid SUBSET moi_s35_mid /\
    moi_s35_mid SUBSET moi_s35_lower /\ moi_s35_mid SUBSET moi_s35_upper /\
    (vec 0:real^3) IN moi_s35_mid`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; POLYTOPE_IMP_CLOSED] THEN
    MP_TAC MOI_S5H_MID_RELINT THEN
    MP_TAC(ISPEC `moi_s35_mid` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `moi_s35_lower INTER moi_s35_upper = moi_s35_mid` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`du INTER dv:real^N->bool`; `jp:real^N->bool`; `m:real^N`]
    MOI_S5H_DISK_CENTRE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `th:real^3->real^N` (X_CHOOSE_THEN `th':real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`moi_s35_lower`; `relative_frontier moi_s35_lower`; `moi_s35_mid`;
                 `relative_frontier moi_s35_mid`; `du:real^N->bool`; `bdu:real^N->bool`;
                 `du INTER dv:real^N->bool`; `jp:real^N->bool`; `th:real^3->real^N`;
                 `th':real^N->real^3`] MOI_S5H_EXTN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fu:real^3->real^N` (X_CHOOSE_THEN `gu:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`moi_s35_upper`; `relative_frontier moi_s35_upper`; `moi_s35_mid`;
                 `relative_frontier moi_s35_mid`; `dv:real^N->bool`; `bdv:real^N->bool`;
                 `du INTER dv:real^N->bool`; `jp:real^N->bool`; `th:real^3->real^N`;
                 `th':real^N->real^3`] MOI_S5H_EXTN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fv:real^3->real^N` (X_CHOOSE_THEN `gv:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (fu:real^3->real^N) moi_s35_lower = du /\
                IMAGE (fv:real^3->real^N) moi_s35_upper = dv /\
                IMAGE (th:real^3->real^N) moi_s35_mid = du INTER dv`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`pl_homeomorphism (moi_s35_lower,du:real^N->bool)
         ((fu:real^3->real^N),(gu:real^N->real^3))`;
      `pl_homeomorphism (moi_s35_upper,dv:real^N->bool)
         ((fv:real^3->real^N),(gv:real^N->real^3))`;
      `pl_homeomorphism (moi_s35_mid,du INTER dv:real^N->bool)
         ((th:real^3->real^N),(th':real^N->real^3))`] THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s35_lower`; `moi_s35_upper`; `du:real^N->bool`; `dv:real^N->bool`;
                 `fu:real^3->real^N`; `gu:real^N->real^3`; `fv:real^3->real^N`;
                 `gv:real^N->real^3`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `compact(du:real^N->bool) /\ compact(dv:real^N->bool)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_CEL_CELL_COMPACT]; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    SUBGOAL_THEN `IMAGE (fu:real^3->real^N) moi_s35_mid = IMAGE th moi_s35_mid`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!z:real^3. z IN s ==> (f:real^3->real^N) z = g z) ==> IMAGE f s = IMAGE g s`) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `psi = \x:real^3. if x IN moi_s35_lower then (fu:real^3->real^N) x
                               else fv x` THEN
  ABBREV_TAC `q = \y:real^N. if y IN du then (gu:real^N->real^3) y else gv y` THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`psi:real^3->real^N`; `q:real^N->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!x. x IN moi_s35_lower ==> (psi:real^3->real^N) x = fu x) /\
    (!x. x IN moi_s35_upper ==> (psi:real^3->real^N) x = fv x) /\
    (!x. x IN moi_s35_mid ==> (psi:real^3->real^N) x = th x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^3) IN moi_s35_mid` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]];
      SUBGOAL_THEN `(x:real^3) IN moi_s35_lower` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s f. s SUBSET moi_s35_cube /\ (!x. x IN s ==> (psi:real^3->real^N) x = f x)
          ==> IMAGE psi s = IMAGE f s`
  ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_lower SUBSET moi_s35_cube /\ moi_s35_upper SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_lower UNION moi_s35_upper = moi_s35_cube` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (psi:real^3->real^N) moi_s35_lower = IMAGE fu moi_s35_lower`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) moi_s35_upper = IMAGE fv moi_s35_upper`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) moi_s35_mid = IMAGE th moi_s35_mid`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_lower) =
                  IMAGE fu (relative_frontier moi_s35_lower)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_upper) =
                  IMAGE fv (relative_frontier moi_s35_upper)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_mid) =
                  IMAGE th (relative_frontier moi_s35_mid)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                        ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[]]);;

let MOI_S5H_NOT_RELINT_MID = prove
 (`!(y:real^3) i.
     y IN moi_s35_mid /\ (i = 1 \/ i = 2) /\ abs(y$i) = &1
     ==> ~(y IN relative_interior moi_s35_mid)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `1 <= i /\ i <= dimindex(:3)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_3] THEN UNDISCH_TAC `i = 1 \/ i = 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `z:real^3 = y + (e / &2 * y$i) % basis i` THEN
  SUBGOAL_THEN `(z:real^3) IN ball(y,e) INTER affine hull moi_s35_mid` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
     [EXPAND_TAC "z" THEN
      REWRITE_TAC[dist; VECTOR_ARITH `y - (y + v):real^3 = --v`; NORM_NEG; NORM_MUL] THEN
      ASM_SIMP_TAC[NORM_BASIS; REAL_ABS_MUL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `z:real^3 = (&1 + e / &2) % y + (--(e / &2)) % (y - y$i % basis i)`
    SUBST1_TAC THENL [EXPAND_TAC "z" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_mid` THEN
      REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN
      REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; DIMINDEX_3;
                  FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT;
                  VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      UNDISCH_TAC `i = 1 \/ i = 2` THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[ARITH] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN moi_s35_mid` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN
  REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "z" THEN ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                                   BASIS_COMPONENT; REAL_MUL_RID] THEN
  SUBGOAL_THEN `(y:real^3)$i = &1 \/ y$i = -- &1` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5H_RF_LATERAL = prove
 (`!y:real^3.
     y IN moi_s35_cube /\ moi_s35_n y = &1
     ==> (y$3 <= &0 ==> y IN relative_frontier moi_s35_lower) /\
         (&0 <= y$3 ==> y IN relative_frontier moi_s35_upper) /\
         (y$3 = &0 ==> y IN relative_frontier moi_s35_mid)`,
  GEN_TAC THEN STRIP_TAC THEN STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  SUBGOAL_THEN `abs((y:real^3)$1) = &1 \/ abs(y$2) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_n y = &1` THEN REWRITE_TAC[moi_s35_n] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `-- &1 <= (y:real^3)$1 /\ y$1 <= &1 /\ -- &1 <= y$2 /\ y$2 <= &1 /\
                -- &1 <= y$3 /\ y$3 <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN moi_s35_cube` THEN
    REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior moi_s35_lower = {}) /\ ~(interior moi_s35_upper = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5H_BOXES; INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
    REWRITE_TAC[MOI_S5H_BOXES; FRONTIER_CLOSED_INTERVAL; IN_DIFF; IN_INTERVAL] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
    REWRITE_TAC[MOI_S5H_BOXES; FRONTIER_CLOSED_INTERVAL; IN_DIFF; IN_INTERVAL] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(y:real^3) IN moi_s35_mid` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_s35_mid; IN_ELIM_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED; IN_DIFF] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [MATCH_MP_TAC MOI_S5H_NOT_RELINT_MID THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5H_NOT_RELINT_MID THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[]]]);;

let MOI_S5H_SLAB_SMALL = prove
 (`!k. compact k /\ DISJOINT k moi_s35_mid
       ==> ?c. &0 < c /\ !x:real^3. x IN k /\ x IN moi_s35_cube ==> c < abs(x$3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `moi_s35_mid`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM DISJOINT] THEN
    MESON_TAC[MOI_S5H_MODEL; POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `vector[(x:real^3)$1; x$2; &0]:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN moi_s35_cube` THEN
    REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN
    REWRITE_TAC[MOI_S5H_BOXES; IN_INTERVAL; DIMINDEX_3;
                FORALL_3; VECTOR_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(x:real^3,vector[x$1; x$2; &0]) = abs(x$3)` SUBST1_TAC THENL
   [SUBGOAL_THEN `(x:real^3) - vector[x$1; x$2; &0] = x$3 % basis 3` ASSUME_TAC THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
               VECTOR_3; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[dist; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID]];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 6. The chart of one edge: the base chart composed with a vertical squeeze *)
(* making the slab image lie in a given open set w around the disk, the     *)
(* lateral band in fr (the boundary of the cells near the disk lies in fr   *)
(* or off w), and the closed set lc (the graph) near the axis.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S5H_HH_CLOSED = prove
 (`closed({x:real^3 | x$1 >= &1 / &16} UNION {x | x$1 <= --(&1 / &16)} UNION
          {x | x$2 >= &1 / &16} UNION {x | x$2 <= --(&1 / &16)})`,
  REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
  REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; CLOSED_HALFSPACE_COMPONENT_LE]);;

let MOI_S5H_EDGE = prove
 (`!(du:real^N->bool) bdu dv bdv jp m w lc fr.
     pl_cell_with_boundary 3 du bdu /\ pl_cell_with_boundary 3 dv bdv /\
     pl_cell_with_boundary 2 (du INTER dv) jp /\
     du INTER dv SUBSET bdu /\ du INTER dv SUBSET bdv /\
     m IN du INTER dv /\ ~(m IN jp) /\ jp SUBSET fr /\
     open w /\ du INTER dv SUBSET w /\
     bdu SUBSET fr UNION (du INTER dv) UNION ((:real^N) DIFF w) /\
     bdv SUBSET fr UNION (du INTER dv) UNION ((:real^N) DIFF w) /\
     closed lc /\ lc INTER (du INTER dv) SUBSET {m}
     ==> ?psi q. pl_homeomorphism (moi_s35_cube,du UNION dv) (psi,q) /\
                 IMAGE psi moi_s35_lower = du /\ IMAGE psi moi_s35_upper = dv /\
                 psi (vec 0) = m /\
                 IMAGE psi moi_s35_slab SUBSET w /\
                 IMAGE psi {x | x IN moi_s35_slab /\ moi_s35_n x = &1} SUBSET fr /\
                 (!x. x IN moi_s35_slab /\ psi x IN lc ==> moi_s35_n x < &1 / &16)`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  MP_TAC(ISPECL [`du:real^N->bool`; `bdu:real^N->bool`; `dv:real^N->bool`;
                 `bdv:real^N->bool`; `jp:real^N->bool`; `m:real^N`] MOI_S5H_BASE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^3->real^N` (X_CHOOSE_THEN `q0:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(p0:real^3->real^N) continuous_on moi_s35_cube /\
    (!x. x IN moi_s35_cube ==> (q0:real^N->real^3) (p0 x) = x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,du UNION dv:real^N->bool)
                   ((p0:real^3->real^N),(q0:real^N->real^3))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s35_mid SUBSET moi_s35_cube /\ (vec 0:real^3) IN moi_s35_mid /\
    moi_s35_lower SUBSET moi_s35_cube /\ moi_s35_upper SUBSET moi_s35_cube /\
    moi_s35_slab SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [MP_TAC MOI_S5H_MID_RELINT THEN
    MP_TAC(ISPEC `moi_s35_mid` RELATIVE_INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC [`moi_s35_lower UNION moi_s35_upper = moi_s35_cube`;
                           `moi_s35_lower INTER moi_s35_upper = moi_s35_mid`] THEN
    REWRITE_TAC[moi_s35_slab] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `hh = {x:real^3 | x$1 >= &1 / &16} UNION {x | x$1 <= --(&1 / &16)} UNION
                   {x | x$2 >= &1 / &16} UNION {x | x$2 <= --(&1 / &16)}` THEN
  ABBREV_TAC `kk = {x | x IN moi_s35_cube /\
                        (p0:real^3->real^N) x IN (:real^N) DIFF w} UNION
                   {x | x IN moi_s35_cube INTER hh /\ p0 x IN lc}` THEN
  SUBGOAL_THEN `compact(kk:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      CONJ_TAC THENL [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN ASM_REWRITE_TAC[]; SET_TAC[]];
      MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
         [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_REWRITE_TAC[];
          EXPAND_TAC "hh" THEN REWRITE_TAC[MOI_S5H_HH_CLOSED]];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (kk:real^3->bool) moi_s35_mid` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION;
                                     IN_ELIM_THM; NOT_IN_EMPTY; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN moi_s35_mid` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p0:real^3->real^N) x IN du INTER dv` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(p0:real^3->real^N) x = p0 (vec 0)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `q0:real^N->real^3`) THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s35_cube /\ (vec 0:real^3) IN moi_s35_cube`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(vec 0:real^3) IN hh` THEN EXPAND_TAC "hh" THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `kk:real^3->bool` MOI_S5H_SLAB_SMALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `c:real` MOI_S5H_SQUEEZE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) moi_s35_cube = moi_s35_cube` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,moi_s35_cube)
                   ((f:real^3->real^3),(g:real^3->real^3))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN moi_s35_slab
        ==> (f:real^3->real^3) x IN moi_s35_cube /\ ~(f x IN kk) /\
            moi_s35_n (f x) = moi_s35_n x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN moi_s35_cube` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_s35_n] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c < abs(((f:real^3->real^3) x)$3)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun t ->
        can (find_term ((=) `kk:real^3->bool`)) (concl t) && is_forall (concl t))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_NOT_LT] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(p0:real^3->real^N) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o (q0:real^N->real^3)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s35_cube` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o];
    ASM_REWRITE_TAC[IMAGE_o];
    ASM_REWRITE_TAC[o_THM];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "kk" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
    MESON_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `y = (f:real^3->real^3) x` THEN
    EXPAND_TAC "kk" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `y:real^3` MOI_S5H_RF_LATERAL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lo")
      (CONJUNCTS_THEN2 (LABEL_TAC "up") (LABEL_TAC "md"))) THEN
    SUBGOAL_THEN `~((p0:real^3->real^N) y IN du INTER dv) \/ (y:real^3)$3 = &0`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `(y:real^3)$3 = &0` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `?z. z IN moi_s35_mid /\ (p0:real^3->real^N) z = p0 y`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `z:real^3 = y` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o AP_TERM `q0:real^N->real^3`) THEN
        SUBGOAL_THEN `(z:real^3) IN moi_s35_cube` ASSUME_TAC THENL
         [ASM SET_TAC[]; ASM_SIMP_TAC[]];
        UNDISCH_TAC `(y:real^3) IN moi_s35_mid` THEN
        ASM_REWRITE_TAC[moi_s35_mid; IN_ELIM_THM]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^3)$3 = &0` THENL
     [SUBGOAL_THEN `(y:real^3) IN relative_frontier moi_s35_mid` ASSUME_TAC THENL
       [USE_THEN "md" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(p0:real^3->real^N) y IN jp` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (p0:real^3->real^N) (relative_frontier moi_s35_mid) = jp` THEN
        UNDISCH_TAC `(y:real^3) IN relative_frontier moi_s35_mid` THEN SET_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^3)$3 <= &0` THENL
     [SUBGOAL_THEN `(y:real^3) IN relative_frontier moi_s35_lower` ASSUME_TAC THENL
       [USE_THEN "lo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(p0:real^3->real^N) y IN bdu` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (p0:real^3->real^N) (relative_frontier moi_s35_lower) = bdu` THEN
        UNDISCH_TAC `(y:real^3) IN relative_frontier moi_s35_lower` THEN SET_TAC[];
        ASM SET_TAC[]];
      SUBGOAL_THEN `(y:real^3) IN relative_frontier moi_s35_upper` ASSUME_TAC THENL
       [USE_THEN "up" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(p0:real^3->real^N) y IN bdv` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (p0:real^3->real^N) (relative_frontier moi_s35_upper) = bdv` THEN
        UNDISCH_TAC `(y:real^3) IN relative_frontier moi_s35_upper` THEN SET_TAC[];
        ASM SET_TAC[]]];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "kk" THEN EXPAND_TAC "hh" THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_INTER] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[moi_s35_n] THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 7. Graph facts (ends of edges, finitely many edges at a vertex) and the  *)
(* separation sets.  moi_s5h_near p f: the points closer to p than to f     *)
(* (everything when f is empty).  moi_s5h_far t l a b: the parts of the     *)
(* dual cells of a and b shared with dual cells of other vertices.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S5H_ENDS_IN = prove
 (`!(t:(real^N->bool)->bool) l u w.
     graph_in_complex t l /\ segment[u,w] IN l ==> {u} IN l /\ {w} IN l`,
  REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `segment[u:real^N,w]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_S5H_EDGE_ENDS = prove
 (`!(t:(real^N->bool)->bool) l e.
     graph_in_complex t l /\ moi_s35_edge l e
     ==> ?a b. {a} IN l /\ {b} IN l /\ ~(a = b) /\ e = segment[a,b]`,
  REWRITE_TAC[moi_s35_edge] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 simplex (e:real^N->bool)` MP_TAC THENL
   [UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex; lf_simplicial_complex] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (e:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S5H_ENDS_IN THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
  ASM_MESON_TAC[]);;

let MOI_S5H_NBRS_FINITE = prove
 (`!(t:(real^N->bool)->bool) l u.
     graph_in_complex t l /\ {u} IN l
     ==> FINITE {w | ~(w = u) /\ segment[u,w] IN l}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `u:real^N`] MOI_FN1_FAR_ENDS_CARD) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
  REWRITE_TAC[graph_in_complex; simplicial_subcomplex; lf_simplicial_complex] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `open:(real^N->bool)->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
    REWRITE_TAC[IN_SING] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{s:real^N->bool | s IN t /\ ~(s INTER v = {})}` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let moi_s5h_near = new_definition
 `moi_s5h_near (p:real^N->bool) (f:real^N->bool) =
    {x | f = {} \/ setdist({x},p) < setdist({x},f)}`;;

let MOI_S5H_NEAR_OPEN = prove
 (`!p f:real^N->bool. open(moi_s5h_near p f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5h_near] THEN
  ASM_CASES_TAC `f:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SET_RULE `{x:real^N | T} = UNIV`; OPEN_UNIV] THEN
  SUBGOAL_THEN
   `{x:real^N | setdist({x},p) < setdist({x},f)} =
    {x | (\x. lift(setdist({x},p)) - lift(setdist({x},f))) x IN {y:real^1 | y$1 < &0}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; VECTOR_SUB_COMPONENT; LIFT_COMPONENT] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC[CONTINUOUS_AT_LIFT_SETDIST]]);;

let MOI_S5H_NEAR_CONTAINS = prove
 (`!p f:real^N->bool. closed f /\ DISJOINT p f ==> p SUBSET moi_s5h_near p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; moi_s5h_near; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `f:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SETDIST_SING_IN_SET] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ ~(a = &0) ==> &0 < a`) THEN
  ASM_SIMP_TAC[SETDIST_POS_LE; SETDIST_EQ_0_CLOSED] THEN ASM SET_TAC[]);;

let MOI_S5H_NEAR_FAR = prove
 (`!p f:real^N->bool. DISJOINT (moi_s5h_near p f) f`,
  REWRITE_TAC[DISJOINT] THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; moi_s5h_near; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN f` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(f:real^N->bool = {})` (fun t -> REWRITE_TAC[t]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SETDIST_SING_IN_SET; REAL_NOT_LT; SETDIST_POS_LE]);;

let MOI_S5H_NEAR_DISJ = prove
 (`!p f p' f':real^N->bool.
     ~(p = {}) /\ ~(p' = {}) /\ p' SUBSET f /\ p SUBSET f'
     ==> DISJOINT (moi_s5h_near p f) (moi_s5h_near p' f')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(f:real^N->bool = {}) /\ ~(f':real^N->bool = {})` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DISJOINT] THEN ONCE_REWRITE_TAC[EXTENSION] THEN
  ASM_REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; moi_s5h_near; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`{x:real^N}`; `p':real^N->bool`; `f:real^N->bool`]
    SETDIST_SUBSET_RIGHT) THEN
  MP_TAC(ISPECL [`{x:real^N}`; `p:real^N->bool`; `f':real^N->bool`]
    SETDIST_SUBSET_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let moi_s5h_far = new_definition
 `moi_s5h_far (t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (a:real^N) b =
    UNIONS {derived_dual_cell t l y INTER derived_dual_cell t l z | y,z |
            (y = a \/ y = b) /\ {z} IN l /\ ~(z = a) /\ ~(z = b)}`;;

let MOI_S5H_FAR_SUB = prove
 (`!(t:(real^N->bool)->bool) l a b y z.
     (y = a \/ y = b) /\ {z} IN l /\ ~(z = a) /\ ~(z = b)
     ==> derived_dual_cell t l y INTER derived_dual_cell t l z SUBSET
         moi_s5h_far t l a b`,
  REWRITE_TAC[moi_s5h_far; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S5H_FAR_COMPACT = prove
 (`!(t:(real^N->bool)->bool) l a b.
     graph_in_complex t l /\ {a} IN l /\ {b} IN l /\
     (!v. {v} IN l ==> compact(derived_dual_cell t l v)) /\
     (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
            ==> derived_dual_cell t l u INTER derived_dual_cell t l v = {})
     ==> compact(moi_s5h_far t l a b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s5h_far t l a (b:real^N) =
    UNIONS (IMAGE (\z. derived_dual_cell t l a INTER derived_dual_cell t l z)
                  {z | ~(z = a) /\ segment[a,z] IN l /\ ~(z = b)} UNION
            IMAGE (\z. derived_dual_cell t l b INTER derived_dual_cell t l z)
                  {z | ~(z = b) /\ segment[b,z] IN l /\ ~(z = a)})`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_s5h_far] THEN ONCE_REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNION; IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `z:real^N`
          (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) ASSUME_TAC)))
        ASSUME_TAC)) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `segment[y:real^N,z] IN l` ASSUME_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        SUBGOAL_THEN `derived_dual_cell t l (y:real^N) INTER derived_dual_cell t l z = {}`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
          ASM SET_TAC[]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
      ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_S5H_ENDS_IN]];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `{z | ~(z = a) /\ segment[a:real^N,z] IN l}`;
      EXISTS_TAC `{z | ~(z = b) /\ segment[b:real^N,z] IN l}`] THEN
    (CONJ_TAC THENL [MATCH_MP_TAC MOI_S5H_NBRS_FINITE THEN
                     EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
                     SET_TAC[]]);
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_INTER THEN
    ASM_MESON_TAC[MOI_S5H_ENDS_IN]]);;

let MOI_S5H_FAR_DISJOINT = prove
 (`!(t:(real^N->bool)->bool) l a b.
     (!z. {z} IN l /\ ~(z = a) /\ ~(z = b)
          ==> derived_dual_cell t l a INTER derived_dual_cell t l b INTER
              derived_dual_cell t l z = {})
     ==> DISJOINT (derived_dual_cell t l a INTER derived_dual_cell t l b)
                  (moi_s5h_far t l a b)`,
  REWRITE_TAC[moi_s5h_far; DISJOINT; EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM;
              NOT_IN_EMPTY] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN
  ASM_MESON_TAC[IN_INTER]);;

(* ------------------------------------------------------------------------- *)
(* 8. The chart of one edge of the graph (EDGE with the dual cells of the   *)
(* ends, w = the open sets of g at both ends and the near set, lc = the     *)
(* graph in the two cells).                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S5H_MID_NOT_FRONTIER = prove
 (`!(t:(real^N->bool)->bool) l a b.
     graph_in_complex t l /\ segment[a,b] IN l
     ==> ~(midpoint(a,b) IN derived_frontier t l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[graph_in_complex] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FTA_FRONTIER_IFF] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `midpoint(a:real^N,b) IN UNIONS l` MP_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[a:real^N,b]` THEN
    ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    ASM SET_TAC[]]);;

let MOI_S5H_GRAPH_EDGE = prove
 (mk_imp(mk_conj(MOI_FND_GRAPH_TUBE,MOI_S35_TUBE_TRIPLE),
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) a b.
     graph_in_complex t l /\
     (!v. {v} IN l ==> open_in (subtopology euclidean (UNIONS t)) (g v) /\
                       derived_dual_cell t l v SUBSET g v) /\
     ~(a = b) /\ segment[a,b] IN l
     ==> ?psi q. pl_homeomorphism
                   (moi_s35_cube,derived_dual_cell t l a UNION derived_dual_cell t l b)
                   (psi,q) /\
                 IMAGE psi moi_s35_lower = derived_dual_cell t l a /\
                 IMAGE psi moi_s35_upper = derived_dual_cell t l b /\
                 psi (vec 0) = midpoint(a,b) /\
                 IMAGE psi moi_s35_slab SUBSET g a INTER g b /\
                 IMAGE psi {x | x IN moi_s35_slab /\ moi_s35_n x = &1}
                   SUBSET derived_frontier t l /\
                 (!x. x IN moi_s35_slab /\ psi x IN UNIONS l
                      ==> moi_s35_n x < &1 / &16) /\
                 IMAGE psi moi_s35_slab SUBSET
                   moi_s5h_near (derived_dual_cell t l a INTER derived_dual_cell t l b)
                                (moi_s5h_far t l a b)`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tube") (LABEL_TAC "triple")) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `g:real^N->real^N->bool`; `a:real^N`; `b:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "g")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `{a:real^N} IN l /\ {b:real^N} IN l` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5H_ENDS_IN THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "tube" (MP_TAC o C MATCH_MP (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "vtx")
    (CONJUNCTS_THEN2 (LABEL_TAC "edg") (LABEL_TAC "non")))) THEN
  USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{a:real^N} IN l`)) THEN STRIP_TAC THEN
  USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{b:real^N} IN l`)) THEN STRIP_TAC THEN
  USE_THEN "edg" (MP_TAC o C MATCH_MP (CONJ (ASSUME `~(a:real^N = b)`)
    (ASSUME `segment[a:real^N,b] IN l`))) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v. {v} IN l ==> compact(derived_dual_cell t l (v:real^N))`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`)) THEN
    MESON_TAC[MOI_CEL_CELL_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed(moi_s5h_far t l a (b:real^N)) /\
    DISJOINT (derived_dual_cell t l a INTER derived_dual_cell t l b)
             (moi_s5h_far t l a b)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S5H_FAR_COMPACT THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "non" ACCEPT_TAC;
      MATCH_MP_TAC MOI_S5H_FAR_DISJOINT THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
      USE_THEN "triple" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "g" (MP_TAC o C MATCH_MP (ASSUME `{a:real^N} IN l`)) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `oa:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  USE_THEN "g" (MP_TAC o C MATCH_MP (ASSUME `{b:real^N} IN l`)) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `ob:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`derived_dual_cell t l (a:real^N)`;
    `(derived_dual_cell t l a INTER derived_frontier t l) UNION
     UNIONS {derived_dual_cell t l a INTER derived_dual_cell t l w | w |
             ~(w = a) /\ segment[a:real^N,w] IN l}`;
    `derived_dual_cell t l (b:real^N)`;
    `(derived_dual_cell t l b INTER derived_frontier t l) UNION
     UNIONS {derived_dual_cell t l b INTER derived_dual_cell t l w | w |
             ~(w = b) /\ segment[b:real^N,w] IN l}`;
    `derived_dual_cell t l a INTER derived_dual_cell t l b INTER
     derived_frontier t l:real^N->bool`;
    `midpoint(a:real^N,b)`;
    `oa INTER ob INTER
     moi_s5h_near (derived_dual_cell t l a INTER derived_dual_cell t l b)
                  (moi_s5h_far t l a (b:real^N))`;
    `(derived_dual_cell t l a INTER UNIONS l) UNION
     (derived_dual_cell t l (b:real^N) INTER UNIONS l)`;
    `derived_frontier (t:(real^N->bool)->bool) l`] MOI_S5H_EDGE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `derived_dual_cell t l a INTER derived_dual_cell t l (b:real^N)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `b:real^N` THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `derived_dual_cell t l b INTER derived_dual_cell t l (a:real^N)` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      UNDISCH_TAC `derived_dual_cell t l a INTER derived_dual_cell t l b INTER UNIONS l =
                   {midpoint(a:real^N,b)}` THEN SET_TAC[];
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`;
                     `b:real^N`] MOI_S5H_MID_NOT_FRONTIER) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[];
      ASM_SIMP_TAC[OPEN_INTER; MOI_S5H_NEAR_OPEN];
      MP_TAC(ISPECL [`derived_dual_cell t l a INTER derived_dual_cell t l (b:real^N)`;
                     `moi_s5h_far t l a (b:real^N)`] MOI_S5H_NEAR_CONTAINS) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`derived_dual_cell t l (a:real^N) SUBSET g a`;
        `derived_dual_cell t l (b:real^N) SUBSET g b`;
        `(g:real^N->real^N->bool) a = UNIONS t INTER oa`;
        `(g:real^N->real^N->bool) b = UNIONS t INTER ob`] THEN
      SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_INTER] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `w:real^N = b` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM SET_TAC[];
        SUBGOAL_THEN `(x:real^N) IN moi_s5h_far t l a b` MP_TAC THENL
         [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`;
                         `b:real^N`; `a:real^N`; `w:real^N`] MOI_S5H_FAR_SUB) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[MOI_S5H_ENDS_IN]; ASM SET_TAC[]];
          MP_TAC(ISPECL [`derived_dual_cell t l a INTER derived_dual_cell t l (b:real^N)`;
                         `moi_s5h_far t l a (b:real^N)`] MOI_S5H_NEAR_FAR) THEN
          SET_TAC[]]];
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_INTER] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `w:real^N = a` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM SET_TAC[];
        SUBGOAL_THEN `(x:real^N) IN moi_s5h_far t l a b` MP_TAC THENL
         [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`;
                         `b:real^N`; `b:real^N`; `w:real^N`] MOI_S5H_FAR_SUB) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[MOI_S5H_ENDS_IN]; ASM SET_TAC[]];
          MP_TAC(ISPECL [`derived_dual_cell t l a INTER derived_dual_cell t l (b:real^N)`;
                         `moi_s5h_far t l a (b:real^N)`] MOI_S5H_NEAR_FAR) THEN
          SET_TAC[]]];
      MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_INSERT THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; CLOSED_SEGMENT] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC MOI_S5H_NBRS_FINITE THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `derived_dual_cell t l a INTER derived_dual_cell t l b INTER UNIONS l =
                   {midpoint(a:real^N,b)}` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^N` (X_CHOOSE_THEN `q:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->real^N) moi_s35_slab SUBSET
                derived_dual_cell t l a UNION derived_dual_cell t l b` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (psi:real^3->real^N) moi_s35_cube` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[moi_s35_slab] THEN SET_TAC[];
      UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,
                     derived_dual_cell t l a UNION derived_dual_cell t l b)
                     ((psi:real^3->real^N),(q:real^N->real^3))` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism; SUBSET_REFL]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`psi:real^3->real^N`; `q:real^N->real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (psi:real^3->real^N) moi_s35_slab SUBSET
       derived_dual_cell t l a UNION derived_dual_cell t l b`;
      `IMAGE (psi:real^3->real^N) moi_s35_slab SUBSET
       oa INTER ob INTER
       moi_s5h_near (derived_dual_cell t l a INTER derived_dual_cell t l b)
                    (moi_s5h_far t l a (b:real^N))`;
      `derived_dual_cell t l (a:real^N) SUBSET UNIONS {s | s IN t /\ a IN s}`;
      `derived_dual_cell t l (b:real^N) SUBSET UNIONS {s | s IN t /\ b IN s}`;
      `(g:real^N->real^N->bool) a = UNIONS t INTER oa`;
      `(g:real^N->real^N->bool) b = UNIONS t INTER ob`] THEN
    SET_TAC[];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `moi_s35_n`)) (concl th))) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (psi:real^3->real^N) moi_s35_slab SUBSET
       derived_dual_cell t l a UNION derived_dual_cell t l b`;
      `(x:real^3) IN moi_s35_slab`; `(psi:real^3->real^N) x IN UNIONS l`] THEN
    SET_TAC[];
    UNDISCH_TAC
     `IMAGE (psi:real^3->real^N) moi_s35_slab SUBSET
      oa INTER ob INTER
      moi_s5h_near (derived_dual_cell t l a INTER derived_dual_cell t l b)
                   (moi_s5h_far t l a (b:real^N))` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. Slabs of distinct edges are disjoint, and the theorem CHARTS.         *)
(* ------------------------------------------------------------------------- *)

let MOI_S5H_P_SUB_FAR = prove
 (`!(t:(real^N->bool)->bool) l a b c d.
     {c} IN l /\ {d} IN l /\ ~(c = d) /\ ~({a,b} = {c,d}) /\
     ~(DISJOINT {a,b} {c,d})
     ==> derived_dual_cell t l c INTER derived_dual_cell t l d SUBSET
         moi_s5h_far t l a b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((c:real^N) = a \/ c = b) /\ ~(d = a) /\ ~(d = b) \/
    (d = a \/ d = b) /\ ~(c = a) /\ ~(c = b)`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THENL
   [MATCH_MP_TAC MOI_S5H_FAR_SUB THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC MOI_S5H_FAR_SUB THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S5H_SLABS_DISJOINT = prove
 (`!(t:(real^N->bool)->bool) l a b c d.
     graph_in_complex t l /\
     ~(a = b) /\ segment[a,b] IN l /\ ~(c = d) /\ segment[c,d] IN l /\
     ~(segment[a,b] = segment[c,d]) /\
     ~(derived_dual_cell t l a INTER derived_dual_cell t l b = {}) /\
     ~(derived_dual_cell t l c INTER derived_dual_cell t l d = {})
     ==> DISJOINT
          ((derived_dual_cell t l a UNION derived_dual_cell t l b) INTER
           moi_s5h_near (derived_dual_cell t l a INTER derived_dual_cell t l b)
                        (moi_s5h_far t l a b))
          ((derived_dual_cell t l c UNION derived_dual_cell t l d) INTER
           moi_s5h_near (derived_dual_cell t l c INTER derived_dual_cell t l d)
                        (moi_s5h_far t l c d))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a:real^N} IN l /\ {b} IN l /\ {c} IN l /\ {d} IN l`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_S5H_ENDS_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `~({a:real^N,b} = {c,d})` ASSUME_TAC THENL
   [ASM_MESON_TAC[SEGMENT_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `DISJOINT {a:real^N,b} {c,d}` THENL
   [SUBGOAL_THEN `~(a:real^N = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT] THEN ONCE_REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)
                               (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `?u y. (u = a \/ u = b) /\ (y:real^N = c \/ y = d) /\
            x IN derived_dual_cell t l u /\ x IN derived_dual_cell t l y`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `y:real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `(x:real^N) IN moi_s5h_far t l a b` MP_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`;
                     `b:real^N`; `u:real^N`; `y:real^N`] MOI_S5H_FAR_SUB) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
      MP_TAC(ISPECL [`derived_dual_cell t l a INTER derived_dual_cell t l (b:real^N)`;
                     `moi_s5h_far t l a (b:real^N)`] MOI_S5H_NEAR_FAR) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `DISJOINT (s:real^N->bool) t ==> DISJOINT (u INTER s) (v INTER t)`) THEN
  MATCH_MP_TAC MOI_S5H_NEAR_DISJ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_S5H_P_SUB_FAR THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[DISJOINT_SYM]);;

let CHARTS = prove
 (MOI_S35_CHARTS,
  DISCH_THEN(LABEL_TAC "hyp") THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `g:real^N->real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g")) THEN
  SUBGOAL_THEN `(vec 0:real^3) IN moi_s35_lower /\ vec 0 IN moi_s35_upper /\
                moi_s35_slab SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [MP_TAC MOI_S5H_MID_RELINT THEN
    MP_TAC(ISPEC `moi_s35_mid` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC MOI_S5H_MODEL THEN REWRITE_TAC[moi_s35_slab] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. ?a b psi.
      moi_s35_edge l e
      ==> {a} IN l /\ {b} IN l /\ ~(a = b) /\ e = segment[a,b] /\
          (?q. pl_homeomorphism
                 (moi_s35_cube,derived_dual_cell t l a UNION derived_dual_cell t l b)
                 (psi,q)) /\
          IMAGE psi moi_s35_lower = derived_dual_cell t l a /\
          IMAGE psi moi_s35_upper = derived_dual_cell t l b /\
          psi (vec 0) = midpoint(a,b) /\
          IMAGE psi moi_s35_slab SUBSET g a INTER g b /\
          IMAGE psi {x | x IN moi_s35_slab /\ moi_s35_n x = &1}
            SUBSET derived_frontier t l /\
          (!x. x IN moi_s35_slab /\ psi x IN UNIONS l ==> moi_s35_n x < &1 / &16) /\
          IMAGE psi moi_s35_slab SUBSET
            (derived_dual_cell t l a UNION derived_dual_cell t l b) INTER
            moi_s5h_near (derived_dual_cell t l a INTER derived_dual_cell t l b)
                         (moi_s5h_far t l a (b:real^N)) /\
          ~(derived_dual_cell t l a INTER derived_dual_cell t l b = {})`
  MP_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN
    ASM_CASES_TAC `moi_s35_edge l (e:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `e:real^N->bool`] MOI_S5H_EDGE_ENDS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `segment[a:real^N,b] IN l` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s35_edge l (e:real^N->bool)` THEN
      ASM_REWRITE_TAC[moi_s35_edge] THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "hyp" (MP_TAC o MATCH_MP MOI_S5H_GRAPH_EDGE) THEN
    DISCH_THEN(MP_TAC o SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                               `g:real^N->real^N->bool`; `a:real^N`; `b:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "g" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^N` (X_CHOOSE_THEN `q:real^N->real^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `IMAGE (p:real^3->real^N) moi_s35_cube =
                  derived_dual_cell t l a UNION derived_dual_cell t l b`
    ASSUME_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,
                     derived_dual_cell t l a UNION derived_dual_cell t l b)
                     ((p:real^3->real^N),(q:real^N->real^3))` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `p:real^3->real^N`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `q:real^N->real^3` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE
       `!c. IMAGE (p:real^3->real^N) s SUBSET n /\ s SUBSET c /\ IMAGE p c = d
            ==> IMAGE p s SUBSET d INTER n`) THEN
      EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE
       `!z:real^N. z IN s /\ z IN t ==> ~(s INTER t = {})`) THEN
      EXISTS_TAC `(p:real^3->real^N) (vec 0)` THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (p:real^3->real^N) moi_s35_lower = derived_dual_cell t l a`;
        `IMAGE (p:real^3->real^N) moi_s35_upper = derived_dual_cell t l b`;
        `(vec 0:real^3) IN moi_s35_lower`; `(vec 0:real^3) IN moi_s35_upper`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `av:(real^N->bool)->real^N`
    (X_CHOOSE_THEN `bv:(real^N->bool)->real^N`
      (X_CHOOSE_THEN `psi:(real^N->bool)->real^3->real^N` (LABEL_TAC "ch")))) THEN
  MAP_EVERY EXISTS_TAC [`av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                        `psi:(real^N->bool)->real^3->real^N`] THEN
  REWRITE_TAC[moi_s35_charts] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "ch" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    EXISTS_TAC `q:real^N->real^3` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `e':real^N->bool`] THEN STRIP_TAC THEN
  USE_THEN "ch" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
  USE_THEN "ch" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e':real^N->bool)`)) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `(av:(real^N->bool)->real^N) e`; `(bv:(real^N->bool)->real^N) e`;
                 `(av:(real^N->bool)->real^N) e'`; `(bv:(real^N->bool)->real^N) e'`]
    MOI_S5H_SLABS_DISJOINT) THEN
  SUBGOAL_THEN `segment[(av:(real^N->bool)->real^N) e,bv e] = e /\
                segment[(av:(real^N->bool)->real^N) e',bv e'] = e'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s35_edge l (e:real^N->bool)` THEN
    UNDISCH_TAC `moi_s35_edge l (e':real^N->bool)` THEN
    REWRITE_TAC[moi_s35_edge] THEN SIMP_TAC[];
    MATCH_MP_TAC(SET_RULE
     `(s:real^N->bool) SUBSET u /\ t SUBSET v ==> DISJOINT u v ==> DISJOINT s t`) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

