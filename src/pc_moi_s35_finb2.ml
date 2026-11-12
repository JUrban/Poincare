(* ========================================================================= *)
(* pc_moi_s35_finb2: the Sec 35 unit s35_fin_b, part 2, main theorem        *)
(* MOI_S5P_FINAL_R3 : |- MOI_S35_FINAL_R3 (pc_moi_s35_stmt_r3.ml): the PL   *)
(* embedding of the derived neighbourhood N of the graph with f(C_v) = D_v  *)
(* (the final cells of FINAL_CELLS).  Per vertex v: f_v on the core, an     *)
(* A-side squeeze (TWO_DISK_EXT on a model box, the top square onto the     *)
(* planar disk of the single circle) near each A-side edge, a B-side piece  *)
(* (TWO_DISK_EXT onto the side of D_v cut by the B-chart level square,      *)
(* SPLIT_BALL) near each B-side edge; the maps agree on the splitting disks *)
(* and paste.  The invariance-of-domain tools of pc_moi_s35_approx are      *)
(* reused.                                                                  *)
(* ========================================================================= *)

needs "src/pc_moi_s35_finb1.ml";;
needs "src/pc_moi_s35_approx.ml";;
needs "src/pc_moi_s35_stmt_r3.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. A chart of a planar polygonal disk around a central square: if the    *)
(* square of radius 3/16 lies inside the PL circle j, the square [-2,2]^2   *)
(* maps PL onto j UNION inside j, boundary onto j, by y -> y / 8 on the     *)
(* unit square (the outer part by the annulus chart MOI_S5C_ANN_INNER).      *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_SQ_SCALE = prove
 (`!c. &0 < c
       ==> pl_homeomorphism
             (interval[--vector[&1;&1]:real^2,vector[&1;&1]],
              interval[--vector[c;c],vector[c;c]])
             ((\x. c % x),(\x. inv c % x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  SUBGOAL_THEN `!x:real^2. inv c % c % x = x /\ c % inv c % x = x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                 VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:real^2. max (abs((c % x)$1)) (abs((c % x)$2)) = c * max (abs(x$1)) (abs(x$2))) /\
    (!x:real^2. max (abs((inv c % x)$1)) (abs((inv c % x)$2)) =
                inv c * max (abs(x$1)) (abs(x$2)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S5C_N2_CMUL; REAL_LT_IMP_LE; REAL_LE_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(!m. c * m <= c <=> m <= &1) /\ (!m. inv c * m <= &1 <=> m <= c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
    ASM_REWRITE_TAC[EXTENSION; IN_IMAGE; MOI_S5C_IN_SQI] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `inv c % (x:real^2)` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `c % (x:real^2)` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_S5C_PL_LINEAR THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL] THEN
    REWRITE_TAC[linear; VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_SYM]]);;

let MOI_S5P_DISK_CHART = prove
 (`!j:real^2->bool.
     pl_sphere 1 j /\
     (!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN inside j)
     ==> ?t t'. pl_homeomorphism
                  (interval[--vector[&2;&2],vector[&2;&2]],j UNION inside j) (t,t') /\
                (!y. y IN interval[--vector[&1;&1],vector[&1;&1]]
                     ==> t y = (&1 / &8) % y) /\
                IMAGE t (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])) = j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&1 / &8` MOI_S5C_SQ_JORDAN) THEN
  ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier(interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]]) =
    interval[--vector[&1 / &8;&1 / &8],vector[&1 / &8;&1 / &8]] DIFF
    interval(--vector[&1 / &8;&1 / &8],vector[&1 / &8;&1 / &8])`
  (ASSUME_TAC o SYM) THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_FRONTIER_NONEMPTY_INTERIOR o
      lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MOI_S5C_SQ_INTERIOR THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FRONTIER_CLOSED_INTERVAL]];
    ALL_TAC] THEN
  ABBREV_TAC `k = relative_frontier(interval[--vector[&1 / &8;&1 / &8]:real^2,
                                              vector[&1 / &8;&1 / &8]])` THEN
  SUBGOAL_THEN `interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]]
                SUBSET inside j` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_S5C_IN_SQI] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^2->bool) SUBSET inside j` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]] SUBSET inside j`;
      `interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]] DIFF
           interval(--vector[&1 / &8;&1 / &8],vector[&1 / &8;&1 / &8]) = k`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(j:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
    MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `j:real^2->bool`] MOI_S5C_ANN2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`&1`; `&1 / &8`] MOI_S5C_SQ_RF_SCALE) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(j UNION inside j) DIFF
                  interval(--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8])`;
                 `k:real^2->bool`;
                 `j:real^2->bool`; `\x:real^2. (&1 / &8) % x`;
                 `\x:real^2. &8 % x`] MOI_S5C_ANN_INNER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM)))))) THEN
  MP_TAC(SPEC `&1 / &8` MOI_S5P_SQ_SCALE) THEN
  ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN
   `closed((j UNION inside j) DIFF
           interval(--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8])) /\
    interval[--vector[&1;&1]:real^2,vector[&1;&1]] INTER
    (interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1])) =
    relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) /\
    interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]] INTER
    ((j UNION inside j) DIFF
     interval(--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8])) = k /\
    interval[--vector[&1;&1]:real^2,vector[&1;&1]] UNION
    (interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1])) =
    interval[--vector[&2;&2],vector[&2;&2]] /\
    interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]] UNION
    ((j UNION inside j) DIFF
     interval(--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8])) =
    j UNION inside j /\
    relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) INTER
    interval[--vector[&1;&1],vector[&1;&1]] = {}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      REWRITE_TAC[UNION_WITH_INSIDE; GSYM OPEN_CLOSED] THEN
      MATCH_MP_TAC OPEN_OUTSIDE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF] THEN
      SIMP_TAC[MOI_S5C_IN_SQI; MOI_S5C_IN_SQO; MOI_S5C_SQ_RF; REAL_LT_01] THEN
      REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]] SUBSET
         inside j`;
        `interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]] DIFF
             interval(--vector[&1 / &8;&1 / &8],vector[&1 / &8;&1 / &8]) = k`] THEN
      SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF] THEN
      REWRITE_TAC[MOI_S5C_IN_SQI; MOI_S5C_IN_SQO] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`--vector[&1 / &8;&1 / &8]:real^2`; `vector[&1 / &8;&1 / &8]:real^2`]
        INTERVAL_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC
       `interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]] SUBSET
        inside j` THEN
      SET_TAC[];
      SIMP_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; MOI_S5C_IN_SQI; MOI_S5C_SQ_RF;
               REAL_ARITH `&0 < &2`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval[--vector[&1;&1]:real^2,vector[&1;&1]]`;
                 `interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                  interval(--vector[&1;&1],vector[&1;&1])`;
                 `interval[--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8]]`;
                 `(j UNION inside j) DIFF
                  interval(--vector[&1 / &8;&1 / &8]:real^2,vector[&1 / &8;&1 / &8])`;
                 `\x:real^2. (&1 / &8) % x`; `\x:real^2. inv(&1 / &8) % x`;
                 `f:real^2->real^2`; `g:real^2->real^2`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ASM_REWRITE_TAC[CLOSED_INTERVAL] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_INTERVAL; OPEN_INTERVAL];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN BETA_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `pl_homeomorphism
         (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]),k)
         ((\x. &1 / &8 % x),(\x. &8 % x))` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^2. if x IN interval[--vector[&1;&1],vector[&1;&1]] then &1 / &8 % x
                else (f:real^2->real^2) x`;
    `\y:real^2. if y IN interval[--vector[&1 / &8;&1 / &8],vector[&1 / &8;&1 / &8]]
                then inv(&1 / &8) % y else (g:real^2->real^2) y`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^2)
                 (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])) = j`
    (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> (u:real^2->real^2) x = v x)
                         ==> IMAGE u s = IMAGE v s`) THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `~((x:real^2) IN interval[--vector[&1;&1],vector[&1;&1]])`
    (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) INTER
               interval[--vector[&1;&1],vector[&1;&1]] = {}` THEN
  UNDISCH_TAC `(x:real^2) IN relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. The A-side squeeze (model): a PL homeomorphism of the box             *)
(* -1/8 <= x3 <= 0 of the model cube onto the box -1/8 <= x3 <= c, the      *)
(* identity on the bottom face and the disk chart (lifted to the level c)   *)
(* on the middle square; it is (x1/4, x2/4, c) near the centre of the       *)
(* middle square.  By TWO_DISK_EXT with explicit local extensions (the      *)
(* identity and an affine map with positive determinant).                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_LIN_AT_AFFINE = prove
 (`!(l:real^3->real^3) b x m.
     linear l /\ moi_s35_lin_at (\z. l z + b) x m ==> m = l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_lin_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + (r / &2) % basis i:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^3,x + y) = norm y`] THEN
    ASM_SIMP_TAC[NORM_MUL; NORM_BASIS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[VECTOR_ARITH `(x + y) - x:real^3 = y`] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + b) + c:real^3 = (a + c) + d <=> b = d`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. inv(r / &2) % v`) THEN
  BETA_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `inv(r / &2) * r / &2 = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN MESON_TAC[]);;

let MOI_S5P_BOX = prove
 (`!a b. a < b
         ==> pl_ball 3 (interval[vector[-- &1;-- &1;a]:real^3,vector[&1;&1;b]]) /\
             (!x:real^3. x IN interval[vector[-- &1;-- &1;a],vector[&1;&1;b]] <=>
                         abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ a <= x$3 /\ x$3 <= b) /\
             (!x:real^3. x IN frontier(interval[vector[-- &1;-- &1;a],vector[&1;&1;b]]) <=>
                         (abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ a <= x$3 /\ x$3 <= b) /\
                         (abs(x$1) = &1 \/ abs(x$2) = &1 \/ x$3 = a \/ x$3 = b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3
                    ==> (vector[-- &1;-- &1;a]:real^3)$i < (vector[&1;&1;b]:real^3)$i`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_3; VECTOR_3] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`vector[-- &1;-- &1;a]:real^3`; `vector[&1;&1;b]:real^3`]
      MOI_S5N_BOX_CELL) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[];
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC;
    REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; IN_DIFF; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_3] THEN
    REAL_ARITH_TAC]);;

let MOI_S5P_TOP_MAP = prove
 (`!c j:real^2->bool.
     pl_sphere 1 j /\
     (!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN inside j)
     ==> ?g g'. pl_homeomorphism
                  (moi_s35_mid,IMAGE (moi_s35_lift c) (j UNION inside j)) (g,g') /\
                (!x. x IN moi_s35_mid /\ abs(x$1) <= &1 / &2 /\ abs(x$2) <= &1 / &2
                     ==> g x = vector[x$1 / &4; x$2 / &4; c]) /\
                IMAGE g (IMAGE (moi_s35_lift (&0))
                   (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) =
                IMAGE (moi_s35_lift c) j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `j:real^2->bool` MOI_S5P_DISK_CHART) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->real^2` (X_CHOOSE_THEN `t':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism (moi_s35_mid,
                  interval[--vector[&1;&1]:real^2,vector[&1;&1]])
                  (moi_s5c_proj,moi_s35_lift (&0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s35_mid`; `&0`] MOI_S5C_LEVEL_PLH) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5C_CELL_POLYHEDRON THEN
        MAP_EVERY EXISTS_TAC [`2`; `IMAGE (moi_s35_lift (&0))
          (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`] THEN
        REWRITE_TAC[GSYM MOI_S5N_MID_SQ; MOI_S5N_SQ];
        REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MOI_S5N_MID_SQ; GSYM IMAGE_o; o_DEF; MOI_S5C_PROJ_LIFT; IMAGE_ID] THEN
    REWRITE_TAC[ETA_AX] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `&2` MOI_S5P_SQ_SCALE) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (j UNION inside j,
                                  IMAGE (moi_s35_lift c) (j UNION inside j))
                                 (moi_s35_lift c,moi_s5c_proj)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    MP_TAC(ISPECL [`IMAGE (moi_s35_lift c) ((j:real^2->bool) UNION inside j)`; `c:real`]
      MOI_S5C_LEVEL_PLH) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5C_CELL_POLYHEDRON THEN
        MAP_EVERY EXISTS_TAC [`2`; `IMAGE (moi_s35_lift c) (j:real^2->bool)`] THEN
        MATCH_MP_TAC MOI_S5C_LIFT_DISK THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE; MOI_S5C_PROJ_LIFT]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_S5C_PROJ_LIFT; IMAGE_ID] THEN
    REWRITE_TAC[ETA_AX] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `moi_s35_lift c o (t:real^2->real^2) o (\x:real^2. &2 % x) o moi_s5c_proj` THEN
  EXISTS_TAC `(((moi_s35_lift (&0) o (\x:real^2. inv(&2) % x)) o (t':real^2->real^2)) o
               moi_s5c_proj)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(j:real^2->bool) UNION inside j` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[--vector[&2;&2]:real^2,vector[&2;&2]]` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[--vector[&1;&1]:real^2,vector[&1;&1]]` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `&2 % moi_s5c_proj x IN interval[--vector[&1;&1]:real^2,vector[&1;&1]]`
    ASSUME_TAC THENL
     [REWRITE_TAC[MOI_S5C_IN_SQI; moi_s5c_proj; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[moi_s35_lift; moi_s5c_proj; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE moi_s5c_proj (IMAGE (moi_s35_lift (&0))
                    (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) =
                  relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_S5C_PROJ_LIFT; IMAGE_ID] THEN
      REWRITE_TAC[ETA_AX; IMAGE_ID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`&1`; `&2`] MOI_S5C_SQ_RF_SCALE) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S5P_PLH_ID = prove
 (`!s:real^N->bool. locally_polyhedral s ==> pl_homeomorphism (s,s) ((\x. x),(\x. x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  REWRITE_TAC[HOMEOMORPHISM_ID] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. x`; `vec 0:real^N`] PL_MAP_ON_AFFINE) THEN
  ASM_REWRITE_TAC[LINEAR_ID; VECTOR_ADD_RID]);;

let MOI_S5P_DET_QUARTER = prove
 (`det(matrix(\x:real^3. vector[x$1 / &4; x$2 / &4; x$3]:real^3)) = &1 / &16`,
  REWRITE_TAC[DET_3] THEN
  SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_3; ARITH; VECTOR_3; BASIS_COMPONENT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

let MOI_S5P_QUARTER_LINEAR = prove
 (`linear (\x:real^3. vector[x$1 / &4; x$2 / &4; x$3]:real^3)`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let MOI_S5P_LIN_AT_AFFINE_EQ = prove
 (`!(f:real^3->real^3) l b x m.
     linear l /\ (!z. f z = l z + b) /\ moi_s35_lin_at f x m ==> m = l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5P_LIN_AT_AFFINE THEN
  MAP_EVERY EXISTS_TAC [`b:real^3`; `x:real^3`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\z. (l:real^3->real^3) z + b) = f` (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[FUN_EQ_THM]);;

let MOI_S5P_BALL_COMP = prove
 (`!(a:real^3) r x.
     x IN ball(a,r)
     ==> abs(x$1 - a$1) < r /\ abs(x$2 - a$2) < r /\ abs(x$3 - a$3) < r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a - x:real^3`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`a - x:real^3`; `2`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`a - x:real^3`; `3`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5P_SQ_LIFT = prove
 (`(!a x:real^3.
      x IN IMAGE (moi_s35_lift a) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) <=>
      x$3 = a /\ abs(x$1) <= &1 /\ abs(x$2) <= &1) /\
   (!a x:real^3.
      x IN IMAGE (moi_s35_lift a)
             (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) <=>
      x$3 = a /\ abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ (abs(x$1) = &1 \/ abs(x$2) = &1))`,
  SIMP_TAC[MOI_S5C_IN_LIFT; moi_s5c_proj; MOI_S5C_IN_SQI; MOI_S5C_SQ_RF; REAL_LT_01;
           VECTOR_2] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5P_SQUEEZE = prove
 (mk_imp(MOI_S35_TWO_DISK_EXT,
  `!c j:real^2->bool.
     abs c <= &1 / &512 /\ pl_sphere 1 j /\
     (!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN inside j) /\
     (!y:real^2. y IN j ==> max (abs(y$1)) (abs(y$2)) <= &5 / &16)
     ==> ?M M' g g'.
           pl_homeomorphism
             (interval[vector[-- &1;-- &1;-- &1 / &8]:real^3,vector[&1;&1;&0]],
              interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;c]]) (M,M') /\
           (!x. x IN interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;&0]] /\
                x$3 = -- &1 / &8 ==> M x = x) /\
           pl_homeomorphism
             (moi_s35_mid,IMAGE (moi_s35_lift c) (j UNION inside j)) (g,g') /\
           (!x. x IN moi_s35_mid ==> M x = g x) /\
           (!x. x IN moi_s35_mid /\ abs(x$1) <= &1 / &2 /\ abs(x$2) <= &1 / &2
                ==> g x = vector[x$1 / &4; x$2 / &4; c]) /\
           IMAGE g (IMAGE (moi_s35_lift (&0))
              (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) =
           IMAGE (moi_s35_lift c) j`),
  DISCH_THEN(LABEL_TAC "tde") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real`; `j:real^2->bool`] MOI_S5P_TOP_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `g':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_mid <=>
                           x$3 = &0 /\ abs(x$1) <= &1 /\ abs(x$2) <= &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_S5N_MID_SQ; MOI_S5P_SQ_LIFT]; ALL_TAC] THEN
  ABBREV_TAC `sq = interval[--vector[&1;&1]:real^2,vector[&1;&1]]` THEN
  MP_TAC MOI_S5P_SQ_LIFT THEN
  REWRITE_TAC[ASSUME `interval[--vector[&1;&1]:real^2,vector[&1;&1]] = sq`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (sq:real^2->bool) (relative_frontier sq)`
  ASSUME_TAC THENL
   [EXPAND_TAC "sq" THEN MATCH_MP_TAC MOI_S5C_POLYTOPE_CELL THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(j UNION inside j) SUBSET
                interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(j:real^2->bool) SUBSET
                  interval[--vector[&5 / &16;&5 / &16],vector[&5 / &16;&5 / &16]]`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; MOI_S5C_IN_SQI] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN IMAGE (moi_s35_lift c) (j UNION inside j)
                           ==> x$3 = c /\ abs(x$1) <= &5 / &16 /\ abs(x$2) <= &5 / &16`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[MOI_S5C_IN_LIFT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET] (ASSUME
     `(j UNION inside j) SUBSET
      interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]`))) THEN
    REWRITE_TAC[MOI_S5C_IN_SQI; moi_s5c_proj; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`-- &1 / &8`; `&0`] MOI_S5P_BOX) THEN
  MP_TAC(ISPECL [`-- &1 / &8`; `c:real`] MOI_S5P_BOX) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (IMAGE (moi_s35_lift (-- &1 / &8)) sq)
                            (IMAGE (moi_s35_lift (-- &1 / &8)) (relative_frontier sq)) /\
    pl_cell_with_boundary 2 moi_s35_mid (IMAGE (moi_s35_lift (&0)) (relative_frontier sq)) /\
    pl_cell_with_boundary 2 (IMAGE (moi_s35_lift c) (j UNION inside j))
                            (IMAGE (moi_s35_lift c) j)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5C_LIFT_CELL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MOI_S5N_MID_SQ] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_S5C_LIFT_CELL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5C_LIFT_DISK THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`interval[vector[-- &1;-- &1;-- &1 / &8]:real^3,vector[&1;&1;&0]]`;
    `interval[vector[-- &1;-- &1;-- &1 / &8]:real^3,vector[&1;&1;c]]`;
    `IMAGE (moi_s35_lift (-- &1 / &8)) sq`;
    `IMAGE (moi_s35_lift (-- &1 / &8)) (relative_frontier sq)`;
    `moi_s35_mid`; `IMAGE (moi_s35_lift (&0)) (relative_frontier sq)`;
    `IMAGE (moi_s35_lift (-- &1 / &8)) sq`;
    `IMAGE (moi_s35_lift (-- &1 / &8)) (relative_frontier sq)`;
    `IMAGE (moi_s35_lift c) ((j:real^2->bool) UNION inside j)`;
    `IMAGE (moi_s35_lift c) (j:real^2->bool)`;
    `\x:real^3. x`; `\x:real^3. x`; `g:real^3->real^3`; `g':real^3->real^3`;
    `ball(vector[&0;&0;-- &1 / &8]:real^3,&1 / &16)`; `ball(vec 0:real^3,&1 / &16)`;
    `\x:real^3. x`; `\x:real^3. vector[x$1 / &4; x$2 / &4; c + x$3]:real^3`]
    (REWRITE_RULE[] (ASSUME MOI_S35_TWO_DISK_EXT))) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN REPEAT CONJ_TAC THENL
     [(* 1 *) FIRST_ASSUM ACCEPT_TAC;
      (* 2 *) FIRST_ASSUM ACCEPT_TAC;
      (* 3 *) FIRST_ASSUM ACCEPT_TAC;
      (* 4 *) FIRST_ASSUM ACCEPT_TAC;
      (* 5 *) REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      (* 6 *) REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      (* 7 *) REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      (* 8 *) FIRST_ASSUM ACCEPT_TAC;
      (* 9 *) FIRST_ASSUM ACCEPT_TAC;
      (* 10 *) REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      (* 11 *) REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
       `!x:real^3. x IN IMAGE (moi_s35_lift c) (j UNION inside j)
                   ==> x$3 = c /\ abs(x$1) <= &5 / &16 /\ abs(x$2) <= &5 / &16`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      (* 12 *) REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_lift c) (j UNION inside j)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
       `!x:real^3. x IN IMAGE (moi_s35_lift c) (j UNION inside j)
                   ==> x$3 = c /\ abs(x$1) <= &5 / &16 /\ abs(x$2) <= &5 / &16`)) THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_lift (-- &1 / &8)) sq` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      (* 13 *) MATCH_MP_TAC MOI_S5P_PLH_ID THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_S5C_CELL_POLYHEDRON THEN
      MAP_EVERY EXISTS_TAC
       [`2`; `IMAGE (moi_s35_lift (-- &1 / &8)) (relative_frontier sq)`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      (* 14 *) FIRST_ASSUM ACCEPT_TAC;
      (* 15 *) REWRITE_TAC[OPEN_BALL];
      (* 16 *) REWRITE_TAC[OPEN_BALL];
      (* 17 *) REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `vector[&0;&0;-- &1 / &8]:real^3` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; CENTRE_IN_BALL; VECTOR_3] THEN
      REAL_ARITH_TAC;
      (* 18 *) REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^3` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; CENTRE_IN_BALL; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      (* 19 *) REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_OPEN THEN REWRITE_TAC[OPEN_BALL];
      (* 20 *) MESON_TAC[];
      (* 21 *) MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `\x:real^3. (\x:real^3. vector[x$1 / &4; x$2 / &4; x$3]:real^3) x +
                             vector[&0;&0;c]` THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_3] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
        SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL; MOI_S5P_QUARTER_LINEAR]];
      (* 22 *) REPEAT GEN_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      (* 23 *) REWRITE_TAC[];
      (* 24 *) X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`vec 0:real^3`; `&1 / &16`; `x:real^3`] MOI_S5P_BALL_COMP) THEN
      ASM_REWRITE_TAC[VEC_COMPONENT; REAL_SUB_RZERO] THEN STRIP_TAC THEN
      SUBGOAL_THEN `abs((x:real^3)$1) <= &1 / &2 /\ abs(x$2) <= &1 / &2 /\ x$3 = &0`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^3->real^3) x = vector[x$1 / &4; x$2 / &4; c]` SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_ADD_RID]];
      (* 25 *) REWRITE_TAC[IMAGE_ID; SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`vector[&0;&0;-- &1 / &8]:real^3`; `&1 / &16`; `x:real^3`]
        MOI_S5P_BALL_COMP) THEN
      UNDISCH_TAC `(x:real^3) IN interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;&0]]` THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN ASM_REAL_ARITH_TAC;
      (* 26 *) REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`vec 0:real^3`; `&1 / &16`; `x:real^3`] MOI_S5P_BALL_COMP) THEN
      UNDISCH_TAC `(x:real^3) IN interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;&0]]` THEN
      ASM_REWRITE_TAC[VECTOR_3; VEC_COMPONENT; REAL_SUB_RZERO] THEN ASM_REAL_ARITH_TAC;
      (* 27 *) REWRITE_TAC[moi_s35_same_orient] THEN
      MAP_EVERY X_GEN_TAC
       [`x:real^3`; `y:real^3`; `m:real^3->real^3`; `m':real^3->real^3`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`\x:real^3. x`; `\x:real^3. x`; `vec 0:real^3`; `x:real^3`;
                     `m:real^3->real^3`] MOI_S5P_LIN_AT_AFFINE_EQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[LINEAR_ID; VECTOR_ADD_RID]; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(ISPECL [`\x:real^3. vector[x$1 / &4; x$2 / &4; c + x$3]:real^3`;
                     `\x:real^3. vector[x$1 / &4; x$2 / &4; x$3]:real^3`;
                     `vector[&0;&0;c]:real^3`; `y:real^3`; `m':real^3->real^3`]
        MOI_S5P_LIN_AT_AFFINE_EQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[MOI_S5P_QUARTER_LINEAR] THEN GEN_TAC THEN
        REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_3] THEN
        REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[MATRIX_ID; DET_I; MOI_S5P_DET_QUARTER] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^3->real^3` (X_CHOOSE_THEN `M':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bot") ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC
   [`M:real^3->real^3`; `M':real^3->real^3`; `g:real^3->real^3`; `g':real^3->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    USE_THEN "bot" (MP_TAC o SPEC `x:real^3`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;&0]]` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[]];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 3. Helpers: PL maps are local; boundary points of a 3-cell detected by a  *)
(* local injective chart (invariance of domain); a ball minus a boundary     *)
(* disk is connected; local linear parts through an affine change.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_PL_LOCAL = prove
 (`!(s:real^M->bool) (f:real^M->real^N).
     (!x. x IN s ==> ?u. open u /\ x IN u /\ pl_map_on (s INTER u) f)
     ==> pl_map_on s f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC I [pl_map_on] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `pl_map_on (s INTER u:real^M->bool) (f:real^M->real^N)` THEN
  REWRITE_TAC[pl_map_on] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool`
    (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:(real^M->bool)->bool`; `u INTER v:real^M->bool`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ASM_SIMP_TAC[OPEN_INTER];
    ASM_REWRITE_TAC[IN_INTER];
    UNDISCH_TAC `(s INTER u) INTER v SUBSET UNIONS (c:(real^M->bool)->bool)` THEN
    SET_TAC[];
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `k SUBSET s INTER (u:real^M->bool)` THEN SET_TAC[];
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
      ASM_REWRITE_TAC[]]]);;

(* A point of a 3-cell (in real^N) is a boundary point when a local         *)
(* continuous injective map of a neighbourhood into real^3 sends it outside  *)
(* the interior of a set containing the image (invariance of domain).       *)

let MOI_S5P_BD_BY_CHART = prove
 (`!(s:real^N->bool) bs (phi:real^N->real^3) z r k.
     pl_cell_with_boundary 3 s bs /\ z IN s /\ &0 < r /\
     phi continuous_on (s INTER ball(z,r)) /\
     (!x y. x IN s INTER ball(z,r) /\ y IN s INTER ball(z,r) /\ phi x = phi y
            ==> x = y) /\
     IMAGE phi (s INTER ball(z,r)) SUBSET k /\ ~(phi z IN interior k)
     ==> z IN bs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S5A_CELL_DOWN o
    check (can (term_match [] `pl_cell_with_boundary 3 (s:real^N->bool) bs`) o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^N`
    (X_CHOOSE_THEN `q:real^N->real^3` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `pl_homeomorphism (S,s) ((p:real^3->real^N),(q:real^N->real^3))` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `S:real^3->bool` MOI_STA_SIMPLEX_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^N->real^3) z IN interior S /\ (p:real^3->real^N) (q z) = z`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
      `S DIFF relative_frontier S = interior (S:real^3->bool)`) o concl)) THEN
    REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((z:real^N) IN bs)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
      `IMAGE (p:real^3->real^N) (relative_frontier S) = bs`) o concl)) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(q:real^N->real^3) z` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sg = (q:real^N->real^3) z` THEN
  SUBGOAL_THEN `(p:real^3->real^N) continuous (at sg)` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `interior S:real^3->bool` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `sg:real^3`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(sg:real^3,min d1 d2) SUBSET interior S /\
                ball(sg:real^3,min d1 d2) SUBSET S /\
                IMAGE (p:real^3->real^N) (ball(sg,min d1 d2)) SUBSET s INTER ball(z,r)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(sg:real^3,min d1 d2) SUBSET ball(sg,d2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ball(sg:real^3,min d1 d2) SUBSET interior S` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_BALL] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN S` MP_TAC THENL
       [MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `ball(sg:real^3,min d1 d2) SUBSET interior S` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[];
        ASM SET_TAC[]];
      ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `~((phi:real^N->real^3) z IN interior k)` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `(p:real^3->real^N) sg = z` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(phi:real^N->real^3) ((p:real^3->real^N) sg) = (phi o p) sg`
  SUBST1_TAC THENL [REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5A_IOD_INTERIOR THEN
  MAP_EVERY EXISTS_TAC [`ball(sg:real^3,min d1 d2)`; `ball(sg:real^3,min d1 d2)`] THEN
  REWRITE_TAC[OPEN_BALL; SUBSET_REFL; CENTRE_IN_BALL; REAL_LT_MIN] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s INTER ball(z:real^N,r)` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^3->real^N) y1 = p y2` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y. x IN s INTER ball(z,r) /\ y IN s INTER ball(z,r) /\
                   (phi:real^N->real^3) x = phi y ==> x = y`) (concl th))) THEN
      ASM SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(y1:real^3) IN S /\ (y2:real^3) IN S` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]]];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (phi:real^N->real^3) (s INTER ball(z,r))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* A PL 3-ball minus part of its frontier is connected.                      *)

let MOI_S5P_BALL_DIFF_CONNECTED = prove
 (`!x d:real^3->bool. pl_ball 3 x /\ d SUBSET frontier x ==> connected (x DIFF d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `x:real^3->bool` MOI_S5F_BALL_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `interior x:real^3->bool` THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPEC `x:real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`(d:real^3->bool) SUBSET frontier x`;
      `x DIFF interior x:real^3->bool = frontier x`] THEN
    SET_TAC[];
    UNDISCH_TAC `closure(interior x):real^3->bool = x` THEN SET_TAC[]]);;

(* Local linear parts through an affine bijection of real^3.                *)

let MOI_S5P_LIN_AT_COMPOSE = prove
 (`!(f:real^3->real^3) (a:real^3->real^3) L L' b x m.
     linear L /\ linear L' /\ (!z. L'(L z) = z) /\ (!z. L(L' z) = z) /\
     (!z. a z = L z + b) /\ moi_s35_lin_at (f o a) x m
     ==> moi_s35_lin_at f (a x) (m o L')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_lin_at; o_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^3->real^3) = \z. (L:real^3->real^3) z + b` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  RULE_ASSUM_TAC BETA_RULE THEN BETA_TAC THEN
  CONJ_TAC THENL [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `L':real^3->real^3` LINEAR_BOUNDED_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r / B` THEN CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(L':real^3->real^3) (w - b) - x = L'(w - ((L:real^3->real^3) x + b))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `w - ((L:real^3->real^3) x + b) = (w - b) - L x` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w - ((L:real^3->real^3) x + b)) * B < r` ASSUME_TAC THENL
   [UNDISCH_TAC `dist((L:real^3->real^3) x + b,w) < r / B` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REWRITE_TAC[dist] THEN
    MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L':real^3->real^3) (w - b) IN ball(x,r)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; dist] THEN
    SUBGOAL_THEN `norm(x - (L':real^3->real^3) (w - b)) =
                  norm(L' (w - ((L:real^3->real^3) x + b)))` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `B * norm(w - ((L:real^3->real^3) x + b))` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->real^3) w = f ((L:real^3->real^3) ((L':real^3->real^3) (w - b)) + b)`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `!z:real^3. z IN ball(x,r)
                          ==> (f:real^3->real^3) ((L:real^3->real^3) z + b) =
                              f (L x + b) + (m:real^3->real^3) (z - x)` THEN
  DISCH_THEN(MP_TAC o SPEC `(L':real^3->real^3) (w - b)`) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. The B-side model piece: a PL homeomorphism of the box 0 <= x3 <= 1/8  *)
(* of the model cube onto a PL 3-ball T which has the A-chart disk          *)
(* pa(lift c (j UNION inside j)) and the B-chart square pb(level 1/8) in its *)
(* frontier; it is pa o g on the middle square and pb on the top square.    *)
(* TWO_DISK_EXT with the local extensions pa o (x1/4, x2/4, c + x3) near 0  *)
(* and pb near (0,0,1/8); the orientation agreement comes from that of the  *)
(* two charts.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_LEVEL_SQ = prove
 (`!a. abs a <= &1
       ==> IMAGE (moi_s35_lift a) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) =
           moi_s35_level a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; MOI_S5P_SQ_LIFT] THEN
  REWRITE_TAC[moi_s35_level; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3;
              FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S5P_PLH_IMAGE = prove
 (`!(k:real^3->bool) u (f:real^3->real^3).
     compact k /\ locally_polyhedral k /\ k SUBSET u /\ pl_map_on u f /\
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)
     ==> ?f'. pl_homeomorphism (k,IMAGE f k) (f,f')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_map_on k (f:real^3->real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `f:real^3->real^3`; `IMAGE (f:real^3->real^3) k`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `f':real^3->real^3`) THEN
    EXISTS_TAC `f':real^3->real^3` THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[]]);;

let MOI_S5P_CELL_EMBED = prove
 (`!(d:real^3->bool) j u (f:real^3->real^3).
     pl_cell_with_boundary 2 d j /\ d SUBSET u /\ pl_map_on u f /\
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)
     ==> pl_cell_with_boundary 2 (IMAGE f d) (IMAGE f j) /\
         ?f'. pl_homeomorphism (d,IMAGE f d) (f,f')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `u:real^3->bool`; `f:real^3->real^3`]
    MOI_S5P_PLH_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S5C_CELL_COMPACT];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_S5C_CELL_POLYHEDRON THEN
      MAP_EVERY EXISTS_TAC [`2`; `j:real^3->bool`] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `f':real^3->real^3`)] THEN
  CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `f':real^3->real^3` THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MOI_S5C_CELL_PLH THEN
  MAP_EVERY EXISTS_TAC [`d:real^3->bool`; `f':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^3->bool) j` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN MESON_TAC[]);;

let MOI_S5P_DET_FOUR = prove
 (`det(matrix(\x:real^3. vector[&4 * x$1; &4 * x$2; x$3]:real^3)) = &16`,
  REWRITE_TAC[DET_3] THEN
  SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_3; ARITH; VECTOR_3; BASIS_COMPONENT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

let MOI_S5P_FOUR_LINEAR = prove
 (`linear (\x:real^3. vector[&4 * x$1; &4 * x$2; x$3]:real^3)`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let MOI_S5P_BPIECE = prove
 (mk_imp(MOI_S35_TWO_DISK_EXT,
  `!c j (g:real^3->real^3) g' (pa:real^3->real^3) (pb:real^3->real^3) (tb:real^3->bool).
     abs c <= &1 / &512 /\ pl_sphere 1 j /\
     (!y:real^2. y IN j ==> max (abs(y$1)) (abs(y$2)) <= &5 / &16) /\
     pl_homeomorphism (moi_s35_mid,IMAGE (moi_s35_lift c) (j UNION inside j)) (g,g') /\
     (!x. x IN moi_s35_mid /\ abs(x$1) <= &1 / &2 /\ abs(x$2) <= &1 / &2
          ==> g x = vector[x$1 / &4; x$2 / &4; c]) /\
     pl_map_on moi_s35_dom pa /\
     (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ pa x = pa y ==> x = y) /\
     pl_map_on moi_s35_upper pb /\
     (!x y. x IN moi_s35_upper /\ y IN moi_s35_upper /\ pb x = pb y ==> x = y) /\
     moi_s35_same_orient pa (interior moi_s35_dom) pb (interior moi_s35_bcell) /\
     pl_ball 3 tb /\
     IMAGE pa (IMAGE (moi_s35_lift c) (j UNION inside j)) SUBSET frontier tb /\
     IMAGE pb (moi_s35_level (&1 / &8)) SUBSET frontier tb /\
     DISJOINT (IMAGE pa (IMAGE (moi_s35_lift c) (j UNION inside j)))
              (IMAGE pb (moi_s35_level (&1 / &8))) /\
     (?r. &0 < r /\
          IMAGE (\x:real^3. pa(vector[x$1 / &4; x$2 / &4; c + x$3]:real^3))
                (ball(vec 0,r) INTER
                 interval[vector[-- &1;-- &1;&0],vector[&1;&1;&1 / &8]]) SUBSET tb) /\
     (?r. &0 < r /\
          IMAGE pb (ball(vector[&0;&0;&1 / &8],r) INTER
                    interval[vector[-- &1;-- &1;&0],vector[&1;&1;&1 / &8]]) SUBSET tb)
     ==> ?Q Q'. pl_homeomorphism
                  (interval[vector[-- &1;-- &1;&0]:real^3,vector[&1;&1;&1 / &8]],tb) (Q,Q') /\
                (!x. x IN moi_s35_mid ==> Q x = pa (g x)) /\
                (!x. x IN moi_s35_level (&1 / &8) ==> Q x = pb x)`),
  DISCH_THEN(LABEL_TAC "tde") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `sq = interval[--vector[&1;&1]:real^2,vector[&1;&1]]` THEN
  MP_TAC MOI_S5P_SQ_LIFT THEN
  REWRITE_TAC[ASSUME `interval[--vector[&1;&1]:real^2,vector[&1;&1]] = sq`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (sq:real^2->bool) (relative_frontier sq)`
  ASSUME_TAC THENL
   [EXPAND_TAC "sq" THEN MATCH_MP_TAC MOI_S5C_POLYTOPE_CELL THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_mid <=>
                           x$3 = &0 /\ abs(x$1) <= &1 /\ abs(x$2) <= &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_S5N_MID_SQ] THEN
    REWRITE_TAC[ASSUME `interval[--vector[&1;&1]:real^2,vector[&1;&1]] = sq`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (moi_s35_lift (&1 / &8)) sq = moi_s35_level (&1 / &8)`
  ASSUME_TAC THENL
   [EXPAND_TAC "sq" THEN MATCH_MP_TAC MOI_S5P_LEVEL_SQ THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (moi_s35_level (&1 / &8))
                  (IMAGE (moi_s35_lift (&1 / &8)) (relative_frontier sq))`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (moi_s35_lift (&1 / &8)) sq = moi_s35_level (&1 / &8)`)) THEN
    MATCH_MP_TAC MOI_S5C_LIFT_CELL THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (moi_s35_lift c) ((j:real^2->bool) UNION inside j))
                  (IMAGE (moi_s35_lift c) j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_LIFT_DISK THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(j UNION inside j) SUBSET
                interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(j:real^2->bool) SUBSET
                  interval[--vector[&5 / &16;&5 / &16],vector[&5 / &16;&5 / &16]]`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; MOI_S5C_IN_SQI] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (moi_s35_lift c) ((j:real^2->bool) UNION inside j) SUBSET
                moi_s35_dom`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_S5C_IN_LIFT; moi_s35_dom; moi_s35_cube; IN_ELIM_THM;
                IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT;
                VEC_COMPONENT] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_s5c_proj x IN
                  interval[--vector[&5 / &16;&5 / &16]:real^2,vector[&5 / &16;&5 / &16]]`
    MP_TAC THENL
     [UNDISCH_TAC `moi_s5c_proj x IN (j:real^2->bool) UNION inside j` THEN
      UNDISCH_TAC `(j UNION inside j) SUBSET
                   interval[--vector[&5 / &16;&5 / &16]:real^2,
                            vector[&5 / &16;&5 / &16]]` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_S5C_IN_SQI; moi_s5c_proj; VECTOR_2] THEN
    UNDISCH_TAC `(x:real^3)$3 = c` THEN UNDISCH_TAC `abs c <= &1 / &512` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_level (&1 / &8) SUBSET moi_s35_upper`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; moi_s35_level; moi_s35_upper; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (moi_s35_lift c) ((j:real^2->bool) UNION inside j)`;
                 `IMAGE (moi_s35_lift c) (j:real^2->bool)`; `moi_s35_dom`;
                 `pa:real^3->real^3`] MOI_S5P_CELL_EMBED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `pa':real^3->real^3`))] THEN
  MP_TAC(ISPECL [`moi_s35_level (&1 / &8)`;
                 `IMAGE (moi_s35_lift (&1 / &8)) (relative_frontier sq)`;
                 `moi_s35_upper`;
                 `pb:real^3->real^3`] MOI_S5P_CELL_EMBED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `pb':real^3->real^3`))] THEN
  MP_TAC(ISPECL [`&0`; `&1 / &8`] MOI_S5P_BOX) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 moi_s35_mid
                  (IMAGE (moi_s35_lift (&0)) (relative_frontier sq))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_S5N_MID_SQ] THEN
    REWRITE_TAC[ASSUME `interval[--vector[&1;&1]:real^2,vector[&1;&1]] = sq`] THEN
    MATCH_MP_TAC MOI_S5C_LIFT_CELL THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (moi_s35_mid,IMAGE pa (IMAGE (moi_s35_lift c) (j UNION inside j)))
                     ((pa:real^3->real^3) o (g:real^3->real^3),
                      (g':real^3->real^3) o (pa':real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (moi_s35_lift c) ((j:real^2->bool) UNION inside j)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = min r0 (&1 / &64)` THEN
  ABBREV_TAC `s1 = min r1 (&1 / &64)` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 <= r0 /\ s0 <= &1 / &64 /\
                &0 < s1 /\ s1 <= r1 /\ s1 <= &1 / &64` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < r0` THEN UNDISCH_TAC `&0 < r1` THEN
    MAP_EVERY EXPAND_TAC ["s0"; "s1"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* model facts near the two centres *)
  SUBGOAL_THEN
   `(!x:real^3. x IN ball(vec 0,s0)
                ==> abs(x$1) < &1 / &64 /\ abs(x$2) < &1 / &64 /\ abs(x$3) < &1 / &64) /\
    (!x:real^3. x IN ball(vector[&0;&0;&1 / &8],s1)
                ==> abs(x$1) < &1 / &64 /\ abs(x$2) < &1 / &64 /\
                    abs(x$3 - &1 / &8) < &1 / &64)`
  (CONJUNCTS_THEN2 (LABEL_TAC "nb0") (LABEL_TAC "nb1")) THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S5P_BALL_COMP) THEN
    REWRITE_TAC[VEC_COMPONENT; VECTOR_3; REAL_SUB_RZERO] THENL
     [UNDISCH_TAC `s0 <= &1 / &64`; UNDISCH_TAC `s1 <= &1 / &64`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:real^3. x IN ball(vec 0,s0)
                ==> vector[x$1 / &4; x$2 / &4; c + x$3]:real^3 IN interior moi_s35_dom) /\
    (!x:real^3. x IN ball(vector[&0;&0;&1 / &8],s1)
                ==> x IN moi_s35_upper /\ x IN interior moi_s35_bcell)`
  (CONJUNCTS_THEN2 (LABEL_TAC "ib0") (LABEL_TAC "ib1")) THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!u. (y:real^3) IN u /\ u SUBSET interior s ==> y IN interior s`) THEN
      EXISTS_TAC `ball(vector[&0;&0;c]:real^3,&1 / &32)` THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_BALL; dist] THEN
        MATCH_MP_TAC(REAL_ARITH `!a. n <= a /\ a < b ==> n < b`) THEN
        EXISTS_TAC `abs(x$1 / &4) + abs(x$2 / &4) + abs((x:real^3)$3)` THEN
        CONJ_TAC THENL
         [MP_TAC(ISPEC `vector[&0;&0;c] -
                        vector[(x:real^3)$1 / &4; x$2 / &4; c + x$3]:real^3`
            NORM_LE_L1) THEN
          REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
          REAL_ARITH_TAC;
          USE_THEN "nb0" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(vec 0,s0)`)) THEN
          REAL_ARITH_TAC];
        MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[OPEN_BALL] THEN
        REWRITE_TAC[SUBSET; IN_BALL; moi_s35_dom; moi_s35_cube; IN_ELIM_THM;
                    IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT;
                    VEC_COMPONENT] THEN
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`vector[&0;&0;c]:real^3`; `&1 / &32`; `y:real^3`] MOI_S5P_BALL_COMP) THEN
        ASM_REWRITE_TAC[IN_BALL; VECTOR_3] THEN
        UNDISCH_TAC `abs c <= &1 / &512` THEN REAL_ARITH_TAC];
      USE_THEN "nb1" (MP_TAC o C MATCH_MP
        (ASSUME `(x:real^3) IN ball(vector[&0;&0;&1 / &8],s1)`)) THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_s35_upper; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3;
                    FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
        UNDISCH_TAC `abs((x:real^3)$1) < &1 / &64 /\ abs(x$2) < &1 / &64 /\
                     abs(x$3 - &1 / &8) < &1 / &64` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(SET_RULE `!u. (y:real^3) IN u /\ u SUBSET interior s ==> y IN interior s`) THEN
        EXISTS_TAC `ball(vector[&0;&0;&1 / &8]:real^3,s1)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[OPEN_BALL] THEN
        REWRITE_TAC[SUBSET; moi_s35_bcell; moi_s35_n; moi_s35_cube; IN_ELIM_THM;
                    IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT;
                    VEC_COMPONENT] THEN
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        USE_THEN "nb1" (MP_TAC o C MATCH_MP
          (ASSUME `(y:real^3) IN ball(vector[&0;&0;&1 / &8],s1)`)) THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`interval[vector[-- &1;-- &1;&0]:real^3,vector[&1;&1;&1 / &8]]`;
    `tb:real^3->bool`;
    `moi_s35_mid`; `IMAGE (moi_s35_lift (&0)) (relative_frontier sq)`;
    `moi_s35_level (&1 / &8)`; `IMAGE (moi_s35_lift (&1 / &8)) (relative_frontier sq)`;
    `IMAGE (pa:real^3->real^3) (IMAGE (moi_s35_lift c) ((j:real^2->bool) UNION inside j))`;
    `IMAGE (pa:real^3->real^3) (IMAGE (moi_s35_lift c) (j:real^2->bool))`;
    `IMAGE (pb:real^3->real^3) (moi_s35_level (&1 / &8))`;
    `IMAGE (pb:real^3->real^3) (IMAGE (moi_s35_lift (&1 / &8)) (relative_frontier sq))`;
    `(pa:real^3->real^3) o (g:real^3->real^3)`;
    `(g':real^3->real^3) o (pa':real^3->real^3)`;
    `pb:real^3->real^3`; `pb':real^3->real^3`;
    `ball(vec 0:real^3,s0)`; `ball(vector[&0;&0;&1 / &8]:real^3,s1)`;
    `\x:real^3. (pa:real^3->real^3) (vector[x$1 / &4; x$2 / &4; c + x$3]:real^3)`;
    `pb:real^3->real^3`]
    (REWRITE_RULE[] (ASSUME MOI_S35_TWO_DISK_EXT))) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN REPEAT CONJ_TAC THENL
     [(* 1 *) FIRST_ASSUM ACCEPT_TAC;
      (* 2 *) FIRST_ASSUM ACCEPT_TAC;
      (* 3 *) FIRST_ASSUM ACCEPT_TAC;
      (* 4 *) FIRST_ASSUM ACCEPT_TAC;
      (* 5 *) REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      (* 6 *) REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[moi_s35_level; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3;
                  FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      (* 7 *) REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; moi_s35_level;
                          IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      (* 8 *) FIRST_ASSUM ACCEPT_TAC;
      (* 9 *) FIRST_ASSUM ACCEPT_TAC;
      (* 10 *) FIRST_ASSUM ACCEPT_TAC;
      (* 11 *) FIRST_ASSUM ACCEPT_TAC;
      (* 12 *) FIRST_ASSUM ACCEPT_TAC;
      (* 13 *) FIRST_ASSUM ACCEPT_TAC;
      (* 14 *) FIRST_ASSUM ACCEPT_TAC;
      (* 15 *) REWRITE_TAC[OPEN_BALL];
      (* 16 *) REWRITE_TAC[OPEN_BALL];
      (* 17 *) REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^3` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; CENTRE_IN_BALL; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      (* 18 *) REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `vector[&0;&0;&1 / &8]:real^3` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; CENTRE_IN_BALL] THEN
      REWRITE_TAC[moi_s35_level; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3;
                  FORALL_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT; VECTOR_3] THEN
      REAL_ARITH_TAC;
      (* 19 *) MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `(pa:real^3->real^3) o
                  (\x:real^3. vector[x$1 / &4; x$2 / &4; c + x$3]:real^3)` THEN
      CONJ_TAC THENL [REWRITE_TAC[o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_s35_dom` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_EQ THEN
        EXISTS_TAC `\x:real^3. (\x:real^3. vector[x$1 / &4; x$2 / &4; x$3]:real^3) x +
                               vector[&0;&0;c]` THEN
        CONJ_TAC THENL
         [REPEAT STRIP_TAC THEN
          REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_3] THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
          SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL; MOI_S5P_QUARTER_LINEAR]];
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
        DISCH_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN
        USE_THEN "ib0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      (* 20 *) MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `vector[(x:real^3)$1 / &4; x$2 / &4; c + x$3]:real^3 =
                    vector[(y:real^3)$1 / &4; y$2 / &4; c + y$3]` MP_TAC THENL
       [MATCH_MP_TAC(ASSUME `!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\
                                   (pa:real^3->real^3) x = pa y ==> x = y`) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN
        USE_THEN "ib0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
        REAL_ARITH_TAC];
      (* 21 *) MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_upper` THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL] THEN
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "ib1" (MP_TAC o C MATCH_MP
        (ASSUME `(x:real^3) IN ball(vector[&0;&0;&1 / &8],s1)`)) THEN
      SIMP_TAC[];
      (* 22 *) MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC(ASSUME `!x y. x IN moi_s35_upper /\ y IN moi_s35_upper /\
                                 (pb:real^3->real^3) x = pb y ==> x = y`) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "ib1" (fun th ->
        MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN ball(vector[&0;&0;&1 / &8],s1)`)) THEN
        MP_TAC(MATCH_MP th (ASSUME `(y:real^3) IN ball(vector[&0;&0;&1 / &8],s1)`))) THEN
      SIMP_TAC[];
      (* 23 *) X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER; o_THM] THEN STRIP_TAC THEN
      USE_THEN "nb0" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(vec 0,s0)`)) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3)$3 = &0` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^3->real^3) x = vector[x$1 / &4; x$2 / &4; c]` SUBST1_TAC THENL
       [MATCH_MP_TAC(ASSUME `!x. x IN moi_s35_mid /\ abs(x$1) <= &1 / &2 /\
                                 abs(x$2) <= &1 / &2
                                 ==> (g:real^3->real^3) x = vector[x$1 / &4; x$2 / &4; c]`) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `abs((x:real^3)$1) < &1 / &64` THEN
        UNDISCH_TAC `abs((x:real^3)$2) < &1 / &64` THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_ADD_RID]];
      (* 24 *) REWRITE_TAC[];
      (* 25 *) MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (\x:real^3. (pa:real^3->real^3)
                                     (vector[x$1 / &4; x$2 / &4; c + x$3]:real^3))
                        (ball(vec 0,r0) INTER
                         interval[vector[-- &1;-- &1;&0],vector[&1;&1;&1 / &8]])` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        MP_TAC(ISPECL [`vec 0:real^3`; `s0:real`; `r0:real`] SUBSET_BALL) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      (* 26 *) MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (pb:real^3->real^3)
                        (ball(vector[&0;&0;&1 / &8],r1) INTER
                         interval[vector[-- &1;-- &1;&0],vector[&1;&1;&1 / &8]])` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        MP_TAC(ISPECL [`vector[&0;&0;&1 / &8]:real^3`; `s1:real`; `r1:real`] SUBSET_BALL) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      (* 27 *) REWRITE_TAC[moi_s35_same_orient] THEN
      MAP_EVERY X_GEN_TAC
       [`x:real^3`; `y:real^3`; `m:real^3->real^3`; `m':real^3->real^3`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`pa:real^3->real^3`;
                     `\x:real^3. vector[x$1 / &4; x$2 / &4; c + x$3]:real^3`;
                     `\x:real^3. vector[x$1 / &4; x$2 / &4; x$3]:real^3`;
                     `\x:real^3. vector[&4 * x$1; &4 * x$2; x$3]:real^3`;
                     `vector[&0;&0;c]:real^3`; `x:real^3`; `m:real^3->real^3`]
        MOI_S5P_LIN_AT_COMPOSE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[MOI_S5P_QUARTER_LINEAR; MOI_S5P_FOUR_LINEAR] THEN
        REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_3] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[o_DEF] THEN FIRST_ASSUM ACCEPT_TAC;
        BETA_TAC THEN DISCH_TAC] THEN
      MP_TAC(SPECL [`vector[(x:real^3)$1 / &4; x$2 / &4; c + x$3]:real^3`; `y:real^3`;
                    `(m:real^3->real^3) o
                     (\x:real^3. vector[&4 * x$1; &4 * x$2; x$3]:real^3)`;
                    `m':real^3->real^3`]
        (REWRITE_RULE[moi_s35_same_orient]
          (ASSUME `moi_s35_same_orient (pa:real^3->real^3) (interior moi_s35_dom)
                                       (pb:real^3->real^3) (interior moi_s35_bcell)`))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [USE_THEN "ib0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          USE_THEN "ib1" (MP_TAC o C MATCH_MP
            (ASSUME `(y:real^3) IN ball(vector[&0;&0;&1 / &8],s1)`)) THEN
          SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `linear (m:real^3->real^3)` ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s35_lin_at
                      (\x:real^3. (pa:real^3->real^3)
                                    (vector[x$1 / &4; x$2 / &4; c + x$3]:real^3)) x m` THEN
        SIMP_TAC[moi_s35_lin_at];
        ALL_TAC] THEN
      SIMP_TAC[MATRIX_COMPOSE; MOI_S5P_FOUR_LINEAR; DET_MUL; MOI_S5P_DET_FOUR;
               ASSUME `linear (m:real^3->real^3)`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:real^3->real^3` (X_CHOOSE_THEN `Q':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "qm") ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`Q:real^3->real^3`; `Q':real^3->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "qm" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN moi_s35_mid`)) THEN
    REWRITE_TAC[o_THM];
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 5. Sides of a properly embedded disk.  If D (a PL 3-ball) is covered by   *)
(* two closed sets X1, X2 meeting exactly in the disk E, the two balls of    *)
(* SPLIT_BALL lie one in X1 and one in X2 (each ball minus E is connected). *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_CONN_SIDE = prove
 (`!(c:real^3->bool) x1 x2.
     connected c /\ closed x1 /\ closed x2 /\ c SUBSET x1 UNION x2 /\
     c INTER (x1 INTER x2) = {}
     ==> c SUBSET x1 \/ c SUBSET x2`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `connected(c:real^3->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`x1:real^3->bool`; `x2:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x1 INTER x2 INTER (c:real^3->bool) = {}` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `c INTER (x1 INTER x2):real^3->bool = {}` THEN SET_TAC[];
    UNDISCH_TAC `(c:real^3->bool) SUBSET x1 UNION x2` THEN SET_TAC[]]);;

let MOI_S5P_SIDES = prove
 (`!d e j x1 x2 (p:real^3) (q:real^3).
     PL_SCHOENFLIES_3_STATEMENT /\ pl_ball 3 d /\ pl_cell_with_boundary 2 e j /\
     e SUBSET d /\ e INTER frontier d = j /\
     closed x1 /\ closed x2 /\ x1 INTER x2 = e /\ d SUBSET x1 UNION x2 /\
     p IN d /\ p IN x2 /\ ~(p IN e) /\ q IN d /\ q IN x1 /\ ~(q IN e)
     ==> ?tt rr. pl_ball 3 tt /\ pl_ball 3 rr /\ tt UNION rr = d /\ tt INTER rr = e /\
                 tt SUBSET x2 /\ rr SUBSET x1 /\ p IN tt /\
                 e SUBSET frontier tt /\ frontier d INTER tt SUBSET frontier tt`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `e:real^3->bool`; `j:real^3->bool`]
    MOI_S5N_SPLIT_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^3->bool` (X_CHOOSE_THEN `y2:real^3->bool`
    (X_CHOOSE_THEN `s1:real^3->bool` (X_CHOOSE_THEN `s2:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(s1:real^3->bool) SUBSET y1 /\ (s2:real^3->bool) SUBSET y2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `frontier y1:real^3->bool`; EXISTS_TAC `frontier y2:real^3->bool`] THEN
    CONJ_TAC THEN TRY(ASM_REWRITE_TAC[SUBSET_UNION] THEN NO_TAC) THEN
    MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN ASM_MESON_TAC[MOI_S5F_BALL_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (y1 DIFF e:real^3->bool) /\ connected (y2 DIFF e:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5P_BALL_DIFF_CONNECTED THEN
    ASM_REWRITE_TAC[SUBSET_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `((y1 DIFF e:real^3->bool) SUBSET x1 \/ (y1 DIFF e) SUBSET x2) /\
                ((y2 DIFF e:real^3->bool) SUBSET x1 \/ (y2 DIFF e) SUBSET x2)`
  (CONJUNCTS_THEN2 (LABEL_TAC "a1") (LABEL_TAC "a2")) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5P_CONN_SIDE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`y1 UNION y2:real^3->bool = d`; `(d:real^3->bool) SUBSET x1 UNION x2`;
      `x1 INTER x2:real^3->bool = e`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real^3) IN x1) /\ ~((q:real^3) IN x2)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`x1 INTER x2:real^3->bool = e`; `(p:real^3) IN x2`; `~((p:real^3) IN e)`;
      `(q:real^3) IN x1`; `~((q:real^3) IN e)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->bool) SUBSET x1 /\ (e:real^3->bool) SUBSET x2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `x1 INTER x2:real^3->bool = e` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(p:real^3) IN y1` THENL
   [SUBGOAL_THEN `(y1 DIFF e:real^3->bool) SUBSET x2` ASSUME_TAC THENL
     [USE_THEN "a1" MP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(p:real^3) IN y1`; `~((p:real^3) IN x1)`; `~((p:real^3) IN e)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^3) IN y2 DIFF e` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(y1 DIFF e:real^3->bool) SUBSET x2`; `~((q:real^3) IN x2)`;
        `~((q:real^3) IN e)`; `(q:real^3) IN d`; `y1 UNION y2:real^3->bool = d`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y2 DIFF e:real^3->bool) SUBSET x1` ASSUME_TAC THENL
     [USE_THEN "a2" MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(q:real^3) IN y2 DIFF e`; `~((q:real^3) IN x2)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`y1:real^3->bool`; `y2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(y1 DIFF e:real^3->bool) SUBSET x2`; `(e:real^3->bool) SUBSET x2`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(y2 DIFF e:real^3->bool) SUBSET x1`; `(e:real^3->bool) SUBSET x1`] THEN
      SET_TAC[];
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`s1 UNION s2:real^3->bool = frontier d`; `(s2:real^3->bool) SUBSET y2`;
        `y1 INTER y2:real^3->bool = e`] THEN
      SET_TAC[]];
    SUBGOAL_THEN `(p:real^3) IN y2` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`~((p:real^3) IN y1)`; `(p:real^3) IN d`; `y1 UNION y2:real^3->bool = d`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y2 DIFF e:real^3->bool) SUBSET x2` ASSUME_TAC THENL
     [USE_THEN "a2" MP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(p:real^3) IN y2`; `~((p:real^3) IN x1)`; `~((p:real^3) IN e)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^3) IN y1 DIFF e` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(y2 DIFF e:real^3->bool) SUBSET x2`; `~((q:real^3) IN x2)`;
        `~((q:real^3) IN e)`; `(q:real^3) IN d`; `y1 UNION y2:real^3->bool = d`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y1 DIFF e:real^3->bool) SUBSET x1` ASSUME_TAC THENL
     [USE_THEN "a1" MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(q:real^3) IN y1 DIFF e`; `~((q:real^3) IN x2)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`y2:real^3->bool`; `y1:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `y1 UNION y2:real^3->bool = d` THEN SET_TAC[];
      UNDISCH_TAC `y1 INTER y2:real^3->bool = e` THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(y2 DIFF e:real^3->bool) SUBSET x2`; `(e:real^3->bool) SUBSET x2`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(y1 DIFF e:real^3->bool) SUBSET x1`; `(e:real^3->bool) SUBSET x1`] THEN
      SET_TAC[];
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`s1 UNION s2:real^3->bool = frontier d`; `(s1:real^3->bool) SUBSET y1`;
        `y1 INTER y2:real^3->bool = e`] THEN
      SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 6. The source side at a vertex v: the core K_v (the dual cell minus the   *)
(* open slabs of the edges at v) and K'_v (the core with the A-side slabs    *)
(* cut at the levels cc e); facts from the charts.                          *)
(* ------------------------------------------------------------------------- *)

let moi_s5p_osl = new_definition
 `moi_s5p_osl = {x:real^3 | x IN moi_s35_cube /\ abs(x$3) < &1 / &8}`;;

let moi_s5p_core = new_definition
 `moi_s5p_core (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
               (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
               (psi:(real^N->bool)->real^3->real^N) (v:real^N) =
    derived_dual_cell t l v DIFF
    UNIONS {IMAGE (psi e) moi_s5p_osl | e | moi_s35_edge l e /\ (av e = v \/ bv e = v)}`;;

let moi_s5p_core2 = new_definition
 `moi_s5p_core2 (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
                (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
                (psi:(real^N->bool)->real^3->real^N) (cc:(real^N->bool)->real)
                (v:real^N) =
    moi_s5p_core t l av bv psi v UNION
    UNIONS {IMAGE (psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e} | e |
            moi_s35_edge l e /\ av e = v}`;;

let MOI_S5P_CHART_FACTS = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> {av e} IN l /\ {bv e} IN l /\ ~(av e = bv e) /\
         (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\ psi e x = psi e y ==> x = y) /\
         (?q. pl_homeomorphism
                (moi_s35_cube,
                 derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e))
                (psi e,q)) /\
         IMAGE (psi e) moi_s35_lower = derived_dual_cell t l (av e) /\
         IMAGE (psi e) moi_s35_upper = derived_dual_cell t l (bv e) /\
         IMAGE (psi e) {x | x IN moi_s35_slab /\ moi_s35_n x = &1}
           SUBSET derived_frontier t l /\
         (!e'. moi_s35_edge l e' /\ ~(e = e')
               ==> DISJOINT (IMAGE (psi e) moi_s35_slab) (IMAGE (psi e') moi_s35_slab))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "ed") (LABEL_TAC "dj"))
    ASSUME_TAC) THEN
  USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism
                  (moi_s35_cube,
                   derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                   derived_dual_cell t l (bv e))
                  ((psi:(real^N->bool)->real^3->real^N) e,q)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    EXISTS_TAC `q:real^N->real^3` THEN FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S5P_CORE_B = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> moi_s5p_core t l av bv psi (bv e) SUBSET
         IMAGE (psi e) {x | x IN moi_s35_cube /\ &1 / &8 <= x$3}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS) THEN
  REWRITE_TAC[SUBSET; moi_s5p_core; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_osl` o
     REWRITE_RULE[NOT_EXISTS_THM])) THEN
  MATCH_MP_TAC(TAUT `a /\ (~b ==> c) ==> ~(a /\ b) ==> c`) THEN CONJ_TAC THENL
   [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  UNDISCH_TAC `(y:real^3) IN moi_s35_upper` THEN
  REWRITE_TAC[moi_s35_upper; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_osl)` THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
  ASM_REWRITE_TAC[moi_s5p_osl; IN_ELIM_THM] THEN
  UNDISCH_TAC `&0 <= (y:real^3)$3` THEN UNDISCH_TAC `(y:real^3)$3 < &1 / &8` THEN
  REAL_ARITH_TAC);;

let MOI_S5P_CORE_A = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> moi_s5p_core t l av bv psi (av e) SUBSET
         IMAGE (psi e) {x | x IN moi_s35_cube /\ x$3 <= -- &1 / &8}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS) THEN
  REWRITE_TAC[SUBSET; moi_s5p_core; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_osl` o
     REWRITE_RULE[NOT_EXISTS_THM])) THEN
  MATCH_MP_TAC(TAUT `a /\ (~b ==> c) ==> ~(a /\ b) ==> c`) THEN CONJ_TAC THENL
   [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  UNDISCH_TAC `(y:real^3) IN moi_s35_lower` THEN
  REWRITE_TAC[moi_s35_lower; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_osl)` THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
  ASM_REWRITE_TAC[moi_s5p_osl; IN_ELIM_THM] THEN
  UNDISCH_TAC `(y:real^3)$3 <= &0` THEN UNDISCH_TAC `-- &1 / &8 < (y:real^3)$3` THEN
  REAL_ARITH_TAC);;


let MOI_S5P_LEVEL_IN_CORE = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> IMAGE (psi e) (moi_s35_level (&1 / &8)) SUBSET
         moi_s5p_core t l av bv psi (bv e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_s5p_core; IN_DIFF; moi_s35_level;
              IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                 derived_dual_cell t l (bv e)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[moi_s35_upper; IN_ELIM_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `e':real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) SUBST1_TAC) THEN
  ASM_CASES_TAC `e':real^N->bool = e` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[moi_s5p_osl; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) = z` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                   (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`)
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `abs((z:real^3)$3) < &1 / &8` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                         (IMAGE (psi e') moi_s35_slab)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!e'. moi_s35_edge l e' /\ ~(e = e')
                 ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                              (IMAGE (psi e') moi_s35_slab)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `(psi:(real^N->bool)->real^3->real^N) e y`) THEN
  MATCH_MP_TAC(TAUT `p /\ (~q ==> r) ==> ~(p /\ q) ==> r`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[moi_s35_slab; IN_ELIM_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> ~(x IN t) ==> ~(x IN s)`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; moi_s5p_osl; moi_s35_slab; IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LT_IMP_LE]]);;

let MOI_S5P_CSRC_COVER = prove
 (`!(t:(real^N->bool)->bool) l av bv (psi:(real^N->bool)->real^3->real^N) cc v.
     moi_s35_csrc t l av bv psi cc v SUBSET
     moi_s5p_core2 t l av bv psi cc v UNION
     UNIONS {IMAGE (psi e) (moi_s35_bcell INTER moi_s35_slab) | e |
             moi_s35_edge l e /\ bv e = v}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!e x. x IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_osl
                      ==> x IN IMAGE (psi e) moi_s35_slab`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN SPEC_TAC(`x:real^N`,`x:real^N`) THEN
    REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; moi_s5p_osl; moi_s35_slab; IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; moi_s35_csrc; moi_s5p_core2; moi_s5p_core; IN_UNION; IN_DIFF;
              UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN POP_ASSUM MP_TAC THEN MESON_TAC[]);;

let MOI_S5P_CORE2_CPLUS = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc v.
     moi_s35_charts t l g av bv psi
     ==> moi_s5p_core2 t l av bv psi cc v SUBSET moi_s35_cplus t l av bv psi v /\
         (!e. moi_s35_edge l e /\ bv e = v
              ==> IMAGE (psi e) (moi_s35_bcell INTER moi_s35_slab) SUBSET
                  moi_s35_cplus t l av bv psi v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e
        ==> IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower =
            derived_dual_cell t l (av e) /\
            IMAGE (psi e) moi_s35_upper = derived_dual_cell t l (bv e)`
  (LABEL_TAC "hv") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`] MOI_S5P_CHART_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_s5p_core2; moi_s5p_core; moi_s35_cplus; UNION_SUBSET] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) MP_TAC)) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `(y:real^3)$3 <= &0` THENL
     [DISJ1_TAC THEN DISJ1_TAC THEN
      USE_THEN "hv" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN UNDISCH_TAC `(y:real^3)$3 <= &0` THEN
      REWRITE_TAC[moi_s35_slab; moi_s35_lower; IN_ELIM_THM] THEN SIMP_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN UNDISCH_TAC `~((y:real^3)$3 <= &0)` THEN
      REWRITE_TAC[moi_s35_slab; moi_s35_upper; IN_ELIM_THM] THEN SIMP_TAC[] THEN
      REAL_ARITH_TAC];
    X_GEN_TAC `e:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; moi_s35_cplus; IN_UNION;
                UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 <= (y:real^3)$3` THENL
     [DISJ1_TAC THEN DISJ1_TAC THEN
      USE_THEN "hv" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN UNDISCH_TAC `&0 <= (y:real^3)$3` THEN
      REWRITE_TAC[moi_s35_slab; moi_s35_upper; IN_ELIM_THM] THEN SIMP_TAC[];
      DISJ1_TAC THEN DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN UNDISCH_TAC `~(&0 <= (y:real^3)$3)` THEN
      REWRITE_TAC[moi_s35_slab; moi_s35_lower; IN_ELIM_THM] THEN SIMP_TAC[] THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* 7. Abstract set facts for the vertex maps: injectivity of a map pasted    *)
(* from a core and boxes, and the cover of D_v by the core image and the    *)
(* B-side pieces.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_INJ_PASTE = prove
 (`!(f:A->B) a (bb:I->A->bool) ix.
     (!x y. x IN a /\ y IN a /\ f x = f y ==> x = y) /\
     (!i x y. i IN ix /\ x IN bb i /\ y IN bb i /\ f x = f y ==> x = y) /\
     (!i j. i IN ix /\ j IN ix /\ ~(i = j)
            ==> DISJOINT (IMAGE f (bb i)) (IMAGE f (bb j))) /\
     (!i. i IN ix ==> IMAGE f a INTER IMAGE f (bb i) SUBSET IMAGE f (a INTER bb i))
     ==> !x y. x IN a UNION UNIONS (IMAGE bb ix) /\ y IN a UNION UNIONS (IMAGE bb ix) /\
               f x = f y ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ia") (CONJUNCTS_THEN2 (LABEL_TAC "ib")
    (CONJUNCTS_THEN2 (LABEL_TAC "dj") (LABEL_TAC "ov")))) THEN
  SUBGOAL_THEN
   `!i x y. i IN ix /\ x IN a /\ y IN (bb:I->A->bool) i /\ (f:A->B) x = f y ==> x = y`
  (LABEL_TAC "ab") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "ov" (MP_TAC o C MATCH_MP (ASSUME `(i:I) IN ix`)) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:A->B) x`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `(x:A) = z /\ (y:A) = z` (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [USE_THEN "ia" MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "ib" MATCH_MP_TAC THEN EXISTS_TAC `i:I` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `(f:A->B) x = f y` THEN UNDISCH_TAC `(f:A->B) x = f z` THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; UNIONS_IMAGE; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `i:I` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `j:I` STRIP_ASSUME_TAC)) THENL
   [USE_THEN "ia" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN USE_THEN "ab" MATCH_MP_TAC THEN EXISTS_TAC `j:I` THEN
    ASM_REWRITE_TAC[];
    USE_THEN "ab" MATCH_MP_TAC THEN EXISTS_TAC `i:I` THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `i:I = j` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "ib" MATCH_MP_TAC THEN
      EXISTS_TAC `j:I` THEN ASM_REWRITE_TAC[];
      USE_THEN "dj" (MP_TAC o SPECL [`i:I`; `j:I`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(f:A->B) x`) THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN CONJ_TAC THENL
       [EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]]]]);;

let MOI_S5P_COVER = prove
 (`!(d:A->bool) y (tt:I->A->bool) rr x1 x2 ee ix.
     (!i. i IN ix ==> tt i UNION rr i = d /\ rr i SUBSET x1 i /\ ee i SUBSET tt i /\
                      x1 i INTER x2 i = ee i) /\
     d SUBSET y UNION UNIONS (IMAGE x2 ix)
     ==> d SUBSET y UNION UNIONS (IMAGE tt ix)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tr") (LABEL_TAC "cv")) THEN
  REWRITE_TAC[SUBSET; IN_UNION; UNIONS_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `?i:I. i IN ix /\ (z:A) IN (tt:I->A->bool) i` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "cv" (MP_TAC o SPEC `z:A` o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_UNION; UNIONS_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC (X_CHOOSE_THEN `i:I` STRIP_ASSUME_TAC)) THEN
  USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(i:I) IN ix`)) THEN STRIP_TAC THEN
  UNDISCH_TAC `~(?i:I. i IN ix /\ (z:A) IN (tt:I->A->bool) i)` THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  EXISTS_TAC `i:I` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`(z:A) IN d`; `(tt:I->A->bool) i UNION rr i = d`; `(rr:I->A->bool) i SUBSET x1 i`;
    `(ee:I->A->bool) i SUBSET tt i`; `(x1:I->A->bool) i INTER x2 i = ee i`;
    `(z:A) IN x2 (i:I)`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 8. The target side at a B-side edge e of v: the finger W_e, the tube of  *)
(* e and the level square E_e; X1 = f_v(K'_v) plus the fingers and tubes of *)
(* the other B-side edges of v, X2 = W_e plus the tube of e.  They meet      *)
(* exactly in E_e (injectivity of f_v, sep, sep2, disjoint A-slabs).         *)
(* ------------------------------------------------------------------------- *)

let moi_s5p_x2 = new_definition
 `moi_s5p_x2 (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N) bv
             (psi:(real^N->bool)->real^3->real^N) e =
    IMAGE (moi_s35_bch ff bv psi e) (moi_s35_bcell INTER moi_s35_slab) UNION
    IMAGE (moi_s35_ach ff av psi e) moi_s35_stube`;;

let moi_s5p_x1 = new_definition
 `moi_s5p_x1 (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
             (av:(real^N->bool)->real^N) bv (psi:(real^N->bool)->real^3->real^N)
             (ff:real^N->real^N->real^3) (cc:(real^N->bool)->real) v e =
    IMAGE (ff v) (moi_s5p_core2 t l av bv psi cc v) UNION
    UNIONS {moi_s5p_x2 ff av bv psi e' | e' |
            moi_s35_edge l e' /\ bv e' = v /\ ~(e' = e)}`;;

let MOI_S5P_CORE2_FINGER = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> moi_s5p_core2 t l av bv psi cc (bv e) INTER
         IMAGE (psi e) (moi_s35_bcell INTER moi_s35_slab) SUBSET
         IMAGE (psi e) (moi_s35_level (&1 / &8))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S5P_CORE_B) THEN
  REWRITE_TAC[SUBSET; IN_INTER; moi_s5p_core2; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                    {x | x IN moi_s35_cube /\ &1 / &8 <= x$3}` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                   (moi_s35_bcell INTER moi_s35_slab)` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) = z` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                   (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`)
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
      SIMP_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) IN moi_s35_slab` THEN UNDISCH_TAC `&1 / &8 <= (z:real^3)$3` THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(e':real^N->bool = e)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                         (IMAGE (psi e') moi_s35_slab)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!e'. moi_s35_edge l e' /\ ~(e = e')
                 ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                              (IMAGE (psi e') moi_s35_slab)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(x:real^N) IN s /\ x IN t ==> DISJOINT s t ==> P`) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                   (moi_s35_bcell INTER moi_s35_slab)` THEN
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                   {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e'}` THEN
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

let MOI_S5P_MODEL_INCL = prove
 (`moi_s35_stube SUBSET {x | x IN moi_s35_slab /\ x$3 <= &1 / &16} /\
   moi_s35_level (&1 / &8) SUBSET moi_s35_bcell INTER moi_s35_slab /\
   moi_s35_level (&1 / &8) SUBSET {x | x IN moi_s35_cube /\ &1 / &8 <= x$3} /\
   {x | x IN moi_s35_slab /\ x$3 <= &1 / &16} SUBSET moi_s35_slab /\
   moi_s35_bcell INTER moi_s35_slab SUBSET moi_s35_slab /\
   moi_s35_stube SUBSET moi_s35_slab`,
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
  REAL_ARITH_TAC);;

let MOI_S5P_IMAGE_INTER_INJ = prove
 (`!(f:A->B) u a b.
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\ a SUBSET u /\ b SUBSET u
     ==> IMAGE f a INTER IMAGE f b = IMAGE f (a INTER b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE] THEN
  X_GEN_TAC `z:B` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MESON_TAC[]]);;

let MOI_S5P_X_INTER = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e
     ==> moi_s5p_x1 t l av bv psi ff cc (bv e) e INTER moi_s5p_x2 ff av bv psi e =
         IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (MP_TAC o SPEC `e:real^N->bool` o REWRITE_RULE[moi_s35_sep])
      (CONJUNCTS_THEN2 (LABEL_TAC "sep2" o REWRITE_RULE[moi_s35_sep2]) ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sep") THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (LABEL_TAC "fv") (CONJUNCTS_THEN2 (LABEL_TAC "fe")
     (CONJUNCTS_THEN2 (LABEL_TAC "fo") (CONJUNCTS_THEN2 (LABEL_TAC "fs")
       (CONJUNCTS_THEN2 (LABEL_TAC "fn") (LABEL_TAC "fg"))))))
   (K ALL_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  USE_THEN "fv" (MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`)) THEN
  DISCH_THEN(LABEL_TAC "inj" o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `cc:(real^N->bool)->real`; `(bv:(real^N->bool)->real^N) e`]
    MOI_S5P_CORE2_CPLUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c2p") (LABEL_TAC "fgp")) THEN
  MP_TAC MOI_S5P_MODEL_INCL THEN STRIP_TAC THEN
  ABBREV_TAC `v = (bv:(real^N->bool)->real^N) e` THEN
  SUBGOAL_THEN
   `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
          (moi_s35_bcell INTER moi_s35_slab) =
    IMAGE (ff v) (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                        (moi_s35_bcell INTER moi_s35_slab)) /\
    IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) =
    IMAGE (ff v) (IMAGE (psi e) (moi_s35_level (&1 / &8))) /\
    IMAGE (moi_s35_bch ff bv psi e) {x | x IN moi_s35_cube /\ &1 / &8 <= x$3} =
    IMAGE (ff v) (IMAGE (psi e) {x | x IN moi_s35_cube /\ &1 / &8 <= x$3})`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s35_bch; IMAGE_o]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s5p_core2 t l av bv psi cc v INTER
    IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_bcell INTER moi_s35_slab) =
    IMAGE (psi e) (moi_s35_level (&1 / &8))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                     `cc:(real^N->bool)->real`; `e:real^N->bool`] MOI_S5P_CORE2_FINGER) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                     `e:real^N->bool`] MOI_S5P_LEVEL_IN_CORE) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `moi_s35_level (&1 / &8)` (ISPEC `(psi:(real^N->bool)->real^3->real^N) e`
        (INST_TYPE [`:real^3`,`:A`; `:real^N`,`:B`] IMAGE_SUBSET))) THEN
      REWRITE_TAC[moi_s5p_core2] THEN
      MAP_EVERY UNDISCH_TAC [`moi_s35_level (&1 / &8) SUBSET moi_s35_bcell INTER moi_s35_slab`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((ff:real^N->real^N->real^3) v) (moi_s5p_core t l av bv psi v) SUBSET
    IMAGE (moi_s35_bch ff bv psi e) {x | x IN moi_s35_cube /\ &1 / &8 <= x$3}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`] MOI_S5P_CORE_B) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e'. moi_s35_edge l e' /\ (av:(real^N->bool)->real^N) e' = v
         ==> ~(e' = e) /\
             IMAGE ((ff:real^N->real^N->real^3) v)
                   (IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                          {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e'})
             SUBSET IMAGE (moi_s35_ach ff av psi e') moi_s35_slab`
  (LABEL_TAC "cut") THENL
   [X_GEN_TAC `e':real^N->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = v)` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(av:(real^N->bool)->real^N) e' = v`)) THEN
      REWRITE_TAC[moi_s35_ach; IMAGE_o] THEN
      REPEAT(MATCH_MP_TAC IMAGE_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE ((ff:real^N->real^N->real^3) v) (moi_s5p_core2 t l av bv psi cc v))
             (IMAGE (moi_s35_ach ff av psi e) moi_s35_stube)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5p_core2; IMAGE_UNION; DISJOINT_UNION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s' t'. (s:real^3->bool) SUBSET s' /\ t SUBSET t' /\
                               DISJOINT s' t' ==> DISJOINT s t`) THEN
      MAP_EVERY EXISTS_TAC
       [`IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
               {x | x IN moi_s35_cube /\ &1 / &8 <= x$3}`;
        `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
               {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC)) THEN
      USE_THEN "cut" (MP_TAC o C MATCH_MP (CONJ (ASSUME `moi_s35_edge l (e':real^N->bool)`)
        (ASSUME `(av:(real^N->bool)->real^N) e' = v`))) THEN STRIP_TAC THEN
      USE_THEN "fs" (MP_TAC o SPECL [`e':real^N->bool`; `e:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      MAP_EVERY UNDISCH_TAC
       [`z = (ff:real^N->real^N->real^3) v x`;
        `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                  {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e'}`;
        `IMAGE ((ff:real^N->real^N->real^3) v)
               (IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                      {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e'})
         SUBSET IMAGE (moi_s35_ach ff av psi e') moi_s35_slab`;
        `(z:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                       moi_s35_stube`;
        `moi_s35_stube SUBSET moi_s35_slab`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e'. moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = v /\ ~(e' = e)
         ==> DISJOINT (moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e')
                      (moi_s5p_x2 ff av bv psi e)`
  (LABEL_TAC "x2d") THENL
   [X_GEN_TAC `e':real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `DISJOINT (IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e')
                      (moi_s35_bcell INTER moi_s35_slab))
               (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_bcell INTER moi_s35_slab)) /\
      DISJOINT (IMAGE (moi_s35_bch ff bv psi e') (moi_s35_bcell INTER moi_s35_slab))
               (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab) /\
      DISJOINT (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_bcell INTER moi_s35_slab))
               (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab) /\
      DISJOINT (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab)
               (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[moi_s35_bch; IMAGE_o] THEN
        MP_TAC(ISPECL [`(ff:real^N->real^N->real^3) v`;
                       `moi_s35_cplus t l av bv psi (v:real^N)`;
                       `IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                              (moi_s35_bcell INTER moi_s35_slab)`;
                       `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                              (moi_s35_bcell INTER moi_s35_slab)`] MOI_S5P_IMAGE_INTER_INJ) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [USE_THEN "inj" ACCEPT_TAC;
            USE_THEN "fgp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
            USE_THEN "fgp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
          DISCH_TAC] THEN
        REWRITE_TAC[DISJOINT] THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
        SUBGOAL_THEN `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                               (IMAGE (psi e') moi_s35_slab)` MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!e'. moi_s35_edge l e' /\ ~(e = e')
                   ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                                (IMAGE (psi e') moi_s35_slab)`) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE `(a:real^N->bool) SUBSET s /\ b SUBSET t
                               ==> DISJOINT t s ==> a INTER b = {}`) THEN
        CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        USE_THEN "sep2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "sep2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
        USE_THEN "fs" (MP_TAC o SPECL [`e':real^N->bool`; `e:real^N->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s5p_x2] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e')
                       (moi_s35_bcell INTER moi_s35_slab))
                (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_bcell INTER moi_s35_slab))`;
      `DISJOINT (IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e')
                       (moi_s35_bcell INTER moi_s35_slab))
                (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab)`;
      `DISJOINT (IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                       (moi_s35_bcell INTER moi_s35_slab))
                (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab)`;
      `DISJOINT (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e') moi_s35_slab)
                (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab)`] THEN
    MP_TAC(ISPECL [`moi_s35_ach (ff:real^N->real^N->real^3) av psi e`;
                   `moi_s35_stube`; `moi_s35_slab`] IMAGE_SUBSET) THEN
    MP_TAC(ISPECL [`moi_s35_ach (ff:real^N->real^N->real^3) av psi e'`;
                   `moi_s35_stube`; `moi_s35_slab`] IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((ff:real^N->real^N->real^3) v) (moi_s5p_core2 t l av bv psi cc v) INTER
    IMAGE (moi_s35_bch ff bv psi e) (moi_s35_bcell INTER moi_s35_slab) =
    IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(ff:real^N->real^N->real^3) v`;
                   `moi_s35_cplus t l av bv psi (v:real^N)`;
                   `moi_s5p_core2 t l av bv psi cc (v:real^N)`;
                   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                          (moi_s35_bcell INTER moi_s35_slab)`] MOI_S5P_IMAGE_INTER_INJ) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "inj" ACCEPT_TAC; USE_THEN "c2p" ACCEPT_TAC;
        USE_THEN "fgp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; moi_s5p_x1; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e':real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THENL
     [UNDISCH_TAC `(z:real^3) IN moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e` THEN
      REWRITE_TAC[moi_s5p_x2; IN_UNION] THEN STRIP_TAC THENL
       [UNDISCH_TAC `IMAGE ((ff:real^N->real^N->real^3) v) (moi_s5p_core2 t l av bv psi cc v)
                     INTER IMAGE (moi_s35_bch ff bv psi e) (moi_s35_bcell INTER moi_s35_slab) =
                     IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8))` THEN
        MAP_EVERY UNDISCH_TAC
         [`(z:real^3) IN IMAGE ((ff:real^N->real^N->real^3) v)
                         (moi_s5p_core2 t l av bv psi cc v)`;
          `(z:real^3) IN IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                         (moi_s35_bcell INTER moi_s35_slab)`] THEN
        SET_TAC[];
        UNDISCH_TAC `DISJOINT (IMAGE ((ff:real^N->real^N->real^3) v)
                                     (moi_s5p_core2 t l av bv psi cc v))
                              (IMAGE (moi_s35_ach ff av psi e) moi_s35_stube)` THEN
        MAP_EVERY UNDISCH_TAC
         [`(z:real^3) IN IMAGE ((ff:real^N->real^N->real^3) v)
                         (moi_s5p_core2 t l av bv psi cc v)`;
          `(z:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                         moi_s35_stube`] THEN
        SET_TAC[]];
      USE_THEN "x2d" (MP_TAC o SPEC `e':real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(z:real^3) IN moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e'`;
        `(z:real^3) IN moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e`] THEN
      SET_TAC[]];
    REWRITE_TAC[moi_s5p_x1; moi_s5p_x2] THEN
    UNDISCH_TAC `IMAGE ((ff:real^N->real^N->real^3) v) (moi_s5p_core2 t l av bv psi cc v)
                 INTER IMAGE (moi_s35_bch ff bv psi e) (moi_s35_bcell INTER moi_s35_slab) =
                 IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8))` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. The two charts of an edge after the approximations: bch e is a PL     *)
(* embedding of the upper half, ach e one of the model domain (edge_conf).   *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_CHART_PL = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_edge l e
     ==> pl_map_on moi_s35_upper (moi_s35_bch ff bv psi e) /\
         (!x y. x IN moi_s35_upper /\ y IN moi_s35_upper /\
                moi_s35_bch ff bv psi e x = moi_s35_bch ff bv psi e y ==> x = y) /\
         pl_map_on moi_s35_dom (moi_s35_ach ff av psi e) /\
         (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\
                moi_s35_ach ff av psi e x = moi_s35_ach ff av psi e y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "fv") (K ALL_TAC))
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pe"))) THEN
  SUBGOAL_THEN
   `pl_map_on moi_s35_upper ((psi:(real^N->bool)->real^3->real^N) e) /\
    IMAGE (psi e) moi_s35_upper SUBSET moi_s35_cplus t l av bv psi (bv e) /\
    pl_map_on (moi_s35_cplus t l av bv psi (bv e)) ((ff:real^N->real^N->real^3) (bv e)) /\
    (!x y. x IN moi_s35_cplus t l av bv psi (bv e) /\
           y IN moi_s35_cplus t l av bv psi (bv e) /\ ff (bv e) x = ff (bv e) y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN CONJ_TAC THENL
       [UNDISCH_TAC `pl_homeomorphism
                      (moi_s35_cube,derived_dual_cell t l ((av:(real^N->bool)->real^N) e)
                                    UNION derived_dual_cell t l (bv e))
                      ((psi:(real^N->bool)->real^3->real^N) e,q)` THEN
        SIMP_TAC[pl_homeomorphism];
        REWRITE_TAC[MOI_S5N_HALVES; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
        REWRITE_TAC[SUBSET_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT;
                    VEC_COMPONENT] THEN REAL_ARITH_TAC];
      ASM_REWRITE_TAC[moi_s35_cplus] THEN SET_TAC[];
      USE_THEN "fv" (MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`)) THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
      USE_THEN "fv" (MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`)) THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)];
    ALL_TAC] THEN
  USE_THEN "pe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[moi_s35_edge_conf] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_s35_bch] THEN MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s35_bch; o_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                 (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`) (concl th))) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN moi_s35_upper` THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN moi_s35_upper` THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x y. x IN moi_s35_cplus t l av bv psi (bv e) /\
                 y IN moi_s35_cplus t l av bv psi (bv e) /\
                 (ff:real^N->real^N->real^3) (bv e) x = ff (bv e) y ==> x = y`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper SUBSET
                  moi_s35_cplus t l av bv psi (bv e)`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC]);;

(* The core as an intersection of chart images.                             *)

let MOI_S5P_CORE_INTERS = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi v.
     moi_s35_charts t l g av bv psi
     ==> moi_s5p_core t l av bv psi v =
         derived_dual_cell t l (v:real^N) INTER
         INTERS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                       (moi_s35_cube DIFF moi_s5p_osl) | e |
                 moi_s35_edge l e /\ ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e
        ==> derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
            derived_dual_cell t l (bv e) =
            IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube /\
            (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\ psi e x = psi e y ==> x = y) /\
            (psi e) continuous_on moi_s35_cube`
  (LABEL_TAC "cv") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`] MOI_S5P_CHART_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^N->real^3`) (K ALL_TAC)))))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pl_homeomorphism
                  (moi_s35_cube,derived_dual_cell t l ((av:(real^N->bool)->real^N) e)
                                UNION derived_dual_cell t l (bv e))
                  ((psi:(real^N->bool)->real^3->real^N) e,q)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[moi_s5p_core; IN_DIFF; IN_INTER; INTERS_GSPEC; IN_ELIM_THM;
                IN_UNIONS; NOT_EXISTS_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN derived_dual_cell t l v` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC `e:real^N->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      (SUBGOAL_THEN `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                         moi_s35_cube` MP_TAC THENL
        [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
           is_comb (lhs (concl th)) && is_comb(rand(concl th)) &&
           can (find_term ((=) `moi_s35_cube`)) (rand (concl th)))) THEN
         REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[];
         ALL_TAC] THEN
       REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
       DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                         moi_s5p_osl` o check (is_forall o concl)) THEN
       REWRITE_TAC[] THEN CONJ_TAC THENL
        [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
         ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]]);
      DISCH_TAC THEN X_GEN_TAC `s:real^N->bool` THEN
      REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `e:real^N->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) SUBST1_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^3) = z` SUBST_ALL_TAC THENL
       [USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
        REPEAT CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          UNDISCH_TAC `(z:real^3) IN moi_s5p_osl` THEN SIMP_TAC[moi_s5p_osl; IN_ELIM_THM];
          MAP_EVERY UNDISCH_TAC
           [`(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y`;
            `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e z`] THEN
          MESON_TAC[]];
        UNDISCH_TAC `~((z:real^3) IN moi_s5p_osl)` THEN ASM_REWRITE_TAC[]]]);;

(* The core and its cut version are compact.                                 *)

let MOI_S5P_CORE_COMPACT = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ {v} IN l
     ==> compact (moi_s5p_core t l av bv psi v) /\
         compact (moi_s5p_core2 t l av bv psi cc v)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (derived_dual_cell t l (v:real^N))` ASSUME_TAC THENL
   [USE_THEN "tube" (MP_TAC o C MATCH_MP
      (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`) o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    MESON_TAC[MOI_S5C_CELL_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {e | moi_s35_edge l e /\
                ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5V_EDGES_FINITE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi` THEN
    REWRITE_TAC[moi_s35_charts] THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`) o
      CONJUNCT1) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e
        ==> (psi:(real^N->bool)->real^3->real^N) e continuous_on moi_s35_cube`
  (LABEL_TAC "pc") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`] MOI_S5P_CHART_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->real^3` MP_TAC) THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (moi_s5p_core t l av bv psi (v:real^N))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `v:real^N`] MOI_S5P_CORE_INTERS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_INTERS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `e:real^N->bool` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      CONJ_TAC THENL [USE_THEN "pc" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
      SUBGOAL_THEN `moi_s35_cube DIFF moi_s5p_osl =
                    moi_s35_cube INTER {x:real^3 | &1 / &8 <= abs(x$3)}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; moi_s5p_osl; IN_ELIM_THM] THEN
        GEN_TAC THEN ASM_CASES_TAC `(x:real^3) IN moi_s35_cube` THEN
        ASM_REWRITE_TAC[REAL_NOT_LT];
        ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
      SUBGOAL_THEN `{x:real^3 | &1 / &8 <= abs(x$3)} =
                    {x | x$3 >= &1 / &8} UNION {x | x$3 <= -- (&1 / &8)}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
        MATCH_MP_TAC CLOSED_UNION THEN
        REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; CLOSED_HALFSPACE_COMPONENT_LE]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s5p_core2] THEN MATCH_MP_TAC COMPACT_UNION THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{e | moi_s35_edge l e /\ ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      CONJ_TAC THENL
       [USE_THEN "pc" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
        SIMP_TAC[]];
      SUBGOAL_THEN `{x:real^3 | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e} =
                    moi_s35_slab INTER {x | x$3 <= cc e}` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
      REWRITE_TAC[MOI_S5A_MODEL_COMPACT; CLOSED_HALFSPACE_COMPONENT_LE]]]);;

(* ------------------------------------------------------------------------- *)
(* 10. Compactness of the regions, the core image inside D_v, and the cover  *)
(* of D_v by the core image and the B-side regions.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_X2_COMPACT = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_edge l e
     ==> compact (moi_s5p_x2 ff av bv psi e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_CHART_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `cc:(real^N->bool)->real`; `(bv:(real^N->bool)->real^N) e`]
    MOI_S5P_CORE2_CPLUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `e:real^N->bool`] MOI_S5P_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e continuous_on moi_s35_cube`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism
                  (moi_s35_cube,derived_dual_cell t l ((av:(real^N->bool)->real^N) e)
                                UNION derived_dual_cell t l (bv e))
                  ((psi:(real^N->bool)->real^3->real^N) e,q)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`) o
    CONJUNCT1 o CONJUNCT1) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP PL_MAP_ON_IMP_CONTINUOUS_ON o CONJUNCT1) THEN
  REWRITE_TAC[moi_s5p_x2] THEN MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[moi_s35_bch] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER] THEN
        REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC COMPACT_INTER THEN REWRITE_TAC[MOI_S5A_MODEL_COMPACT]];
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN REWRITE_TAC[MOI_S5A_MODEL_BASIC];
      REWRITE_TAC[MOI_S5A_MODEL_COMPACT]]]);;

let MOI_S5P_CORE_CSRC = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc v.
     moi_s35_charts t l g av bv psi /\ (!e. moi_s35_edge l e ==> abs(cc e) <= &1 / &512)
     ==> moi_s5p_core t l av bv psi v SUBSET moi_s35_csrc t l av bv psi cc v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `?e. moi_s35_edge l e /\ ((av:(real^N->bool)->real^N) e = v \/ bv e = v) /\
                     (x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`] MOI_S5P_CHART_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs((y:real^3)$3) = &1 / &8` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN moi_s5p_core t l av bv psi v` THEN
      REWRITE_TAC[moi_s5p_core; IN_DIFF; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_osl` o
        CONJUNCT2) THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `(~r ==> p /\ q) ==> ~(p /\ q) ==> r`) THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN UNDISCH_TAC `~(abs((y:real^3)$3) = &1 / &8)` THEN
        REWRITE_TAC[moi_s5p_osl; IN_ELIM_THM] THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
        SIMP_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN derived_dual_cell t l v` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN moi_s5p_core t l av bv psi v` THEN
      SIMP_TAC[moi_s5p_core; IN_DIFF];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s35_csrc; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(bv:(real^N->bool)->real^N) e = v` THENL
     [DISJ1_TAC THEN DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      SUBGOAL_THEN `&0 <= (y:real^3)$3` MP_TAC THENL
       [SUBGOAL_THEN `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                          moi_s35_upper` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:real^3) = y'` SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                   (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`)
                (concl th))) THEN
          REPEAT CONJ_TAC THENL
           [UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
            SIMP_TAC[];
            UNDISCH_TAC `(y':real^3) IN moi_s35_upper` THEN
            REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[];
            ASM_MESON_TAC[]];
          UNDISCH_TAC `(y':real^3) IN moi_s35_upper` THEN
          REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN
      UNDISCH_TAC `abs((y:real^3)$3) = &1 / &8` THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `(av:(real^N->bool)->real^N) e = v` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^3)$3 <= &0` MP_TAC THENL
       [SUBGOAL_THEN `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                          moi_s35_lower` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:real^3) = y'` SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                   (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`)
                (concl th))) THEN
          REPEAT CONJ_TAC THENL
           [UNDISCH_TAC `(y:real^3) IN moi_s35_slab` THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
            SIMP_TAC[];
            UNDISCH_TAC `(y':real^3) IN moi_s35_lower` THEN
            REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[];
            ASM_MESON_TAC[]];
          UNDISCH_TAC `(y':real^3) IN moi_s35_lower` THEN
          REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `abs((y:real^3)$3) = &1 / &8` THEN
      MP_TAC(MATCH_MP (ASSUME `!e:real^N->bool. moi_s35_edge l e
                                   ==> abs((cc:(real^N->bool)->real) e) <= &1 / &512`)
                      (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[moi_s35_csrc; IN_UNION; IN_DIFF] THEN DISJ1_TAC THEN DISJ1_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN moi_s5p_core t l av bv psi v` THEN
      SIMP_TAC[moi_s5p_core; IN_DIFF];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      UNDISCH_TAC `~(?e. moi_s35_edge l e /\ ((av:(real^N->bool)->real^N) e = v \/ bv e = v) /\
                     (x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)` THEN
      MESON_TAC[]]]);;

(* The core image lies in D_v, off the tubes and the A-cells of the B-side   *)
(* edges of v.                                                              *)

let MOI_S5P_CORE_IN_D = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc v.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ {v} IN l
     ==> IMAGE (ff v) (moi_s5p_core t l av bv psi v) SUBSET xx v /\
         (!e. moi_s35_edge l e /\ bv e = v
              ==> DISJOINT (IMAGE (ff v) (moi_s5p_core t l av bv psi v))
                           (IMAGE (moi_s35_ach ff av psi e)
                                  {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}) /\
                  DISJOINT (IMAGE (ff v) (moi_s5p_core t l av bv psi v)) (xx (av e))) /\
         IMAGE (ff v) (moi_s5p_core t l av bv psi v) SUBSET
         moi_s35_dcell l av bv xx v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sep" o REWRITE_RULE[moi_s35_sep]) ASSUME_TAC))) THEN
  UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (LABEL_TAC "fv") (CONJUNCTS_THEN2 (LABEL_TAC "fe") (K ALL_TAC)))
   (CONJUNCTS_THEN2 (LABEL_TAC "pc") (LABEL_TAC "pe"))) THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e /\ bv e = v
        ==> DISJOINT (IMAGE ((ff:real^N->real^N->real^3) v)
                            (moi_s5p_core t l av bv psi v))
                     (IMAGE (moi_s35_ach ff av psi e)
                            {x | x IN moi_s35_slab /\ x$3 <= &1 / &16})`
  (LABEL_TAC "d1") THENL
   [X_GEN_TAC `e:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "sep" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET s' ==> DISJOINT s' t ==> DISJOINT s t`) THEN
    REWRITE_TAC[moi_s35_bch; IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`] MOI_S5P_CORE_B) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((ff:real^N->real^N->real^3) v) (moi_s5p_core t l av bv psi v)
                SUBSET xx v`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_s5p_core t l av bv psi (v:real^N) SUBSET moi_s35_csrc t l av bv psi cc v`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S5P_CORE_CSRC THEN EXISTS_TAC `g:real^N->real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`)) THEN
    MATCH_MP_TAC(SET_RULE
     `(k:real^3->bool) SUBSET c /\ DISJOINT k u ==> x DIFF u = c DIFF u ==> k SUBSET x`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(!u. u IN f ==> DISJOINT (k:real^3->bool) u)
                           ==> DISJOINT k (UNIONS f)`) THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "d1" (MP_TAC o C MATCH_MP (ASSUME
      `moi_s35_edge l (e:real^N->bool) /\ (bv:(real^N->bool)->real^N) e = v`)) THEN
    MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET t' ==> DISJOINT s t' ==> DISJOINT s t`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[MOI_S5P_MODEL_INCL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e /\ bv e = v
        ==> DISJOINT (IMAGE ((ff:real^N->real^N->real^3) v)
                            (moi_s5p_core t l av bv psi v)) (xx ((av:(real^N->bool)->real^N) e))`
  (LABEL_TAC "d2") THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "d1" (MP_TAC o C MATCH_MP (ASSUME
      `moi_s35_edge l (e:real^N->bool) /\ (bv:(real^N->bool)->real^N) e = v`)) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1 o CONJUNCT2)) THEN
    USE_THEN "pe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[moi_s35_edge_conf] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2 o CONJUNCT2) THEN
    SUBGOAL_THEN `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                    {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e} SUBSET
                  IMAGE (moi_s35_ach ff av psi e)
                    {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN
      UNDISCH_TAC `(x:real^3)$3 <= (cc:(real^N->bool)->real) e` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(bv:(real^N->bool)->real^N) e = v`] THEN
    UNDISCH_TAC `IMAGE ((ff:real^N->real^N->real^3) v)
                   (moi_s5p_core t l av bv psi v) SUBSET xx v` THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!k x a s s1 s2:real^3->bool.
        (k SUBSET x ==> s1 SUBSET s2 ==> a INTER s = s1 ==> a INTER x SUBSET s ==>
         DISJOINT k s2 ==> DISJOINT k a)`);
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "d1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "d2" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[moi_s35_dcell] THEN
    MATCH_MP_TAC(SET_RULE `(k:real^3->bool) SUBSET x /\ (!u. u IN f ==> DISJOINT k u)
                           ==> k SUBSET x DIFF UNIONS f`) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "d2" (MP_TAC o C MATCH_MP (ASSUME
      `moi_s35_edge l (e:real^N->bool) /\ (bv:(real^N->bool)->real^N) e = v`)) THEN
    MP_TAC(ISPEC `(xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e)`
      INTERIOR_SUBSET) THEN
    SET_TAC[]]);;

(* D_v is covered by the core image and the B-side regions of v.             *)

let MOI_S5P_D_COVER = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w av bv psi ff xx cc v.
     moi_s35_post t l h w av bv psi ff xx cc /\ {v} IN l
     ==> moi_s35_dcell l av bv xx v SUBSET
         IMAGE (ff v) (moi_s5p_core2 t l av bv psi cc v) UNION
         UNIONS {moi_s5p_x2 ff av bv psi e | e | moi_s35_edge l e /\ bv e = v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
  REWRITE_TAC[moi_s35_post] THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`) o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `cc:(real^N->bool)->real`;
                 `v:real^N`] MOI_S5P_CSRC_COVER) THEN
  DISCH_THEN(LABEL_TAC "scv" o REWRITE_RULE[SUBSET]) THEN
  REWRITE_TAC[SUBSET; moi_s35_dcell; IN_DIFF] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  ASM_CASES_TAC
   `?e. (moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v) /\
        (z:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                            moi_s35_stube` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[moi_s5p_x2; IN_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN IMAGE ((ff:real^N->real^N->real^3) v)
                                (moi_s35_csrc t l av bv psi cc v)` MP_TAC THENL
   [UNDISCH_TAC `xx (v:real^N) DIFF
                 UNIONS {IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                               moi_s35_stube | e | moi_s35_edge l e /\ bv e = v} =
                 IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v) DIFF
                 UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
                         moi_s35_edge l e /\ bv e = v}` THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(?e. (moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v) /\
        (z:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                            moi_s35_stube)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN moi_s5p_core2 t l av bv psi cc v UNION
                UNIONS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                              (moi_s35_bcell INTER moi_s35_slab) | e |
                        moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}` MP_TAC THENL
   [USE_THEN "scv" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real^N->bool`
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC))) THENL
   [DISJ1_TAC THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[moi_s5p_x2; IN_UNION] THEN
    DISJ1_TAC THEN REWRITE_TAC[moi_s35_bch; IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 11. The level square E_e = bch e(level 1/8) of a B-side edge e of v: a    *)
(* PL 2-cell inside D_v.                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_E_BASIC = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_edge l e
     ==> IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) SUBSET
         IMAGE (ff (bv e)) (moi_s5p_core t l av bv psi (bv e)) /\
         IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) SUBSET
         moi_s35_dcell l av bv xx (bv e) /\
         pl_cell_with_boundary 2
           (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)))
           (IMAGE (moi_s35_bch ff bv psi e)
              (IMAGE (moi_s35_lift (&1 / &8))
                 (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  SUBGOAL_THEN
   `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e) (moi_s35_level (&1 / &8))
    SUBSET IMAGE (ff (bv e)) (moi_s5p_core t l av bv psi (bv e))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_bch; IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC MOI_S5P_LEVEL_IN_CORE THEN EXISTS_TAC `g:real^N->real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((ff:real^N->real^N->real^3) (bv e))
                      (moi_s5p_core t l av bv psi (bv e))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                   `(bv:(real^N->bool)->real^N) e`] MOI_S5P_CORE_IN_D) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_CHART_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s35_level (&1 / &8)`;
                 `IMAGE (moi_s35_lift (&1 / &8))
                    (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`;
                 `moi_s35_upper`; `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e`]
    MOI_S5P_CELL_EMBED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `&1 / &8` MOI_S5P_LEVEL_SQ) THEN
      ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC MOI_S5C_LIFT_CELL THEN MATCH_MP_TAC MOI_S5C_POLYTOPE_CELL THEN
      REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET] THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
      SIMP_TAC[] THEN REAL_ARITH_TAC];
    SIMP_TAC[]]);;

(* A continuous map keeps a small ball around an interior point of its      *)
(* domain off a closed set that misses the image point.                      *)

let MOI_S5P_CONT_AVOID = prove
 (`!(f:real^M->real^N) s x k.
     f continuous_on s /\ x IN interior s /\ closed k /\ ~(f x IN k)
     ==> ?r. &0 < r /\ !z. z IN ball(x,r) ==> z IN s /\ ~(f z IN k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous (at x)` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^N) DIFF k` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `interior s:real^M->bool` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^M` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `ball(x:real^M,d2) SUBSET interior s` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `(f:real^M->real^N) z IN ball(f x,d)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `ball((f:real^M->real^N) x,d) SUBSET (:real^N) DIFF k` THEN
      SET_TAC[]]]);;

(* Points of the chart of a B-side edge e above the level 1/8 (off the other *)
(* slabs at bv e) lie in the core of bv e; points of the B-cell part of the   *)
(* slab that avoid the A-side tube and the A-cell of e lie in D_(bv e).      *)

let MOI_S5P_UPPER_CORE = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e z.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\
     z IN moi_s35_cube /\ &1 / &8 <= z$3 /\
     ~(psi e z IN UNIONS {IMAGE (psi e') moi_s35_slab | e' |
                          moi_s35_edge l e' /\ (av e' = bv e \/ bv e' = bv e) /\
                          ~(e' = e)})
     ==> psi e z IN moi_s5p_core t l av bv psi (bv e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  REWRITE_TAC[moi_s5p_core; IN_DIFF] THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                 derived_dual_cell t l (bv e)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[moi_s35_upper; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 / &8 <= (z:real^3)$3` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `e':real^N->bool` THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `e':real^N->bool = e` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM; moi_s5p_osl; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) = x` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!a b. a IN moi_s35_cube /\ b IN moi_s35_cube /\
               (psi:(real^N->bool)->real^3->real^N) e a = psi e b ==> a = b`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `&1 / &8 <= (x:real^3)$3` THEN
      UNDISCH_TAC `abs((x:real^3)$3) < &1 / &8` THEN REAL_ARITH_TAC];
    UNDISCH_TAC `~((psi:(real^N->bool)->real^3->real^N) e z IN
                   UNIONS {IMAGE (psi e') moi_s35_slab | e' |
                           moi_s35_edge l e' /\
                           ((av:(real^N->bool)->real^N) e' = bv e \/ bv e' = bv e) /\
                           ~(e' = e)})` THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `!(f:real^3->real^N) s t x. s SUBSET t ==> ~(x IN IMAGE f t) ==> ~(x IN IMAGE f s)`) THEN
    REWRITE_TAC[SUBSET; moi_s5p_osl; moi_s35_slab; IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LT_IMP_LE]]);;

let MOI_S5P_BSLAB_IN_D = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w (g:real^N->real^N->bool)
    av bv psi ff xx cc e z.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e /\
     z IN moi_s35_bcell INTER moi_s35_slab /\
     ~(moi_s35_bch ff bv psi e z IN
       IMAGE (moi_s35_ach ff av psi e) moi_s35_stube UNION xx (av e))
     ==> moi_s35_bch ff bv psi e z IN moi_s35_dcell l av bv xx (bv e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fe") (K ALL_TAC)))
   (CONJUNCTS_THEN2 (LABEL_TAC "pc") (K ALL_TAC))) THEN
  UNDISCH_TAC `moi_s35_sep2 l (av:(real^N->bool)->real^N) bv psi ff` THEN
  REWRITE_TAC[moi_s35_sep2] THEN DISCH_THEN(LABEL_TAC "s2") THEN
  SUBGOAL_THEN
   `!e'. moi_s35_edge l e' /\ ~(e' = e)
         ==> ~(moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
               IMAGE (moi_s35_ach ff av psi e') moi_s35_slab)`
  (LABEL_TAC "oth") THENL
   [X_GEN_TAC `e':real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "s2" (MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!(x:real^3) s t. x IN s ==> DISJOINT s t ==> ~(x IN t)`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
    xx ((bv:(real^N->bool)->real^N) e)`
  ASSUME_TAC THENL
   [USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`)) THEN
    MATCH_MP_TAC(SET_RULE
     `!(x:real^3) a b u. x IN b /\ ~(x IN u) ==> a DIFF u = b DIFF u ==> x IN a`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[moi_s35_bch; o_THM] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[moi_s35_csrc; IN_UNION] THEN DISJ1_TAC THEN DISJ2_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `e':real^N->bool` THEN
      ASM_CASES_TAC `e':real^N->bool = e` THENL
       [FIRST_X_ASSUM SUBST1_TAC THEN
        UNDISCH_TAC `~(moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
                       IMAGE (moi_s35_ach ff av psi e) moi_s35_stube UNION xx (av e))` THEN
        SET_TAC[];
        REWRITE_TAC[GSYM CONJ_ASSOC; TAUT `~(p /\ q /\ r) <=> p /\ q ==> ~r`] THEN
        STRIP_TAC THEN
        USE_THEN "oth" (MP_TAC o SPEC `e':real^N->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE
         `!(f:real^3->real^3) s t x. s SUBSET t ==> ~(x IN IMAGE f t) ==> ~(x IN IMAGE f s)`) THEN
        REWRITE_TAC[MOI_S5P_MODEL_INCL]]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_dcell; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `e':real^N->bool` THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; TAUT `~(p /\ q /\ r) <=> p /\ q ==> ~r`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!(x:real^3) s. ~(x IN s) /\ interior s SUBSET s ==> ~(x IN interior s)`) THEN
  REWRITE_TAC[INTERIOR_SUBSET] THEN
  ASM_CASES_TAC `e':real^N->bool = e` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    UNDISCH_TAC `~(moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
                   IMAGE (moi_s35_ach ff av psi e) moi_s35_stube UNION xx (av e))` THEN
    SET_TAC[];
    DISCH_TAC THEN
    USE_THEN "oth" (MP_TAC o SPEC `e':real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e':real^N->bool)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
                 xx ((bv:(real^N->bool)->real^N) e)` THEN
    UNDISCH_TAC `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
                 xx ((av:(real^N->bool)->real^N) e')` THEN
    SET_TAC[]]);;

(* Interior points of E_e are interior points of D_v (invariance of domain  *)
(* for bch e on a small ball; the ball maps into the core image above the    *)
(* level and into the finger image below it, off the tubes and A-cells).    *)

let MOI_S5P_E_INTERIOR = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e y.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e /\
     y IN moi_s35_level (&1 / &8) /\ abs(y$1) < &1 /\ abs(y$2) < &1
     ==> moi_s35_bch ff bv psi e y IN interior (moi_s35_dcell l av bv xx (bv e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_CHART_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN interior moi_s35_upper /\ (y:real^3) IN interior moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5N_HALVES; INTERIOR_INTERVAL; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_level (&1 / &8)` THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
    UNDISCH_TAC `abs((y:real^3)$1) < &1` THEN UNDISCH_TAC `abs((y:real^3)$2) < &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (LABEL_TAC "fv") (CONJUNCTS_THEN2 (LABEL_TAC "fe")
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fs") (K ALL_TAC)))))
   (CONJUNCTS_THEN2 (LABEL_TAC "pc") (K ALL_TAC))) THEN
  SUBGOAL_THEN
   `FINITE {e':real^N->bool | moi_s35_edge l e' /\
                              ((av:(real^N->bool)->real^N) e' = bv e \/ bv e' = bv e)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5V_EDGES_FINITE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi` THEN
    REWRITE_TAC[moi_s35_charts] THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e':real^N->bool)`) o
      CONJUNCT1) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2);
    ALL_TAC] THEN
  ABBREV_TAC `ss = UNIONS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab | e' |
                          moi_s35_edge l e' /\
                          ((av:(real^N->bool)->real^N) e' = bv e \/ bv e' = bv e) /\
                          ~(e' = e)}` THEN
  SUBGOAL_THEN `closed (ss:real^N->bool) /\
                ~((psi:(real^N->bool)->real^3->real^N) e y IN ss)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{e':real^N->bool | moi_s35_edge l e' /\
                         ((av:(real^N->bool)->real^N) e' = bv e \/ bv e' = bv e)}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e':real^N->bool` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
        MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                       `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                       `e':real^N->bool`] MOI_S5P_CHART_FACTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
        DISCH_THEN(X_CHOOSE_THEN `q':real^N->real^3` MP_TAC) THEN
        REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
        ASM_REWRITE_TAC[MOI_S5A_MODEL_BASIC]];
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `e':real^N->bool` THEN
      REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                             (IMAGE (psi e') moi_s35_slab)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!e'. moi_s35_edge l e' /\ ~(e = e')
                 ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                              (IMAGE (psi e') moi_s35_slab)`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^N) IN s ==> DISJOINT s t ==> ~(x IN t)`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_level (&1 / &8)` THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_stube UNION
            xx ((av:(real^N->bool)->real^N) e)) /\
    ~(moi_s35_bch ff bv psi e y IN
      IMAGE (moi_s35_ach ff av psi e) moi_s35_stube UNION xx (av e))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `moi_s35_dom` THEN REWRITE_TAC[MOI_S5A_MODEL_BASIC] THEN
        MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "fv" (MP_TAC o C MATCH_MP (ASSUME `{(av:(real^N->bool)->real^N) e} IN l`)) THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        MESON_TAC[MOI_S5F_BALL_FACTS]];
      USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> DISJOINT s t /\ DISJOINT s u
                             ==> ~(x IN t UNION u)`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(psi:(real^N->bool)->real^3->real^N) e`; `moi_s35_cube`; `y:real^3`;
                 `ss:real^N->bool`] MOI_S5P_CONT_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pl_homeomorphism
                  (moi_s35_cube,derived_dual_cell t l ((av:(real^N->bool)->real^N) e)
                                UNION derived_dual_cell t l (bv e))
                  ((psi:(real^N->bool)->real^3->real^N) e,q)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))] THEN
  MP_TAC(ISPECL [`moi_s35_bch (ff:real^N->real^N->real^3) bv psi e`; `moi_s35_upper`;
                 `y:real^3`;
                 `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_stube UNION
                  xx ((av:(real^N->bool)->real^N) e)`] MOI_S5P_CONT_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2")))] THEN
  SUBGOAL_THEN
   `!z. z IN ball(y:real^3,min (min r1 r2) (&1 / &64))
        ==> moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
            moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN ball(y,r1) /\ z IN ball(y,r2) /\ abs(z$3 - y$3) < &1 / &64`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(y,min (min r1 r2) (&1 / &64))` THEN
      REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dist(y:real^3,z)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[dist] THEN
      MP_TAC(ISPECL [`y - z:real^3`; `3`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN moi_s35_cube /\ z IN moi_s35_upper /\
                  ~((psi:(real^N->bool)->real^3->real^N) e z IN ss) /\
                  ~(moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
                    IMAGE (moi_s35_ach ff av psi e) moi_s35_stube UNION xx (av e))`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "r1" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(y,r1)`)) THEN
      USE_THEN "r2" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(y,r2)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `&1 / &8 <= (z:real^3)$3` THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `(bv:(real^N->bool)->real^N) e`] MOI_S5P_CORE_IN_D) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[moi_s35_bch; o_THM] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      MATCH_MP_TAC MOI_S5P_UPPER_CORE THEN EXISTS_TAC `g:real^N->real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5P_BSLAB_IN_D THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^3`;
                            `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                            `cc:(real^N->bool)->real`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN moi_s35_upper` THEN
      UNDISCH_TAC `~(&1 / &8 <= (z:real^3)$3)` THEN
      UNDISCH_TAC `abs((z:real^3)$3 - (y:real^3)$3) < &1 / &64` THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_level (&1 / &8)` THEN
      REWRITE_TAC[IN_INTER] THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^3,min (min r1 r2) (&1 / &64)) SUBSET moi_s35_upper`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "r2" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(y,min (min r1 r2) (&1 / &64))` THEN
      REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                      (ball(y:real^3,min (min r1 r2) (&1 / &64))) SUBSET
                moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5A_IOD_INTERIOR THEN
  MAP_EVERY EXISTS_TAC [`moi_s35_upper`; `ball(y:real^3,min (min r1 r2) (&1 / &64))`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_MIN; REAL_ARITH `&0 < &1 / &64`] THEN
  MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* 12. The boundary square of E_e lies in the frontier of D_v: through the   *)
(* inverse chart of e the source cell csrc v has the image of the cube       *)
(* boundary on its boundary, and near E_e the cell D_v is ff v(csrc v).      *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_VERT_EDGES_FINITE = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ {v} IN l
     ==> FINITE {e | moi_s35_edge l e /\ (av e = v \/ bv e = v)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5V_EDGES_FINITE THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi` THEN
  REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`) o
    CONJUNCT1) THEN
  DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2));;

let MOI_S5P_MODEL_INCL2 = prove
 (`moi_s35_upper SUBSET moi_s35_cube /\
   moi_s35_bcell INTER moi_s35_slab SUBSET moi_s35_cube /\
   moi_s35_bcell INTER moi_s35_slab SUBSET moi_s35_slab /\
   (!c. {x | x IN moi_s35_slab /\ x$3 <= c} SUBSET moi_s35_slab)`,
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[]);;

let MOI_S5P_IMAGE_MONO = prove
 (`!(f:real^3->real^N) s t x. s SUBSET t ==> x IN IMAGE f s ==> x IN IMAGE f t`,
  SET_TAC[]);;

let MOI_S5P_OTHER_SLABS = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\
     {v} IN l
     ==> closed (UNIONS {IMAGE (psi e') moi_s35_slab | e' |
                         moi_s35_edge l e' /\ (av e' = v \/ bv e' = v) /\ ~(e' = e)}) /\
         DISJOINT (IMAGE (psi e) moi_s35_slab)
                  (UNIONS {IMAGE (psi e') moi_s35_slab | e' |
                           moi_s35_edge l e' /\ (av e' = v \/ bv e' = v) /\ ~(e' = e)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{e':real^N->bool | moi_s35_edge l e' /\
                       ((av:(real^N->bool)->real^N) e' = v \/ bv e' = v)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5P_VERT_EDGES_FINITE THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `g:real^N->real^N->bool`;
                              `psi:(real^N->bool)->real^3->real^N`] THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e':real^N->bool` THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN MATCH_MP_TAC MOI_S5V_SLAB_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                            `bv:(real^N->bool)->real^N`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[SET_RULE `DISJOINT (s:real^N->bool) t <=> !x. x IN s ==> ~(x IN t)`] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `e':real^N->bool` THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; TAUT `~(p /\ q /\ r /\ s) <=> p /\ q /\ r ==> ~s`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                           (IMAGE (psi e') moi_s35_slab)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!e'. moi_s35_edge l e' /\ ~(e = e')
               ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                            (IMAGE (psi e') moi_s35_slab)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
      UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab` THEN
      SET_TAC[]]]);;

let MOI_S5P_CSRC_IN_CHART = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> moi_s35_csrc t l av bv psi cc (bv e) DIFF
         UNIONS {IMAGE (psi e') moi_s35_slab | e' |
                 moi_s35_edge l e' /\ (av e' = bv e \/ bv e' = bv e) /\ ~(e' = e)}
         SUBSET IMAGE (psi e) moi_s35_cube`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "off")) THEN
  REWRITE_TAC[moi_s35_csrc; IN_UNION; IN_DIFF] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (DISJ_CASES_THEN2 STRIP_ASSUME_TAC MP_TAC) MP_TAC) THENL
   [UNDISCH_TAC `(z:real^N) IN derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)` THEN
    UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                 derived_dual_cell t l (bv e)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN
    REWRITE_TAC[MOI_S5P_MODEL_INCL2];
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `e':real^N->bool = e` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                  (moi_s35_bcell INTER moi_s35_slab)` THEN
      MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN REWRITE_TAC[MOI_S5P_MODEL_INCL2];
      USE_THEN "off" MP_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `e':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                                  (moi_s35_bcell INTER moi_s35_slab)` THEN
      MATCH_MP_TAC(TAUT `(p ==> q) ==> p ==> ~q ==> r`) THEN
      MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN REWRITE_TAC[MOI_S5P_MODEL_INCL2]];
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(e':real^N->bool = e)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "off" MP_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                                {x | x IN moi_s35_slab /\ x$3 <= cc e'}` THEN
    MATCH_MP_TAC(TAUT `(p ==> q) ==> p ==> ~q ==> r`) THEN
    MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN REWRITE_TAC[MOI_S5P_MODEL_INCL2]]);;

let MOI_S5P_LEFT_INV_INJ = prove
 (`!(f:A->B) (g:B->A) t u.
     (!y. y IN t ==> f (g y) = y) /\ u SUBSET t
     ==> !x y. x IN u /\ y IN u /\ g x = g y ==> x = y`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

let MOI_S5P_IMAGE_SUB = prove
 (`!(g:A->B) u t s. u SUBSET t /\ IMAGE g t = s ==> IMAGE g u SUBSET s`,
  SET_TAC[]);;

let MOI_S5P_INJ_MONO = prove
 (`!(f:A->B) s t.
     (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y) /\ s SUBSET t
     ==> (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

(* The source cell is a PL 3-cell for the levels cc of post, which are only *)
(* bounded on edges (source_ok asks for all arguments; csrc reads cc only   *)
(* on edges).                                                                *)

let MOI_S5P_CSRC_CELL = prove
 (`!(t:(real^N->bool)->bool) l av bv (psi:(real^N->bool)->real^3->real^N) cc v.
     moi_s35_source_ok t l av bv psi /\
     (!e. moi_s35_edge l e ==> abs(cc e) <= &1 / &512) /\ {v} IN l
     ==> (?bs. pl_cell_with_boundary 3 (moi_s35_csrc t l av bv psi cc v) bs) /\
         moi_s35_csrc t l av bv psi cc v SUBSET moi_s35_cplus t l av bv psi v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s35_csrc t l av bv psi cc (v:real^N) =
    moi_s35_csrc t l av bv psi (\e. if moi_s35_edge l e then cc e else &0) v`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_s35_csrc] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN EQ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s35_source_ok t l (av:(real^N->bool)->real^N) bv psi` THEN
  REWRITE_TAC[moi_s35_source_ok] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`\e. if moi_s35_edge l e then (cc:(real^N->bool)->real) e else &0`; `v:real^N`] o
    CONJUNCT1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    DISCH_THEN ACCEPT_TAC]);;

(* Points of the cube boundary in the B-cell part of the slab of e give     *)
(* boundary points of csrc (bv e): near them csrc lies in the chart image,  *)
(* and the inverse chart sends them to the boundary of the cube.            *)

let MOI_S5P_CSRC_BD = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi cc e bs y.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\
     pl_cell_with_boundary 3 (moi_s35_csrc t l av bv psi cc (bv e)) bs /\
     y IN moi_s35_bcell INTER moi_s35_slab /\ ~(y IN interior moi_s35_cube)
     ==> psi e y IN bs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `e:real^N->bool`; `(bv:(real^N->bool)->real^N) e`] MOI_S5P_OTHER_SLABS) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `cc:(real^N->bool)->real`; `e:real^N->bool`] MOI_S5P_CSRC_IN_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `ss = UNIONS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab | e' |
                           moi_s35_edge l e' /\
                           ((av:(real^N->bool)->real^N) e' = bv e \/ bv e' = bv e) /\
                           ~(e' = e)}` THEN
  DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~((psi:(real^N->bool)->real^3->real^N) e y IN ss)` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                          ss` THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^N) s t x.
       x IN s ==> DISJOINT (IMAGE f s) t ==> ~(f x IN t)`) THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_bcell INTER moi_s35_slab` THEN SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^N) DIFF ss` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN
  DISCH_THEN(MP_TAC o SPEC `(psi:(real^N->bool)->real^3->real^N) e y`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e y IN
                moi_s35_csrc t l av bv psi cc (bv e)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_csrc; IN_UNION] THEN DISJ1_TAC THEN DISJ2_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s35_cube` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN moi_s35_bcell INTER moi_s35_slab` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[MOI_S5P_MODEL_INCL2];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism
                (moi_s35_cube,derived_dual_cell t l ((av:(real^N->bool)->real^N) e)
                              UNION derived_dual_cell t l (bv e))
                ((psi:(real^N->bool)->real^3->real^N) e,q)` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e) INTER
                ball((psi:(real^N->bool)->real^3->real^N) e y,r) SUBSET
                derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube =
                 derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e) DIFF ss
                 SUBSET IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube` THEN
    UNDISCH_TAC `ball((psi:(real^N->bool)->real^3->real^N) e y,r) SUBSET
                 (:real^N) DIFF ss` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->real^3) ((psi:(real^N->bool)->real^3->real^N) e y) = y`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5P_BD_BY_CHART THEN
  MAP_EVERY EXISTS_TAC [`moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)`;
                        `q:real^N->real^3`; `r:real`; `moi_s35_cube`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                derived_dual_cell t l (bv e)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5P_LEFT_INV_INJ THEN
    MAP_EVERY EXISTS_TAC [`(psi:(real^N->bool)->real^3->real^N) e`;
                          `derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                           derived_dual_cell t l (bv e)`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5P_IMAGE_SUB THEN
    EXISTS_TAC `derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                derived_dual_cell t l (bv e)` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S5P_TUBES_CLOSED = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\ {v} IN l
     ==> closed (UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
                         moi_s35_edge l e /\ bv e = v})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{e:real^N->bool | moi_s35_edge l e /\
                     ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5P_VERT_EDGES_FINITE THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `g:real^N->real^N->bool`;
                            `psi:(real^N->bool)->real^3->real^N`] THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^N->bool` THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
      MOI_S5P_CHART_PL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
    REWRITE_TAC[MOI_S5A_MODEL_BASIC] THEN
    MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S5P_E_OFF_TUBES = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w av bv psi ff xx cc e.
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_edge l e
     ==> DISJOINT (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)))
                  (UNIONS {IMAGE (moi_s35_ach ff av psi e') moi_s35_stube | e' |
                           moi_s35_edge l e' /\ bv e' = bv e})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fe")
       (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fs") (K ALL_TAC)))))
     (K ALL_TAC))
   ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE `DISJOINT (s:real^3->bool) t <=> !x. x IN s ==> ~(x IN t)`] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `e':real^N->bool` THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; TAUT `~(p /\ q /\ r) <=> p /\ q ==> ~r`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `e':real^N->bool = e` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                                    (moi_s35_level (&1 / &8))` THEN
    SET_TAC[];
    USE_THEN "fs" (MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                                    (moi_s35_level (&1 / &8))` THEN
    MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S5P_MODEL_INCL))))) THEN
    SET_TAC[]]);;

(* Boundary points of the level square E_e lie in the frontier of D_(bv e). *)

let MOI_S5P_E_BOUNDARY = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e y.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_source_ok t l av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_edge l e /\
     y IN moi_s35_level (&1 / &8) /\ ~(y IN interior moi_s35_cube)
     ==> moi_s35_bch ff bv psi e y IN frontier (moi_s35_dcell l av bv xx (bv e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_E_BASIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e y IN
                moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                       (moi_s35_level (&1 / &8)) SUBSET
                 moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_level (&1 / &8)` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[frontier; IN_DIFF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC] THEN
  MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (LABEL_TAC "fv") (CONJUNCTS_THEN2 (LABEL_TAC "fe") (K ALL_TAC)))
   (CONJUNCTS_THEN2 (LABEL_TAC "pc") (K ALL_TAC))) THEN
  USE_THEN "fv" (MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `cc:(real^N->bool)->real`;
                 `(bv:(real^N->bool)->real^N) e`] MOI_S5P_CSRC_CELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e':real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e':real^N->bool)`)) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `bs:real^N->bool`) ASSUME_TAC)] THEN
  SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e y IN bs` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5P_CSRC_BD THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                          `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                          `bv:(real^N->bool)->real^N`; `cc:(real^N->bool)->real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_level (&1 / &8)` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[MOI_S5P_MODEL_INCL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(moi_s35_bch (ff:real^N->real^N->real^3) bv psi e y IN
      interior (IMAGE (ff ((bv:(real^N->bool)->real^N) e))
                      (moi_s35_csrc t l av bv psi cc (bv e))))`
  MP_TAC THENL
   [REWRITE_TAC[moi_s35_bch; o_THM] THEN
    MATCH_MP_TAC MOI_S5A_CELL_BD_NOT_INTERIOR THEN
    EXISTS_TAC `bs:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MOI_S5P_INJ_MONO THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN
  MP_TAC(ISPECL
   [`IMAGE ((ff:real^N->real^N->real^3) ((bv:(real^N->bool)->real^N) e))
           (moi_s35_csrc t l av bv psi cc (bv e))`;
    `interior (moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)) DIFF
     UNIONS {IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e') moi_s35_stube | e' |
             moi_s35_edge l e' /\ bv e' = bv e}`] INTERIOR_MAXIMAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e) SUBSET
                    xx (bv e)` MP_TAC THENL
       [REWRITE_TAC[moi_s35_dcell] THEN SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)`
        INTERIOR_SUBSET) THEN
      USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`)) THEN
      MATCH_ACCEPT_TAC(SET_RULE
       `!(a:real^3->bool) b u i d.
          a DIFF u = b DIFF u ==> i SUBSET d ==> d SUBSET a ==> i DIFF u SUBSET b`);
      MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN
      MATCH_MP_TAC MOI_S5P_TUBES_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^3`;
                            `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                            `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC(SET_RULE `!(x:real^3) t s. x IN t ==> t SUBSET s ==> x IN s`) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
      MOI_S5P_E_OFF_TUBES) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) s u y.
      y IN s ==> DISJOINT (IMAGE f s) u ==> ~(f y IN u)`) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S5P_LEVEL_RF = prove
 (`!y:real^3.
     (y IN IMAGE (moi_s35_lift (&1 / &8))
            (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) <=>
      y IN moi_s35_level (&1 / &8) /\ ~(y IN interior moi_s35_cube)) /\
     (y IN moi_s35_level (&1 / &8) /\
      ~(y IN IMAGE (moi_s35_lift (&1 / &8))
              (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))
      ==> abs(y$1) < &1 /\ abs(y$2) < &1)`,
  GEN_TAC THEN REWRITE_TAC[MOI_S5P_SQ_LIFT] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
  REWRITE_TAC[moi_s35_level; IN_ELIM_THM; MOI_S5A_CUBE_IN] THEN
  REWRITE_TAC[moi_s35_cube; INTERIOR_INTERVAL; IN_INTERVAL; DIMINDEX_3; FORALL_3;
              VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* E_e is properly embedded in D_(bv e): a PL 2-cell inside D_(bv e)        *)
(* meeting its frontier exactly in the boundary square.                     *)

let MOI_S5P_E_PROPER = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_source_ok t l av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e
     ==> pl_cell_with_boundary 2
           (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)))
           (IMAGE (moi_s35_bch ff bv psi e)
              (IMAGE (moi_s35_lift (&1 / &8))
                 (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))) /\
         IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) SUBSET
         moi_s35_dcell l av bv xx (bv e) /\
         IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) INTER
         frontier (moi_s35_dcell l av bv xx (bv e)) =
         IMAGE (moi_s35_bch ff bv psi e)
           (IMAGE (moi_s35_lift (&1 / &8))
              (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_E_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_INTER] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(CONJUNCT2(SPEC `y:real^3` MOI_S5P_LEVEL_RF)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_IMAGE]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`;
                   `y:real^3`] MOI_S5P_E_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x IN frontier (moi_s35_dcell l (av:(real^N->bool)->real^N) bv xx
                                  ((bv:(real^N->bool)->real^N) e))` THEN
    ASM_REWRITE_TAC[frontier; IN_DIFF] THEN SIMP_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s35_level (&1 / &8) /\ ~(y IN interior moi_s35_cube)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT1(SPEC `y:real^3` MOI_S5P_LEVEL_RF))] THEN
      REWRITE_TAC[IN_IMAGE] THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5P_E_BOUNDARY THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^3`;
                            `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                            `cc:(real^N->bool)->real`] THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 13. The two sides of E_e in D_(bv e): the disk ddisk e misses X1(e), a   *)
(* core point above the level misses X2(e); facts from post for one edge.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_POST_EDGE = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w av bv psi ff xx cc e.
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_edge l e
     ==> abs(cc e) <= &1 / &512 /\
         xx (av e) INTER IMAGE (moi_s35_ach ff av psi e) moi_s35_slab =
         IMAGE (moi_s35_ach ff av psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e} /\
         frontier (xx (av e)) INTER xx (bv e) SUBSET
         IMAGE (moi_s35_ach ff av psi e)
               {x | x IN moi_s35_level (cc e) /\ moi_s35_n x < &5 / &16} /\
         frontier (xx (av e)) INTER frontier (xx (bv e)) SUBSET
         IMAGE (moi_s35_ach ff av psi e) (moi_s35_aflat (cc e)) /\
         moi_s35_single (moi_s35_ach ff av psi e) (xx (av e)) (xx (bv e)) (cc e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_post] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (K ALL_TAC)
     (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `e:real^N->bool`)))
   ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^3->bool` MP_TAC) ASSUME_TAC) THEN
  REWRITE_TAC[moi_s35_edge_conf] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_S5P_FF_ACUTS = prove
 (`!(ff:real^N->real^N->real^3) av (psi:(real^N->bool)->real^3->real^N) l cc v x.
     x IN IMAGE (ff v) (UNIONS {IMAGE (psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e} | e |
                                moi_s35_edge l e /\ av e = v})
     ==> ?e. moi_s35_edge l e /\ av e = v /\
             x IN IMAGE (moi_s35_ach ff av psi e) moi_s35_slab`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_IMAGE; UNIONS_GSPEC; IN_ELIM_THM; moi_s35_ach; o_THM] THEN
  MESON_TAC[]);;

let MOI_S5P_X1_CASES = prove
 (`!(t:(real^N->bool)->bool) l av bv (psi:(real^N->bool)->real^3->real^N)
    (ff:real^N->real^N->real^3) cc v e x.
     x IN moi_s5p_x1 t l av bv psi ff cc v e
     ==> x IN IMAGE (ff v) (moi_s5p_core t l av bv psi v) \/
         (?e'. moi_s35_edge l e' /\ av e' = v /\
               x IN IMAGE (moi_s35_ach ff av psi e') moi_s35_slab) \/
         (?e'. moi_s35_edge l e' /\ bv e' = v /\ ~(e' = e) /\
               x IN moi_s5p_x2 ff av bv psi e')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5p_x1; moi_s5p_core2; IMAGE_UNION; IN_UNION] THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC MOI_S5P_FF_ACUTS THEN
    EXISTS_TAC `cc:(real^N->bool)->real` THEN FIRST_ASSUM ACCEPT_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MOI_S5P_ACH_OFF_X1 = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e
     ==> DISJOINT (IMAGE (moi_s35_ach ff av psi e)
                         {x | x IN moi_s35_slab /\ x$3 <= &1 / &16})
                  (moi_s5p_x1 t l av bv psi ff cc (bv e) e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                 `(bv:(real^N->bool)->real^N) e`] MOI_S5P_CORE_IN_D) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fs") (K ALL_TAC)))))
   (K ALL_TAC)) THEN
  UNDISCH_TAC `moi_s35_sep2 l (av:(real^N->bool)->real^N) bv psi ff` THEN
  REWRITE_TAC[moi_s35_sep2] THEN DISCH_THEN(LABEL_TAC "s2") THEN
  REWRITE_TAC[SET_RULE `DISJOINT (s:real^3->bool) t <=> !x. x IN s ==> ~(x IN t)`] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                                    moi_s35_slab` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                                     {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}` THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) s t x.
      s SUBSET t ==> x IN IMAGE f s ==> x IN IMAGE f t`) THEN
    REWRITE_TAC[MOI_S5P_MODEL_INCL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S5P_X1_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
    (X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC))) THENL
   [UNDISCH_TAC `DISJOINT
                  (IMAGE ((ff:real^N->real^N->real^3) ((bv:(real^N->bool)->real^N) e))
                         (moi_s5p_core t l av bv psi (bv e)))
                  (IMAGE (moi_s35_ach ff av psi e)
                         {x | x IN moi_s35_slab /\ x$3 <= &1 / &16})` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                                     {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE ((ff:real^N->real^N->real^3) ((bv:(real^N->bool)->real^N) e))
                                     (moi_s5p_core t l av bv psi (bv e))` THEN
    MATCH_ACCEPT_TAC(SET_RULE `!(x:real^3) s t. x IN s ==> x IN t ==> DISJOINT s t ==> F`);
    SUBGOAL_THEN `~(e':real^N->bool = e)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "fs" (MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e')
                                     moi_s35_slab` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                                     moi_s35_slab` THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!(x:real^3) s t. x IN s ==> x IN t ==> DISJOINT s t ==> F`);
    USE_THEN "s2" (MP_TAC o SPECL [`e':real^N->bool`; `e:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "fs" (MP_TAC o SPECL [`e':real^N->bool`; `e:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `(x:real^3) IN moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e'` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                                     moi_s35_slab` THEN
    MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S5P_MODEL_INCL))))) THEN
    REWRITE_TAC[moi_s5p_x2] THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!(x:real^3) (f:real^3->real^3) (f':real^3->real^3) (g:real^3->real^3) s1 s2 a.
        s1 SUBSET s2 ==> x IN IMAGE f s2 ==> x IN IMAGE g a UNION IMAGE f' s1 ==>
        DISJOINT (IMAGE f' s2) (IMAGE f s2) ==> ~DISJOINT (IMAGE g a) (IMAGE f s2)`)]);;

(* Points of the A-chart slab image of e in xx (bv e) and off the interior  *)
(* of xx (av e) lie in D_(bv e) (the other A-cells at bv e meet xx (bv e)   *)
(* only in their own slab images).                                          *)

let MOI_S5P_ACH_IN_D = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e x.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_edge l e /\
     x IN IMAGE (moi_s35_ach ff av psi e) moi_s35_slab /\ x IN xx (bv e) /\
     ~(x IN interior (xx (av e)))
     ==> x IN moi_s35_dcell l av bv xx (bv e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fe")
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fs") (K ALL_TAC)))))
   (K ALL_TAC)) THEN
  REWRITE_TAC[moi_s35_dcell; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `e':real^N->bool` THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; TAUT `~(p /\ q /\ r) <=> p /\ q ==> ~r`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `e':real^N->bool = e` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC(SET_RULE
     `!(x:real^3) s. ~(x IN s) /\ interior s SUBSET s ==> ~(x IN interior s)`) THEN
    REWRITE_TAC[INTERIOR_SUBSET] THEN DISCH_TAC THEN
    USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e':real^N->bool)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fs" (MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                                     moi_s35_slab` THEN
    UNDISCH_TAC `(x:real^3) IN xx ((bv:(real^N->bool)->real^N) e)` THEN
    UNDISCH_TAC `(x:real^3) IN xx ((av:(real^N->bool)->real^N) e')` THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!(x:real^3) a b i j. x IN a ==> x IN b ==> x IN i ==> DISJOINT i j ==>
                           ~(a INTER b SUBSET j)`)]);;

let MOI_S5P_LEVEL_LOW = prove
 (`!c. abs c <= &1 / &512
       ==> {x | x IN moi_s35_level c /\ moi_s35_n x < &5 / &16} SUBSET
           {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REWRITE_TAC[moi_s35_level; IN_ELIM_THM] THEN
  REWRITE_TAC[MOI_S5A_CUBE_IN] THEN GEN_TAC THEN
  UNDISCH_TAC `abs c <= &1 / &512` THEN REAL_ARITH_TAC);;

(* The disk ddisk e = Bd X_a INTER X_b: inside the low A-slab image, with   *)
(* the chart image of the centre, off X1(e), inside D_(bv e).               *)

let MOI_S5P_DDISK = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e
     ==> moi_s35_ddisk av bv xx e SUBSET
         IMAGE (moi_s35_ach ff av psi e) {x | x IN moi_s35_slab /\ x$3 <= &1 / &16} /\
         moi_s35_ach ff av psi e (vector[&0; &0; cc e]) IN moi_s35_ddisk av bv xx e /\
         DISJOINT (moi_s35_ddisk av bv xx e) (moi_s5p_x1 t l av bv psi ff cc (bv e) e) /\
         moi_s35_ddisk av bv xx e SUBSET moi_s35_dcell l av bv xx (bv e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_POST_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s35_ddisk av bv xx e SUBSET
    IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
          {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_ddisk] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                      {x | x IN moi_s35_level (cc e) /\ moi_s35_n x < &5 / &16}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC MOI_S5P_LEVEL_LOW THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_s35_ach (ff:real^N->real^N->real^3) av psi e (vector[&0; &0; cc e]) IN
                moi_s35_ddisk av bv xx e` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_single (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                  (xx ((av:(real^N->bool)->real^N) e)) (xx (bv e)) (cc e)` THEN
    REWRITE_TAC[moi_s35_single; moi_s35_ddisk] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^2->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s35_lift; VEC_COMPONENT];
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[MOI_S5C_N_LIFT; VEC_COMPONENT] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
      MOI_S5P_ACH_OFF_X1) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s35_ddisk av bv xx e SUBSET
                 IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                       {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}` THEN
    MATCH_ACCEPT_TAC(SET_RULE `!(a:real^3->bool) b c. a SUBSET b ==> DISJOINT b c ==>
                                                      DISJOINT a c`);
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5P_ACH_IN_D THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^3`;
                          `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                          `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                          `cc:(real^N->bool)->real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN moi_s35_ddisk (av:(real^N->bool)->real^N) bv xx e` THEN
    UNDISCH_TAC `moi_s35_ddisk av bv xx e SUBSET
                 IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                       {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}` THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S5P_MODEL_INCL)))) THEN
    REWRITE_TAC[moi_s35_ddisk; frontier] THEN SET_TAC[]]);;

(* A point of D_(bv e) in X1(e) off E_e: the B-chart image of a point just   *)
(* above the level 1/8 on the axis (in the core of bv e, off the other      *)
(* slabs by the positive distance).                                          *)

let MOI_S5P_Q_POINT = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_sep l av bv psi ff /\
     moi_s35_edge l e
     ==> ?q. q IN moi_s35_dcell l av bv xx (bv e) /\
             q IN moi_s5p_x1 t l av bv psi ff cc (bv e) e /\
             ~(q IN IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_CHART_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `e:real^N->bool`; `(bv:(real^N->bool)->real^N) e`] MOI_S5P_OTHER_SLABS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `ss = UNIONS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab | e' |
                           moi_s35_edge l e' /\
                           ((av:(real^N->bool)->real^N) e' = bv e \/ bv e' = bv e) /\
                           ~(e' = e)}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(psi:(real^N->bool)->real^3->real^N) e`; `moi_s35_cube`;
                 `vector[&0; &0; &1 / &8]:real^3`; `ss:real^N->bool`] MOI_S5P_CONT_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism
                    (moi_s35_cube,derived_dual_cell t l ((av:(real^N->bool)->real^N) e)
                                  UNION derived_dual_cell t l (bv e))
                    ((psi:(real^N->bool)->real^3->real^N) e,q)` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism];
      REWRITE_TAC[moi_s35_cube; INTERIOR_INTERVAL; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                  VECTOR_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      UNDISCH_TAC `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                            ss` THEN
      MATCH_MP_TAC(SET_RULE `!(f:real^3->real^N) s t x.
         x IN s ==> DISJOINT (IMAGE f s) t ==> ~(f x IN t)`) THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REWRITE_TAC[MOI_S5A_CUBE_IN; VECTOR_3] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r")))] THEN
  ABBREV_TAC `z = vector[&0; &0; &1 / &8 + min (r / &2) (&1 / &2)]:real^3` THEN
  SUBGOAL_THEN `(z:real^3) IN ball(vector[&0; &0; &1 / &8],r)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPEC `vector[&0; &0; &1 / &8] - z:real^3` NORM_LE_L1) THEN
    EXPAND_TAC "z" THEN
    REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
    UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "r" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vector[&0; &0; &1 / &8],r)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &8 < (z:real^3)$3` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[VECTOR_3] THEN UNDISCH_TAC `&0 < r` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e z IN
                moi_s5p_core t l av bv psi (bv e)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5P_UPPER_CORE THEN EXISTS_TAC `g:real^N->real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                 `(bv:(real^N->bool)->real^N) e`] MOI_S5P_CORE_IN_D) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  EXISTS_TAC `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE ((ff:real^N->real^N->real^3) ((bv:(real^N->bool)->real^N) e))
                       (moi_s5p_core t l av bv psi (bv e)) SUBSET
                 moi_s35_dcell l av bv xx (bv e)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_s35_bch; o_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[moi_s5p_x1; moi_s5p_core2; IN_UNION; IMAGE_UNION; moi_s35_bch; o_THM] THEN
    DISJ1_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) = y` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y. x IN moi_s35_upper /\ y IN moi_s35_upper /\
               moi_s35_bch (ff:real^N->real^N->real^3) bv psi e x =
               moi_s35_bch ff bv psi e y ==> x = y`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN moi_s35_cube` THEN UNDISCH_TAC `&1 / &8 < (z:real^3)$3` THEN
        REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN SIMP_TAC[] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `(y:real^3) IN moi_s35_level (&1 / &8)` THEN
        REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REWRITE_TAC[moi_s35_level; IN_ELIM_THM] THEN
        SIMP_TAC[] THEN REAL_ARITH_TAC];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_level (&1 / &8)` THEN
      UNDISCH_TAC `&1 / &8 < (y:real^3)$3` THEN
      REWRITE_TAC[moi_s35_level; IN_ELIM_THM] THEN REAL_ARITH_TAC]]);;

let MOI_S5P_X1_COMPACT = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_edge l e
     ==> compact (moi_s5p_x1 t l av bv psi ff cc (bv e) e)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  REWRITE_TAC[moi_s5p_x1] THEN MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
        UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
        REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
        DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`) o
          CONJUNCT1 o CONJUNCT1) THEN
        SIMP_TAC[];
        MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                       `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                       `cc:(real^N->bool)->real`; `(bv:(real^N->bool)->real^N) e`]
          MOI_S5P_CORE2_CPLUS) THEN
        ASM_SIMP_TAC[]];
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                     `cc:(real^N->bool)->real`; `(bv:(real^N->bool)->real^N) e`]
        (UNDISCH MOI_S5P_CORE_COMPACT)) THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{e':real^N->bool | moi_s35_edge l e' /\
                       ((av:(real^N->bool)->real^N) e' = bv e \/ bv e' = bv e)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5P_VERT_EDGES_FINITE THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `g:real^N->real^N->bool`;
                              `psi:(real^N->bool)->real^3->real^N`] THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e':real^N->bool` THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN MATCH_MP_TAC MOI_S5P_X2_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `h:real^N->real^3`; `w:real^N->real^3->bool`;
                            `g:real^N->real^N->bool`; `xx:real^N->real^3->bool`;
                            `cc:(real^N->bool)->real`] THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_S5P_D_X12 = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_edge l e
     ==> moi_s35_dcell l av bv xx (bv e) SUBSET
         moi_s5p_x1 t l av bv psi ff cc (bv e) e UNION moi_s5p_x2 ff av bv psi e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                 `(bv:(real^N->bool)->real^N) e`] MOI_S5P_D_COVER) THEN
  ASM_REWRITE_TAC[moi_s5p_x1; SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* Near the top centre (0,0,1/8) of the box under E_e, the B-chart stays in *)
(* D_(bv e) and in X2(e).                                                    *)

let MOI_S5P_B_NEAR = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e
     ==> ?r. &0 < r /\
             !z. z IN ball(vector[&0;&0;&1 / &8],r) /\
                 z IN interval[vector[-- &1;-- &1;&0],vector[&1;&1;&1 / &8]]
                 ==> moi_s35_bch ff bv psi e z IN moi_s35_dcell l av bv xx (bv e) /\
                     moi_s35_bch ff bv psi e z IN moi_s5p_x2 ff av bv psi e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_CHART_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (LABEL_TAC "fv") (CONJUNCTS_THEN2 (LABEL_TAC "fe") (K ALL_TAC)))
   (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `closed (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_stube UNION
            xx ((av:(real^N->bool)->real^N) e)) /\
    ~(moi_s35_bch ff bv psi e (vector[&0;&0;&1 / &8]) IN
      IMAGE (moi_s35_ach ff av psi e) moi_s35_stube UNION xx (av e))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `moi_s35_dom` THEN REWRITE_TAC[MOI_S5A_MODEL_BASIC] THEN
        MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "fv" (MP_TAC o C MATCH_MP (ASSUME `{(av:(real^N->bool)->real^N) e} IN l`)) THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        MESON_TAC[MOI_S5F_BALL_FACTS]];
      USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> DISJOINT s t /\ DISJOINT s u
                             ==> ~(x IN t UNION u)`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REWRITE_TAC[moi_s35_level; IN_ELIM_THM] THEN
      REWRITE_TAC[MOI_S5A_CUBE_IN; VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s35_bch (ff:real^N->real^N->real^3) bv psi e`; `moi_s35_upper`;
                 `vector[&0;&0;&1 / &8]:real^3`;
                 `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_stube UNION
                  xx ((av:(real^N->bool)->real^N) e)`] MOI_S5P_CONT_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[MOI_S5N_HALVES; INTERIOR_INTERVAL; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                  VECTOR_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))] THEN
  EXISTS_TAC `min r1 (&1 / &32)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_ARITH `&0 < &1 / &32`] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN ball(vector[&0;&0;&1 / &8],r1) /\
                abs(z$3 - &1 / &8) < &1 / &32` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN ball(vector[&0;&0;&1 / &8],min r1 (&1 / &32))` THEN
    REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dist(vector[&0;&0;&1 / &8]:real^3,z)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[dist] THEN
    MP_TAC(ISPECL [`vector[&0;&0;&1 / &8] - z:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT; VECTOR_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "r1" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(vector[&0;&0;&1 / &8],r1)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN moi_s35_bcell INTER moi_s35_slab` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN interval[vector[-- &1;-- &1;&0],vector[&1;&1;&1 / &8]]` THEN
    UNDISCH_TAC `abs((z:real^3)$3 - &1 / &8) < &1 / &32` THEN
    REWRITE_TAC[IN_INTER] THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
    REWRITE_TAC[MOI_S5A_CUBE_IN; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5P_BSLAB_IN_D THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^3`;
                          `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                          `cc:(real^N->bool)->real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s5p_x2; IN_UNION] THEN DISJ1_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC]);;

(* Just above the centre (0,0,cc e) of the disk, the A-chart stays in        *)
(* D_(bv e) and off X1(e): the centre is interior to X_b (it is off the     *)
(* common frontier, which lies over the flat annulus), the A-cell X_a meets *)
(* the A-slab image only below the level cc e, and at the level the points  *)
(* lie on the disk, hence on the frontier of X_a.                           *)

let MOI_S5P_A_NEAR = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e
     ==> ?r. &0 < r /\
             !y. y IN ball(vector[&0;&0;cc e],r) /\ cc e <= y$3
                 ==> moi_s35_ach ff av psi e y IN moi_s35_dcell l av bv xx (bv e) /\
                     ~(moi_s35_ach ff av psi e y IN
                       moi_s5p_x1 t l av bv psi ff cc (bv e) e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_CHART_PL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_POST_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
    MOI_S5P_DDISK) THEN
  ASM_REWRITE_TAC[moi_s35_ddisk] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (xx ((bv:(real^N->bool)->real^N) e):real^3->bool) /\
                xx (bv e) DIFF interior (xx (bv e)) = frontier (xx (bv e))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`] MOI_S5F_POST_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`) o
      CONJUNCT1) THEN
    MESON_TAC[MOI_S5F_BALL_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `vector[&0;&0;cc e] IN moi_s35_dom /\
                moi_s35_aflat ((cc:(real^N->bool)->real) e) SUBSET moi_s35_dom /\
                {x | x IN moi_s35_slab /\ x$3 <= cc e} SUBSET moi_s35_dom /\
                moi_s35_slab SUBSET moi_s35_dom`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s35_aflat] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REWRITE_TAC[MOI_S5A_CUBE_IN; VECTOR_3] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THEN TRY GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_ach (ff:real^N->real^N->real^3) av psi e (vector[&0;&0;cc e]) IN
                interior (xx ((bv:(real^N->bool)->real^N) e))` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!(x:real^3) a b f. x IN a /\ ~(x IN f) /\ a DIFF b = f
                                              ==> x IN b`) THEN
    EXISTS_TAC `xx ((bv:(real^N->bool)->real^N) e):real^3->bool` THEN
    EXISTS_TAC `frontier (xx ((bv:(real^N->bool)->real^N) e)):real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_s35_ach (ff:real^N->real^N->real^3) av psi e (vector[&0;&0;cc e]) IN
                   frontier (xx ((av:(real^N->bool)->real^N) e)) INTER xx (bv e)` THEN
      SIMP_TAC[IN_INTER];
      DISCH_TAC THEN
      SUBGOAL_THEN `moi_s35_ach (ff:real^N->real^N->real^3) av psi e (vector[&0;&0;cc e]) IN
                    IMAGE (moi_s35_ach ff av psi e) (moi_s35_aflat (cc e))` MP_TAC THENL
       [UNDISCH_TAC `frontier (xx ((av:(real^N->bool)->real^N) e)) INTER
                     frontier (xx (bv e)) SUBSET
                     IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                           (moi_s35_aflat (cc e))` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_INTER] THEN
        UNDISCH_TAC `moi_s35_ach (ff:real^N->real^N->real^3) av psi e (vector[&0;&0;cc e]) IN
                     frontier (xx ((av:(real^N->bool)->real^N) e)) INTER xx (bv e)` THEN
        SIMP_TAC[IN_INTER];
        REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `u:real^3` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        SUBGOAL_THEN `vector[&0;&0;(cc:(real^N->bool)->real) e] = u:real^3` MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\
                   moi_s35_ach (ff:real^N->real^N->real^3) av psi e x =
                   moi_s35_ach ff av psi e y ==> x = y`) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `moi_s35_aflat ((cc:(real^N->bool)->real) e) SUBSET moi_s35_dom` THEN
          UNDISCH_TAC `(u:real^3) IN moi_s35_aflat ((cc:(real^N->bool)->real) e)` THEN
          SET_TAC[];
          DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
          UNDISCH_TAC `(vector[&0;&0;(cc:(real^N->bool)->real) e]:real^3) IN moi_s35_aflat (cc e)` THEN
          REWRITE_TAC[moi_s35_aflat; IN_ELIM_THM; moi_s35_n; VECTOR_3] THEN
          REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s35_ach (ff:real^N->real^N->real^3) av psi e`; `moi_s35_dom`;
                 `vector[&0;&0;(cc:(real^N->bool)->real) e]:real^3`;
                 `(:real^3) DIFF interior (xx ((bv:(real^N->bool)->real^N) e))`]
    MOI_S5P_CONT_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; GSYM OPEN_CLOSED; OPEN_INTERIOR] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN
      REWRITE_TAC[MOI_S5A_DOM_INTERVAL; INTERIOR_INTERVAL; IN_INTERVAL; DIMINDEX_3;
                  FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))] THEN
  EXISTS_TAC `min r1 (&1 / &64)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_ARITH `&0 < &1 / &64`] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN ball(vector[&0;&0;cc e],r1) /\
                abs(y$1) < &1 / &64 /\ abs(y$2) < &1 / &64 /\
                abs(y$3 - (cc:(real^N->bool)->real) e) < &1 / &64`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN ball(vector[&0;&0;(cc:(real^N->bool)->real) e],min r1 (&1 / &64))` THEN
    REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`vector[&0;&0;(cc:(real^N->bool)->real) e] - y:real^3`; `1`]
      COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`vector[&0;&0;(cc:(real^N->bool)->real) e] - y:real^3`; `2`]
      COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`vector[&0;&0;(cc:(real^N->bool)->real) e] - y:real^3`; `3`]
      COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
    UNDISCH_TAC `dist(vector[&0;&0;(cc:(real^N->bool)->real) e],y:real^3) < &1 / &64` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "r1" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN ball(vector[&0;&0;(cc:(real^N->bool)->real) e],r1)`)) THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s35_slab /\ y IN {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN
    UNDISCH_TAC `abs((y:real^3)$1) < &1 / &64` THEN UNDISCH_TAC `abs((y:real^3)$2) < &1 / &64` THEN
    UNDISCH_TAC `abs((y:real^3)$3 - (cc:(real^N->bool)->real) e) < &1 / &64` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
    REWRITE_TAC[MOI_S5A_CUBE_IN] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s35_ach (ff:real^N->real^N->real^3) av psi e y IN
                  interior (xx ((av:(real^N->bool)->real^N) e)))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3)$3 = (cc:(real^N->bool)->real) e` ASSUME_TAC THENL
     [SUBGOAL_THEN `moi_s35_ach (ff:real^N->real^N->real^3) av psi e y IN
                    IMAGE (moi_s35_ach ff av psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e}`
      MP_TAC THENL
       [UNDISCH_TAC `xx ((av:(real^N->bool)->real^N) e) INTER
                     IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab =
                     IMAGE (moi_s35_ach ff av psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e}` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
         [MP_TAC(ISPEC `xx ((av:(real^N->bool)->real^N) e):real^3->bool` INTERIOR_SUBSET) THEN
          UNDISCH_TAC `moi_s35_ach (ff:real^N->real^N->real^3) av psi e y IN
                       interior (xx ((av:(real^N->bool)->real^N) e))` THEN
          SET_TAC[];
          MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:real^3) = u` SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\
                   moi_s35_ach (ff:real^N->real^N->real^3) av psi e x =
                   moi_s35_ach ff av psi e y ==> x = y`) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_dom` THEN
          UNDISCH_TAC `(u:real^3) IN moi_s35_slab` THEN SET_TAC[];
          UNDISCH_TAC `(cc:(real^N->bool)->real) e <= (u:real^3)$3` THEN
          UNDISCH_TAC `(u:real^3)$3 <= (cc:(real^N->bool)->real) e` THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s35_single (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                  (xx ((av:(real^N->bool)->real^N) e)) (xx (bv e)) (cc e)` THEN
    REWRITE_TAC[moi_s35_single] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_s35_ach (ff:real^N->real^N->real^3) av psi e y IN
                  frontier (xx ((av:(real^N->bool)->real^N) e)) INTER xx (bv e)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `vector[(y:real^3)$1; y$2]:real^2` THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_s35_lift; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[MOI_S5C_N_LIFT; VECTOR_2] THEN
        UNDISCH_TAC `abs((y:real^3)$1) < &1 / &64` THEN
        UNDISCH_TAC `abs((y:real^3)$2) < &1 / &64` THEN REAL_ARITH_TAC];
      REWRITE_TAC[IN_INTER; frontier; IN_DIFF] THEN
      UNDISCH_TAC `moi_s35_ach (ff:real^N->real^N->real^3) av psi e y IN
                   interior (xx ((av:(real^N->bool)->real^N) e))` THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5P_ACH_IN_D THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^3`;
                          `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                          `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                          `cc:(real^N->bool)->real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPEC `xx ((bv:(real^N->bool)->real^N) e):real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `moi_s35_ach (ff:real^N->real^N->real^3) av psi e y IN
                   interior (xx ((bv:(real^N->bool)->real^N) e))` THEN
      SET_TAC[]];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `e:real^N->bool`]
      MOI_S5P_ACH_OFF_X1) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) s t x.
      x IN s ==> DISJOINT (IMAGE f s) t ==> ~(f x IN t)`) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* The B-side piece T_e: the side of E_e in D_(bv e) containing ddisk e.    *)

let MOI_S5P_ARGS =
  [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`;
   `w:real^N->real^3->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
   `e:real^N->bool`];;

let MOI_S5P_SIDES_SETS = prove
 (`!(d:real^3->bool) tt rr x1 x2 e dd p.
     tt UNION rr = d /\ tt INTER rr = e /\ rr SUBSET x1 /\ x1 INTER x2 = e /\
     dd SUBSET d /\ DISJOINT dd x1 /\ d SUBSET x1 UNION x2 /\ p IN dd
     ==> p IN d /\ p IN x2 /\ ~(p IN e) /\
         dd SUBSET tt /\ d INTER x2 SUBSET tt /\ d DIFF x1 SUBSET tt`,
  SET_TAC[]);;

let MOI_S5P_P_POINT_SETS = prove
 (`!(d:real^3->bool) x1 x2 e dd p.
     x1 INTER x2 = e /\ dd SUBSET d /\ DISJOINT dd x1 /\ d SUBSET x1 UNION x2 /\ p IN dd
     ==> p IN d /\ p IN x2 /\ ~(p IN e)`,
  SET_TAC[]);;

let MOI_S5P_B_SIDE = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     PL_SCHOENFLIES_3_STATEMENT /\
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_source_ok t l av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e /\
     pl_ball 3 (moi_s35_dcell l av bv xx (bv e))
     ==> ?tt rr. pl_ball 3 tt /\ pl_ball 3 rr /\
                 tt UNION rr = moi_s35_dcell l av bv xx (bv e) /\
                 tt INTER rr = IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) /\
                 tt SUBSET moi_s5p_x2 ff av bv psi e /\
                 rr SUBSET moi_s5p_x1 t l av bv psi ff cc (bv e) e /\
                 moi_s35_ddisk av bv xx e SUBSET tt /\
                 IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) SUBSET
                 frontier tt /\
                 frontier (moi_s35_dcell l av bv xx (bv e)) INTER tt SUBSET frontier tt /\
                 moi_s35_dcell l av bv xx (bv e) INTER moi_s5p_x2 ff av bv psi e SUBSET tt /\
                 moi_s35_dcell l av bv xx (bv e) DIFF
                 moi_s5p_x1 t l av bv psi ff cc (bv e) e SUBSET tt`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_E_PROPER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_X_INTER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_D_X12) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS (UNDISCH MOI_S5P_X1_COMPACT)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_X2_COMPACT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_DDISK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_Q_POINT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)`;
    `moi_s5p_x1 t l av bv psi (ff:real^N->real^N->real^3) cc ((bv:(real^N->bool)->real^N) e) e`;
    `moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e`;
    `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e) (moi_s35_level (&1 / &8))`;
    `moi_s35_ddisk (av:(real^N->bool)->real^N) bv xx e`;
    `moi_s35_ach (ff:real^N->real^N->real^3) av psi e (vector[&0; &0; cc e])`]
   MOI_S5P_P_POINT_SETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)`;
    `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e) (moi_s35_level (&1 / &8))`;
    `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
       (IMAGE (moi_s35_lift (&1 / &8))
          (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))`;
    `moi_s5p_x1 t l av bv psi (ff:real^N->real^N->real^3) cc ((bv:(real^N->bool)->real^N) e) e`;
    `moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e`;
    `moi_s35_ach (ff:real^N->real^N->real^3) av psi e (vector[&0; &0; cc e])`;
    `q:real^3`] MOI_S5P_SIDES) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:real^3->bool` (X_CHOOSE_THEN `rr:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`tt:real^3->bool`; `rr:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)`;
    `tt:real^3->bool`; `rr:real^3->bool`;
    `moi_s5p_x1 t l av bv psi (ff:real^N->real^N->real^3) cc ((bv:(real^N->bool)->real^N) e) e`;
    `moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e`;
    `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e) (moi_s35_level (&1 / &8))`;
    `moi_s35_ddisk (av:(real^N->bool)->real^N) bv xx e`;
    `moi_s35_ach (ff:real^N->real^N->real^3) av psi e (vector[&0; &0; cc e])`]
   MOI_S5P_SIDES_SETS) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 14. The data of one edge e: the A-side squeeze M_e (Box_A onto the cut   *)
(* box, identity on the bottom) and the B-side piece Q_e (Box_B onto T_e,   *)
(* ach e o M_e on the middle square, bch e on the level 1/8).               *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_ARGS11 =
  [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`;
   `w:real^N->real^3->bool`; `av:(real^N->bool)->real^N`;
   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
   `e:real^N->bool`];;

let MOI_S5P_IMAGE_EQ = prove
 (`!(f:A->B) g s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`,
  SET_TAC[]);;

let MOI_S5P_EDGE_DATA = prove
 (mk_imp(MOI_FND_GRAPH_TUBE, mk_imp(MOI_S35_TWO_DISK_EXT,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     PL_SCHOENFLIES_3_STATEMENT /\
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_source_ok t l av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e /\
     pl_ball 3 (moi_s35_dcell l av bv xx (bv e)) /\
     moi_s35_ddisk av bv xx e SUBSET frontier (moi_s35_dcell l av bv xx (bv e))
     ==> ?M M' Q Q' tt.
           pl_homeomorphism
             (interval[vector[-- &1;-- &1;-- &1 / &8]:real^3,vector[&1;&1;&0]],
              interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;cc e]]) (M,M') /\
           (!x. x IN interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;&0]] /\
                x$3 = -- &1 / &8 ==> M x = x) /\
           IMAGE (moi_s35_ach ff av psi e) (IMAGE M moi_s35_mid) =
           moi_s35_ddisk av bv xx e /\
           pl_homeomorphism
             (interval[vector[-- &1;-- &1;&0]:real^3,vector[&1;&1;&1 / &8]],tt) (Q,Q') /\
           (!x. x IN moi_s35_mid ==> Q x = moi_s35_ach ff av psi e (M x)) /\
           (!x. x IN moi_s35_level (&1 / &8) ==> Q x = moi_s35_bch ff bv psi e x) /\
           tt SUBSET moi_s35_dcell l av bv xx (bv e) /\
           tt SUBSET moi_s5p_x2 ff av bv psi e /\
           IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) SUBSET tt /\
           moi_s35_ddisk av bv xx e SUBSET tt /\
           moi_s35_dcell l av bv xx (bv e) SUBSET
           tt UNION moi_s5p_x1 t l av bv psi ff cc (bv e) e`)),
  DISCH_THEN(LABEL_TAC "tube") THEN DISCH_THEN(LABEL_TAC "tde") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_CHART_PL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS11 MOI_S5P_POST_EDGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s35_single (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                (xx ((av:(real^N->bool)->real^N) e)) (xx (bv e)) (cc e)` THEN
  REWRITE_TAC[moi_s35_single] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(!y:real^2. max (abs(y$1)) (abs(y$2)) <= &3 / &16 ==> y IN inside j) /\
    (!y:real^2. y IN j ==> max (abs(y$1)) (abs(y$2)) <= &5 / &16)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[MOI_S5C_N_LIFT];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      UNDISCH_TAC `IMAGE (moi_s35_lift ((cc:(real^N->bool)->real) e)) j SUBSET
                   moi_s35_aflat (cc e) DIFF
                   (moi_s35_sq (&3 / &16) (cc e) UNION moi_s35_sq (&5 / &16) (cc e))` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN
      ASM_REWRITE_TAC[IN_DIFF; moi_s35_aflat; IN_ELIM_THM; MOI_S5C_N_LIFT] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(cc:(real^N->bool)->real) e`; `j:real^2->bool`]
    (UNDISCH MOI_S5P_SQUEEZE)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^3->real^3` (X_CHOOSE_THEN `M':real^3->real^3`
    (X_CHOOSE_THEN `gm:real^3->real^3` (X_CHOOSE_THEN `gm':real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS (UNDISCH MOI_S5P_B_SIDE)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:real^3->bool` (X_CHOOSE_THEN `rr:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_DDISK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_X_INTER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
      (IMAGE (moi_s35_lift (cc e)) (j UNION inside j)) = moi_s35_ddisk av bv xx e`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[moi_s35_ddisk]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(cc:(real^N->bool)->real) e`; `j:real^2->bool`; `gm:real^3->real^3`;
                 `gm':real^3->real^3`; `moi_s35_ach (ff:real^N->real^N->real^3) av psi e`;
                 `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e`; `tt:real^3->bool`]
    (UNDISCH MOI_S5P_BPIECE)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
      REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
      DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`) o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT1) THEN
      SIMP_TAC[];
      MATCH_MP_TAC(SET_RULE `!(dd:real^3->bool) tt fd ft.
        dd SUBSET tt /\ dd SUBSET fd /\ fd INTER tt SUBSET ft ==> dd SUBSET ft`) THEN
      MAP_EVERY EXISTS_TAC
       [`tt:real^3->bool`;
        `frontier (moi_s35_dcell l (av:(real^N->bool)->real^N) bv xx (bv e))`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `!(dd:real^3->bool) x1 x2 e.
        DISJOINT dd x1 /\ x1 INTER x2 = e ==> DISJOINT dd e`) THEN
      MAP_EVERY EXISTS_TAC
       [`moi_s5p_x1 t l av bv psi (ff:real^N->real^N->real^3) cc
           ((bv:(real^N->bool)->real^N) e) e`;
        `moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_A_NEAR) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r0"))) THEN
      EXISTS_TAC `r0 / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN BETA_TAC THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      UNDISCH_TAC `moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e) DIFF
                   moi_s5p_x1 t l av bv psi (ff:real^N->real^N->real^3) cc (bv e) e SUBSET
                   tt` THEN
      REWRITE_TAC[SUBSET; IN_DIFF] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "r0" MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_BALL; dist] THEN
        MP_TAC(ISPEC `vector[&0;&0;(cc:(real^N->bool)->real) e] -
                      vector[(x:real^3)$1 / &4; x$2 / &4; cc e + x$3]:real^3` NORM_LE_L1) THEN
        REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
        MP_TAC(ISPECL [`x:real^3`; `1`] COMPONENT_LE_NORM) THEN
        MP_TAC(ISPECL [`x:real^3`; `2`] COMPONENT_LE_NORM) THEN
        MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
        REWRITE_TAC[DIMINDEX_3; ARITH] THEN
        UNDISCH_TAC `(x:real^3) IN ball(vec 0,r0 / &2)` THEN REWRITE_TAC[IN_BALL_0] THEN
        UNDISCH_TAC `&0 < r0` THEN REAL_ARITH_TAC;
        REWRITE_TAC[VECTOR_3] THEN
        UNDISCH_TAC `(x:real^3) IN interval[vector[-- &1;-- &1;&0],vector[&1;&1;&1 / &8]]` THEN
        REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC];
      MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_B_NEAR) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1"))) THEN
      EXISTS_TAC `r1:real` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      UNDISCH_TAC `moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e) INTER
                   moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e SUBSET tt` THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "r1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `Q:real^3->real^3` (X_CHOOSE_THEN `Q':real^3->real^3`
      STRIP_ASSUME_TAC))] THEN
  MAP_EVERY EXISTS_TAC [`M:real^3->real^3`; `M':real^3->real^3`; `Q:real^3->real^3`;
                        `Q':real^3->real^3`; `tt:real^3->bool`] THEN
  SUBGOAL_THEN `IMAGE (M:real^3->real^3) moi_s35_mid =
                IMAGE (moi_s35_lift ((cc:(real^N->bool)->real) e)) (j UNION inside j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (gm:real^3->real^3) moi_s35_mid` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5P_IMAGE_EQ THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `pl_homeomorphism
                    (moi_s35_mid,
                     IMAGE (moi_s35_lift ((cc:(real^N->bool)->real) e)) (j UNION inside j))
                    (gm:real^3->real^3,gm')` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `tt SUBSET moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e) /\
    IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e) (moi_s35_level (&1 / &8))
    SUBSET tt /\
    moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e) SUBSET
    tt UNION moi_s5p_x1 t l av bv psi ff cc (bv e) e`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `tt UNION rr = moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)` THEN
    UNDISCH_TAC `tt INTER rr = IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                                     (moi_s35_level (&1 / &8))` THEN
    UNDISCH_TAC `rr SUBSET moi_s5p_x1 t l av bv psi (ff:real^N->real^N->real^3) cc
                                   ((bv:(real^N->bool)->real^N) e) e` THEN
    MATCH_ACCEPT_TAC(SET_RULE `!(tt:real^3->bool) rr d e x1.
      rr SUBSET x1 ==> tt INTER rr = e ==> tt UNION rr = d
      ==> tt SUBSET d /\ e SUBSET tt /\ d SUBSET tt UNION x1`);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN moi_s35_mid`)])));;

(* ------------------------------------------------------------------------- *)
(* 15. Dual cells against the edge charts: two adjacent cells meet in the    *)
(* chart image of the middle square, a slab image meets only the cells of   *)
(* the two ends of its edge, and slab images of distinct edges are disjoint. *)
(* ------------------------------------------------------------------------- *)

let moi_s5p_boxa = new_definition
 `moi_s5p_boxa = interval[vector[-- &1;-- &1;-- &1 / &8]:real^3,vector[&1;&1;&0]]`;;

let moi_s5p_boxb = new_definition
 `moi_s5p_boxb = interval[vector[-- &1;-- &1;&0]:real^3,vector[&1;&1;&1 / &8]]`;;

let MOI_S5P_MODEL_INCL3 = prove
 (`moi_s35_lower INTER moi_s35_upper = moi_s35_mid /\
   moi_s35_mid SUBSET moi_s35_slab /\ moi_s35_mid SUBSET moi_s5p_osl /\
   moi_s5p_boxa SUBSET moi_s35_slab /\ moi_s5p_boxb SUBSET moi_s35_slab /\
   moi_s5p_boxa SUBSET moi_s35_lower /\ moi_s5p_boxb SUBSET moi_s35_upper /\
   moi_s5p_boxa SUBSET moi_s35_dom /\ moi_s35_mid SUBSET moi_s5p_boxa /\
   moi_s35_mid SUBSET moi_s5p_boxb /\ moi_s35_level (&1 / &8) SUBSET moi_s5p_boxb /\
   moi_s5p_boxa INTER moi_s5p_boxb = moi_s35_mid /\
   moi_s35_slab = moi_s5p_boxa UNION moi_s5p_boxb /\
   moi_s5p_boxa SUBSET moi_s35_cube /\ moi_s5p_boxb SUBSET moi_s35_cube`,
  REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_UNION; moi_s5p_boxa; moi_s5p_boxb;
              moi_s5p_osl; IN_ELIM_THM] THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
  REWRITE_TAC[moi_s35_level; IN_ELIM_THM; MOI_S5A_CUBE_IN] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5P_CELL_PAIR = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) =
         IMAGE (psi e) moi_s35_mid`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS) THEN
  UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower =
               derived_dual_cell t l (av e)` THEN
  UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
               derived_dual_cell t l (bv e)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                    (moi_s35_lower INTER moi_s35_upper)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5P_IMAGE_INTER_INJ THEN EXISTS_TAC `moi_s35_cube` THEN
    ASM_REWRITE_TAC[MOI_S5A_MODEL_BASIC];
    REWRITE_TAC[MOI_S5P_MODEL_INCL3]]);;

let MOI_S5P_DOUBLETON_CASES = prove
 (`!(a:A) b c d. {a,b} = {c,d} ==> (a = c /\ b = d) \/ (a = d /\ b = c)`,
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let MOI_S5P_SLAB_UNIQUE = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e e' x.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\ moi_s35_edge l e' /\
     x IN IMAGE (psi e) moi_s35_slab /\ x IN IMAGE (psi e') moi_s35_slab
     ==> e = e'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`] o
    CONJUNCT2) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab` THEN
  UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab` THEN
  SET_TAC[]);;

let MOI_S5P_CELLS_MEET = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi u v x.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     {u} IN l /\ {v} IN l /\ ~(u = v) /\
     x IN derived_dual_cell t l u /\ x IN derived_dual_cell t l v
     ==> ?e. moi_s35_edge l e /\
             ((av e = u /\ bv e = v) \/ (av e = v /\ bv e = u)) /\
             x IN IMAGE (psi e) moi_s35_mid`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "tube" (MP_TAC o C MATCH_MP
    (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `segment[u:real^N,v] IN l` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    UNDISCH_TAC `(x:real^N) IN derived_dual_cell t l u` THEN
    UNDISCH_TAC `(x:real^N) IN derived_dual_cell t l v` THEN SET_TAC[]] THEN
  SUBGOAL_THEN `moi_s35_edge l (segment[u:real^N,v])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s35_edge; AFF_DIM_SEGMENT]; ALL_TAC] THEN
  EXISTS_TAC `segment[u:real^N,v]` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((av:(real^N->bool)->real^N) (segment[u,v]) = u /\ bv (segment[u,v]) = v) \/
    (av (segment[u,v]) = v /\ bv (segment[u,v]) = u)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi` THEN
    REWRITE_TAC[moi_s35_charts] THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (segment[u:real^N,v])`) o
      CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[SEGMENT_EQ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S5P_DOUBLETON_CASES) THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `segment[u:real^N,v]`] MOI_S5P_CELL_PAIR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let MOI_S5P_SLAB_AT = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e v x.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\
     {v} IN l /\ x IN IMAGE (psi e) moi_s35_slab /\ x IN derived_dual_cell t l v
     ==> v = av e \/ v = bv e`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN derived_dual_cell t l ((av:(real^N->bool)->real^N) e) \/
                x IN derived_dual_cell t l (bv e)` MP_TAC THENL
   [UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower =
                 derived_dual_cell t l (av e)` THEN
    UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                 derived_dual_cell t l (bv e)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IN_UNION; GSYM IMAGE_UNION] THEN
    UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab` THEN
    MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN
    REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2
      (CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2
      (CONJUNCT2 MOI_S5A_MODEL_BASIC))))))))))))))] THEN
    REWRITE_TAC[MOI_S5A_MODEL_BASIC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N. {w} IN l /\ ~(w = v) /\ x IN derived_dual_cell t l w /\
               ~(v = (av:(real^N->bool)->real^N) e) /\ ~(v = bv e) /\
               (w = av e \/ w = bv e) ==> F`
  (LABEL_TAC "hw") THENL
   [X_GEN_TAC `w:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `w:real^N`; `v:real^N`; `x:real^N`] (UNDISCH MOI_S5P_CELLS_MEET)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`; `e1:real^N->bool`; `x:real^N`] MOI_S5P_SLAB_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e1) moi_s35_slab`
    (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e1) moi_s35_mid` THEN
      MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN REWRITE_TAC[MOI_S5P_MODEL_INCL3];
      ALL_TAC] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `((av:(real^N->bool)->real^N) e = w /\ bv e = v) \/ (av e = v /\ bv e = w)` THEN
    UNDISCH_TAC `~(v = (av:(real^N->bool)->real^N) e)` THEN
    UNDISCH_TAC `~(v = (bv:(real^N->bool)->real^N) e)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [USE_THEN "hw" MATCH_MP_TAC THEN EXISTS_TAC `(av:(real^N->bool)->real^N) e` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(v = (av:(real^N->bool)->real^N) e)` THEN MESON_TAC[];
    USE_THEN "hw" MATCH_MP_TAC THEN EXISTS_TAC `(bv:(real^N->bool)->real^N) e` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(v = (bv:(real^N->bool)->real^N) e)` THEN MESON_TAC[]]);;

(* The pasted map: on the A-half of the slab of e (chart coordinates in     *)
(* Box_A) ach e o M_e o q_e, on the B-half Q_e o q_e, elsewhere ff v on the  *)
(* dual cell of v.                                                           *)

let moi_s5p_glob = new_definition
 `moi_s5p_glob (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
               (av:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N)
               (ff:real^N->real^N->real^3) (q:(real^N->bool)->real^N->real^3)
               (mm:(real^N->bool)->real^3->real^3) (qq:(real^N->bool)->real^3->real^3)
               (x:real^N) =
    if ?e. moi_s35_edge l e /\ x IN IMAGE (psi e) moi_s5p_boxa
    then moi_s35_ach ff av psi (@e. moi_s35_edge l e /\ x IN IMAGE (psi e) moi_s5p_boxa)
           (mm (@e. moi_s35_edge l e /\ x IN IMAGE (psi e) moi_s5p_boxa)
               (q (@e. moi_s35_edge l e /\ x IN IMAGE (psi e) moi_s5p_boxa) x))
    else if ?e. moi_s35_edge l e /\ x IN IMAGE (psi e) moi_s5p_boxb
    then qq (@e. moi_s35_edge l e /\ x IN IMAGE (psi e) moi_s5p_boxb)
            (q (@e. moi_s35_edge l e /\ x IN IMAGE (psi e) moi_s5p_boxb) x)
    else ff (@v. {v} IN l /\ x IN derived_dual_cell t l v) x`;;

let MOI_S5P_BOX_SLAB = prove
 (`!(f:real^3->real^N) x.
     (x IN IMAGE f moi_s5p_boxa ==> x IN IMAGE f moi_s35_slab) /\
     (x IN IMAGE f moi_s5p_boxb ==> x IN IMAGE f moi_s35_slab) /\
     (x IN IMAGE f moi_s35_mid ==> x IN IMAGE f moi_s5p_boxa) /\
     (x IN IMAGE f moi_s35_mid ==> x IN IMAGE f moi_s5p_boxb)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN
  REWRITE_TAC[MOI_S5P_MODEL_INCL3]);;

let MOI_S5P_BOX_UNIQUE = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi e x.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> (x IN IMAGE (psi e) moi_s5p_boxa
          ==> !e'. moi_s35_edge l e' /\ x IN IMAGE (psi e') moi_s5p_boxa <=> e' = e) /\
         (x IN IMAGE (psi e) moi_s5p_boxb
          ==> !e'. moi_s35_edge l e' /\ x IN IMAGE (psi e') moi_s5p_boxb <=> e' = e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e':real^N->bool` THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S5P_SLAB_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                        `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                        `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                        `x:real^N`] THEN
  ASM_SIMP_TAC[MOI_S5P_BOX_SLAB]);;

let MOI_S5P_GLOB_A = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff q mm qq e x.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\ x IN IMAGE (psi e) moi_s5p_boxa
     ==> moi_s5p_glob t l av psi ff q mm qq x = moi_s35_ach ff av psi e (mm e (q e x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `e:real^N->bool`; `x:real^N`] MOI_S5P_BOX_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_REWRITE_TAC[moi_s5p_glob; EXISTS_REFL; SELECT_REFL]);;

let MOI_S5P_BOXES_MID = prove
 (`!y:real^3. y IN moi_s5p_boxa /\ y IN moi_s5p_boxb ==> y IN moi_s35_mid`,
  MP_TAC MOI_S5P_MODEL_INCL3 THEN SET_TAC[]);;

let MOI_S5P_GLOB_B = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff q mm qq e x.
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e /\
     x IN IMAGE (psi e) moi_s5p_boxb /\
     (!y. y IN moi_s35_cube ==> q e (psi e y) = y) /\
     (!y. y IN moi_s35_mid ==> qq e y = moi_s35_ach ff av psi e (mm e y))
     ==> moi_s5p_glob t l av psi ff q mm qq x = qq e (q e x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  ASM_CASES_TAC `?e'. moi_s35_edge l e' /\
                      (x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                                          moi_s5p_boxa` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `e':real^N->bool = e` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_S5P_SLAB_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                            `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                            `x:real^N`] THEN
      ASM_SIMP_TAC[MOI_S5P_BOX_SLAB];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `e:real^N->bool`; `x:real^N`] MOI_S5P_GLOB_A) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxa` THEN
    UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxb` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y2:real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y1:real^3) IN moi_s35_cube /\ y2 IN moi_s35_cube` STRIP_ASSUME_TAC THENL
     [MP_TAC MOI_S5P_MODEL_INCL3 THEN
      UNDISCH_TAC `(y1:real^3) IN moi_s5p_boxa` THEN UNDISCH_TAC `(y2:real^3) IN moi_s5p_boxb` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y1:real^3) = y2` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!a b. a IN moi_s35_cube /\ b IN moi_s35_cube /\
               (psi:(real^N->bool)->real^3->real^N) e a = psi e b ==> a = b`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y1` THEN
      UNDISCH_TAC `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y2` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y2:real^3) IN moi_s35_mid` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S5P_BOXES_MID THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(q:(real^N->bool)->real^N->real^3) e x = y2` SUBST1_TAC THENL
     [UNDISCH_TAC `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y2` THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!y. y IN moi_s35_cube ==>
               (q:(real^N->bool)->real^N->real^3) e ((psi:(real^N->bool)->real^3->real^N) e y) = y`)
            (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y. y IN moi_s35_mid ==>
             (qq:(real^N->bool)->real^3->real^3) e y =
             moi_s35_ach (ff:real^N->real^N->real^3) av psi e (mm e y)`) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`; `x:real^N`] MOI_S5P_BOX_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[moi_s5p_glob; EXISTS_REFL; SELECT_REFL]]);;

(* On the core of v the pasted map is ff v: core points in a slab half lie  *)
(* on its outer face (level -1/8 on the A side, 1/8 on the B side), where   *)
(* M_e is the identity and Q_e = bch e; elsewhere v is the unique vertex of *)
(* a dual cell containing the point.                                        *)

let MOI_S5P_GLOB_CORE = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff q mm qq v x.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\ {v} IN l /\
     x IN moi_s5p_core t l av bv psi v /\
     (!e. moi_s35_edge l e
          ==> (!y. y IN moi_s35_cube ==> q e (psi e y) = y) /\
              (!y. y IN moi_s5p_boxa /\ y$3 = -- &1 / &8 ==> mm e y = y) /\
              (!y. y IN moi_s35_mid ==> qq e y = moi_s35_ach ff av psi e (mm e y)) /\
              (!y. y IN moi_s35_level (&1 / &8) ==> qq e y = moi_s35_bch ff bv psi e y))
     ==> moi_s5p_glob t l av psi ff q mm qq x = ff v x`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "ed"))))) THEN
  REWRITE_TAC[moi_s5p_core; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "off")) THEN
  SUBGOAL_THEN
   `!e y. moi_s35_edge l e /\ ((av:(real^N->bool)->real^N) e = v \/ bv e = v) /\
          y IN moi_s35_cube /\
          (x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y
          ==> &1 / &8 <= abs(y$3)`
  (LABEL_TAC "far") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "off" (MP_TAC o SPEC `e:real^N->bool`) THEN
    MATCH_MP_TAC(TAUT `p /\ q /\ r ==> ~((p /\ q) /\ r) ==> F`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[moi_s5p_osl; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `?e. moi_s35_edge l e /\
                     (x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                         moi_s5p_boxa` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
      CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(v:real^N) = (av:(real^N->bool)->real^N) e \/ v = bv e` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (UNDISCH MOI_S5P_SLAB_AT)) THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `g:real^N->real^N->bool`;
                            `psi:(real^N->bool)->real^3->real^N`; `x:real^N`] THEN
      ASM_SIMP_TAC[MOI_S5P_BOX_SLAB];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxa` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s35_cube` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN moi_s5p_boxa` THEN
      MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
      REWRITE_TAC[MOI_S5P_MODEL_INCL3];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3)$3 = -- &1 / &8` ASSUME_TAC THENL
     [USE_THEN "far" (MP_TAC o SPECL [`e:real^N->bool`; `y:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(v:real^N) = (av:(real^N->bool)->real^N) e \/ v = bv e` THEN MESON_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN moi_s5p_boxa` THEN
      REWRITE_TAC[moi_s5p_boxa; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^N) = (av:(real^N->bool)->real^N) e` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper`
      MP_TAC THENL
       [UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                     derived_dual_cell t l (bv e)` THEN
        DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `(v:real^N) = (bv:(real^N->bool)->real^N) e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) = y'` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!a b. a IN moi_s35_cube /\ b IN moi_s35_cube /\
                 (psi:(real^N->bool)->real^3->real^N) e a = psi e b ==> a = b`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(y':real^3) IN moi_s35_upper` THEN
          MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
          REWRITE_TAC[MOI_S5A_MODEL_BASIC];
          UNDISCH_TAC `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y` THEN
          UNDISCH_TAC `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y'` THEN
          MESON_TAC[]];
        UNDISCH_TAC `(y':real^3) IN moi_s35_upper` THEN
        UNDISCH_TAC `(y':real^3)$3 = -- &1 / &8` THEN
        REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `e:real^N->bool`; `x:real^N`] MOI_S5P_GLOB_A) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[moi_s35_ach; o_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `?e. moi_s35_edge l e /\
                     (x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                         moi_s5p_boxb` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
      CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
    USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(v:real^N) = (av:(real^N->bool)->real^N) e \/ v = bv e` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (UNDISCH MOI_S5P_SLAB_AT)) THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `g:real^N->real^N->bool`;
                            `psi:(real^N->bool)->real^3->real^N`; `x:real^N`] THEN
      ASM_SIMP_TAC[MOI_S5P_BOX_SLAB];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxb` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s35_cube` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN moi_s5p_boxb` THEN
      MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
      REWRITE_TAC[MOI_S5P_MODEL_INCL3];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3)$3 = &1 / &8` ASSUME_TAC THENL
     [USE_THEN "far" (MP_TAC o SPECL [`e:real^N->bool`; `y:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(v:real^N) = (av:(real^N->bool)->real^N) e \/ v = bv e` THEN MESON_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN moi_s5p_boxb` THEN
      REWRITE_TAC[moi_s5p_boxb; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^N) = (bv:(real^N->bool)->real^N) e` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC ACCEPT_TAC) THEN
      SUBGOAL_THEN `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower`
      MP_TAC THENL
       [UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower =
                     derived_dual_cell t l (av e)` THEN
        DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `(v:real^N) = (av:(real^N->bool)->real^N) e` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) = y'` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!a b. a IN moi_s35_cube /\ b IN moi_s35_cube /\
                 (psi:(real^N->bool)->real^3->real^N) e a = psi e b ==> a = b`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(y':real^3) IN moi_s35_lower` THEN
          MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
          REWRITE_TAC[MOI_S5A_MODEL_BASIC];
          UNDISCH_TAC `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y` THEN
          UNDISCH_TAC `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y'` THEN
          MESON_TAC[]];
        UNDISCH_TAC `(y':real^3) IN moi_s35_lower` THEN
        UNDISCH_TAC `(y':real^3)$3 = &1 / &8` THEN
        REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `e:real^N->bool`; `x:real^N`] MOI_S5P_GLOB_B) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e y` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s35_level (&1 / &8)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_s35_level; IN_ELIM_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[moi_s35_bch; o_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s5p_glob] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `w:real^N` THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `v:real^N`; `w:real^N`; `x:real^N`] (UNDISCH MOI_S5P_CELLS_MEET)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(w:real^N = v)` THEN MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))) THEN
    UNDISCH_TAC `~(?e. moi_s35_edge l e /\
                       (x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                           moi_s5p_boxa)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `e1:real^N->bool` THEN ASM_SIMP_TAC[MOI_S5P_BOX_SLAB];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 16. The data of all edges at once (inverse charts q, squeezes mm, B-side *)
(* pieces qq onto tb), chosen by Skolemization of EDGE_DATA.                 *)
(* ------------------------------------------------------------------------- *)

let moi_s5p_edata = new_definition
 `moi_s5p_edata (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
     (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
     (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3)
     (xx:real^N->real^3->bool) (cc:(real^N->bool)->real)
     (q:(real^N->bool)->real^N->real^3) (mm:(real^N->bool)->real^3->real^3)
     (qq:(real^N->bool)->real^3->real^3) (tb:(real^N->bool)->real^3->bool) <=>
   !e. moi_s35_edge l e
       ==> pl_homeomorphism
             (moi_s35_cube,derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e))
             (psi e,q e) /\
           (?M'. pl_homeomorphism
                   (moi_s5p_boxa,
                    interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;cc e]])
                   (mm e,M')) /\
           (!y. y IN moi_s5p_boxa /\ y$3 = -- &1 / &8 ==> mm e y = y) /\
           IMAGE (moi_s35_ach ff av psi e) (IMAGE (mm e) moi_s35_mid) =
           moi_s35_ddisk av bv xx e /\
           (?Q'. pl_homeomorphism (moi_s5p_boxb,tb e) (qq e,Q')) /\
           (!y. y IN moi_s35_mid ==> qq e y = moi_s35_ach ff av psi e (mm e y)) /\
           (!y. y IN moi_s35_level (&1 / &8) ==> qq e y = moi_s35_bch ff bv psi e y) /\
           tb e SUBSET moi_s35_dcell l av bv xx (bv e) /\
           tb e SUBSET moi_s5p_x2 ff av bv psi e /\
           IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) SUBSET tb e /\
           moi_s35_ddisk av bv xx e SUBSET tb e /\
           moi_s35_dcell l av bv xx (bv e) SUBSET
           tb e UNION moi_s5p_x1 t l av bv psi ff cc (bv e) e`;;

let MOI_S5P_EDATA_EXISTS = prove
 (mk_imp(MOI_FND_GRAPH_TUBE, mk_imp(MOI_S35_TWO_DISK_EXT,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc.
     PL_SCHOENFLIES_3_STATEMENT /\
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_source_ok t l av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep l av bv psi ff /\ moi_s35_sep2 l av bv psi ff /\
     (!e. moi_s35_edge l e
          ==> pl_ball 3 (moi_s35_dcell l av bv xx (bv e)) /\
              moi_s35_ddisk av bv xx e SUBSET frontier (moi_s35_dcell l av bv xx (bv e)))
     ==> ?q mm qq tb. moi_s5p_edata t l av bv psi ff xx cc q mm qq tb`)),
  DISCH_THEN(LABEL_TAC "tube") THEN DISCH_THEN(LABEL_TAC "tde") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e
        ==> ?q1 mm1 qq1 tb1.
           pl_homeomorphism
             (moi_s35_cube,derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                           derived_dual_cell t l (bv e))
             ((psi:(real^N->bool)->real^3->real^N) e,q1) /\
           (?M'. pl_homeomorphism
                   (moi_s5p_boxa,
                    interval[vector[-- &1;-- &1;-- &1 / &8],
                             vector[&1;&1;(cc:(real^N->bool)->real) e]])
                   (mm1,M')) /\
           (!y. y IN moi_s5p_boxa /\ y$3 = -- &1 / &8 ==> mm1 y = y) /\
           IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) (IMAGE mm1 moi_s35_mid) =
           moi_s35_ddisk av bv xx e /\
           (?Q'. pl_homeomorphism (moi_s5p_boxb,tb1) (qq1,Q')) /\
           (!y. y IN moi_s35_mid ==> qq1 y = moi_s35_ach ff av psi e (mm1 y)) /\
           (!y. y IN moi_s35_level (&1 / &8) ==> qq1 y = moi_s35_bch ff bv psi e y) /\
           tb1 SUBSET moi_s35_dcell l av bv xx (bv e) /\
           tb1 SUBSET moi_s5p_x2 ff av bv psi e /\
           IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) SUBSET tb1 /\
           moi_s35_ddisk av bv xx e SUBSET tb1 /\
           moi_s35_dcell l av bv xx (bv e) SUBSET
           tb1 UNION moi_s5p_x1 t l av bv psi ff cc (bv e) e`
  MP_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
      CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
    MP_TAC(MATCH_MP (ASSUME
     `!e. moi_s35_edge l e
          ==> pl_ball 3 (moi_s35_dcell l (av:(real^N->bool)->real^N) bv xx (bv e)) /\
              moi_s35_ddisk av bv xx e SUBSET frontier (moi_s35_dcell l av bv xx (bv e))`)
     (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL MOI_S5P_ARGS (UNDISCH (UNDISCH MOI_S5P_EDGE_DATA))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real^3->real^3` (X_CHOOSE_THEN `M':real^3->real^3`
      (X_CHOOSE_THEN `Q:real^3->real^3` (X_CHOOSE_THEN `Q':real^3->real^3`
        (X_CHOOSE_THEN `tt:real^3->bool` STRIP_ASSUME_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`q:real^N->real^3`; `M:real^3->real^3`; `Q:real^3->real^3`;
                          `tt:real^3->bool`] THEN
    ASM_REWRITE_TAC[moi_s5p_boxa; moi_s5p_boxb] THEN CONJ_TAC THENL
     [EXISTS_TAC `M':real^3->real^3` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `Q':real^3->real^3` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(fun th -> REWRITE_TAC[moi_s5p_edata] THEN
      MATCH_ACCEPT_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] th))]);;

(* ------------------------------------------------------------------------- *)
(* 17. One dual cell C_v: its decomposition into the core and the slab       *)
(* halves of its edges, and the facts of the edge data used below.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_EDATA_E = prove
 (`!(t:(real^N->bool)->bool) l av bv psi ff xx cc q mm qq tb e.
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e
     ==> pl_homeomorphism
           (moi_s35_cube,derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e))
           (psi e,q e) /\
         (?M'. pl_homeomorphism
                 (moi_s5p_boxa,
                  interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;cc e]])
                 (mm e,M')) /\
         (!y. y IN moi_s5p_boxa /\ y$3 = -- &1 / &8 ==> mm e y = y) /\
         IMAGE (moi_s35_ach ff av psi e) (IMAGE (mm e) moi_s35_mid) =
         moi_s35_ddisk av bv xx e /\
         (?Q'. pl_homeomorphism (moi_s5p_boxb,tb e) (qq e,Q')) /\
         (!y. y IN moi_s35_mid ==> qq e y = moi_s35_ach ff av psi e (mm e y)) /\
         (!y. y IN moi_s35_level (&1 / &8) ==> qq e y = moi_s35_bch ff bv psi e y) /\
         tb e SUBSET moi_s35_dcell l av bv xx (bv e) /\
         tb e SUBSET moi_s5p_x2 ff av bv psi e /\
         IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)) SUBSET tb e /\
         moi_s35_ddisk av bv xx e SUBSET tb e /\
         moi_s35_dcell l av bv xx (bv e) SUBSET
         tb e UNION moi_s5p_x1 t l av bv psi ff cc (bv e) e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5p_edata] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let MOI_S5P_EDATA_MAPS = prove
 (`!(t:(real^N->bool)->bool) l av bv psi ff xx cc q mm qq tb e.
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e
     ==> (!y. y IN moi_s35_cube ==> q e (psi e y) = y) /\
         (!z. z IN derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e)
              ==> psi e (q e z) = z) /\
         pl_map_on (derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e)) (q e) /\
         IMAGE (mm e) moi_s5p_boxa =
         interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;cc e]] /\
         pl_map_on moi_s5p_boxa (mm e) /\
         (!x y. x IN moi_s5p_boxa /\ y IN moi_s5p_boxa /\ mm e x = mm e y ==> x = y) /\
         IMAGE (qq e) moi_s5p_boxb = tb e /\
         pl_map_on moi_s5p_boxb (qq e) /\
         (!x y. x IN moi_s5p_boxb /\ y IN moi_s5p_boxb /\ qq e x = qq e y ==> x = y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_EDATA_E) THEN
  UNDISCH_TAC `pl_homeomorphism
                (moi_s35_cube,derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                              derived_dual_cell t l (bv e))
                ((psi:(real^N->bool)->real^3->real^N) e,(q:(real^N->bool)->real^N->real^3) e)` THEN
  UNDISCH_TAC `pl_homeomorphism
                (moi_s5p_boxa,
                 interval[vector[-- &1;-- &1;-- &1 / &8],
                          vector[&1;&1;(cc:(real^N->bool)->real) e]])
                ((mm:(real^N->bool)->real^3->real^3) e,M')` THEN
  UNDISCH_TAC `pl_homeomorphism (moi_s5p_boxb,(tb:(real^N->bool)->real^3->bool) e)
                ((qq:(real^N->bool)->real^3->real^3) e,Q')` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* The dual cell of v is its core plus the A-halves (chart Box_A) of its    *)
(* A-side edges and the B-halves (chart Box_B) of its B-side edges.         *)

let MOI_S5P_CELL_SPLIT = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi v.
     moi_s35_charts t l g av bv psi /\ {v} IN l
     ==> derived_dual_cell t l v =
         moi_s5p_core t l av bv psi v UNION
         UNIONS {IMAGE (psi e) moi_s5p_boxa | e | moi_s35_edge l e /\ av e = v} UNION
         UNIONS {IMAGE (psi e) moi_s5p_boxb | e | moi_s35_edge l e /\ bv e = v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `(x:real^N) IN moi_s5p_core t l av bv psi v` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((x:real^N) IN moi_s5p_core t l av bv psi v)` THEN
    ASM_REWRITE_TAC[moi_s5p_core; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) MP_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
      CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
    REWRITE_TAC[IN_IMAGE; moi_s5p_osl; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
     [DISJ1_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `y:real^3` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e y IN
                    IMAGE (psi e) moi_s35_lower` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) = y'` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!a b. a IN moi_s35_cube /\ b IN moi_s35_cube /\
                 (psi:(real^N->bool)->real^3->real^N) e a = psi e b ==> a = b`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y':real^3) IN moi_s35_lower` THEN
        MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
        REWRITE_TAC[MOI_S5A_MODEL_BASIC];
        UNDISCH_TAC `(y':real^3) IN moi_s35_lower` THEN
        UNDISCH_TAC `abs((y':real^3)$3) < &1 / &8` THEN
        REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
        REWRITE_TAC[moi_s5p_boxa; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
        REAL_ARITH_TAC];
      DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `y:real^3` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e y IN
                    IMAGE (psi e) moi_s35_upper` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) = y'` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!a b. a IN moi_s35_cube /\ b IN moi_s35_cube /\
                 (psi:(real^N->bool)->real^3->real^N) e a = psi e b ==> a = b`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y':real^3) IN moi_s35_upper` THEN
        MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
        REWRITE_TAC[MOI_S5A_MODEL_BASIC];
        UNDISCH_TAC `(y':real^3) IN moi_s35_upper` THEN
        UNDISCH_TAC `abs((y':real^3)$3) < &1 / &8` THEN
        REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
        REWRITE_TAC[moi_s5p_boxb; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
        REAL_ARITH_TAC]];
    STRIP_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN moi_s5p_core t l av bv psi v` THEN
      SIMP_TAC[moi_s5p_core; IN_DIFF];
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
        CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
      UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower =
                   derived_dual_cell t l (av e)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxa` THEN
      MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN REWRITE_TAC[MOI_S5P_MODEL_INCL3];
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
        CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
      UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper =
                   derived_dual_cell t l (bv e)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxb` THEN
      MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN REWRITE_TAC[MOI_S5P_MODEL_INCL3]]]);;

(* ------------------------------------------------------------------------- *)
(* 18. The pasted map is PL on each dual cell: in the chart of an edge at v  *)
(* it is a model map (squeeze then A-chart on the A side, B-piece then       *)
(* B-chart on the B side), and away from the slabs it is ff v.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_ARGS13 =
  [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
   `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
   `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
   `e:real^N->bool`];;

let MOI_S5P_PL_A_MODEL = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e
     ==> pl_map_on moi_s35_lower
           (\y. if -- &1 / &8 <= y$3 then moi_s35_ach ff av psi e (mm e y)
                else moi_s35_ach ff av psi e y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_CHART_PL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS11 MOI_S5P_POST_EDGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s35_lower =
    moi_s5p_boxa UNION interval[vector[-- &1;-- &1;-- &1]:real^3,vector[&1;&1;-- &1 / &8]]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; moi_s5p_boxa; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_3] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `moi_s35_ach (ff:real^N->real^N->real^3) av psi e o
                (mm:(real^N->bool)->real^3->real^3) e` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[o_THM] THEN
      REWRITE_TAC[moi_s5p_boxa; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; MOI_S5A_DOM_INTERVAL; DIMINDEX_3; FORALL_3;
                  VECTOR_3] THEN
      DISCH_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `moi_s35_ach (ff:real^N->real^N->real^3) av psi e` THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[moi_s5p_boxa; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; MOI_S5A_DOM_INTERVAL; DIMINDEX_3; FORALL_3;
                  VECTOR_3] THEN
      GEN_TAC THEN REAL_ARITH_TAC];
    MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[SUBSET_UNION; moi_s5p_boxa; CLOSED_INTERVAL];
    MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[SUBSET_UNION; CLOSED_INTERVAL]]);;

let MOI_S5P_PL_B_MODEL = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e
     ==> pl_map_on moi_s35_upper
           (\y. if y$3 <= &1 / &8 then qq e y else moi_s35_bch ff bv psi e y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_CHART_PL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s35_upper =
    moi_s5p_boxb UNION interval[vector[-- &1;-- &1;&1 / &8]:real^3,vector[&1;&1;&1]]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; moi_s5p_boxb; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_3] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `(qq:(real^N->bool)->real^3->real^3) e` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[moi_s5p_boxb; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e` THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN STRIP_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[moi_s35_level; IN_ELIM_THM; MOI_S5A_CUBE_IN] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_upper` THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; MOI_S5N_HALVES; DIMINDEX_3; FORALL_3;
                  VECTOR_3; VECTOR_NEG_COMPONENT] THEN
      GEN_TAC THEN REAL_ARITH_TAC];
    MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[SUBSET_UNION; moi_s5p_boxb; CLOSED_INTERVAL];
    MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[SUBSET_UNION; CLOSED_INTERVAL]]);;

let MOI_S5P_EDATA_ED = prove
 (`!(t:(real^N->bool)->bool) l av bv psi ff xx cc q mm qq tb.
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb
     ==> !e. moi_s35_edge l e
             ==> (!y. y IN moi_s35_cube ==> q e (psi e y) = y) /\
                 (!y. y IN moi_s5p_boxa /\ y$3 = -- &1 / &8 ==> mm e y = y) /\
                 (!y. y IN moi_s35_mid ==> qq e y = moi_s35_ach ff av psi e (mm e y)) /\
                 (!y. y IN moi_s35_level (&1 / &8) ==> qq e y = moi_s35_bch ff bv psi e y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC));;

(* Away from the slab halves of the edges at v, the pasted map is ff v.     *)

let MOI_S5P_GLOB_FAR = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff xx cc q mm qq tb v z.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ {v} IN l /\
     z IN derived_dual_cell t l v /\
     (!e. moi_s35_edge l e /\ (av e = v \/ bv e = v) ==> ~(z IN IMAGE (psi e) moi_s35_slab))
     ==> moi_s5p_glob t l av psi ff q mm qq z = ff v z`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(UNDISCH MOI_S5P_GLOB_CORE) THEN
  MAP_EVERY EXISTS_TAC [`g:real^N->real^N->bool`; `bv:(real^N->bool)->real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_s5p_core; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(p ==> q) ==> ~q ==> ~p`) THEN
    MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN
    REWRITE_TAC[SUBSET; moi_s5p_osl; moi_s35_slab; IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC MOI_S5P_EDATA_ED THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `xx:real^N->real^3->bool`;
                          `cc:(real^N->bool)->real`; `tb:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* In the chart of an edge e at its A-end (B-end), off the other slabs at   *)
(* that end, the pasted map is the A-side (B-side) model map composed with  *)
(* the inverse chart.                                                       *)

let MOI_S5P_GLOB_NEAR_A = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff xx cc q mm qq tb e z.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e /\
     z IN derived_dual_cell t l (av e) /\
     (!e'. moi_s35_edge l e' /\ (av e' = av e \/ bv e' = av e) /\ ~(e' = e)
           ==> ~(z IN IMAGE (psi e') moi_s35_slab))
     ==> moi_s5p_glob t l av psi ff q mm qq z =
         (\y. if -- &1 / &8 <= y$3 then moi_s35_ach ff av psi e (mm e y)
              else moi_s35_ach ff av psi e y) (q e z)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "oth")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s35_cube` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN moi_s35_lower` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[MOI_S5A_MODEL_BASIC];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o C MATCH_MP (ASSUME `(y:real^3) IN moi_s35_cube`)) THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `moi_s35_ach (ff:real^N->real^N->real^3) av psi e
                  ((mm:(real^N->bool)->real^3->real^3) e
                    ((q:(real^N->bool)->real^N->real^3) e (psi e y)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5P_GLOB_A THEN
      MAP_EVERY EXISTS_TAC [`g:real^N->real^N->bool`; `bv:(real^N->bool)->real^N`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_lower` THEN
      UNDISCH_TAC `-- &1 / &8 <= (y:real^3)$3` THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
      REWRITE_TAC[moi_s5p_boxa; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      REAL_ARITH_TAC;
      FIRST_ASSUM(SUBST1_TAC o C MATCH_MP (ASSUME `(y:real^3) IN moi_s35_cube`)) THEN
      REFL_TAC];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                   `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `tb:(real^N->bool)->real^3->bool`; `(av:(real^N->bool)->real^N) e`;
                   `(psi:(real^N->bool)->real^3->real^N) e y`] (UNDISCH MOI_S5P_GLOB_FAR)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e':real^N->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      ASM_CASES_TAC `e':real^N->bool = e` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `y2:real^3` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:real^3) = y2` SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!a b. a IN moi_s35_cube /\ b IN moi_s35_cube /\
                   (psi:(real^N->bool)->real^3->real^N) e a = psi e b ==> a = b`) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(y2:real^3) IN moi_s35_slab` THEN
          MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
          REWRITE_TAC[MOI_S5A_MODEL_BASIC];
          UNDISCH_TAC `(y2:real^3) IN moi_s35_slab` THEN
          UNDISCH_TAC `~(-- &1 / &8 <= (y2:real^3)$3)` THEN
          REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REAL_ARITH_TAC];
        USE_THEN "oth" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[moi_s35_ach; o_THM]]]);;

let MOI_S5P_GLOB_NEAR_B = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff xx cc q mm qq tb e z.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e /\
     z IN derived_dual_cell t l (bv e) /\
     (!e'. moi_s35_edge l e' /\ (av e' = bv e \/ bv e' = bv e) /\ ~(e' = e)
           ==> ~(z IN IMAGE (psi e') moi_s35_slab))
     ==> moi_s5p_glob t l av psi ff q mm qq z =
         (\y. if y$3 <= &1 / &8 then qq e y else moi_s35_bch ff bv psi e y) (q e z)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "oth")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s35_cube` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN moi_s35_upper` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[MOI_S5A_MODEL_BASIC];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o C MATCH_MP (ASSUME `(y:real^3) IN moi_s35_cube`)) THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(qq:(real^N->bool)->real^3->real^3) e
                  ((q:(real^N->bool)->real^N->real^3) e (psi e (y:real^3)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5P_GLOB_B THEN
      MAP_EVERY EXISTS_TAC [`g:real^N->real^N->bool`; `bv:(real^N->bool)->real^N`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_upper` THEN
      UNDISCH_TAC `(y:real^3)$3 <= &1 / &8` THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
      REWRITE_TAC[moi_s5p_boxb; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      REAL_ARITH_TAC;
      FIRST_ASSUM(SUBST1_TAC o C MATCH_MP (ASSUME `(y:real^3) IN moi_s35_cube`)) THEN
      REFL_TAC];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                   `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `tb:(real^N->bool)->real^3->bool`; `(bv:(real^N->bool)->real^N) e`;
                   `(psi:(real^N->bool)->real^3->real^N) e y`] (UNDISCH MOI_S5P_GLOB_FAR)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e':real^N->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      ASM_CASES_TAC `e':real^N->bool = e` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `y2:real^3` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:real^3) = y2` SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!a b. a IN moi_s35_cube /\ b IN moi_s35_cube /\
                   (psi:(real^N->bool)->real^3->real^N) e a = psi e b ==> a = b`) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(y2:real^3) IN moi_s35_slab` THEN
          MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
          REWRITE_TAC[MOI_S5A_MODEL_BASIC];
          UNDISCH_TAC `(y2:real^3) IN moi_s35_slab` THEN
          UNDISCH_TAC `~((y2:real^3)$3 <= &1 / &8)` THEN
          REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REAL_ARITH_TAC];
        USE_THEN "oth" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[moi_s35_bch; o_THM]]]);;

let MOI_S5P_CELL_LOCPOLY = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l v.
     graph_in_complex t l /\ {v} IN l ==> locally_polyhedral (derived_dual_cell t l v)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "tube" (MP_TAC o C MATCH_MP (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`) o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S5A_CELL_DOWN o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[pl_homeomorphism] THEN MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL]);;


let MOI_S5P_PL_NEAR_A = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e u.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e /\ open u /\
     (!z e'. z IN derived_dual_cell t l (av e) INTER u /\ moi_s35_edge l e' /\
             (av e' = av e \/ bv e' = av e) /\ ~(e' = e)
             ==> ~(z IN IMAGE (psi e') moi_s35_slab))
     ==> pl_map_on (derived_dual_cell t l (av e) INTER u) (moi_s5p_glob t l av psi ff q mm qq)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "oth"))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `(av:(real^N->bool)->real^N) e`] (UNDISCH MOI_S5P_CELL_LOCPOLY)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `(\y. if -- &1 / &8 <= y$3
                   then moi_s35_ach (ff:real^N->real^N->real^3) av psi e
                          ((mm:(real^N->bool)->real^3->real^3) e y)
                   else moi_s35_ach ff av psi e y) o (q:(real^N->bool)->real^N->real^3) e` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                   `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`; `z:real^N`]
      (UNDISCH MOI_S5P_GLOB_NEAR_A)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^N) IN derived_dual_cell t l ((av:(real^N->bool)->real^N) e) INTER u` THEN
        SIMP_TAC[IN_INTER];
        REPEAT STRIP_TAC THEN USE_THEN "oth" (MP_TAC o SPECL [`z:real^N`; `e':real^N->bool`]) THEN
        ANTS_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM]];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_s35_lower` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                  derived_dual_cell t l (bv e)` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_INTER_OPEN] THEN SET_TAC[];
      MATCH_MP_TAC MOI_S5P_PL_A_MODEL THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `h:real^N->real^3`; `w:real^N->real^3->bool`;
                            `g:real^N->real^N->bool`; `bv:(real^N->bool)->real^N`;
                            `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                            `q:(real^N->bool)->real^N->real^3`;
                            `qq:(real^N->bool)->real^3->real^3`;
                            `tb:(real^N->bool)->real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower`
      MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) IN moi_s35_cube` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN moi_s35_lower` THEN
        MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
        REWRITE_TAC[MOI_S5A_MODEL_BASIC];
        ASM_SIMP_TAC[]]]]);;

let MOI_S5P_PL_NEAR_B = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e u.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e /\ open u /\
     (!z e'. z IN derived_dual_cell t l (bv e) INTER u /\ moi_s35_edge l e' /\
             (av e' = bv e \/ bv e' = bv e) /\ ~(e' = e)
             ==> ~(z IN IMAGE (psi e') moi_s35_slab))
     ==> pl_map_on (derived_dual_cell t l (bv e) INTER u) (moi_s5p_glob t l av psi ff q mm qq)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "oth"))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `(bv:(real^N->bool)->real^N) e`] (UNDISCH MOI_S5P_CELL_LOCPOLY)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `(\y. if y$3 <= &1 / &8
                   then (qq:(real^N->bool)->real^3->real^3) e y
                   else moi_s35_bch (ff:real^N->real^N->real^3) bv psi e y) o
              (q:(real^N->bool)->real^N->real^3) e` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                   `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`; `z:real^N`]
      (UNDISCH MOI_S5P_GLOB_NEAR_B)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^N) IN derived_dual_cell t l ((bv:(real^N->bool)->real^N) e) INTER u` THEN
        SIMP_TAC[IN_INTER];
        REPEAT STRIP_TAC THEN USE_THEN "oth" (MP_TAC o SPECL [`z:real^N`; `e':real^N->bool`]) THEN
        ANTS_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM]];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_s35_upper` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
                  derived_dual_cell t l (bv e)` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_INTER_OPEN] THEN SET_TAC[];
      MATCH_MP_TAC MOI_S5P_PL_B_MODEL THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `h:real^N->real^3`; `w:real^N->real^3->bool`;
                            `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                            `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                            `q:(real^N->bool)->real^N->real^3`;
                            `mm:(real^N->bool)->real^3->real^3`;
                            `tb:(real^N->bool)->real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper`
      MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) IN moi_s35_cube` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN moi_s35_upper` THEN
        MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
        REWRITE_TAC[MOI_S5A_MODEL_BASIC];
        ASM_SIMP_TAC[]]]]);;

let MOI_S5P_GLOB_PL_V = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ {v} IN l
     ==> pl_map_on (derived_dual_cell t l v) (moi_s5p_glob t l av psi ff q mm qq)`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    (UNDISCH MOI_S5P_CELL_LOCPOLY)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_map_on (moi_s35_cplus t l av bv psi v) ((ff:real^N->real^N->real^3) v) /\
                derived_dual_cell t l v SUBSET moi_s35_cplus t l av bv psi v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
      REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
      DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`) o CONJUNCT1 o CONJUNCT1) THEN
      SIMP_TAC[];
      REWRITE_TAC[moi_s35_cplus] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {e | moi_s35_edge l e /\
                            ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5P_VERT_EDGES_FINITE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `g:real^N->real^N->bool`;
                          `psi:(real^N->bool)->real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5P_PL_LOCAL THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `?e. moi_s35_edge l e /\ ((av:(real^N->bool)->real^N) e = v \/ bv e = v) /\
                     (x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                         moi_s35_slab` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    SUBGOAL_THEN
     `open ((:real^N) DIFF
            UNIONS (IMAGE (\e'. IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab)
                          {e' | moi_s35_edge l e' /\
                                ((av:(real^N->bool)->real^N) e' = v \/ bv e' = v) /\
                                ~(e' = e)}))`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC MOI_S5V_SLABS_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                            `bv:(real^N->bool)->real^N`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{e:real^N->bool | moi_s35_edge l e /\
                                      ((av:(real^N->bool)->real^N) e = v \/ bv e = v)}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        SIMP_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    EXISTS_TAC `(:real^N) DIFF
                UNIONS (IMAGE (\e'. IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab)
                              {e' | moi_s35_edge l e' /\
                                    ((av:(real^N->bool)->real^N) e' = v \/ bv e' = v) /\
                                    ~(e' = e)})` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_UNIV; UNIONS_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      BETA_TAC THEN X_GEN_TAC `e':real^N->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) ASSUME_TAC) THEN
      UNDISCH_TAC `~(e':real^N->bool = e)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_S5P_SLAB_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                            `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                            `x:real^N`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(DISJ_CASES_THEN (SUBST_ALL_TAC o SYM) o check (is_disj o concl)) THENL
       [MATCH_MP_TAC(UNDISCH MOI_S5P_PL_NEAR_A) THEN
        MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
                              `g:real^N->real^N->bool`; `bv:(real^N->bool)->real^N`;
                              `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                              `tb:(real^N->bool)->real^3->bool`];
        MATCH_MP_TAC(UNDISCH MOI_S5P_PL_NEAR_B) THEN
        MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
                              `g:real^N->real^N->bool`;
                              `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                              `tb:(real^N->bool)->real^3->bool`]] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; UNIONS_IMAGE; IN_ELIM_THM] THEN BETA_TAC THEN
      MESON_TAC[]];
    EXISTS_TAC `(:real^N) DIFF
                UNIONS (IMAGE (\e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                              {e | moi_s35_edge l e /\
                                   ((av:(real^N->bool)->real^N) e = v \/ bv e = v)})` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC MOI_S5V_SLABS_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                            `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                            `bv:(real^N->bool)->real^N`] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_ELIM_THM];
      REWRITE_TAC[IN_DIFF; IN_UNIV; UNIONS_IMAGE; IN_ELIM_THM] THEN
      UNDISCH_TAC `~(?e. moi_s35_edge l e /\ ((av:(real^N->bool)->real^N) e = v \/ bv e = v) /\
                         (x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                             moi_s35_slab)` THEN
      MESON_TAC[];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `(ff:real^N->real^N->real^3) v` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `z:real^N` THEN
        REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; UNIONS_IMAGE; IN_ELIM_THM] THEN
        STRIP_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC(UNDISCH MOI_S5P_GLOB_FAR) THEN
        MAP_EVERY EXISTS_TAC [`g:real^N->real^N->bool`; `bv:(real^N->bool)->real^N`;
                              `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                              `tb:(real^N->bool)->real^3->bool`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(?e. (moi_s35_edge l e /\
                            ((av:(real^N->bool)->real^N) e = v \/ bv e = v)) /\
                           (z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                               moi_s35_slab)` THEN
        MESON_TAC[];
        MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
        EXISTS_TAC `moi_s35_cplus t l av bv psi (v:real^N)` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `derived_dual_cell t l (v:real^N) SUBSET
                       moi_s35_cplus t l av bv psi v` THEN SET_TAC[];
          MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC MOI_S5V_SLABS_CLOSED THEN
          MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                                `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                                `bv:(real^N->bool)->real^N`] THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_ELIM_THM]]]]]);;

(* ------------------------------------------------------------------------- *)
(* 19. Disjointness of the B-side pieces and the A-slab images at a vertex,  *)
(* the cut A-slab image inside D_v.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_X2_OFF_ACH = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e e'.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e /\ moi_s35_edge l e' /\ ~(e = e')
     ==> DISJOINT (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab) (moi_s5p_x2 ff av bv psi e')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(MP_TAC o SPECL [`e':real^N->bool`; `e:real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e:real^N->bool = e')` THEN MESON_TAC[];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  UNDISCH_TAC `moi_s35_sep2 l (av:(real^N->bool)->real^N) bv psi ff` THEN
  REWRITE_TAC[moi_s35_sep2] THEN
  DISCH_THEN(MP_TAC o SPECL [`e':real^N->bool`; `e:real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e:real^N->bool = e')` THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S5P_MODEL_INCL))))) THEN
  REWRITE_TAC[moi_s5p_x2] THEN
  MATCH_ACCEPT_TAC(SET_RULE
   `!(f:real^3->real^3) (f':real^3->real^3) (g:real^3->real^3) s1 s2 a.
      s1 SUBSET s2 ==> DISJOINT (IMAGE g a) (IMAGE f s2) ==>
      DISJOINT (IMAGE f' s2) (IMAGE f s2) ==>
      DISJOINT (IMAGE f s2) (IMAGE g a UNION IMAGE f' s1)`));;

let MOI_S5P_INJ_DISJ = prove
 (`!(f:A->B) u s t.
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
     s SUBSET u /\ t SUBSET u /\ DISJOINT s t
     ==> DISJOINT (IMAGE f s) (IMAGE f t)`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; SUBSET] THEN
  MESON_TAC[]);;

let MOI_S5P_X2_DISJ = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e e'.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_sep2 l av bv psi ff /\ moi_s35_edge l e /\ moi_s35_edge l e' /\
     ~(e = e') /\ bv e' = bv e
     ==> DISJOINT (moi_s5p_x2 ff av bv psi e) (moi_s5p_x2 ff av bv psi e')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5P_CHART_FACTS
    (CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)
          (ASSUME `moi_s35_edge l (e:real^N->bool)`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab)
             (moi_s5p_x2 ff av bv psi e') /\
    DISJOINT (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab) (moi_s5p_x2 ff av bv psi e)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5P_X2_OFF_ACH THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                          `h:real^N->real^3`; `w:real^N->real^3->bool`;
                          `g:real^N->real^N->bool`; `xx:real^N->real^3->bool`;
                          `cc:(real^N->bool)->real`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e:real^N->bool = e')` THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                    (moi_s35_bcell INTER moi_s35_slab))
             (IMAGE (moi_s35_bch ff bv psi e') (moi_s35_bcell INTER moi_s35_slab))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `cc:(real^N->bool)->real`; `(bv:(real^N->bool)->real^N) e`]
      MOI_S5P_CORE2_CPLUS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `e':real^N->bool` (CONJUNCT2 th)) THEN
                         MP_TAC(SPEC `e:real^N->bool` (CONJUNCT2 th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[moi_s35_bch; IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S5P_INJ_DISJ THEN
    EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
      REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
      DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`) o
        CONJUNCT1 o CONJUNCT1) THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2);
      MATCH_MP_TAC(SET_RULE `!(f:real^3->real^N) g s t.
        s SUBSET t /\ DISJOINT (IMAGE f t) (IMAGE g t)
        ==> DISJOINT (IMAGE f s) (IMAGE g s)`) THEN
      EXISTS_TAC `moi_s35_slab` THEN REWRITE_TAC[MOI_S5P_MODEL_INCL2] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!e'. moi_s35_edge l e' /\ ~(e = e')
               ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)
                            (IMAGE (psi e') moi_s35_slab)`) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`moi_s35_ach (ff:real^N->real^N->real^3) av psi e`; `moi_s35_stube`;
                 `moi_s35_slab`] IMAGE_SUBSET) THEN
  MP_TAC(ISPECL [`moi_s35_ach (ff:real^N->real^N->real^3) av psi e'`; `moi_s35_stube`;
                 `moi_s35_slab`] IMAGE_SUBSET) THEN
  REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S5P_MODEL_INCL))))] THEN
  UNDISCH_TAC `DISJOINT (IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                    (moi_s35_bcell INTER moi_s35_slab))
             (IMAGE (moi_s35_bch ff bv psi e') (moi_s35_bcell INTER moi_s35_slab))` THEN
  UNDISCH_TAC `DISJOINT (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e') moi_s35_slab)
                        (moi_s5p_x2 ff av bv psi e)` THEN
  UNDISCH_TAC `DISJOINT (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab)
                        (moi_s5p_x2 ff av bv psi e')` THEN
  REWRITE_TAC[moi_s5p_x2] THEN
  MATCH_ACCEPT_TAC(SET_RULE
   `!(a1:real^3->bool) b1 a2 b2 s1 s2.
      DISJOINT s1 (a2 UNION b2) ==> DISJOINT s2 (a1 UNION b1) ==> DISJOINT a1 a2 ==>
      b2 SUBSET s2 ==> b1 SUBSET s1 ==>
      DISJOINT (a1 UNION b1) (a2 UNION b2)`));;

(* The cut A-slab image of an A-side edge of v lies in D_v.                 *)

let MOI_S5P_ACUT_IN_D = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s35_edge l e
     ==> IMAGE (moi_s35_ach ff av psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e} SUBSET
         moi_s35_dcell l av bv xx (av e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5P_CHART_FACTS o
    CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS11 MOI_S5P_POST_EDGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fe")
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fs") (K ALL_TAC)))))
   (K ALL_TAC)) THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN xx ((av:(real^N->bool)->real^N) e) /\
                x IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `xx ((av:(real^N->bool)->real^N) e) INTER
                 IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab =
                 IMAGE (moi_s35_ach ff av psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e}` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                                     {x | x IN moi_s35_slab /\ x$3 <= cc e}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_dcell; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `e'':real^N->bool` THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; TAUT `~(p /\ q /\ r) <=> p /\ q ==> ~r`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!(x:real^3) s. ~(x IN s) /\ interior s SUBSET s ==> ~(x IN interior s)`) THEN
  REWRITE_TAC[INTERIOR_SUBSET] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(e'':real^N->bool = e)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e'':real^N->bool)`)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "fs" (MP_TAC o SPECL [`e:real^N->bool`; `e'':real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e'':real^N->bool = e)` THEN MESON_TAC[];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                                   moi_s35_slab` THEN
  UNDISCH_TAC `(x:real^3) IN xx ((av:(real^N->bool)->real^N) e)` THEN
  UNDISCH_TAC `(x:real^3) IN xx ((av:(real^N->bool)->real^N) e'')` THEN
  MATCH_ACCEPT_TAC(SET_RULE
   `!(x:real^3) a b i j. x IN a ==> x IN b ==> x IN i ==> DISJOINT i j ==>
                         ~(a INTER b SUBSET j)`));;

(* ------------------------------------------------------------------------- *)
(* 20. The pasted map on the pieces of a dual cell: values, images,          *)
(* injectivity, and the overlaps of the core image with the slab-half        *)
(* images (only over the outer faces of the halves).                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_MM_DOM = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w av bv psi ff xx cc q mm qq tb e y.
     moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e /\
     y IN moi_s5p_boxa
     ==> mm e y IN moi_s35_dom /\ mm e y IN moi_s35_cube /\
         mm e y IN {x | x IN moi_s35_slab /\ x$3 <= cc e} /\
         -- &1 / &8 <= (mm e y)$3 /\ (mm e y)$3 <= cc e /\ abs(cc e) <= &1 / &512`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS11 MOI_S5P_POST_EDGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(mm:(real^N->bool)->real^3->real^3) e y IN
                interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;(cc:(real^N->bool)->real) e]]`
  MP_TAC THENL
   [UNDISCH_TAC `IMAGE ((mm:(real^N->bool)->real^3->real^3) e) moi_s5p_boxa =
                 interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;(cc:(real^N->bool)->real) e]]` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; IN_ELIM_THM] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REWRITE_TAC[MOI_S5A_CUBE_IN] THEN
  REAL_ARITH_TAC);;

let MOI_S5P_GLOB_IMG_A = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff xx cc q mm qq tb e.
     moi_s35_charts t l g av bv psi /\ moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\
     moi_s35_edge l e
     ==> IMAGE (moi_s5p_glob t l av psi ff q mm qq) (IMAGE (psi e) moi_s5p_boxa) =
         IMAGE (moi_s35_ach ff av psi e) (IMAGE (mm e) moi_s5p_boxa) /\
         (!y. y IN moi_s5p_boxa
              ==> moi_s5p_glob t l av psi ff q mm qq (psi e y) =
                  moi_s35_ach ff av psi e (mm e y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN moi_s5p_boxa
        ==> moi_s5p_glob t l av psi ff q mm qq ((psi:(real^N->bool)->real^3->real^N) e y) =
            moi_s35_ach (ff:real^N->real^N->real^3) av psi e
              ((mm:(real^N->bool)->real^3->real^3) e y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `e:real^N->bool`; `(psi:(real^N->bool)->real^3->real^N) e y`]
      MOI_S5P_GLOB_A) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y. y IN moi_s35_cube ==>
             (q:(real^N->bool)->real^N->real^3) e ((psi:(real^N->bool)->real^3->real^N) e y) = y`)
          (concl th))) THEN
    UNDISCH_TAC `(y:real^3) IN moi_s5p_boxa` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[MOI_S5P_MODEL_INCL3];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC MOI_S5P_IMAGE_EQ THEN
  ASM_SIMP_TAC[o_THM]);;

let MOI_S5P_GLOB_IMG_B = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff xx cc q mm qq tb e.
     moi_s35_charts t l g av bv psi /\ moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\
     moi_s35_edge l e
     ==> IMAGE (moi_s5p_glob t l av psi ff q mm qq) (IMAGE (psi e) moi_s5p_boxb) = tb e /\
         (!y. y IN moi_s5p_boxb
              ==> moi_s5p_glob t l av psi ff q mm qq (psi e y) = qq e y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN moi_s5p_boxb
        ==> moi_s5p_glob t l av psi ff q mm qq ((psi:(real^N->bool)->real^3->real^N) e y) =
            (qq:(real^N->bool)->real^3->real^3) e y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `e:real^N->bool`; `(psi:(real^N->bool)->real^3->real^N) e y`]
      MOI_S5P_GLOB_B) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y. y IN moi_s35_cube ==>
             (q:(real^N->bool)->real^N->real^3) e ((psi:(real^N->bool)->real^3->real^N) e y) = y`)
          (concl th))) THEN
    UNDISCH_TAC `(y:real^3) IN moi_s5p_boxb` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[MOI_S5P_MODEL_INCL3];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE ((qq:(real^N->bool)->real^3->real^3) e) moi_s5p_boxb` THEN
  CONJ_TAC THENL [MATCH_MP_TAC MOI_S5P_IMAGE_EQ THEN ASM_SIMP_TAC[o_THM]; ASM_REWRITE_TAC[]]);;

let MOI_S5P_GLOB_ON_CORE = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff xx cc q mm qq tb v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ {v} IN l
     ==> (!x. x IN moi_s5p_core t l av bv psi v
              ==> moi_s5p_glob t l av psi ff q mm qq x = ff v x) /\
         IMAGE (moi_s5p_glob t l av psi ff q mm qq) (moi_s5p_core t l av bv psi v) =
         IMAGE (ff v) (moi_s5p_core t l av bv psi v)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN moi_s5p_core t l av bv psi v
                    ==> moi_s5p_glob t l av psi ff q mm qq x = (ff:real^N->real^N->real^3) v x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(UNDISCH MOI_S5P_GLOB_CORE) THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^N->bool`; `bv:(real^N->bool)->real^N`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5P_EDATA_ED THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `xx:real^N->real^3->bool`;
                          `cc:(real^N->bool)->real`; `tb:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5P_IMAGE_EQ THEN ASM_REWRITE_TAC[]]);;

let MOI_S5P_GLOB_INJ_A = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e
     ==> !x y. x IN IMAGE (psi e) moi_s5p_boxa /\ y IN IMAGE (psi e) moi_s5p_boxa /\
               moi_s5p_glob t l av psi ff q mm qq x = moi_s5p_glob t l av psi ff q mm qq y
               ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_A) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_CHART_PL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `y1:real^3` THEN DISCH_TAC THEN X_GEN_TAC `y2:real^3` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP th (ASSUME `(y1:real^3) IN moi_s5p_boxa`);
                MATCH_MP th (ASSUME `(y2:real^3) IN moi_s5p_boxa`)]) THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                 `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                 `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                 `e:real^N->bool`; `y1:real^3`] MOI_S5P_MM_DOM) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                 `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                 `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                 `e:real^N->bool`; `y2:real^3`] MOI_S5P_MM_DOM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (term_match [] `!x y. x IN moi_s5p_boxa /\ y IN moi_s5p_boxa /\
           (mm:(real^N->bool)->real^3->real^3) e x = mm e y ==> x = y`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (term_match [] `!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\
           moi_s35_ach (ff:real^N->real^N->real^3) av psi e x = moi_s35_ach ff av psi e y
           ==> x = y`) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5P_GLOB_INJ_B = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff xx cc q mm qq tb e.
     moi_s35_charts t l g av bv psi /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e
     ==> !x y. x IN IMAGE (psi e) moi_s5p_boxb /\ y IN IMAGE (psi e) moi_s5p_boxb /\
               moi_s5p_glob t l av psi ff q mm qq x = moi_s5p_glob t l av psi ff q mm qq y
               ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_B) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `y1:real^3` THEN DISCH_TAC THEN X_GEN_TAC `y2:real^3` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (term_match [] `!x y. x IN moi_s5p_boxb /\ y IN moi_s5p_boxb /\
           (qq:(real^N->bool)->real^3->real^3) e x = qq e y ==> x = y`) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5P_GLOB_INJ_CORE = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ {v} IN l
     ==> !x y. x IN moi_s5p_core t l av bv psi v /\ y IN moi_s5p_core t l av bv psi v /\
               moi_s5p_glob t l av psi ff q mm qq x = moi_s5p_glob t l av psi ff q mm qq y
               ==> x = y`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `v:real^N`]
    (UNDISCH MOI_S5P_GLOB_ON_CORE)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `cc:(real^N->bool)->real`; `v:real^N`] MOI_S5P_CORE2_CPLUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`) o CONJUNCT1 o CONJUNCT1) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (term_match [] `!x y. x IN moi_s35_cplus t l av bv psi v /\
           y IN moi_s35_cplus t l av bv psi v /\
           (ff:real^N->real^N->real^3) v x = ff v y ==> x = y`) (concl th))) THEN
  SUBGOAL_THEN `moi_s5p_core t l av bv psi (v:real^N) SUBSET moi_s35_cplus t l av bv psi v`
  MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s5p_core2 t l av bv psi (cc:(real^N->bool)->real) (v:real^N)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s5p_core2] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) =
               moi_s5p_glob t l av psi ff q mm qq y` THEN
  ASM_SIMP_TAC[]);;

let MOI_S5P_OVERLAP_A = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e
     ==> IMAGE (moi_s5p_glob t l av psi ff q mm qq) (moi_s5p_core t l av bv psi (av e)) INTER
         IMAGE (moi_s5p_glob t l av psi ff q mm qq) (IMAGE (psi e) moi_s5p_boxa) SUBSET
         IMAGE (moi_s5p_glob t l av psi ff q mm qq)
               (moi_s5p_core t l av bv psi (av e) INTER IMAGE (psi e) moi_s5p_boxa)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5P_CHART_FACTS
    (CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)
          (ASSUME `moi_s35_edge l (e:real^N->bool)`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `(av:(real^N->bool)->real^N) e`]
    (UNDISCH MOI_S5P_GLOB_ON_CORE)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gc") (LABEL_TAC "gci")) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gai") (LABEL_TAC "ga")) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `cc:(real^N->bool)->real`; `(av:(real^N->bool)->real^N) e`]
    MOI_S5P_CORE2_CPLUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{(av:(real^N->bool)->real^N) e} IN l`) o
    CONJUNCT1 o CONJUNCT1) THEN
  DISCH_THEN(LABEL_TAC "inj" o CONJUNCT1 o CONJUNCT2) THEN
  USE_THEN "gci" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "gai" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `w0:real^3` THEN
  REWRITE_TAC[IN_IMAGE; o_THM; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^N` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                 `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                 `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                 `e:real^N->bool`; `y2:real^3`] MOI_S5P_MM_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `moi_s5p_core t l av bv psi ((av:(real^N->bool)->real^N) e) SUBSET
    moi_s5p_core2 t l av bv psi (cc:(real^N->bool)->real) (av e) /\
    (psi:(real^N->bool)->real^3->real^N) e ((mm:(real^N->bool)->real^3->real^3) e y2) IN
    moi_s5p_core2 t l av bv psi cc (av e)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5p_core2] THEN CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z1:real^N) = (psi:(real^N->bool)->real^3->real^N) e
                                ((mm:(real^N->bool)->real^3->real^3) e y2)` ASSUME_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `moi_s5p_core2 t l av bv psi (cc:(real^N->bool)->real)
                     ((av:(real^N->bool)->real^N) e) SUBSET moi_s35_cplus t l av bv psi (av e)` THEN
      UNDISCH_TAC `moi_s5p_core t l av bv psi ((av:(real^N->bool)->real^N) e) SUBSET
                   moi_s5p_core2 t l av bv psi (cc:(real^N->bool)->real) (av e)` THEN
      UNDISCH_TAC `(z1:real^N) IN moi_s5p_core t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
      SET_TAC[];
      UNDISCH_TAC `moi_s5p_core2 t l av bv psi (cc:(real^N->bool)->real)
                     ((av:(real^N->bool)->real^N) e) SUBSET moi_s35_cplus t l av bv psi (av e)` THEN
      UNDISCH_TAC `(psi:(real^N->bool)->real^3->real^N) e ((mm:(real^N->bool)->real^3->real^3) e y2) IN
                   moi_s5p_core2 t l av bv psi (cc:(real^N->bool)->real) ((av:(real^N->bool)->real^N) e)` THEN
      SET_TAC[];
      UNDISCH_TAC `(w0:real^3) = (ff:real^N->real^N->real^3) ((av:(real^N->bool)->real^N) e) z1` THEN
      UNDISCH_TAC `(w0:real^3) = moi_s35_ach (ff:real^N->real^N->real^3) av psi e
                                   ((mm:(real^N->bool)->real^3->real^3) e y2)` THEN
      REWRITE_TAC[moi_s35_ach; o_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((mm:(real^N->bool)->real^3->real^3) e y2)$3 = -- &1 / &8` ASSUME_TAC THENL
   [UNDISCH_TAC `(z1:real^N) IN moi_s5p_core t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
    ASM_REWRITE_TAC[moi_s5p_core; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_IMAGE; moi_s5p_osl; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(mm:(real^N->bool)->real^3->real^3) e y2`) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `-- &1 / &8 <= ((mm:(real^N->bool)->real^3->real^3) e y2)$3` THEN
    UNDISCH_TAC `((mm:(real^N->bool)->real^3->real^3) e y2)$3 <= (cc:(real^N->bool)->real) e` THEN
    UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(mm:(real^N->bool)->real^3->real^3) e y2 IN moi_s5p_boxa` ASSUME_TAC THENL
   [UNDISCH_TAC `(mm:(real^N->bool)->real^3->real^3) e y2 IN moi_s35_cube` THEN
    UNDISCH_TAC `((mm:(real^N->bool)->real^3->real^3) e y2)$3 = -- &1 / &8` THEN
    REWRITE_TAC[moi_s5p_boxa; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; MOI_S5A_CUBE_IN] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y2:real^3) = (mm:(real^N->bool)->real^3->real^3) e y2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x y. x IN moi_s5p_boxa /\ y IN moi_s5p_boxa /\
             (mm:(real^N->bool)->real^3->real^3) e x = mm e y ==> x = y`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y. y IN moi_s5p_boxa /\ y$3 = -- &1 / &8 ==>
             (mm:(real^N->bool)->real^3->real^3) e y = y`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(psi:(real^N->bool)->real^3->real^N) e y2` THEN REPEAT CONJ_TAC THENL
   [USE_THEN "ga" (fun th ->
      REWRITE_TAC[MATCH_MP th (ASSUME `(y2:real^3) IN moi_s5p_boxa`)]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `(z1:real^N) IN moi_s5p_core t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y2:real^3) = (mm:(real^N->bool)->real^3->real^3) e y2` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
    SIMP_TAC[];
    EXISTS_TAC `y2:real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_S5P_OVERLAP_B = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_sep l av bv psi ff /\
     moi_s35_sep2 l av bv psi ff /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e
     ==> IMAGE (moi_s5p_glob t l av psi ff q mm qq) (moi_s5p_core t l av bv psi (bv e)) INTER
         IMAGE (moi_s5p_glob t l av psi ff q mm qq) (IMAGE (psi e) moi_s5p_boxb) SUBSET
         IMAGE (moi_s5p_glob t l av psi ff q mm qq)
               (moi_s5p_core t l av bv psi (bv e) INTER IMAGE (psi e) moi_s5p_boxb)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5P_CHART_FACTS
    (CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)
          (ASSUME `moi_s35_edge l (e:real^N->bool)`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `(bv:(real^N->bool)->real^N) e`]
    (UNDISCH MOI_S5P_GLOB_ON_CORE)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gc") (LABEL_TAC "gci")) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gbi") (LABEL_TAC "gb")) THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_X_INTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "gci" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "gbi" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `IMAGE ((ff:real^N->real^N->real^3) ((bv:(real^N->bool)->real^N) e))
          (moi_s5p_core t l av bv psi (bv e)) SUBSET
    moi_s5p_x1 t l av bv psi ff (cc:(real^N->bool)->real) (bv e) e`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5p_x1; moi_s5p_core2; IMAGE_UNION] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `w0:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w0:real^3) IN IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                                     (moi_s35_level (&1 / &8))` MP_TAC THENL
   [UNDISCH_TAC `moi_s5p_x1 t l av bv psi (ff:real^N->real^N->real^3) cc
                   ((bv:(real^N->bool)->real^N) e) e INTER moi_s5p_x2 ff av bv psi e =
                 IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE ((ff:real^N->real^N->real^3) ((bv:(real^N->bool)->real^N) e))
                         (moi_s5p_core t l av bv psi (bv e)) SUBSET
                   moi_s5p_x1 t l av bv psi ff (cc:(real^N->bool)->real) (bv e) e` THEN
      UNDISCH_TAC `(w0:real^3) IN IMAGE ((ff:real^N->real^N->real^3) ((bv:(real^N->bool)->real^N) e))
                                        (moi_s5p_core t l av bv psi (bv e))` THEN
      SET_TAC[];
      UNDISCH_TAC `(tb:(real^N->bool)->real^3->bool) e SUBSET
                   moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e` THEN
      UNDISCH_TAC `(w0:real^3) IN (tb:(real^N->bool)->real^3->bool) e` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y3:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `(psi:(real^N->bool)->real^3->real^N) e y3` THEN
  SUBGOAL_THEN `(y3:real^3) IN moi_s5p_boxb` ASSUME_TAC THENL
   [UNDISCH_TAC `(y3:real^3) IN moi_s35_level (&1 / &8)` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[MOI_S5P_MODEL_INCL3];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "gb" (fun th -> ASM_SIMP_TAC[th]);
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`] MOI_S5P_LEVEL_IN_CORE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^N) s t x. x IN s ==> IMAGE f s SUBSET t ==>
                                                      f x IN t`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 21. On each dual cell C_v the pasted map is injective with image D_v.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_CUTBOX = prove
 (`!c. abs c <= &1 / &512
       ==> interval[vector[-- &1;-- &1;-- &1 / &8]:real^3,vector[&1;&1;c]] =
           {x | x IN moi_s35_slab /\ x$3 <= c}`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; IN_ELIM_THM] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S5P_CELL_SPLIT2 = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi v.
     moi_s35_charts t l g av bv psi /\ {v} IN l
     ==> derived_dual_cell t l v =
         moi_s5p_core t l av bv psi v UNION
         UNIONS (IMAGE (\e. if av e = v then IMAGE (psi e) moi_s5p_boxa
                            else IMAGE (psi e) moi_s5p_boxb)
                       {e | moi_s35_edge l e /\ (av e = v \/ bv e = v)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `v:real^N`] MOI_S5P_CELL_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!e. moi_s35_edge l e ==> ~((av:(real^N->bool)->real^N) e = bv e)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `e:real^N->bool`] MOI_S5P_CHART_FACTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; UNIONS_IMAGE; IN_ELIM_THM; COND_RAND; COND_EXPAND] THEN
  POP_ASSUM MP_TAC THEN MESON_TAC[]);;

let MOI_S5P_HALF_IMG = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e
     ==> IMAGE (moi_s5p_glob t l av psi ff q mm qq) (IMAGE (psi e) moi_s5p_boxa) SUBSET
         IMAGE (moi_s35_ach ff av psi e) moi_s35_slab /\
         IMAGE (moi_s5p_glob t l av psi ff q mm qq) (IMAGE (psi e) moi_s5p_boxb) SUBSET
         moi_s5p_x2 ff av bv psi e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_A) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL MOI_S5P_ARGS11 MOI_S5P_POST_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                   (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxa) =
                 IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                   (IMAGE ((mm:(real^N->bool)->real^3->real^3) e) moi_s5p_boxa)` THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    UNDISCH_TAC `IMAGE ((mm:(real^N->bool)->real^3->real^3) e) moi_s5p_boxa =
                 interval[vector[-- &1;-- &1;-- &1 / &8],vector[&1;&1;(cc:(real^N->bool)->real) e]]` THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPEC `(cc:(real^N->bool)->real) e` MOI_S5P_CUTBOX) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_S5P_MODEL_INCL2];
    UNDISCH_TAC `IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                   (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxb) =
                 (tb:(real^N->bool)->real^3->bool) e` THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S5P_GLOB_INJ_V = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_sep l av bv psi ff /\
     moi_s35_sep2 l av bv psi ff /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ {v} IN l
     ==> !x y. x IN derived_dual_cell t l v /\ y IN derived_dual_cell t l v /\
               moi_s5p_glob t l av psi ff q mm qq x = moi_s5p_glob t l av psi ff q mm qq y
               ==> x = y`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `v:real^N`] MOI_S5P_CELL_SPLIT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_S5P_INJ_PASTE THEN REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN
  REWRITE_TAC[ETA_AX] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(UNDISCH MOI_S5P_GLOB_INJ_CORE) THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
                          `g:real^N->real^N->bool`; `xx:real^N->real^3->bool`;
                          `cc:(real^N->bool)->real`; `tb:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) MP_TAC) THEN
    COND_CASES_TAC THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                     `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                     `e:real^N->bool`] MOI_S5P_GLOB_INJ_A);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:real^N->real^N->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                     `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                     `e:real^N->bool`] MOI_S5P_GLOB_INJ_B)] THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `j:real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)
      (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                   `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                   `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                   `i:real^N->bool`] MOI_S5P_HALF_IMG) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                   `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                   `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                   `j:real^N->bool`] MOI_S5P_HALF_IMG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `DISJOINT (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi i) moi_s35_slab)
               (moi_s5p_x2 ff av bv psi j) /\
      DISJOINT (IMAGE (moi_s35_ach ff av psi j) moi_s35_slab) (moi_s5p_x2 ff av bv psi i) /\
      DISJOINT (IMAGE (moi_s35_ach ff av psi i) moi_s35_slab)
               (IMAGE (moi_s35_ach ff av psi j) moi_s35_slab)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5P_X2_OFF_ACH THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                              `h:real^N->real^3`; `w:real^N->real^3->bool`;
                              `g:real^N->real^N->bool`; `xx:real^N->real^3->bool`;
                              `cc:(real^N->bool)->real`] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_S5P_X2_OFF_ACH THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                              `h:real^N->real^3`; `w:real^N->real^3->bool`;
                              `g:real^N->real^N->bool`; `xx:real^N->real^3->bool`;
                              `cc:(real^N->bool)->real`] THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(i:real^N->bool = j)` THEN MESON_TAC[];
        UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
        REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
        DISCH_THEN(MP_TAC o SPECL [`i:real^N->bool`; `j:real^N->bool`] o
          CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(av:(real^N->bool)->real^N) i = v` THEN
    ASM_CASES_TAC `(av:(real^N->bool)->real^N) j = v` THEN ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `DISJOINT (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi i) moi_s35_slab)
                            (IMAGE (moi_s35_ach ff av psi j) moi_s35_slab)`;
      UNDISCH_TAC `DISJOINT (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi i) moi_s35_slab)
                            (moi_s5p_x2 ff av bv psi j)`;
      UNDISCH_TAC `DISJOINT (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi j) moi_s35_slab)
                            (moi_s5p_x2 ff av bv psi i)`;
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `i:real^N->bool`; `j:real^N->bool`] MOI_S5P_X2_DISJ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(av:(real^N->bool)->real^N) i = v \/ bv i = v` THEN
        UNDISCH_TAC `(av:(real^N->bool)->real^N) j = v \/ bv j = v` THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC]] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET"))) THEN
    SET_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    ASM_CASES_TAC `(av:(real^N->bool)->real^N) e = v` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                     `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                     `e:real^N->bool`] (UNDISCH MOI_S5P_OVERLAP_A)) THEN
      ANTS_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(bv:(real^N->bool)->real^N) e = v` ASSUME_TAC THENL
       [UNDISCH_TAC `(av:(real^N->bool)->real^N) e = v \/ bv e = v` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                     `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                     `e:real^N->bool`] (UNDISCH MOI_S5P_OVERLAP_B)) THEN
      ANTS_TAC THEN ASM_REWRITE_TAC[]]]);;

let MOI_S5P_GLOB_IMAGE_V = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb v.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_sep l av bv psi ff /\
     moi_s35_sep2 l av bv psi ff /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ {v} IN l
     ==> IMAGE (moi_s5p_glob t l av psi ff q mm qq) (derived_dual_cell t l v) =
         moi_s35_dcell l av bv xx v`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                 `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                 `tb:(real^N->bool)->real^3->bool`; `v:real^N`]
    (UNDISCH MOI_S5P_GLOB_ON_CORE)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gc") (K ALL_TAC))] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                 `v:real^N`] MOI_S5P_CORE_IN_D) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "cd" o CONJUNCT2 o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `v:real^N`] MOI_S5P_CELL_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 MP_TAC MP_TAC)) THENL
     [USE_THEN "gc" (fun th -> ASM_SIMP_TAC[th]) THEN
      USE_THEN "cd" (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))
        (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                     `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                     `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                     `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                     `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_A) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `w:real^N->real^3->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                     `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                     `e:real^N->bool`; `y:real^3`] MOI_S5P_MM_DOM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_ACUT_IN_D) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))
        (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                     `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                     `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                     `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                     `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_B) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
      MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `(tb:(real^N->bool)->real^3->bool) e SUBSET
                   moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e)` THEN
      UNDISCH_TAC `IMAGE ((qq:(real^N->bool)->real^3->real^3) e) moi_s5p_boxb =
                   (tb:(real^N->bool)->real^3->bool) e` THEN
      UNDISCH_TAC `(y:real^3) IN moi_s5p_boxb` THEN
      MATCH_ACCEPT_TAC(SET_RULE
       `!(f:real^3->real^3) y s t d. y IN s ==> IMAGE f s = t ==> t SUBSET d ==> f y IN d`)];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`; `v:real^N`]
      MOI_S5P_D_COVER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[moi_s5p_core2; IMAGE_UNION; IN_UNION] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (DISJ_CASES_THEN2 MP_TAC MP_TAC) MP_TAC) THENL
     [REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "gc" (fun th -> ASM_SIMP_TAC[th]);
      REWRITE_TAC[IN_IMAGE; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2
          (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)
          (X_CHOOSE_THEN `p:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)))))) THEN
      MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_MAPS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL MOI_S5P_ARGS11 MOI_S5P_POST_EDGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(SPEC `(cc:(real^N->bool)->real) e` MOI_S5P_CUTBOX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `(p:real^3) IN IMAGE ((mm:(real^N->bool)->real^3->real^3) e) moi_s5p_boxa`
      MP_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                     `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                     `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                     `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                     `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_A) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE; UNIONS_GSPEC; IN_ELIM_THM] THEN
      EXISTS_TAC `(psi:(real^N->bool)->real^3->real^N) e y` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[] THEN
        UNDISCH_TAC `(av:(real^N->bool)->real^N) e = v` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[moi_s35_ach; o_THM];
        EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC)) THEN
      MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_X_INTER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                     `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                     `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                     `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                     `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] MOI_S5P_GLOB_IMG_B) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
      SUBGOAL_THEN `(x:real^3) IN (tb:(real^N->bool)->real^3->bool) e` MP_TAC THENL
       [UNDISCH_TAC `moi_s35_dcell l av bv xx ((bv:(real^N->bool)->real^N) e) SUBSET
                     (tb:(real^N->bool)->real^3->bool) e UNION
                     moi_s5p_x1 t l av bv psi ff cc (bv e) e` THEN
        UNDISCH_TAC `moi_s5p_x1 t l av bv psi (ff:real^N->real^N->real^3) cc
                       ((bv:(real^N->bool)->real^N) e) e INTER moi_s5p_x2 ff av bv psi e =
                     IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8))` THEN
        UNDISCH_TAC `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                       (moi_s35_level (&1 / &8)) SUBSET (tb:(real^N->bool)->real^3->bool) e` THEN
        UNDISCH_TAC `(x:real^3) IN moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e` THEN
        UNDISCH_TAC `(x:real^3) IN moi_s35_dcell l av bv xx (v:real^N)` THEN
        UNDISCH_TAC `(bv:(real^N->bool)->real^N) e = v` THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_ACCEPT_TAC(SET_RULE
         `!(x:real^3) d x2 ee t x1.
            x IN d ==> x IN x2 ==> ee SUBSET t ==> x1 INTER x2 = ee ==>
            d SUBSET t UNION x1 ==> x IN t`);
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                     (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxb) =
                   (tb:(real^N->bool)->real^3->bool) e` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      DISCH_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                     (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5p_boxb)` THEN
      REWRITE_TAC[IN_IMAGE; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)))) THEN
      EXISTS_TAC `(psi:(real^N->bool)->real^3->real^N) e y` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 22. The only points of C_(av e) or C_(bv e) that the pasted map sends     *)
(* into the disk ddisk e = D_(av e) INTER D_(bv e) are those of the middle   *)
(* square psi e(mid).                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_ARGS16 =
  [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`;
   `w:real^N->real^3->bool`; `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
   `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
   `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
   `e:real^N->bool`];;

let MOI_S5P_ARGS14 =
  [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
   `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
   `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`];;

(* The disk is the image of the middle square under both half maps.         *)

let MOI_S5P_DDISK_MID = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi ff xx cc q mm qq tb e.
     moi_s35_charts t l g av bv psi /\ moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\
     moi_s35_edge l e
     ==> moi_s35_ddisk av bv xx e =
         IMAGE (moi_s5p_glob t l av psi ff q mm qq) (IMAGE (psi e) moi_s35_mid) /\
         moi_s35_ddisk av bv xx e = IMAGE (qq e) moi_s35_mid`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS14 MOI_S5P_GLOB_IMG_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL MOI_S5P_ARGS13 MOI_S5P_EDATA_E) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                 (IMAGE ((mm:(real^N->bool)->real^3->real^3) e) moi_s35_mid) =
               moi_s35_ddisk av bv xx e` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM IMAGE_o] THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_S5P_IMAGE_EQ THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_mid` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[MOI_S5P_MODEL_INCL3];
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y. y IN moi_s35_mid ==>
             (qq:(real^N->bool)->real^3->real^3) e y =
             moi_s35_ach (ff:real^N->real^N->real^3) av psi e (mm e y)`) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S5P_DISK_PRE_A = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e x.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_sep l av bv psi ff /\
     moi_s35_sep2 l av bv psi ff /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e /\
     x IN derived_dual_cell t l (av e) /\
     moi_s5p_glob t l av psi ff q mm qq x IN moi_s35_ddisk av bv xx e
     ==> x IN IMAGE (psi e) moi_s35_mid`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5P_CHART_FACTS
    (CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)
          (ASSUME `moi_s35_edge l (e:real^N->bool)`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_DDISK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN
                IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_ddisk av bv xx e SUBSET
                 IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                       {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}` THEN
    UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN moi_s35_ddisk av bv xx e` THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S5P_MODEL_INCL)))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `(av:(real^N->bool)->real^N) e`] MOI_S5P_CELL_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> UNDISCH_TAC
    `(x:real^N) IN derived_dual_cell t l ((av:(real^N->bool)->real^N) e)` THEN
    SUBST1_TAC th)] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
    (X_CHOOSE_THEN `e':real^N->bool` (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC))
    (X_CHOOSE_THEN `e':real^N->bool` (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC)))) THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                   `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `tb:(real^N->bool)->real^3->bool`; `(av:(real^N->bool)->real^N) e`]
      (UNDISCH MOI_S5P_GLOB_ON_CORE)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL MOI_S5P_ARGS11 MOI_S5P_POST_EDGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(ff:real^N->real^N->real^3) ((av:(real^N->bool)->real^N) e) x IN
                  IMAGE (moi_s35_ach ff av psi e)
                        {x | x IN moi_s35_level ((cc:(real^N->bool)->real) e) /\
                             moi_s35_n x < &5 / &16}` MP_TAC THENL
     [UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN moi_s35_ddisk av bv xx e` THEN
      ASM_REWRITE_TAC[moi_s35_ddisk] THEN
      UNDISCH_TAC `frontier (xx ((av:(real^N->bool)->real^N) e)) INTER xx (bv e) SUBSET
                   IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                         {x | x IN moi_s35_level ((cc:(real^N->bool)->real) e) /\
                              moi_s35_n x < &5 / &16}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `cc:(real^N->bool)->real`; `(av:(real^N->bool)->real^N) e`]
      MOI_S5P_CORE2_CPLUS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `(p:real^3) IN moi_s35_cube /\ abs(p$3) < &1 / &8 /\
                  p IN {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e}`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^3) IN moi_s35_level ((cc:(real^N->bool)->real) e)` THEN
      UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN
      REWRITE_TAC[moi_s35_level; IN_ELIM_THM] THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
      REWRITE_TAC[MOI_S5A_CUBE_IN] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) = (psi:(real^N->bool)->real^3->real^N) e p` ASSUME_TAC THENL
     [MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
      REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
      DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{(av:(real^N->bool)->real^N) e} IN l`) o
        CONJUNCT1 o CONJUNCT1) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `moi_s5p_core2 t l av bv psi (cc:(real^N->bool)->real)
                       ((av:(real^N->bool)->real^N) e) SUBSET moi_s35_cplus t l av bv psi (av e)` THEN
        UNDISCH_TAC `(x:real^N) IN moi_s5p_core t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
        REWRITE_TAC[moi_s5p_core2] THEN SET_TAC[];
        UNDISCH_TAC `moi_s5p_core2 t l av bv psi (cc:(real^N->bool)->real)
                       ((av:(real^N->bool)->real^N) e) SUBSET moi_s35_cplus t l av bv psi (av e)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[moi_s5p_core2; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
        EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `(ff:real^N->real^N->real^3) ((av:(real^N->bool)->real^N) e) x =
                     moi_s35_ach ff av psi e p` THEN
        REWRITE_TAC[moi_s35_ach; o_THM]];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN moi_s5p_core t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
    ASM_REWRITE_TAC[moi_s5p_core; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[moi_s5p_osl; IN_ELIM_THM];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                   `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                   `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                   `e':real^N->bool`] MOI_S5P_HALF_IMG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    ASM_CASES_TAC `e':real^N->bool = e` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL MOI_S5P_ARGS14 MOI_S5P_DDISK_MID) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
      SUBGOAL_THEN `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN
                    IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                          (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_mid)` MP_TAC THENL
       [UNDISCH_TAC `moi_s35_ddisk (av:(real^N->bool)->real^N) bv xx e =
                     IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                           (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_mid)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:real^N) = z` (fun th -> REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC) THEN
      MP_TAC(ISPECL MOI_S5P_ARGS16 MOI_S5P_GLOB_INJ_A) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_mid` THEN
      MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN REWRITE_TAC[MOI_S5P_MODEL_INCL3];
      MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
      REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
      DISCH_THEN(MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`] o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
        DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      UNDISCH_TAC `IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                     (IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s5p_boxa) SUBSET
                   IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e') moi_s35_slab` THEN
      UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s5p_boxa` THEN
      UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN
                   IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab` THEN
      MATCH_ACCEPT_TAC(SET_RULE
       `!(f:real^N->real^3) x a b c. f x IN a ==> x IN b ==> IMAGE f b SUBSET c ==>
                                     DISJOINT a c ==> x IN d`)];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                   `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                   `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                   `e':real^N->bool`] MOI_S5P_HALF_IMG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                   `e:real^N->bool`; `e':real^N->bool`] MOI_S5P_X2_OFF_ACH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    UNDISCH_TAC `DISJOINT (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab)
                          (moi_s5p_x2 ff av bv psi e')` THEN
    UNDISCH_TAC `IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                   (IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s5p_boxb) SUBSET
                 moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e'` THEN
    UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s5p_boxb` THEN
    UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN
                 IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab` THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!(f:real^N->real^3) x a b c d. f x IN a ==> x IN b ==> IMAGE f b SUBSET c ==>
                                     DISJOINT a c ==> x IN d`)]);;

let MOI_S5P_DISK_PRE_B = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e x.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_sep l av bv psi ff /\
     moi_s35_sep2 l av bv psi ff /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e /\
     x IN derived_dual_cell t l (bv e) /\
     moi_s5p_glob t l av psi ff q mm qq x IN moi_s35_ddisk av bv xx e
     ==> x IN IMAGE (psi e) moi_s35_mid`),
  DISCH_THEN(LABEL_TAC "tube") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5P_CHART_FACTS
    (CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)
          (ASSUME `moi_s35_edge l (e:real^N->bool)`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL MOI_S5P_ARGS MOI_S5P_DDISK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN
                IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab /\
                ~(moi_s5p_glob t l av psi ff q mm qq x IN
                  moi_s5p_x1 t l av bv psi ff cc (bv e) e)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `moi_s35_ddisk av bv xx e SUBSET
                   IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                         {x | x IN moi_s35_slab /\ x$3 <= &1 / &16}` THEN
      UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN moi_s35_ddisk av bv xx e` THEN
      MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S5P_MODEL_INCL)))) THEN
      SET_TAC[];
      UNDISCH_TAC `DISJOINT (moi_s35_ddisk av bv xx e)
                     (moi_s5p_x1 t l av bv psi (ff:real^N->real^N->real^3) cc
                                 ((bv:(real^N->bool)->real^N) e) e)` THEN
      UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN moi_s35_ddisk av bv xx e` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `(bv:(real^N->bool)->real^N) e`] MOI_S5P_CELL_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> UNDISCH_TAC
    `(x:real^N) IN derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)` THEN
    SUBST1_TAC th)] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
    (X_CHOOSE_THEN `e':real^N->bool` (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC))
    (X_CHOOSE_THEN `e':real^N->bool` (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC)))) THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                   `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                   `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                   `mm:(real^N->bool)->real^3->real^3`; `qq:(real^N->bool)->real^3->real^3`;
                   `tb:(real^N->bool)->real^3->bool`; `(bv:(real^N->bool)->real^N) e`]
      (UNDISCH MOI_S5P_GLOB_ON_CORE)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN
                   moi_s5p_x1 t l av bv psi ff cc ((bv:(real^N->bool)->real^N) e) e)` THEN
    ASM_REWRITE_TAC[moi_s5p_x1; moi_s5p_core2; IMAGE_UNION; IN_UNION] THEN
    MATCH_MP_TAC(TAUT `a ==> ~((a \/ b) \/ c) ==> d`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                   `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                   `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                   `e':real^N->bool`] MOI_S5P_HALF_IMG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `~(e':real^N->bool = e)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
    REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
    DISCH_THEN(MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e':real^N->bool = e)` THEN MESON_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    UNDISCH_TAC `IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                   (IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s5p_boxa) SUBSET
                 IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e') moi_s35_slab` THEN
    UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s5p_boxa` THEN
    UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN
                 IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_slab` THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!(f:real^N->real^3) x a b c d. f x IN a ==> x IN b ==> IMAGE f b SUBSET c ==>
                                     DISJOINT a c ==> x IN d`);
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                   `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                   `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                   `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                   `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                   `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                   `e':real^N->bool`] MOI_S5P_HALF_IMG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
    ASM_CASES_TAC `e':real^N->bool = e` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL MOI_S5P_ARGS14 MOI_S5P_DDISK_MID) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
      SUBGOAL_THEN `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN
                    IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                          (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_mid)` MP_TAC THENL
       [UNDISCH_TAC `moi_s35_ddisk (av:(real^N->bool)->real^N) bv xx e =
                     IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                           (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_mid)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:real^N) = z` (fun th -> REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC) THEN
      MP_TAC(ISPECL MOI_S5P_ARGS14 MOI_S5P_GLOB_INJ_B) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_mid` THEN
      MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN REWRITE_TAC[MOI_S5P_MODEL_INCL3];
      SUBGOAL_THEN `moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e' SUBSET
                    moi_s5p_x1 t l av bv psi ff cc ((bv:(real^N->bool)->real^N) e) e`
      ASSUME_TAC THENL
       [REWRITE_TAC[moi_s5p_x1; SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISJ2_TAC THEN
        EXISTS_TAC `e':real^N->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `~(moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN
                     moi_s5p_x1 t l av bv psi ff cc ((bv:(real^N->bool)->real^N) e) e)` THEN
      UNDISCH_TAC `moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e' SUBSET
                   moi_s5p_x1 t l av bv psi ff cc ((bv:(real^N->bool)->real^N) e) e` THEN
      UNDISCH_TAC `IMAGE (moi_s5p_glob t l av psi ff q mm qq)
                     (IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s5p_boxb) SUBSET
                   moi_s5p_x2 (ff:real^N->real^N->real^3) av bv psi e'` THEN
      UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s5p_boxb` THEN
      MATCH_ACCEPT_TAC(SET_RULE
       `!(f:real^N->real^3) x b c x1 d. x IN b ==> IMAGE f b SUBSET c ==> c SUBSET x1 ==>
                                       ~(f x IN x1) ==> x IN d`)]]);;

(* ------------------------------------------------------------------------- *)
(* 23. The final step FINAL_R3: the pasted map is a PL embedding of N with   *)
(* f(C_v) = D_v.                                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S5P_EDGE_OF_PAIR = prove
 (`!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi u v.
     moi_s35_charts t l g av bv psi /\ ~(u = v) /\ segment[u,v] IN l
     ==> moi_s35_edge l (segment[u,v]) /\
         ((av (segment[u,v]) = u /\ bv (segment[u,v]) = v) \/
          (av (segment[u,v]) = v /\ bv (segment[u,v]) = u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_edge l (segment[u:real^N,v])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s35_edge; AFF_DIM_SEGMENT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi` THEN
  REWRITE_TAC[moi_s35_charts] THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (segment[u:real^N,v])`) o
    CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[SEGMENT_EQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S5P_DOUBLETON_CASES) THEN MESON_TAC[]);;

let MOI_S5P_INJ_PAIR = prove
 (mk_imp(MOI_FND_GRAPH_TUBE,
  `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc q mm qq tb e x y.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_post t l h w av bv psi ff xx cc /\ moi_s35_sep l av bv psi ff /\
     moi_s35_sep2 l av bv psi ff /\
     moi_s5p_edata t l av bv psi ff xx cc q mm qq tb /\ moi_s35_edge l e /\
     moi_s35_dcell l av bv xx (av e) INTER moi_s35_dcell l av bv xx (bv e) =
     moi_s35_ddisk av bv xx e /\
     x IN derived_dual_cell t l (av e) /\ y IN derived_dual_cell t l (bv e) /\
     moi_s5p_glob t l av psi ff q mm qq x = moi_s5p_glob t l av psi ff q mm qq y
     ==> x = y`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5P_CHART_FACTS
    (CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)
          (ASSUME `moi_s35_edge l (e:real^N->bool)`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN moi_s35_ddisk av bv xx e`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_dcell l av bv xx ((av:(real^N->bool)->real^N) e) INTER
                 moi_s35_dcell l av bv xx (bv e) = moi_s35_ddisk av bv xx e` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                     `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                     `(av:(real^N->bool)->real^N) e`] (UNDISCH MOI_S5P_GLOB_IMAGE_V)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                     `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                     `(bv:(real^N->bool)->real^N) e`] (UNDISCH MOI_S5P_GLOB_IMAGE_V)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                 `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                 `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                 `e:real^N->bool`; `x:real^N`] (UNDISCH MOI_S5P_DISK_PRE_A)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                 `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                 `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                 `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                 `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                 `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                 `e:real^N->bool`; `y:real^N`] (UNDISCH MOI_S5P_DISK_PRE_B)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) IN moi_s35_ddisk av bv xx e` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL MOI_S5P_ARGS16 MOI_S5P_GLOB_INJ_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_mid`;
    UNDISCH_TAC `(y:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_mid`] THEN
  MATCH_MP_TAC MOI_S5P_IMAGE_MONO THEN REWRITE_TAC[MOI_S5P_MODEL_INCL3]);;

let MOI_S5P_FINAL_R3 = prove
 (MOI_S35_FINAL_R3,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tube") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "cells") (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "tde") (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)))))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "cells" (MP_TAC o C MATCH_MP (ASSUME `PL_SCHOENFLIES_3_STATEMENT`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
    `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fc1") (CONJUNCTS_THEN2 (LABEL_TAC "fc2")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "fc4") (LABEL_TAC "fc5"))))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
    `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`]
    (UNDISCH(UNDISCH MOI_S5P_EDATA_EXISTS))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(MATCH_MP MOI_S5P_CHART_FACTS
      (CONJ (ASSUME `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi`)
            (ASSUME `moi_s35_edge l (e:real^N->bool)`))) THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "fc1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "fc2" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `q:(real^N->bool)->real^N->real^3`
      (X_CHOOSE_THEN `mm:(real^N->bool)->real^3->real^3`
        (X_CHOOSE_THEN `qq:(real^N->bool)->real^3->real^3`
          (X_CHOOSE_THEN `tb:(real^N->bool)->real^3->bool` ASSUME_TAC))))] THEN
  EXISTS_TAC `moi_s5p_glob (t:(real^N->bool)->bool) l av psi ff q mm qq` THEN
  USE_THEN "tube" (MP_TAC o C MATCH_MP (ASSUME `graph_in_complex (t:(real^N->bool)->bool) l`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vtx")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "non")))) THEN
  SUBGOAL_THEN
   `!v:real^N. {v} IN l
        ==> IMAGE (moi_s5p_glob t l av psi ff q mm qq) (derived_dual_cell t l v) =
            moi_s35_dcell l av bv xx v`
  (LABEL_TAC "img") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(UNDISCH MOI_S5P_GLOB_IMAGE_V) THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
                          `g:real^N->real^N->bool`; `cc:(real^N->bool)->real`;
                          `tb:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `UNIONS {derived_dual_cell t l v | v | {v} IN l} =
      UNIONS {(if {v} IN l then derived_dual_cell t l v else {}) | v | {v:real^N} IN l}`
    SUBST1_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_CEL_PL_MAP_ON_UNIONS_LF_INDEXED THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP MOI_S5A_CELL_COMPACT o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
        SIMP_TAC[COMPACT_IMP_CLOSED];
        MATCH_MP_TAC(UNDISCH MOI_S5P_GLOB_PL_V) THEN
        MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
                              `g:real^N->real^N->bool`; `bv:(real^N->bool)->real^N`;
                              `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                              `tb:(real^N->bool)->real^3->bool`] THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `v0:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^N) IN derived_dual_cell t l v0` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN (if {v0:real^N} IN l then derived_dual_cell t l v0 else {})` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
        MOI_S5V_LF_DUAL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{v0:real^N} IN l`)) THEN
          DISCH_THEN(MP_TAC o CONJUNCT1) THEN
          UNDISCH_TAC `(x:real^N) IN derived_dual_cell t l v0` THEN SET_TAC[];
          X_GEN_TAC `w0:real^N` THEN DISCH_TAC THEN
          USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{w0:real^N} IN l`)) THEN SIMP_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{w0:real^N | {w0} IN l /\ ~(derived_dual_cell t l w0 INTER u = {})}` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[INTER_EMPTY]];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_CASES_TAC `u:real^N = v` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `w:real^N->real^3->bool`; `g:real^N->real^N->bool`;
                     `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                     `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                     `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`;
                     `q:(real^N->bool)->real^N->real^3`; `mm:(real^N->bool)->real^3->real^3`;
                     `qq:(real^N->bool)->real^3->real^3`; `tb:(real^N->bool)->real^3->bool`;
                     `v:real^N`] (UNDISCH MOI_S5P_GLOB_INJ_V)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[];
      ASM_CASES_TAC `segment[u:real^N,v] IN l` THENL
       [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                       `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                       `u:real^N`; `v:real^N`] MOI_S5P_EDGE_OF_PAIR) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ABBREV_TAC `e = segment[u:real^N,v]` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
          (DISJ_CASES_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)))) THEN
        USE_THEN "fc2" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
        DISCH_THEN(ASSUME_TAC o CONJUNCT1) THENL
         [ALL_TAC; CONV_TAC SYM_CONV] THEN
        MATCH_MP_TAC(UNDISCH MOI_S5P_INJ_PAIR) THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                              `h:real^N->real^3`; `w:real^N->real^3->bool`;
                              `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                              `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                              `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                              `cc:(real^N->bool)->real`; `q:(real^N->bool)->real^N->real^3`;
                              `mm:(real^N->bool)->real^3->real^3`;
                              `qq:(real^N->bool)->real^3->real^3`;
                              `tb:(real^N->bool)->real^3->bool`; `e:real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        USE_THEN "fc4" (MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "img" (MP_TAC o C MATCH_MP (ASSUME `{u:real^N} IN l`)) THEN
        USE_THEN "img" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`)) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `moi_s5p_glob t l av psi ff q mm qq (x:real^N) =
                     moi_s5p_glob t l av psi ff q mm qq y` THEN
        UNDISCH_TAC `(x:real^N) IN derived_dual_cell t l u` THEN
        UNDISCH_TAC `(y:real^N) IN derived_dual_cell t l v` THEN
        MATCH_ACCEPT_TAC(SET_RULE
         `!(f:real^N->real^3) x y a b. y IN b ==> x IN a ==> f x = f y ==>
                                       DISJOINT (IMAGE f a) (IMAGE f b) ==> x = y`)]];
    SUBGOAL_THEN
     `IMAGE (moi_s5p_glob t l av psi ff q mm qq)
        (UNIONS {derived_dual_cell t l v | v | {v:real^N} IN l}) =
      UNIONS {moi_s35_dcell l av bv xx v | v | {v} IN l}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
      REWRITE_TAC[IN_IMAGE; UNIONS_GSPEC; IN_ELIM_THM] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
          (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC))) THEN
        EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "img" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`)) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        FIRST_ASSUM ACCEPT_TAC;
        DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `(z:real^3) IN moi_s35_dcell l av bv xx (v:real^N)` THEN
        USE_THEN "img" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`)) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "fc5" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ASSUME `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc`) THEN
    REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`(xx:real^N->real^3->bool) v`;
                   `UNIONS {(xx:real^N->real^3->bool) v | v | {v} IN l}`] SUBSET_INTERIOR) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN
      DISCH_TAC THEN EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "img" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `{v:real^N} IN l`)]) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(xx:real^N->real^3->bool) v` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[moi_s35_dcell] THEN SET_TAC[];
      UNDISCH_TAC `moi_s35_post t l (h:real^N->real^3) w av bv psi ff xx cc` THEN
      REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
      DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`) o CONJUNCT1 o CONJUNCT1) THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2)]]);;

