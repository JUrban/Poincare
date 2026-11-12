(* ========================================================================= *)
(* pc_moi_s32_handles: the slabs of the s35 edge charts and the handle       *)
(* decomposition of Moise 32.3 (GTM 47, p.228).  Main theorems               *)
(* SLAB_W : |- MOI_S32_SLAB_W: the two half slabs of an edge chart are PL    *)
(* 3-cells meeting in the splitting disk, with a closed neighbourhood W of   *)
(* the open splitting disk minus its centre that is pinched at the centre;   *)
(* and HANDLES : |- MOI_S32_HANDLES_2: the pseudo-cells in the slabs give    *)
(* the handle decomposition (7)-(10).                                        *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s3032_stmt4.ml";;
needs "src/pc_moi_s34_scella.ml";;
needs "src/pc_moi_fnd_surfa.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: the model boxes, and interiors and frontiers of images           *)
(* under embeddings of compact sets of real^N into real^N.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3HD_CUBE_IN = prove
 (`!x:real^3. x IN moi_s35_cube <=>
              abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ abs(x$3) <= &1`,
  GEN_TAC THEN REWRITE_TAC[moi_s35_cube; IN_INTERVAL; DIMINDEX_3; FORALL_3;
    VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC);;

let MOI_S3HD_SETS_IN = prove
 (`(!x:real^3. x IN moi_s35_slab <=>
               abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ abs(x$3) <= &1 / &8) /\
   (!x:real^3. x IN moi_s32_slab_lo <=>
               abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ --(&1 / &8) <= x$3 /\ x$3 <= &0) /\
   (!x:real^3. x IN moi_s32_slab_hi <=>
               abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ &0 <= x$3 /\ x$3 <= &1 / &8) /\
   (!x:real^3. x IN moi_s35_mid <=>
               abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ x$3 = &0) /\
   (!x:real^3. x IN moi_s35_lower <=>
               abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ --(&1) <= x$3 /\ x$3 <= &0) /\
   (!x:real^3. x IN moi_s35_upper <=>
               abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ &0 <= x$3 /\ x$3 <= &1)`,
  REWRITE_TAC[moi_s35_slab; moi_s32_slab_lo; moi_s32_slab_hi; moi_s35_mid; moi_s35_lower;
    moi_s35_upper; IN_ELIM_THM; MOI_S3HD_CUBE_IN] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3HD_BOXES = prove
 (`moi_s35_slab =
   interval[vector[-- &1; -- &1; --(&1 / &8)], vector[&1; &1; &1 / &8]] /\
   moi_s32_slab_lo =
   interval[vector[-- &1; -- &1; --(&1 / &8)], vector[&1; &1; &0]] /\
   moi_s32_slab_hi =
   interval[vector[-- &1; -- &1; &0], vector[&1; &1; &1 / &8]]`,
  REWRITE_TAC[EXTENSION; MOI_S3HD_SETS_IN; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3HD_INTERIORS = prove
 (`(!x:real^3. x IN interior moi_s35_cube <=>
               abs(x$1) < &1 /\ abs(x$2) < &1 /\ abs(x$3) < &1) /\
   (!x:real^3. x IN interior moi_s35_slab <=>
               abs(x$1) < &1 /\ abs(x$2) < &1 /\ abs(x$3) < &1 / &8) /\
   (!x:real^3. x IN frontier moi_s35_slab <=>
               x IN moi_s35_slab /\
               (abs(x$1) = &1 \/ abs(x$2) = &1 \/ abs(x$3) = &1 / &8))`,
  REWRITE_TAC[CONJUNCT1 MOI_S3HD_BOXES; moi_s35_cube; INTERIOR_CLOSED_INTERVAL;
    FRONTIER_CLOSED_INTERVAL; IN_DIFF] THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3;
    VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3HD_BOX_BALLS = prove
 (`pl_ball 3 moi_s35_slab /\ pl_ball 3 moi_s32_slab_lo /\ pl_ball 3 moi_s32_slab_hi /\
   compact moi_s35_slab /\ compact moi_s32_slab_lo /\ compact moi_s32_slab_hi /\
   compact moi_s35_cube /\ moi_s35_slab SUBSET moi_s35_cube /\
   moi_s32_slab_lo SUBSET moi_s35_slab /\ moi_s32_slab_hi SUBSET moi_s35_slab /\
   moi_s32_slab_lo UNION moi_s32_slab_hi = moi_s35_slab /\
   moi_s32_slab_lo INTER moi_s32_slab_hi = moi_s35_mid /\
   moi_s35_lower INTER moi_s35_upper = moi_s35_mid /\
   moi_s35_mid SUBSET moi_s35_slab /\
   moi_s35_lower SUBSET moi_s35_cube /\ moi_s35_upper SUBSET moi_s35_cube /\
   (vec 0:real^3) IN moi_s35_mid /\
   moi_s32_slo IN moi_s32_slab_lo /\ ~(moi_s32_slo IN moi_s35_mid) /\
   moi_s32_shi IN moi_s32_slab_hi /\ ~(moi_s32_shi IN moi_s35_mid)`,
  SUBGOAL_THEN `!a b:real^3. (!i. 1 <= i /\ i <= 3 ==> a$i < b$i)
                ==> pl_ball 3 (interval[a,b])` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `interval[a:real^3,b]` MOI_S4A_POLY_CELL_3) THEN ANTS_TAC THENL
     [REWRITE_TAC[POLYTOPE_INTERVAL] THEN
      SUBGOAL_THEN `~(interior(interval[a:real^3,b]) = {})` MP_TAC THENL
       [ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_3];
        SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR; DIMINDEX_3]];
      MESON_TAC[pl_ball; pl_cell_with_boundary]];
    ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT1 MOI_S3HD_BOXES; CONJUNCT1(CONJUNCT2 MOI_S3HD_BOXES);
              CONJUNCT2(CONJUNCT2 MOI_S3HD_BOXES)] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; ARITH_RULE
        `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3] THEN REAL_ARITH_TAC) THEN
  TRY(REWRITE_TAC[COMPACT_INTERVAL; moi_s35_cube] THEN NO_TAC) THEN
  REWRITE_TAC[GSYM(CONJUNCT1 MOI_S3HD_BOXES); GSYM(CONJUNCT1(CONJUNCT2 MOI_S3HD_BOXES));
              GSYM(CONJUNCT2(CONJUNCT2 MOI_S3HD_BOXES))] THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_UNION; IN_INTER; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN;
    moi_s32_slo; moi_s32_shi; VECTOR_3; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* Interiors and frontiers under embeddings.                                *)

let MOI_S3HD_HOMEO_INTERIOR = prove
 (`!(f:real^N->real^N) g s t k.
     homeomorphism (s,t) (f,g) /\ k SUBSET s
     ==> interior(IMAGE f k) = IMAGE f (interior k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (k,IMAGE (f:real^N->real^N) k) (f,g)` MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    UNDISCH_TAC `(k:real^N->bool) SUBSET s` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:real^N->real^N`; `IMAGE (f:real^N->real^N) k`]
      CONTINUOUS_IMAGE_SUBSET_INTERIOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (g:real^N->real^N) (IMAGE f k) = k` SUBST1_TAC THENL
     [UNDISCH_TAC `!x:real^N. x IN k ==> (g:real^N->real^N) (f x) = x` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE (f:real^N->real^N) k` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `!y:real^N. y IN IMAGE f k ==> (f:real^N->real^N) (g y) = y` THEN
    SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN ASM_REWRITE_TAC[LE_REFL] THEN
    ASM_MESON_TAC[]]);;

let MOI_S3HD_HOMEO_FRONTIER = prove
 (`!(f:real^N->real^N) g s t k.
     homeomorphism (s,t) (f,g) /\ compact k /\ k SUBSET s
     ==> frontier(IMAGE f k) = IMAGE f (frontier k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  SUBGOAL_THEN `(f:real^N->real^N) continuous_on k` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHISM; CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `closure(IMAGE (f:real^N->real^N) k) = IMAGE f k /\ closure k = k`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`; `s:real^N->bool`;
                 `t:real^N->bool`; `k:real^N->bool`] MOI_S3HD_HOMEO_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    aconv (concl th) `homeomorphism (s,t) (f:real^N->real^N,g)`)) THEN
  MP_TAC(ISPEC `k:real^N->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `(k:real^N->bool) SUBSET s` THEN
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

let MOI_S3HD_EMBED = prove
 (`!(f:real^N->real^N) q k.
     compact q /\ f continuous_on q /\
     (!x y. x IN q /\ y IN q /\ f x = f y ==> x = y) /\
     compact k /\ k SUBSET q
     ==> interior(IMAGE f k) = IMAGE f (interior k) /\
         frontier(IMAGE f k) = IMAGE f (frontier k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^N->bool`; `f:real^N->real^N`; `IMAGE (f:real^N->real^N) q`]
    HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^N`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3HD_HOMEO_INTERIOR; MATCH_MP_TAC MOI_S3HD_HOMEO_FRONTIER] THEN
  MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `q:real^N->bool`;
                        `IMAGE (f:real^N->real^N) q`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: the model neighbourhood W0 of the open middle square minus       *)
(* the centre, pinched at the centre and away from a closed set ll that     *)
(* meets the middle square only at the centre.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3HD_PHI_CONT = prove
 (`!ll:real^3->bool.
     (\x:real^3. lift(min (min (setdist({x},ll)) (&1 - moi_s35_n x)) (&1 / &16) / &2 -
                      abs(x$3)))
     continuous_on (:real^3)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\x:real^3. lift(moi_s35_n x)) continuous_on (:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_n] THEN MATCH_MP_TAC CONTINUOUS_ON_MAX_1 THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_3; ARITH]] THEN
  SUBGOAL_THEN
   `!x:real^3. lift(min (min (setdist({x},ll)) (&1 - moi_s35_n x)) (&1 / &16) / &2) =
               inv(&2) % lift(min (min (setdist({x},ll)) (&1 - moi_s35_n x)) (&1 / &16))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  MATCH_MP_TAC CONTINUOUS_ON_MIN_1 THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MIN_1 THEN REWRITE_TAC[CONTINUOUS_ON_LIFT_SETDIST] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]);;

let MOI_S3HD_W0 = prove
 (`!ll:real^3->bool.
     closed ll /\ (vec 0) IN ll /\ ll INTER moi_s35_mid = {vec 0}
     ==> ?w0 u. compact w0 /\ w0 SUBSET moi_s35_slab /\
                w0 INTER ll = {vec 0} /\
                w0 INTER frontier moi_s35_slab =
                {x | x IN moi_s35_mid /\ moi_s35_n x = &1} /\
                open u /\ u SUBSET w0 /\ u SUBSET interior moi_s35_cube /\
                ({x | x IN moi_s35_mid /\ moi_s35_n x < &1} DELETE vec 0) SUBSET u`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `phi = \x:real^3.
    min (min (setdist({x},ll)) (&1 - moi_s35_n x)) (&1 / &16) / &2` THEN
  SUBGOAL_THEN `(\x:real^3. lift((phi:real^3->real) x - abs(x$3))) continuous_on (:real^3)`
  ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[MOI_S3HD_PHI_CONT]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. (phi:real^3->real) x <= &1 / &32` (LABEL_TAC "p32") THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN ll ==> (phi:real^3->real) x <= &0` (LABEL_TAC "pll") THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `ll:real^3->bool`] SETDIST_SING_IN_SET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. moi_s35_n x = &1 ==> (phi:real^3->real) x = &0`
  (LABEL_TAC "pn1") THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{x:real^3}`; `ll:real^3->bool`] SETDIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. &0 < setdist({x},ll) /\ moi_s35_n x < &1
                ==> &0 < (phi:real^3->real) x` (LABEL_TAC "ppos") THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real) (vec 0) = &0` (LABEL_TAC "p0") THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `ll:real^3->bool`] SETDIST_SING_IN_SET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[moi_s35_n; VEC_COMPONENT; REAL_ABS_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `{x:real^3 | x IN moi_s35_cube /\ abs(x$3) <= (phi:real^3->real) x}` THEN
  EXISTS_TAC `{x:real^3 | x IN interior moi_s35_cube /\ abs(x$3) < (phi:real^3->real) x}` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      REWRITE_TAC[moi_s35_cube; BOUNDED_INTERVAL] THEN SET_TAC[];
      SUBGOAL_THEN
       `{x:real^3 | x IN moi_s35_cube /\ abs(x$3) <= (phi:real^3->real) x} =
        {x | x IN moi_s35_cube /\
             (\x. lift(phi x - abs(x$3))) x IN {y:real^1 | y$1 >= &0}}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; LIFT_COMPONENT] THEN GEN_TAC THEN
        AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; moi_s35_cube; CLOSED_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "p32" (MP_TAC o SPEC `x:real^3`) THEN
    UNDISCH_TAC `abs((x:real^3)$3) <= (phi:real^3->real) x` THEN REAL_ARITH_TAC;
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3)$3 = &0` ASSUME_TAC THENL
       [USE_THEN "pll" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ll`)) THEN
        UNDISCH_TAC `abs((x:real^3)$3) <= (phi:real^3->real) x` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN moi_s35_mid` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN moi_s35_cube` THEN
        ASM_REWRITE_TAC[MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN SIMP_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `ll INTER moi_s35_mid = {vec 0:real^3}` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN UNDISCH_TAC `(x:real^3) IN ll` THEN
      SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MOI_S3HD_CUBE_IN; VEC_COMPONENT] THEN REAL_ARITH_TAC];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; MOI_S3HD_INTERIORS; MOI_S3HD_SETS_IN;
                MOI_S3HD_CUBE_IN] THEN
    USE_THEN "p32" (MP_TAC o SPEC `x:real^3`) THEN
    USE_THEN "pn1" (MP_TAC o SPEC `x:real^3`) THEN
    REWRITE_TAC[moi_s35_n] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN
     `{x:real^3 | x IN interior moi_s35_cube /\ abs(x$3) < (phi:real^3->real) x} =
      {x | x IN interior moi_s35_cube /\
           (\x. lift(phi x - abs(x$3))) x IN {y:real^1 | y$1 > &0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; LIFT_COMPONENT] THEN GEN_TAC THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_INTERIOR] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    MP_TAC(ISPEC `moi_s35_cube` INTERIOR_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DELETE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~((x:real^3) IN ll)` ASSUME_TAC THENL
     [UNDISCH_TAC `ll INTER moi_s35_mid = {vec 0:real^3}` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN UNDISCH_TAC `~(x:real^3 = vec 0)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < setdist({x:real^3},ll)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ ~(a = &0) ==> &0 < a`) THEN
      REWRITE_TAC[SETDIST_POS_LE] THEN ASM_SIMP_TAC[SETDIST_EQ_0_CLOSED] THEN
      UNDISCH_TAC `(vec 0:real^3) IN ll` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "ppos" (MP_TAC o C MATCH_MP (CONJ (ASSUME `&0 < setdist({x:real^3},ll)`)
      (ASSUME `moi_s35_n (x:real^3) < &1`))) THEN
    UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN
    UNDISCH_TAC `moi_s35_n (x:real^3) < &1` THEN
    REWRITE_TAC[MOI_S3HD_SETS_IN; MOI_S3HD_INTERIORS; moi_s35_n] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: the slab facts for one edge chart (core of SLAB_W), stated       *)
(* for abstract cells ca, cb with ca UNION cb = ps(cube), the frontier fr   *)
(* of the tube (disjoint from the interior of ca UNION cb) and the graph.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3HD_IMAGE_INTER = prove
 (`!(f:A->B) s t u.
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\ s SUBSET u /\ t SUBSET u
     ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`,
  SET_TAC[]);;

let MOI_S3HD_SLAB_BASIC = prove
 (`!(ps:real^3->real^3) q ca cb fr (a:real^3) b.
     pl_homeomorphism (moi_s35_cube,ca UNION cb) (ps,q) /\
     IMAGE ps moi_s35_lower = ca /\ IMAGE ps moi_s35_upper = cb /\
     ps (vec 0) = midpoint(a,b) /\
     IMAGE ps {x | x IN moi_s35_slab /\ moi_s35_n x = &1} SUBSET fr /\
     interior(ca UNION cb) INTER fr = {}
     ==> ca INTER cb = IMAGE ps moi_s35_mid /\
         ca INTER cb INTER fr = IMAGE ps {x | x IN moi_s35_mid /\ moi_s35_n x = &1} /\
         (ca INTER cb) DIFF (ca INTER cb INTER fr) =
         IMAGE ps {x | x IN moi_s35_mid /\ moi_s35_n x < &1} /\
         frontier (IMAGE ps moi_s35_slab) = IMAGE ps (frontier moi_s35_slab) /\
         (ca INTER cb) INTER frontier (IMAGE ps moi_s32_slab_lo UNION
                                       IMAGE ps moi_s32_slab_hi) =
         ca INTER cb INTER fr /\
         IMAGE ps moi_s32_slab_lo INTER IMAGE ps moi_s32_slab_hi = ca INTER cb /\
         IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi = IMAGE ps moi_s35_slab /\
         midpoint(a,b) IN (ca INTER cb) DIFF (ca INTER cb INTER fr) /\
         ps moi_s32_slo IN IMAGE ps moi_s32_slab_lo DIFF (ca INTER cb) /\
         ps moi_s32_shi IN IMAGE ps moi_s32_slab_hi DIFF (ca INTER cb) /\
         pl_ball 3 (IMAGE ps moi_s32_slab_lo) /\ pl_ball 3 (IMAGE ps moi_s32_slab_hi) /\
         pl_ball 3 (IMAGE ps moi_s35_slab)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    aconv (concl th) `homeomorphism (moi_s35_cube,ca UNION cb) (ps:real^3->real^3,q)`)) THEN
  SUBGOAL_THEN `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                      (ps:real^3->real^3) x = ps y ==> x = y` (LABEL_TAC "inj") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC MOI_S3HD_BOX_BALLS THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_mid SUBSET moi_s35_cube` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ca INTER cb = IMAGE (ps:real^3->real^3) moi_s35_mid` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if aconv (concl th)
      `moi_s35_lower INTER moi_s35_upper = moi_s35_mid` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s35_lower`; `moi_s35_upper`; `moi_s35_cube`]
      MOI_S3HD_IMAGE_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_mid ==> moi_s35_n x <= &1` (LABEL_TAC "nle") THENL
   [REWRITE_TAC[MOI_S3HD_SETS_IN; moi_s35_n] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_mid /\ moi_s35_n x < &1
                ==> x IN interior moi_s35_cube` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3HD_SETS_IN; MOI_S3HD_INTERIORS; moi_s35_n] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `interior(ca UNION cb) = IMAGE (ps:real^3->real^3) (interior moi_s35_cube)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if aconv (concl th)
      `IMAGE (ps:real^3->real^3) moi_s35_cube = ca UNION cb` then SUBST1_TAC(SYM th)
      else NO_TAC) THEN
    MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s35_cube`; `moi_s35_cube`] MOI_S3HD_EMBED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ca INTER cb INTER fr =
                IMAGE (ps:real^3->real^3) {x | x IN moi_s35_mid /\ moi_s35_n x = &1}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN IMAGE (ps:real^3->real^3) moi_s35_mid` MP_TAC THENL
       [UNDISCH_TAC `ca INTER cb = IMAGE (ps:real^3->real^3) moi_s35_mid` THEN
        UNDISCH_TAC `(y:real^3) IN ca` THEN UNDISCH_TAC `(y:real^3) IN cb` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `moi_s35_n (x:real^3) < &1` THENL
       [SUBGOAL_THEN `(ps:real^3->real^3) x IN IMAGE ps (interior moi_s35_cube)` MP_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `interior(ca UNION cb) INTER fr = {}:real^3->bool` THEN
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
        USE_THEN "nle" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN moi_s35_mid`)) THEN
        UNDISCH_TAC `~(moi_s35_n (x:real^3) < &1)` THEN REAL_ARITH_TAC];
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(ps:real^3->real^3) x IN fr` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
          `IMAGE (ps:real^3->real^3) {x | x IN moi_s35_slab /\ moi_s35_n x = &1} SUBSET fr`)) THEN
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `moi_s35_mid SUBSET moi_s35_slab` THEN
        UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `ca INTER cb = IMAGE (ps:real^3->real^3) moi_s35_mid` THEN
      UNDISCH_TAC `(ps:real^3->real^3) x IN fr` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s35_mid` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (IMAGE (ps:real^3->real^3) moi_s35_slab) =
                IMAGE ps (frontier moi_s35_slab)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s35_cube`; `moi_s35_slab`] MOI_S3HD_EMBED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi =
                IMAGE ps moi_s35_slab` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM IMAGE_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. k SUBSET moi_s35_cube /\ polytope k /\ pl_ball 3 k
                    ==> pl_ball 3 (IMAGE (ps:real^3->real^3) k)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_BALL_PL_HOMEOMORPHIC THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `ps:real^3->real^3`; `q:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_PL_HOMEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_s35_cube`; `ca UNION cb:real^3->bool`] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope moi_s35_slab /\ polytope moi_s32_slab_lo /\ polytope moi_s32_slab_hi`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOI_S3HD_BOXES; POLYTOPE_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s32_slab_lo SUBSET moi_s35_cube /\ moi_s32_slab_hi SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:real^3 | x IN moi_s35_mid /\ moi_s35_n x < &1} =
                  moi_s35_mid DIFF {x | x IN moi_s35_mid /\ moi_s35_n x = &1}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
      ASM_CASES_TAC `(x:real^3) IN moi_s35_mid` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "nle" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN moi_s35_mid`)) THEN
      REAL_ARITH_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s35_mid`; `frontier moi_s35_slab`;
                   `moi_s35_cube`] MOI_S3HD_IMAGE_INTER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "inj" ACCEPT_TAC;
        ASM_REWRITE_TAC[];
        MP_TAC(ISPEC `moi_s35_slab` FRONTIER_SUBSET_CLOSED) THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
        UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN SET_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; MOI_S3HD_INTERIORS; MOI_S3HD_SETS_IN; moi_s35_n] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s32_slab_lo`; `moi_s32_slab_hi`;
                   `moi_s35_cube`] MOI_S3HD_IMAGE_INTER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [USE_THEN "inj" ACCEPT_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(ca INTER cb) DIFF (ca INTER cb INTER fr) =
                  IMAGE (ps:real^3->real^3) {x | x IN moi_s35_mid /\ moi_s35_n x < &1}`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `{x:real^3 | x IN moi_s35_mid /\ moi_s35_n x < &1} =
                    moi_s35_mid DIFF {x | x IN moi_s35_mid /\ moi_s35_n x = &1}` SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
        REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
        ASM_CASES_TAC `(x:real^3) IN moi_s35_mid` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "nle" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN moi_s35_mid`)) THEN
        REAL_ARITH_TAC;
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `vec 0:real^3` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s35_n; VEC_COMPONENT; REAL_ABS_0] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_s32_slo = (z:real^3)` (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_s32_shi = (z:real^3)` (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: the pinched closed neighbourhood W for one edge chart.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3HD_SLAB_WSET = prove
 (`!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
    (ps:real^3->real^3) q ca cb fr (a:real^3) b.
     pl_homeomorphism (moi_s35_cube,ca UNION cb) (ps,q) /\
     IMAGE ps moi_s35_lower = ca /\ IMAGE ps moi_s35_upper = cb /\
     ps (vec 0) = midpoint(a,b) /\
     IMAGE ps {x | x IN moi_s35_slab /\ moi_s35_n x = &1} SUBSET fr /\
     interior(ca UNION cb) INTER fr = {} /\
     ca UNION cb SUBSET UNIONS t /\
     h continuous_on UNIONS t /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
     closed (UNIONS l) /\ UNIONS l SUBSET UNIONS t /\
     midpoint(a,b) IN UNIONS l /\
     (ca INTER cb) INTER UNIONS l = {midpoint(a,b)}
     ==> ?w. closed w /\
             w SUBSET IMAGE h (IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi) /\
             (IMAGE h ((ca INTER cb) DIFF (ca INTER cb INTER fr)) DELETE h(midpoint(a,b)))
             SUBSET interior w /\
             w INTER frontier (IMAGE h (IMAGE ps moi_s32_slab_lo UNION
                                        IMAGE ps moi_s32_slab_hi)) =
             IMAGE h (ca INTER cb INTER fr) /\
             w INTER IMAGE h (UNIONS l) = {h(midpoint(a,b))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ps:real^3->real^3`; `q:real^3->real^3`; `ca:real^3->bool`;
                 `cb:real^3->bool`; `fr:real^3->bool`; `a:real^3`; `b:real^3`]
    MOI_S3HD_SLAB_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    aconv (concl th) `pl_homeomorphism (moi_s35_cube,ca UNION cb) (ps:real^3->real^3,q)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    aconv (concl th) `homeomorphism (moi_s35_cube,ca UNION cb) (ps:real^3->real^3,q)`)) THEN
  SUBGOAL_THEN `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                      (ps:real^3->real^3) x = ps y ==> x = y` (LABEL_TAC "inj") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC MOI_S3HD_BOX_BALLS THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_mid SUBSET moi_s35_cube` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `ll = {x:real^3 | x IN moi_s35_cube /\ (ps:real^3->real^3) x IN UNIONS l}` THEN
  SUBGOAL_THEN `closed (ll:real^3->bool) /\ (vec 0:real^3) IN ll /\
                ll INTER moi_s35_mid = {vec 0}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "ll" THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_REWRITE_TAC[moi_s35_cube; CLOSED_INTERVAL] THEN
      ASM_REWRITE_TAC[GSYM moi_s35_cube];
      EXPAND_TAC "ll" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      EXPAND_TAC "ll" THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
       [STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(ps:real^3->real^3) x IN (ca INTER cb) INTER UNIONS l` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[IN_SING];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `ll:real^3->bool` MOI_S3HD_W0) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^3->bool` (X_CHOOSE_THEN `u:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_cube SUBSET UNIONS t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^3->real^3) o (ps:real^3->real^3)) continuous_on moi_s35_cube`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                      ((h:real^3->real^3) o (ps:real^3->real^3)) x = (h o ps) y ==> x = y`
  (LABEL_TAC "finj") THENL
   [REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> aconv (concl th)
      `!x y. x IN UNIONS t /\ y IN UNIONS t /\ (h:real^3->real^3) x = h y ==> x = y`)) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w0:real^3->bool) SUBSET moi_s35_cube` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) w0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[];
    REPEAT(MATCH_MP_TAC IMAGE_SUBSET) THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
      `(ps:real^3->real^3) (vec 0) = midpoint(a,b)`)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((h:real^3->real^3) o (ps:real^3->real^3)) u` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DELETE; IN_IMAGE; o_THM; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
        `({x | x IN moi_s35_mid /\ moi_s35_n x < &1} DELETE vec 0) SUBSET (u:real^3->bool)`)) THEN
      ASM_REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(y:real^3 = h ((ps:real^3->real^3) (vec 0)))` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[IMAGE_o] THEN REPEAT(MATCH_MP_TAC IMAGE_SUBSET) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
          ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
          REPEAT STRIP_TAC THEN USE_THEN "finj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM SET_TAC[]]]];
    MP_TAC(ISPECL [`(h:real^3->real^3) o (ps:real^3->real^3)`; `moi_s35_cube`;
                   `moi_s35_slab`] MOI_S3HD_EMBED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "finj" ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MP_TAC(ISPECL [`(h:real^3->real^3) o (ps:real^3->real^3)`; `w0:real^3->bool`;
                   `frontier moi_s35_slab`; `moi_s35_cube`] MOI_S3HD_IMAGE_INTER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "finj" ACCEPT_TAC;
        ASM_REWRITE_TAC[];
        MP_TAC(ISPEC `moi_s35_slab` FRONTIER_SUBSET_CLOSED) THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
        UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN SET_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[IMAGE_o];
    SUBGOAL_THEN `IMAGE (ps:real^3->real^3) w0 INTER UNIONS l = {midpoint(a,b)}`
    ASSUME_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
      REWRITE_TAC[IN_INTER; IN_IMAGE; IN_SING] THEN EQ_TAC THENL
       [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
          ASSUME_TAC) THEN
        SUBGOAL_THEN `(x:real^3) IN w0 INTER ll` MP_TAC THENL
         [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "ll" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
          ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `vec 0:real^3` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^3->real^3`; `IMAGE (ps:real^3->real^3) w0`;
                   `UNIONS l:real^3->bool`; `UNIONS t:real^3->bool`] MOI_S3HD_IMAGE_INTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (ps:real^3->real^3) moi_s35_cube SUBSET UNIONS t` THEN
      UNDISCH_TAC `(w0:real^3->bool) SUBSET moi_s35_cube` THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IMAGE_CLAUSES]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: the theorem SLAB_W.                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3HD_SLAB_ALL = prove
 (`!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
    (ps:real^3->real^3) ca cb fr (a:real^3) b.
     (?q. pl_homeomorphism (moi_s35_cube,ca UNION cb) (ps,q)) /\
     IMAGE ps moi_s35_lower = ca /\ IMAGE ps moi_s35_upper = cb /\
     ps (vec 0) = midpoint(a,b) /\
     IMAGE ps {x | x IN moi_s35_slab /\ moi_s35_n x = &1} SUBSET fr /\
     interior(ca UNION cb) INTER fr = {} /\
     ca UNION cb SUBSET UNIONS t /\
     h continuous_on UNIONS t /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
     closed (UNIONS l) /\ UNIONS l SUBSET UNIONS t /\
     midpoint(a,b) IN UNIONS l /\
     (ca INTER cb) INTER UNIONS l = {midpoint(a,b)}
     ==> pl_ball 3 (IMAGE ps moi_s32_slab_lo) /\
         pl_ball 3 (IMAGE ps moi_s32_slab_hi) /\
         pl_ball 3 (IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi) /\
         IMAGE ps moi_s32_slab_lo INTER IMAGE ps moi_s32_slab_hi = ca INTER cb /\
         (ca INTER cb) INTER frontier (IMAGE ps moi_s32_slab_lo UNION
                                       IMAGE ps moi_s32_slab_hi) =
         ca INTER cb INTER fr /\
         midpoint(a,b) IN (ca INTER cb) DIFF (ca INTER cb INTER fr) /\
         ps moi_s32_slo IN IMAGE ps moi_s32_slab_lo DIFF (ca INTER cb) /\
         ps moi_s32_shi IN IMAGE ps moi_s32_slab_hi DIFF (ca INTER cb) /\
         IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi SUBSET UNIONS t /\
         ?w. closed w /\
             w SUBSET IMAGE h (IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi) /\
             (IMAGE h ((ca INTER cb) DIFF (ca INTER cb INTER fr)) DELETE h(midpoint(a,b)))
             SUBSET interior w /\
             w INTER frontier (IMAGE h (IMAGE ps moi_s32_slab_lo UNION
                                        IMAGE ps moi_s32_slab_hi)) =
             IMAGE h (ca INTER cb INTER fr) /\
             w INTER IMAGE h (UNIONS l) = {h(midpoint(a,b))}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^3->real^3`) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ps:real^3->real^3`; `q:real^3->real^3`; `ca:real^3->bool`;
                 `cb:real^3->bool`; `fr:real^3->bool`; `a:real^3`; `b:real^3`]
    MOI_S3HD_SLAB_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `ps:real^3->real^3`; `q:real^3->real^3`; `ca:real^3->bool`;
                 `cb:real^3->bool`; `fr:real^3->bool`; `a:real^3`; `b:real^3`]
    MOI_S3HD_SLAB_WSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_cube = ca UNION cb` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [FIRST_X_ASSUM(fun th -> if aconv (concl th)
      `IMAGE (ps:real^3->real^3) moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi =
       IMAGE ps moi_s35_slab` then SUBST1_TAC th else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(fun th -> if aconv (concl th)
      `IMAGE (ps:real^3->real^3) moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi =
       IMAGE ps moi_s35_slab` then SUBST1_TAC th else NO_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ca UNION cb:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if aconv (concl th)
      `IMAGE (ps:real^3->real^3) moi_s35_cube = ca UNION cb` then SUBST1_TAC(SYM th)
      else NO_TAC) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[MOI_S3HD_BOX_BALLS]]);;

let SLAB_W = prove
 (MOI_S32_SLAB_W,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tube") (CONJUNCTS_THEN2 (LABEL_TAC "fr3") (K ALL_TAC))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e:real^3->bool` o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s35_charts]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(e:real^3->bool) IN l` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s35_edge]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:(real^3->bool)->bool) SUBSET t /\ lf_simplicial_complex t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[graph_in_complex; simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  USE_THEN "tube" (MP_TAC o C MATCH_MP
    (ASSUME `graph_in_complex (t:(real^3->bool)->bool) l`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tv")
    (CONJUNCTS_THEN2 (LABEL_TAC "te") (K ALL_TAC)))) THEN
  USE_THEN "fr3" (MP_TAC o C MATCH_MP
    (CONJ (ASSUME `graph_in_complex (t:(real^3->bool)->bool) l`)
          (ASSUME `FINITE (l:(real^3->bool)->bool)`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `segment[(av:(real^3->bool)->real^3) e,bv e] IN l` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3HD_SLAB_ALL THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [EXISTS_TAC `q:real^3->real^3` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `derived_dual_cell t l ((av:(real^3->bool)->real^3) e) UNION
                  derived_dual_cell t l (bv e) SUBSET derived_nbhd t l` MP_TAC THENL
     [FIRST_ASSUM(fun th -> if aconv (concl th)
        `derived_nbhd t l =
         UNIONS {derived_dual_cell t l v | v | {v} IN (l:(real^3->bool)->bool)}`
        then ONCE_REWRITE_TAC[th] else NO_TAC) THEN
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
      MATCH_MP_TAC(SET_RULE `(s:real^3->bool) IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
    FIRST_ASSUM(fun th -> if aconv (concl th)
      `frontier (derived_nbhd t l) = derived_frontier (t:(real^3->bool)->bool) l`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [USE_THEN "tv" (MP_TAC o CONJUNCT1 o C MATCH_MP
        (ASSUME `{(av:(real^3->bool)->real^3) e} IN l`)) THEN SET_TAC[];
      USE_THEN "tv" (MP_TAC o CONJUNCT1 o C MATCH_MP
        (ASSUME `{(bv:(real^3->bool)->real^3) e} IN l`)) THEN SET_TAC[]];
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `lf_simplicial_complex (t:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(l:(real^3->bool)->bool) SUBSET t` THEN
      UNDISCH_TAC `(s:real^3->bool) IN l` THEN SET_TAC[];
      MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_CLOSED]];
    UNDISCH_TAC `(l:(real^3->bool)->bool) SUBSET t` THEN SET_TAC[];
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(av:(real^3->bool)->real^3) e`; `(bv:(real^3->bool)->real^3) e`]
      (CONJUNCT1 MIDPOINT_IN_SEGMENT)) THEN ASM_REWRITE_TAC[];
    USE_THEN "te" (MP_TAC o CONJUNCT2 o C MATCH_MP
      (CONJ (ASSUME `~((av:(real^3->bool)->real^3) e = bv e)`)
            (ASSUME `segment[(av:(real^3->bool)->real^3) e,bv e] IN l`))) THEN
    REWRITE_TAC[INTER_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: a cell minus disjoint boundary collars stays connected.           *)
(* The collars are images of the lower half slab under charts of the lower  *)
(* half cube onto the cell; one collar is removed by the retraction that     *)
(* pushes a thin layer below it onto its lower face.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3HD_LOWER_EQ = prove
 (`moi_s35_lower = interval[vector[-- &1; -- &1; -- &1], vector[&1; &1; &0]] /\
   moi_s35_upper = interval[vector[-- &1; -- &1; &0], vector[&1; &1; &1]]`,
  REWRITE_TAC[EXTENSION; MOI_S3HD_SETS_IN; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3HD_LOWER_FACTS = prove
 (`compact moi_s35_lower /\ moi_s32_slab_lo SUBSET moi_s35_lower /\
   compact moi_s35_upper /\ moi_s32_slab_hi SUBSET moi_s35_upper /\
   moi_s35_lower SUBSET moi_s35_cube /\ moi_s35_upper SUBSET moi_s35_cube`,
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MOI_S3HD_LOWER_EQ; COMPACT_INTERVAL] THEN NO_TAC) THEN
  REWRITE_TAC[SUBSET; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN REAL_ARITH_TAC);;

let MOI_S3HD_COLLAR_DELTA = prove
 (`!(ps:real^3->real^3) a.
     ps continuous_on moi_s35_lower /\ compact a /\
     DISJOINT a (IMAGE ps moi_s32_slab_lo)
     ==> ?dl. &0 < dl /\ dl <= &1 / &2 /\
              !y. y IN moi_s35_cube /\ --(&1 / &8) - dl <= y$3 /\ y$3 <= --(&1 / &8)
                  ==> ~(ps y IN a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC MOI_S3HD_LOWER_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (ps:real^3->real^3) moi_s32_slab_lo`; `a:real^3->bool`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_S3HD_BOX_BALLS] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_lower` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `DISJOINT a (IMAGE (ps:real^3->real^3) moi_s32_slab_lo)` THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s35_lower`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (eta / &2) (&1 / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `y' = (y:real^3) + (--(&1 / &8) - y$3) % basis 3` THEN
  SUBGOAL_THEN `(y':real^3)$1 = (y:real^3)$1 /\ y'$2 = y$2 /\ y'$3 = --(&1 / &8)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y'" THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3;
             ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y':real^3) IN moi_s32_slab_lo /\ (y:real^3) IN moi_s35_lower /\
                dist(y',y) < eta` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN moi_s35_cube` THEN
    ASM_REWRITE_TAC[MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    EXPAND_TAC "y'" THEN
    REWRITE_TAC[dist; VECTOR_ARITH `(y + c % b) - y = c % b:real^3`] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= dist((ps:real^3->real^3) y',ps y)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x < d ==> d <= x ==> F`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s32_slab_lo SUBSET moi_s35_lower` THEN
  UNDISCH_TAC `(y':real^3) IN moi_s32_slab_lo` THEN SET_TAC[]);;

let MOI_S3HD_COLLAR_STEP = prove
 (`!(ps:real^3->real^3) c a.
     ps continuous_on moi_s35_lower /\
     (!x y. x IN moi_s35_lower /\ y IN moi_s35_lower /\ ps x = ps y ==> x = y) /\
     IMAGE ps moi_s35_lower = c /\
     connected (c DIFF a) /\ compact a /\ DISJOINT a (IMAGE ps moi_s32_slab_lo)
     ==> connected ((c DIFF a) DIFF IMAGE ps moi_s32_slab_lo) /\
         IMAGE ps {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} SUBSET
         closure ((c DIFF a) DIFF IMAGE ps moi_s32_slab_lo)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S3HD_LOWER_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s35_lower`; `ps:real^3->real^3`; `c:real^3->bool`]
    HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ps:real^3->real^3`; `a:real^3->bool`] MOI_S3HD_COLLAR_DELTA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rr = \y:real^3. y - max (&0) (y$3 + &1 / &8 + dl) % basis 3` THEN
  SUBGOAL_THEN `!y:real^3. ((rr:real^3->real^3) y)$1 = y$1 /\ (rr y)$2 = y$2 /\
                           (rr y)$3 = min (y$3) (--(&1 / &8) - dl)` (LABEL_TAC "rrc") THENL
   [EXPAND_TAC "rr" THEN GEN_TAC THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3;
             ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(rr:real^3->real^3) continuous_on (:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MAX_1 THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[LIFT_ADD] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC) THEN
    SIMP_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN moi_s35_lower ==> (rr:real^3->real^3) y IN moi_s35_lower`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MOI_S3HD_SETS_IN] THEN
    USE_THEN "rrc" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `dl <= &1 / &2` THEN UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y$3 <= --(&1 / &8) - dl ==> (rr:real^3->real^3) y = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `max (&0) ((y:real^3)$3 + &1 / &8 + dl) = &0` SUBST1_TAC THENL
     [UNDISCH_TAC `(y:real^3)$3 <= --(&1 / &8) - dl` THEN REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN moi_s35_lower /\ ~(y IN moi_s32_slab_lo) ==> y$3 < --(&1 / &8)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3HD_SETS_IN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN moi_s32_slab_lo ==> --(&1 / &8) <= y$3`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3HD_SETS_IN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = (ps:real^3->real^3) o (rr:real^3->real^3) o (g:real^3->real^3)` THEN
  SUBGOAL_THEN `(r:real^3->real^3) continuous_on (c DIFF a)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `c:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_lower` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_DIFF] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) c = moi_s35_lower` THEN
      UNDISCH_TAC `(z:real^3) IN c` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN moi_s35_cube /\ --(&1 / &8) - dl <= y$3 /\
                           y$3 <= --(&1 / &8) ==> ~((ps:real^3->real^3) y IN a)`
  (LABEL_TAC "dlt") THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (r:real^3->real^3) (c DIFF a) SUBSET
                (c DIFF a) DIFF IMAGE (ps:real^3->real^3) moi_s32_slab_lo` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    EXPAND_TAC "r" THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(g:real^3->real^3) z IN moi_s35_lower` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^3) c = moi_s35_lower` THEN
      UNDISCH_TAC `(z:real^3) IN c` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `((g:real^3->real^3) z)$3 <= --(&1 / &8) - dl` THENL
     [SUBGOAL_THEN `(rr:real^3->real^3) ((g:real^3->real^3) z) = g z` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(ps:real^3->real^3) ((g:real^3->real^3) z) = z` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `--(&1 / &8) <= ((g:real^3->real^3) z)$3` MP_TAC THENL
       [SUBGOAL_THEN `(g:real^3->real^3) z = x` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            aconv (concl th)
            `!x:real^3. x IN moi_s35_lower ==> (g:real^3->real^3) (ps x) = x`)) THEN
          UNDISCH_TAC `moi_s32_slab_lo SUBSET moi_s35_lower` THEN
          UNDISCH_TAC `(x:real^3) IN moi_s32_slab_lo` THEN SET_TAC[];
          ASM_SIMP_TAC[]];
        UNDISCH_TAC `((g:real^3->real^3) z)$3 <= --(&1 / &8) - dl` THEN
        UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `((rr:real^3->real^3) ((g:real^3->real^3) z))$3 = --(&1 / &8) - dl`
      ASSUME_TAC THENL
       [USE_THEN "rrc" (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `~(((g:real^3->real^3) z)$3 <= --(&1 / &8) - dl)` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(rr:real^3->real^3) ((g:real^3->real^3) z) IN moi_s35_lower`
      ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (ps:real^3->real^3) moi_s35_lower = c` THEN
        UNDISCH_TAC `(rr:real^3->real^3) ((g:real^3->real^3) z) IN moi_s35_lower` THEN
        SET_TAC[];
        USE_THEN "dlt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
         [UNDISCH_TAC `moi_s35_lower SUBSET moi_s35_cube` THEN
          UNDISCH_TAC `(rr:real^3->real^3) ((g:real^3->real^3) z) IN moi_s35_lower` THEN
          SET_TAC[];
          UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC];
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(rr:real^3->real^3) ((g:real^3->real^3) z) = x` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> aconv (concl th)
            `!x y. x IN moi_s35_lower /\ y IN moi_s35_lower /\
                   (ps:real^3->real^3) x = ps y ==> x = y`)) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `moi_s32_slab_lo SUBSET moi_s35_lower` THEN
          UNDISCH_TAC `(x:real^3) IN moi_s32_slab_lo` THEN SET_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `--(&1 / &8) <= (x:real^3)$3` MP_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(x:real^3)$3 = --(&1 / &8) - dl` MP_TAC THENL
         [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
            `(rr:real^3->real^3) ((g:real^3->real^3) z) = x`)) THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `lay = {y:real^3 | y IN moi_s35_cube /\ --(&1 / &8) - dl <= y$3 /\
                                y$3 < --(&1 / &8)}` THEN
  SUBGOAL_THEN `(lay:real^3->bool) SUBSET moi_s35_lower /\ connected lay`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "lay" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONVEX_CONNECTED THEN EXPAND_TAC "lay" THEN
      SUBGOAL_THEN
       `{y:real^3 | y IN moi_s35_cube /\ --(&1 / &8) - dl <= y$3 /\ y$3 < --(&1 / &8)} =
        moi_s35_cube INTER ({y | y$3 >= --(&1 / &8) - dl} INTER {y | y$3 < --(&1 / &8)})`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_ge]; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[moi_s35_cube; CONVEX_INTERVAL; CONVEX_HALFSPACE_COMPONENT_GE;
                  CONVEX_HALFSPACE_COMPONENT_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) lay SUBSET
                (c DIFF a) DIFF IMAGE ps moi_s32_slab_lo` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s35_lower /\ y IN moi_s35_cube /\
                  --(&1 / &8) - dl <= y$3 /\ y$3 < --(&1 / &8)` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN moi_s35_lower` ASSUME_TAC THENL
       [UNDISCH_TAC `(lay:real^3->bool) SUBSET moi_s35_lower` THEN
        UNDISCH_TAC `(y:real^3) IN lay` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN lay` THEN EXPAND_TAC "lay" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (ps:real^3->real^3) moi_s35_lower = c` THEN
      UNDISCH_TAC `(y:real^3) IN moi_s35_lower` THEN SET_TAC[];
      USE_THEN "dlt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3)$3 < --(&1 / &8)` THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^3) = x` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> aconv (concl th)
          `!x y. x IN moi_s35_lower /\ y IN moi_s35_lower /\
                 (ps:real^3->real^3) x = ps y ==> x = y`)) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `moi_s32_slab_lo SUBSET moi_s35_lower` THEN
        UNDISCH_TAC `(x:real^3) IN moi_s32_slab_lo` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `--(&1 / &8) <= (x:real^3)$3` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3)$3 < --(&1 / &8)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `y0:real^3 = vector[&0; &0; --(&1 / &8) - dl]` THEN
  SUBGOAL_THEN `(y0:real^3) IN lay /\ y0 IN moi_s35_lower /\ y0$3 <= --(&1 / &8) - dl`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN EXPAND_TAC "lay" THEN
    REWRITE_TAC[IN_ELIM_THM; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN; VECTOR_3] THEN
    UNDISCH_TAC `dl <= &1 / &2` THEN UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c DIFF a) DIFF IMAGE (ps:real^3->real^3) moi_s32_slab_lo =
                IMAGE (r:real^3->real^3) (c DIFF a) UNION IMAGE ps lay` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[UNION_SUBSET]] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^3) z IN moi_s35_lower /\ (ps:real^3->real^3) (g z) = z`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (g:real^3->real^3) c = moi_s35_lower` THEN
        UNDISCH_TAC `(z:real^3) IN c` THEN SET_TAC[];
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((g:real^3->real^3) z IN moi_s32_slab_lo)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((z:real^3) IN IMAGE (ps:real^3->real^3) moi_s32_slab_lo)` THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^3->real^3) z` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `((g:real^3->real^3) z)$3 <= --(&1 / &8) - dl` THENL
     [DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN EXPAND_TAC "r" THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(rr:real^3->real^3) ((g:real^3->real^3) z) = g z` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
      DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^3->real^3) z` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "lay" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `moi_s35_lower SUBSET moi_s35_cube` THEN
        UNDISCH_TAC `(g:real^3->real^3) z IN moi_s35_lower` THEN SET_TAC[];
        UNDISCH_TAC `~(((g:real^3->real^3) z)$3 <= --(&1 / &8) - dl)` THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> aconv (concl th)
          `!y:real^3. y IN moi_s35_lower /\ ~(y IN moi_s32_slab_lo) ==> y$3 < --(&1 / &8)`)) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_lower` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(ps:real^3->real^3) y0` THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(ps:real^3->real^3) y0` THEN CONJ_TAC THENL
         [EXPAND_TAC "r" THEN REWRITE_TAC[o_THM] THEN
          SUBGOAL_THEN `(g:real^3->real^3) (ps y0) = y0` SUBST1_TAC THENL
           [ASM_SIMP_TAC[]; ALL_TAC] THEN
          SUBGOAL_THEN `(rr:real^3->real^3) y0 = y0` SUBST1_TAC THENL
           [ASM_SIMP_TAC[]; REWRITE_TAC[]];
          UNDISCH_TAC `IMAGE (ps:real^3->real^3) lay SUBSET
                       (c DIFF a) DIFF IMAGE ps moi_s32_slab_lo` THEN
          UNDISCH_TAC `(y0:real^3) IN lay` THEN SET_TAC[]];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(IMAGE (ps:real^3->real^3) lay)` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
  STRIP_TAC THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN moi_s35_lower` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_slab_lo SUBSET moi_s35_lower` THEN
    UNDISCH_TAC `(x:real^3) IN moi_s32_slab_lo` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^3` o GEN_REWRITE_RULE I [continuous_on] o check (fun th ->
    aconv (concl th) `(ps:real^3->real^3) continuous_on moi_s35_lower`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `ep:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `tt = min (k / &2) (dl / &2)` THEN
  SUBGOAL_THEN `&0 < tt /\ tt < k /\ tt < dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN UNDISCH_TAC `&0 < k` THEN UNDISCH_TAC `&0 < dl` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x' = (x:real^3) - tt % basis 3` THEN
  SUBGOAL_THEN `(x':real^3) IN lay /\ dist(x',x) < k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "x'" THEN EXPAND_TAC "lay" THEN
      UNDISCH_TAC `(x:real^3) IN moi_s32_slab_lo` THEN
      REWRITE_TAC[IN_ELIM_THM; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN
      SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3;
               ARITH] THEN
      UNDISCH_TAC `(x:real^3)$3 = --(&1 / &8)` THEN
      UNDISCH_TAC `&0 < tt` THEN UNDISCH_TAC `tt < dl` THEN UNDISCH_TAC `dl <= &1 / &2` THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "x'" THEN
      REWRITE_TAC[dist; VECTOR_ARITH `(x - t % b) - x = --(t % b):real^3`] THEN
      REWRITE_TAC[NORM_NEG; NORM_MUL] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
      UNDISCH_TAC `&0 < tt` THEN UNDISCH_TAC `tt < k` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(ps:real^3->real^3) x'` THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(lay:real^3->bool) SUBSET moi_s35_lower` THEN
    UNDISCH_TAC `(x':real^3) IN lay` THEN SET_TAC[]]);;

let MOI_S3HD_COLLARS = prove
 (`!(ps:(real^3->bool)->real^3->real^3) c.
     connected c
     ==> !ee. FINITE ee
              ==> (!e. e IN ee
                       ==> ps e continuous_on moi_s35_lower /\
                           (!x y. x IN moi_s35_lower /\ y IN moi_s35_lower /\
                                  ps e x = ps e y ==> x = y) /\
                           IMAGE (ps e) moi_s35_lower = c) /\
                  (!e e'. e IN ee /\ e' IN ee /\ ~(e = e')
                          ==> DISJOINT (IMAGE (ps e) moi_s32_slab_lo)
                                       (IMAGE (ps e') moi_s32_slab_lo))
                  ==> connected (c DIFF UNIONS {IMAGE (ps e) moi_s32_slab_lo | e IN ee}) /\
                      (!e. e IN ee
                           ==> IMAGE (ps e) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}
                               SUBSET closure (c DIFF UNIONS {IMAGE (ps e) moi_s32_slab_lo |
                                                              e IN ee}))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_0; DIFF_EMPTY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e0:real^3->bool`; `s:(real^3->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ch") (LABEL_TAC "dj")) THEN
  USE_THEN "ih" MP_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
      USE_THEN "ch" (MP_TAC o SPEC `e:real^3->bool`) THEN
      REWRITE_TAC[IN_INSERT] THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))] THEN
  ABBREV_TAC `aa = UNIONS {IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo |
                           e IN s}` THEN
  SUBGOAL_THEN `UNIONS {IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo |
                        e IN e0 INSERT s} = IMAGE (ps e0) moi_s32_slab_lo UNION aa`
  SUBST1_TAC THENL
   [EXPAND_TAC "aa" THEN REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `c DIFF (IMAGE ((ps:(real^3->bool)->real^3->real^3) e0) moi_s32_slab_lo UNION aa) =
                (c DIFF aa) DIFF IMAGE (ps e0) moi_s32_slab_lo` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  USE_THEN "ch" (MP_TAC o SPEC `e0:real^3->bool`) THEN REWRITE_TAC[IN_INSERT] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(ps:(real^3->bool)->real^3->real^3) e0`; `c:real^3->bool`; `aa:real^3->bool`]
    MOI_S3HD_COLLAR_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "aa" THEN MATCH_MP_TAC COMPACT_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_S3HD_BOX_BALLS] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_lower` THEN
      REWRITE_TAC[MOI_S3HD_LOWER_FACTS] THEN
      USE_THEN "ch" (MP_TAC o SPEC `e:real^3->bool`) THEN
      REWRITE_TAC[IN_INSERT] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
      EXPAND_TAC "aa" THEN REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS] THEN
      REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN X_GEN_TAC `e:real^3->bool` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `~((e:real^3->bool) = e0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "dj" (MP_TAC o SPECL [`e:real^3->bool`; `e0:real^3->bool`]) THEN
      REWRITE_TAC[IN_INSERT] THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real^3->bool` THEN REWRITE_TAC[IN_INSERT] THEN
  ASM_CASES_TAC `e:real^3->bool = e0` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `((:real^3) DIFF IMAGE ((ps:(real^3->bool)->real^3->real^3) e0) moi_s32_slab_lo)
              INTER closure (c DIFF aa)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [USE_THEN "dj" (MP_TAC o SPECL [`e:real^3->bool`; `e0:real^3->bool`]) THEN
      REWRITE_TAC[IN_INSERT] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SET_RULE `{x:real^3 | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} SUBSET
                       moi_s32_slab_lo`) THEN
      SET_TAC[];
      USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DIFF IMAGE ((ps:(real^3->bool)->real^3->real^3) e0)
                    moi_s32_slab_lo`; `c DIFF aa:real^3->bool`] OPEN_INTER_CLOSURE_SUBSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_S3HD_BOX_BALLS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_lower` THEN
    ASM_REWRITE_TAC[MOI_S3HD_LOWER_FACTS];
    SUBGOAL_THEN `((:real^3) DIFF IMAGE ((ps:(real^3->bool)->real^3->real^3) e0)
                      moi_s32_slab_lo) INTER (c DIFF aa) =
                  (c DIFF aa) DIFF IMAGE (ps e0) moi_s32_slab_lo`
    (fun th -> REWRITE_TAC[th]) THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 7: the half slabs of an edge chart inside the two cells, their      *)
(* far faces, and the chart of the upper half through the reflection.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3HD_FACES = prove
 (`{x:real^3 | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} SUBSET
   frontier moi_s32_slab_lo INTER frontier moi_s35_slab /\
   {x:real^3 | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} SUBSET
   frontier moi_s32_slab_hi INTER frontier moi_s35_slab /\
   DISJOINT {x:real^3 | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} moi_s35_mid /\
   DISJOINT {x:real^3 | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} moi_s35_mid /\
   ~({x:real^3 | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} = {}) /\
   ~({x:real^3 | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} = {}) /\
   moi_s35_slab INTER moi_s35_lower = moi_s32_slab_lo /\
   moi_s35_slab INTER moi_s35_upper = moi_s32_slab_hi`,
  REWRITE_TAC[MOI_S3HD_BOXES; FRONTIER_CLOSED_INTERVAL] THEN
  REWRITE_TAC[GSYM MOI_S3HD_BOXES] THEN
  REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; IN_DIFF; IN_ELIM_THM; NOT_IN_EMPTY;
              GSYM MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[MOI_S3HD_SETS_IN; MOI_S3HD_BOXES; IN_INTERVAL; DIMINDEX_3; FORALL_3;
              VECTOR_3] THEN
  REPEAT CONJ_TAC THEN TRY (GEN_TAC THEN REAL_ARITH_TAC) THENL
   [EXISTS_TAC `vector[&0; &0; --(&1 / &8)]:real^3`;
    EXISTS_TAC `vector[&0; &0; &1 / &8]:real^3`] THEN
  REWRITE_TAC[VECTOR_3] THEN REAL_ARITH_TAC);;

let MOI_S3HD_EDGE_GEOM = prove
 (`!(ps:real^3->real^3) q ca cb.
     pl_homeomorphism (moi_s35_cube,ca UNION cb) (ps,q) /\
     IMAGE ps moi_s35_lower = ca /\ IMAGE ps moi_s35_upper = cb
     ==> ps continuous_on moi_s35_cube /\
         (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\ ps x = ps y ==> x = y) /\
         IMAGE ps moi_s35_cube = ca UNION cb /\
         IMAGE ps moi_s35_slab INTER ca = IMAGE ps moi_s32_slab_lo /\
         IMAGE ps moi_s35_slab INTER cb = IMAGE ps moi_s32_slab_hi /\
         closure (ca DIFF IMAGE ps moi_s35_slab) INTER IMAGE ps moi_s35_slab SUBSET
         IMAGE ps {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} /\
         closure (cb DIFF IMAGE ps moi_s35_slab) INTER IMAGE ps moi_s35_slab SUBSET
         IMAGE ps {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} /\
         frontier (IMAGE ps moi_s32_slab_lo) = IMAGE ps (frontier moi_s32_slab_lo) /\
         frontier (IMAGE ps moi_s32_slab_hi) = IMAGE ps (frontier moi_s32_slab_hi) /\
         frontier (IMAGE ps moi_s35_slab) = IMAGE ps (frontier moi_s35_slab)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    aconv (concl th) `homeomorphism (moi_s35_cube,ca UNION cb) (ps:real^3->real^3,q)`)) THEN
  SUBGOAL_THEN `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                      (ps:real^3->real^3) x = ps y ==> x = y` (LABEL_TAC "inj") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC MOI_S3HD_BOX_BALLS THEN STRIP_TAC THEN
  MP_TAC MOI_S3HD_LOWER_FACTS THEN STRIP_TAC THEN
  MP_TAC MOI_S3HD_FACES THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. k SUBSET moi_s35_cube /\ compact k
                    ==> frontier (IMAGE (ps:real^3->real^3) k) = IMAGE ps (frontier k)`
  (LABEL_TAC "fr") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s35_cube`; `k:real^3->bool`] MOI_S3HD_EMBED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "inj" ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s k. s SUBSET k /\ closed k /\ k SUBSET moi_s35_cube
                      ==> closure (IMAGE (ps:real^3->real^3) s) SUBSET IMAGE ps k`
  (LABEL_TAC "clim") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `moi_s35_cube` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    USE_THEN "inj" ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(fun th -> if aconv (concl th)
      `IMAGE (ps:real^3->real^3) moi_s35_lower = ca` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s35_slab`; `moi_s35_lower`; `moi_s35_cube`]
      MOI_S3HD_IMAGE_INTER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [USE_THEN "inj" ACCEPT_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    FIRST_ASSUM(fun th -> if aconv (concl th)
      `IMAGE (ps:real^3->real^3) moi_s35_upper = cb` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s35_slab`; `moi_s35_upper`; `moi_s35_cube`]
      MOI_S3HD_IMAGE_INTER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [USE_THEN "inj" ACCEPT_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    FIRST_ASSUM(fun th -> if aconv (concl th)
      `IMAGE (ps:real^3->real^3) moi_s35_lower = ca` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_lower DIFF IMAGE ps moi_s35_slab =
                  IMAGE ps (moi_s35_lower DIFF moi_s35_slab)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ THEN
      REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (ps:real^3->real^3)
                  {x:real^3 | x IN moi_s35_cube /\ x$3 <= --(&1 / &8)} INTER
                IMAGE ps moi_s35_slab` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET b ==> a INTER c SUBSET b INTER c`) THEN
      USE_THEN "clim" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[SET_RULE `{x:real^3 | x IN s /\ P x} = s INTER {x | P x}`] THEN
        MATCH_MP_TAC CLOSED_INTER THEN
        REWRITE_TAC[moi_s35_cube; CLOSED_INTERVAL; CLOSED_HALFSPACE_COMPONENT_LE];
        SET_TAC[]];
      MP_TAC(ISPECL [`ps:real^3->real^3`;
                     `{x:real^3 | x IN moi_s35_cube /\ x$3 <= --(&1 / &8)}`;
                     `moi_s35_slab`; `moi_s35_cube`] MOI_S3HD_IMAGE_INTER) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL [USE_THEN "inj" ACCEPT_TAC; SET_TAC[]; ASM_REWRITE_TAC[]];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN
      REAL_ARITH_TAC];
    FIRST_ASSUM(fun th -> if aconv (concl th)
      `IMAGE (ps:real^3->real^3) moi_s35_upper = cb` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_upper DIFF IMAGE ps moi_s35_slab =
                  IMAGE ps (moi_s35_upper DIFF moi_s35_slab)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ THEN
      REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (ps:real^3->real^3)
                  {x:real^3 | x IN moi_s35_cube /\ &1 / &8 <= x$3} INTER
                IMAGE ps moi_s35_slab` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET b ==> a INTER c SUBSET b INTER c`) THEN
      USE_THEN "clim" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[SET_RULE `{x:real^3 | x IN s /\ P x} = s INTER {x | P x}`] THEN
        MATCH_MP_TAC CLOSED_INTER THEN
        REWRITE_TAC[moi_s35_cube; CLOSED_INTERVAL; GSYM real_ge;
                    CLOSED_HALFSPACE_COMPONENT_GE];
        SET_TAC[]];
      MP_TAC(ISPECL [`ps:real^3->real^3`;
                     `{x:real^3 | x IN moi_s35_cube /\ &1 / &8 <= x$3}`;
                     `moi_s35_slab`; `moi_s35_cube`] MOI_S3HD_IMAGE_INTER) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL [USE_THEN "inj" ACCEPT_TAC; SET_TAC[]; ASM_REWRITE_TAC[]];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN
      REAL_ARITH_TAC];
    USE_THEN "fr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    USE_THEN "fr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    USE_THEN "fr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S3HD_REFL_CHART = prove
 (`!(ps:real^3->real^3).
     ps continuous_on moi_s35_cube /\
     (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\ ps x = ps y ==> x = y)
     ==> (ps o (\x:real^3. x - (&2 * x$3) % basis 3)) continuous_on moi_s35_lower /\
         (!x y. x IN moi_s35_lower /\ y IN moi_s35_lower /\
                (ps o (\x:real^3. x - (&2 * x$3) % basis 3)) x =
                (ps o (\x:real^3. x - (&2 * x$3) % basis 3)) y ==> x = y) /\
         IMAGE (ps o (\x:real^3. x - (&2 * x$3) % basis 3)) moi_s35_lower =
         IMAGE ps moi_s35_upper /\
         IMAGE (ps o (\x:real^3. x - (&2 * x$3) % basis 3)) moi_s32_slab_lo =
         IMAGE ps moi_s32_slab_hi /\
         IMAGE (ps o (\x:real^3. x - (&2 * x$3) % basis 3))
               {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} =
         IMAGE ps {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `rf = \x:real^3. x - (&2 * x$3) % basis 3` THEN
  SUBGOAL_THEN `!x:real^3. ((rf:real^3->real^3) x)$1 = x$1 /\ (rf x)$2 = x$2 /\
                           (rf x)$3 = --(x$3) /\ rf (rf x) = x` (LABEL_TAC "rfc") THENL
   [EXPAND_TAC "rf" THEN GEN_TAC THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3;
             ARITH] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3;
             ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. (!x:real^3. x IN t <=> (rf:real^3->real^3) x IN s)
                      ==> IMAGE rf s = t` (LABEL_TAC "img") THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rfc" (fun th -> ASM_REWRITE_TAC[th]);
      DISCH_TAC THEN EXISTS_TAC `(rf:real^3->real^3) y` THEN
      USE_THEN "rfc" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (rf:real^3->real^3) moi_s35_lower = moi_s35_upper /\
                IMAGE rf moi_s32_slab_lo = moi_s32_slab_hi /\
                IMAGE rf {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} =
                {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} /\
                IMAGE rf moi_s35_lower SUBSET moi_s35_cube` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(USE_THEN "img" MATCH_MP_TAC THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[IN_ELIM_THM; MOI_S3HD_SETS_IN] THEN
      USE_THEN "rfc" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN
    USE_THEN "rfc" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [EXPAND_TAC "rf" THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(rf:real^3->real^3) x = rf y` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (rf:real^3->real^3) moi_s35_lower SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s35_lower` THEN UNDISCH_TAC `(y:real^3) IN moi_s35_lower` THEN
      SET_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `rf:real^3->real^3`) THEN
      USE_THEN "rfc" (fun th -> REWRITE_TAC[th])]]);;

(* ------------------------------------------------------------------------- *)
(* Part 8: the abstract handle setting.  vv vertices with cells cc v,       *)
(* ed edges with ends av e, bv e and charts ps e of the cube onto the union *)
(* of the end cells (lower half onto cc (av e)), slabs ps e (slab) pairwise *)
(* disjoint and free of vertices, an embedding hh of tt, and for each edge  *)
(* the pseudo-cell ee e splitting hh (slab) into the sides uu1 e, uu2 e.     *)
(* Pieces: q v = hh (cc v minus all slabs) plus the v-sides.                *)
(* ------------------------------------------------------------------------- *)

let moi_s3hd_ctx = new_definition
 `moi_s3hd_ctx (vv:real^3->bool) (ed:(real^3->bool)->bool) (cc:real^3->real^3->bool)
               (av:(real^3->bool)->real^3) (bv:(real^3->bool)->real^3)
               (ps:(real^3->bool)->real^3->real^3) (tt:real^3->bool) (hh:real^3->real^3)
               (ee:(real^3->bool)->real^3->bool) (uu1:(real^3->bool)->real^3->bool)
               (uu2:(real^3->bool)->real^3->bool) <=>
    FINITE vv /\ FINITE ed /\
    (!v. v IN vv ==> compact (cc v) /\ connected (cc v) /\ v IN cc v /\ cc v SUBSET tt) /\
    (!e. e IN ed
         ==> av e IN vv /\ bv e IN vv /\ ~(av e = bv e) /\
             ps e continuous_on moi_s35_cube /\
             (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\ ps e x = ps e y ==> x = y) /\
             IMAGE (ps e) moi_s35_lower = cc (av e) /\
             IMAGE (ps e) moi_s35_upper = cc (bv e) /\
             IMAGE (ps e) moi_s35_slab INTER cc (av e) = IMAGE (ps e) moi_s32_slab_lo /\
             IMAGE (ps e) moi_s35_slab INTER cc (bv e) = IMAGE (ps e) moi_s32_slab_hi /\
             closure (cc (av e) DIFF IMAGE (ps e) moi_s35_slab) INTER
             IMAGE (ps e) moi_s35_slab SUBSET
             IMAGE (ps e) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} /\
             closure (cc (bv e) DIFF IMAGE (ps e) moi_s35_slab) INTER
             IMAGE (ps e) moi_s35_slab SUBSET
             IMAGE (ps e) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} /\
             components (IMAGE hh (IMAGE (ps e) moi_s35_slab) DIFF ee e) = {uu1 e, uu2 e} /\
             ~(uu1 e = uu2 e) /\
             closed (ee e) /\ ee e SUBSET IMAGE hh (IMAGE (ps e) moi_s35_slab) /\
             ee e SUBSET closure (uu1 e) /\ ee e SUBSET closure (uu2 e) /\
             IMAGE hh (IMAGE (ps e) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)})
             SUBSET uu1 e /\
             IMAGE hh (IMAGE (ps e) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8})
             SUBSET uu2 e) /\
    (!e e'. e IN ed /\ e' IN ed /\ ~(e = e')
            ==> DISJOINT (IMAGE (ps e) moi_s35_slab) (IMAGE (ps e') moi_s35_slab)) /\
    (!u v. u IN vv /\ v IN vv /\ ~(u = v)
           ==> cc u INTER cc v SUBSET
               UNIONS {IMAGE (ps e) moi_s35_slab | e | e IN ed /\ {av e,bv e} = {u,v}}) /\
    (!v e. v IN vv /\ e IN ed ==> ~(v IN IMAGE (ps e) moi_s35_slab)) /\
    compact tt /\ hh continuous_on tt /\
    (!x y. x IN tt /\ y IN tt /\ hh x = hh y ==> x = y)`;;

let moi_s3hd_ss = new_definition
 `moi_s3hd_ss (ed:(real^3->bool)->bool) (ps:(real^3->bool)->real^3->real^3) =
    UNIONS {IMAGE (ps e) moi_s35_slab | e IN ed}`;;

let moi_s3hd_y = new_definition
 `moi_s3hd_y (vv:real^3->bool) (ed:(real^3->bool)->bool) (cc:real^3->real^3->bool)
             (hh:real^3->real^3) (ee:(real^3->bool)->real^3->bool) =
    IMAGE hh (UNIONS {cc v | v IN vv}) DIFF UNIONS {ee e | e IN ed}`;;

let moi_s3hd_q = new_definition
 `moi_s3hd_q (ed:(real^3->bool)->bool) (cc:real^3->real^3->bool)
             (av:(real^3->bool)->real^3) (bv:(real^3->bool)->real^3)
             (ps:(real^3->bool)->real^3->real^3) (hh:real^3->real^3)
             (uu1:(real^3->bool)->real^3->bool) (uu2:(real^3->bool)->real^3->bool)
             (v:real^3) =
    IMAGE hh (cc v DIFF moi_s3hd_ss ed ps) UNION
    (UNIONS {uu1 e | e | e IN ed /\ av e = v} UNION UNIONS {uu2 e | e | e IN ed /\ bv e = v})`;;

let MOI_S3HD_LOWER_UPPER = prove
 (`moi_s35_lower UNION moi_s35_upper = moi_s35_cube`,
  REWRITE_TAC[EXTENSION; IN_UNION; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN REAL_ARITH_TAC);;

let MOI_S3HD_CTX_FACTS = prove
 (`!vv ed cc av bv ps tt hh ee uu1 uu2.
     moi_s3hd_ctx vv ed cc av bv ps tt hh ee uu1 uu2
     ==> (!e. e IN ed
              ==> IMAGE (ps e) moi_s35_slab SUBSET cc (av e) UNION cc (bv e) /\
                  compact (IMAGE (ps e) moi_s35_slab) /\
                  IMAGE (ps e) moi_s35_slab SUBSET tt /\
                  compact (IMAGE hh (IMAGE (ps e) moi_s35_slab))) /\
         compact (moi_s3hd_ss ed ps) /\ moi_s3hd_ss ed ps SUBSET tt /\
         (!v e. v IN vv /\ e IN ed /\ ~(av e = v) /\ ~(bv e = v)
                ==> cc v INTER IMAGE (ps e) moi_s35_slab = {}) /\
         (!v. v IN vv ==> compact (IMAGE hh (cc v))) /\
         (!s. s SUBSET tt
              ==> closure (IMAGE hh s) SUBSET IMAGE hh (closure s) /\
                  IMAGE hh (closure s) SUBSET closure (IMAGE hh s)) /\
         UNIONS {cc v | v IN vv} SUBSET tt /\ compact (UNIONS {cc v | v IN vv})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3hd_ctx] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cv") (CONJUNCTS_THEN2 (LABEL_TAC "ce")
    (CONJUNCTS_THEN2 (LABEL_TAC "dj") (CONJUNCTS_THEN2 (LABEL_TAC "cm")
    (CONJUNCTS_THEN2 (LABEL_TAC "va") STRIP_ASSUME_TAC))))))) THEN
  MP_TAC MOI_S3HD_BOX_BALLS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!e. e IN ed
                    ==> IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab SUBSET
                        cc ((av:(real^3->bool)->real^3) e) UNION cc (bv e) /\
                        compact (IMAGE (ps e) moi_s35_slab) /\
                        IMAGE (ps e) moi_s35_slab SUBSET tt /\
                        compact (IMAGE (hh:real^3->real^3) (IMAGE (ps e) moi_s35_slab))`
  (LABEL_TAC "se") THENL
   [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab SUBSET
                  cc ((av:(real^3->bool)->real^3) e) UNION cc (bv e)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
        `IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_lower =
         (cc:real^3->real^3->bool) ((av:(real^3->bool)->real^3) e)`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
        `IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_upper =
         (cc:real^3->real^3->bool) ((bv:(real^3->bool)->real^3) e)`)) THEN
      REWRITE_TAC[GSYM IMAGE_UNION; MOI_S3HD_LOWER_UPPER] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab SUBSET tt`
    ASSUME_TAC THENL
     [USE_THEN "cv" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o C MATCH_MP
        (ASSUME `(av:(real^3->bool)->real^3) e IN vv`)) THEN
      USE_THEN "cv" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o C MATCH_MP
        (ASSUME `(bv:(real^3->bool)->real^3) e IN vv`)) THEN
      UNDISCH_TAC `IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab SUBSET
                   cc ((av:(real^3->bool)->real^3) e) UNION cc (bv e)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `compact (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `tt:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed (tt:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s3hd_ss] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE];
    REWRITE_TAC[moi_s3hd_ss; UNIONS_SUBSET; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`v:real^3`; `e:real^3->bool`] THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN cc ((av:(real^3->bool)->real^3) e) \/ x IN cc (bv e)`
    MP_TAC THENL
     [USE_THEN "se" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [USE_THEN "cm" (MP_TAC o SPECL [`v:real^3`; `(av:(real^3->bool)->real^3) e`]);
      USE_THEN "cm" (MP_TAC o SPECL [`v:real^3`; `(bv:(real^3->bool)->real^3) e`])] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    (DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ANTS_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `e':real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    (SUBGOAL_THEN `~((e':real^3->bool) = e)` ASSUME_TAC THENL
      [DISCH_THEN SUBST_ALL_TAC THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
         is_setenum (lhs (concl th)))) THEN
       ASM SET_TAC[];
       ALL_TAC]) THEN
    USE_THEN "dj" (MP_TAC o SPECL [`e:real^3->bool`; `e':real^3->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN vv`)) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `tt:real^3->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `closure s SUBSET (tt:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(hh:real^3->real^3) continuous_on closure s` ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `tt:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET];
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC `tt:real^3->bool` THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]];
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET]];
    REWRITE_TAC[UNIONS_SUBSET; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN vv`)) THEN SIMP_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN vv`)) THEN SIMP_TAC[]]);;

let MOI_S3HD_SIDES = prove
 (`!vv ed cc av bv ps tt hh ee uu1 uu2.
     moi_s3hd_ctx vv ed cc av bv ps tt hh ee uu1 uu2
     ==> (!e. e IN ed
              ==> uu1 e SUBSET IMAGE hh (IMAGE (ps e) moi_s35_slab) DIFF ee e /\
                  uu2 e SUBSET IMAGE hh (IMAGE (ps e) moi_s35_slab) DIFF ee e /\
                  uu1 e UNION uu2 e = IMAGE hh (IMAGE (ps e) moi_s35_slab) DIFF ee e /\
                  DISJOINT (uu1 e) (uu2 e) /\ connected (uu1 e) /\ connected (uu2 e) /\
                  (IMAGE hh (IMAGE (ps e) moi_s35_slab) DIFF ee e) INTER closure (uu1 e) =
                  uu1 e /\
                  (IMAGE hh (IMAGE (ps e) moi_s35_slab) DIFF ee e) INTER closure (uu2 e) =
                  uu2 e /\
                  closure (uu1 e) SUBSET IMAGE hh (IMAGE (ps e) moi_s35_slab) /\
                  closure (uu2 e) SUBSET IMAGE hh (IMAGE (ps e) moi_s35_slab)) /\
         (!e e'. e IN ed /\ e' IN ed /\ ~(e = e')
                 ==> DISJOINT (IMAGE hh (IMAGE (ps e) moi_s35_slab))
                              (IMAGE hh (IMAGE (ps e') moi_s35_slab)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_CTX_FACTS) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s3hd_ctx]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cv") (CONJUNCTS_THEN2 (LABEL_TAC "ce")
    (CONJUNCTS_THEN2 (LABEL_TAC "dj") (CONJUNCTS_THEN2 (LABEL_TAC "cm")
    (CONJUNCTS_THEN2 (LABEL_TAC "va") STRIP_ASSUME_TAC))))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    ABBREV_TAC `xx = IMAGE (hh:real^3->real^3)
                       (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab)` THEN
    SUBGOAL_THEN `closed (xx:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "xx" THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(uu1:(real^3->bool)->real^3->bool) e IN components (xx DIFF ee e) /\
                  (uu2:(real^3->bool)->real^3->bool) e IN components (xx DIFF ee e)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET];
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET];
      MP_TAC(ISPEC `(xx:real^3->bool) DIFF ee (e:real^3->bool)` UNIONS_COMPONENTS) THEN
      ASM_REWRITE_TAC[UNIONS_2] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]);
      REWRITE_TAC[DISJOINT] THEN ASM_MESON_TAC[COMPONENTS_NONOVERLAP];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      REWRITE_TAC[GSYM CLOSED_IN_INTER_CLOSURE] THEN ASM_SIMP_TAC[CLOSED_IN_COMPONENT];
      REWRITE_TAC[GSYM CLOSED_IN_INTER_CLOSURE] THEN ASM_SIMP_TAC[CLOSED_IN_COMPONENT];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(xx:real^3->bool) DIFF ee (e:real^3->bool)`;
                     `(uu1:(real^3->bool)->real^3->bool) e`] IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(xx:real^3->bool) DIFF ee (e:real^3->bool)`;
                     `(uu2:(real^3->bool)->real^3->bool) e`] IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`e:real^3->bool`; `e':real^3->bool`] THEN STRIP_TAC THEN
    USE_THEN "dj" (MP_TAC o SPECL [`e:real^3->bool`; `e':real^3->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`hh:real^3->real^3`;
                   `IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab`;
                   `IMAGE ((ps:(real^3->bool)->real^3->real^3) e') moi_s35_slab`;
                   `tt:real^3->bool`] MOI_S3HD_IMAGE_INTER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[DISJOINT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[IMAGE_CLAUSES]]);;

let MOI_S3HD_INJ_IMAGE = prove
 (`!(f:real^3->real^3) t s x.
     (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y) /\ s SUBSET t /\ x IN t /\
     f x IN IMAGE f s
     ==> x IN s`,
  SET_TAC[]);;

let MOI_S3HD_Q_IN_Y = prove
 (`!vv ed cc av bv ps tt hh ee uu1 uu2.
     moi_s3hd_ctx vv ed cc av bv ps tt hh ee uu1 uu2
     ==> (!v. v IN vv
              ==> moi_s3hd_q ed cc av bv ps hh uu1 uu2 v SUBSET moi_s3hd_y vv ed cc hh ee) /\
         moi_s3hd_y vv ed cc hh ee SUBSET
         UNIONS {moi_s3hd_q ed cc av bv ps hh uu1 uu2 v | v IN vv}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_CTX_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "se") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_SIDES) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sd") (LABEL_TAC "sdj")) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s3hd_ctx]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cv") (CONJUNCTS_THEN2 (LABEL_TAC "ce")
    (CONJUNCTS_THEN2 (LABEL_TAC "dj") (CONJUNCTS_THEN2 (LABEL_TAC "cm")
    (CONJUNCTS_THEN2 (LABEL_TAC "va") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))))))))) THEN
  SUBGOAL_THEN `!e. e IN ed
                    ==> (ee:(real^3->bool)->real^3->bool) e SUBSET
                        IMAGE (hh:real^3->real^3)
                          (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) /\
                        IMAGE (ps e) moi_s35_slab SUBSET
                        UNIONS {(cc:real^3->real^3->bool) v | v IN (vv:real^3->bool)}`
  (LABEL_TAC "eex") THENL
   [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "se" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
    REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[moi_s3hd_q; moi_s3hd_y; UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
        UNDISCH_TAC `~((z:real^3) IN moi_s3hd_ss ed (ps:(real^3->bool)->real^3->real^3))` THEN
        REWRITE_TAC[moi_s3hd_ss; UNIONS_GSPEC; IN_ELIM_THM] THEN
        EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_S3HD_INJ_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`hh:real^3->real^3`; `tt:real^3->bool`] THEN
        REPEAT CONJ_TAC THENL
         [USE_THEN "inj" ACCEPT_TAC;
          USE_THEN "se" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o C MATCH_MP
            (ASSUME `(e:real^3->bool) IN ed`)) THEN SIMP_TAC[];
          USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN vv`)) THEN
          UNDISCH_TAC `(z:real^3) IN cc (v:real^3)` THEN SET_TAC[];
          USE_THEN "eex" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
          UNDISCH_TAC `(hh:real^3->real^3) z IN ee (e:real^3->bool)` THEN SET_TAC[]]];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^3->bool` THEN
      STRIP_TAC THEN
      USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
      STRIP_TAC THEN
      REWRITE_TAC[SUBSET; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "eex" (MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
        DISCH_THEN(MP_TAC o ISPEC `hh:real^3->real^3` o MATCH_MP IMAGE_SUBSET) THEN
        UNDISCH_TAC `(x:real^3) IN uu1 (e:real^3->bool)` THEN
        UNDISCH_TAC `uu1 (e:real^3->bool) SUBSET IMAGE (hh:real^3->real^3)
                       (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) DIFF ee e` THEN
        SET_TAC[];
        X_GEN_TAC `e':real^3->bool` THEN STRIP_TAC THEN
        ASM_CASES_TAC `e':real^3->bool = e` THENL
         [UNDISCH_TAC `(x:real^3) IN ee (e':real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(x:real^3) IN uu1 (e:real^3->bool)` THEN
          UNDISCH_TAC `uu1 (e:real^3->bool) SUBSET IMAGE (hh:real^3->real^3)
                         (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) DIFF ee e` THEN
          SET_TAC[];
          USE_THEN "sdj" (MP_TAC o SPECL [`e:real^3->bool`; `e':real^3->bool`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          USE_THEN "eex" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(e':real^3->bool) IN ed`)) THEN
          UNDISCH_TAC `(x:real^3) IN ee (e':real^3->bool)` THEN
          UNDISCH_TAC `(x:real^3) IN uu1 (e:real^3->bool)` THEN
          UNDISCH_TAC `uu1 (e:real^3->bool) SUBSET IMAGE (hh:real^3->real^3)
                         (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) DIFF ee e` THEN
          SET_TAC[]]];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^3->bool` THEN
      STRIP_TAC THEN
      USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
      STRIP_TAC THEN
      REWRITE_TAC[SUBSET; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "eex" (MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
        DISCH_THEN(MP_TAC o ISPEC `hh:real^3->real^3` o MATCH_MP IMAGE_SUBSET) THEN
        UNDISCH_TAC `(x:real^3) IN uu2 (e:real^3->bool)` THEN
        UNDISCH_TAC `uu2 (e:real^3->bool) SUBSET IMAGE (hh:real^3->real^3)
                       (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) DIFF ee e` THEN
        SET_TAC[];
        X_GEN_TAC `e':real^3->bool` THEN STRIP_TAC THEN
        ASM_CASES_TAC `e':real^3->bool = e` THENL
         [UNDISCH_TAC `(x:real^3) IN ee (e':real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(x:real^3) IN uu2 (e:real^3->bool)` THEN
          UNDISCH_TAC `uu2 (e:real^3->bool) SUBSET IMAGE (hh:real^3->real^3)
                         (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) DIFF ee e` THEN
          SET_TAC[];
          USE_THEN "sdj" (MP_TAC o SPECL [`e:real^3->bool`; `e':real^3->bool`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          USE_THEN "eex" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(e':real^3->bool) IN ed`)) THEN
          UNDISCH_TAC `(x:real^3) IN ee (e':real^3->bool)` THEN
          UNDISCH_TAC `(x:real^3) IN uu2 (e:real^3->bool)` THEN
          UNDISCH_TAC `uu2 (e:real^3->bool) SUBSET IMAGE (hh:real^3->real^3)
                         (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) DIFF ee e` THEN
          SET_TAC[]]]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3hd_y; SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC))) THEN
  ASM_CASES_TAC `(z:real^3) IN moi_s3hd_ss ed (ps:(real^3->bool)->real^3->real^3)` THENL
   [UNDISCH_TAC `(z:real^3) IN moi_s3hd_ss ed (ps:(real^3->bool)->real^3->real^3)` THEN
    REWRITE_TAC[moi_s3hd_ss; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
    STRIP_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN uu1 (e:real^3->bool) UNION uu2 e` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
        aconv (lhs (concl th)) `(uu1:(real^3->bool)->real^3->bool) e UNION uu2 e`
        then REWRITE_TAC[th] else NO_TAC) THEN
      REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN
           UNIONS {(ee:(real^3->bool)->real^3->bool) e | e IN ed})` THEN
        REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
       [EXISTS_TAC `(av:(real^3->bool)->real^3) e`;
        EXISTS_TAC `(bv:(real^3->bool)->real^3) e`] THEN
      ASM_REWRITE_TAC[moi_s3hd_q; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISJ2_TAC THEN ASM_MESON_TAC[]];
    EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[moi_s3hd_q; IN_UNION] THEN DISJ1_TAC THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3HD_CLOSURE_Q = prove
 (`!vv ed cc av bv ps tt hh ee uu1 uu2 w.
     moi_s3hd_ctx vv ed cc av bv ps tt hh ee uu1 uu2
     ==> closure (moi_s3hd_q ed cc av bv ps hh uu1 uu2 w) =
         closure (IMAGE hh (cc w DIFF moi_s3hd_ss ed ps)) UNION
         (UNIONS {closure (uu1 e) | e | e IN ed /\ av e = w} UNION
          UNIONS {closure (uu2 e) | e | e IN ed /\ bv e = w})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3hd_ctx] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s3hd_q; CLOSURE_UNION] THEN
  SUBGOAL_THEN
   `!u:(real^3->bool)->real^3->bool. !p:(real^3->bool)->bool.
      closure (UNIONS {u e | e | e IN ed /\ p e}) =
      UNIONS {closure (u e) | e | e IN ed /\ p e}`
  (fun th -> REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{(u:(real^3->bool)->real^3->bool) e | e | e IN ed /\ p e} =
                IMAGE u {e | e IN ed /\ p e}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{closure((u:(real^3->bool)->real^3->bool) e) | e | e IN ed /\ p e} =
                {closure s | s IN IMAGE u {e | e IN ed /\ p e}}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSURE_UNIONS THEN MATCH_MP_TAC FINITE_IMAGE THEN
  ASM_SIMP_TAC[FINITE_RESTRICT]);;

let MOI_S3HD_Q_SEP = prove
 (`!vv ed cc av bv ps tt hh ee uu1 uu2.
     moi_s3hd_ctx vv ed cc av bv ps tt hh ee uu1 uu2
     ==> !v w. v IN vv /\ w IN vv /\ ~(v = w)
               ==> closure (moi_s3hd_q ed cc av bv ps hh uu1 uu2 w) INTER
                   moi_s3hd_q ed cc av bv ps hh uu1 uu2 v = {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_CTX_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "se") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dis")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "clh") STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_SIDES) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sd") (LABEL_TAC "sdj")) THEN
  MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_S3HD_CLOSURE_Q th]) THEN
  REWRITE_TAC[moi_s3hd_q] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s3hd_ctx]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cv") (CONJUNCTS_THEN2 (LABEL_TAC "ce")
    (CONJUNCTS_THEN2 (LABEL_TAC "dj") (CONJUNCTS_THEN2 (LABEL_TAC "cm")
    (CONJUNCTS_THEN2 (LABEL_TAC "va") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))))))))) THEN
  ABBREV_TAC `ss = moi_s3hd_ss ed (ps:(real^3->bool)->real^3->real^3)` THEN
  SUBGOAL_THEN `!e. e IN ed ==> IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab
                                SUBSET ss` (LABEL_TAC "sss") THENL
   [EXPAND_TAC "ss" THEN REWRITE_TAC[moi_s3hd_ss] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closure (cc (w:real^3) DIFF ss) SUBSET (cc:real^3->real^3->bool) w /\
                cc w SUBSET tt /\ cc v SUBSET tt /\
                closure (IMAGE (hh:real^3->real^3) (cc w DIFF ss)) SUBSET
                IMAGE hh (closure (cc w DIFF ss))` STRIP_ASSUME_TAC THENL
   [USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN vv`)) THEN
    USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN vv`)) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
      USE_THEN "clh" (MP_TAC o SPEC `(cc:real^3->real^3->bool) w DIFF ss`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(cc:real^3->real^3->bool) w INTER (cc v DIFF ss) = {}` ASSUME_TAC THENL
   [USE_THEN "cm" (MP_TAC o SPECL [`w:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((y:real^3) IN ss)` THEN REWRITE_TAC[] THEN
    USE_THEN "sss" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a SUBSET tt /\ b SUBSET tt /\ a INTER b = {}
                      ==> IMAGE (hh:real^3->real^3) a INTER IMAGE hh b = {}`
  (LABEL_TAC "hdis") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`hh:real^3->real^3`; `a:real^3->bool`; `b:real^3->bool`;
                   `tt:real^3->bool`] MOI_S3HD_IMAGE_INTER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [USE_THEN "inj" ACCEPT_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IMAGE_CLAUSES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. e IN ed
                    ==> IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab SUBSET tt`
  (LABEL_TAC "stt") THENL
   [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "se" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. ~(x IN closure (IMAGE (hh:real^3->real^3) (cc (w:real^3) DIFF ss)) /\
                            x IN IMAGE hh (cc (v:real^3) DIFF ss))` (LABEL_TAC "p1") THENL
   [REWRITE_TAC[SET_RULE `(!x:real^3. ~(x IN s /\ x IN t)) <=> s INTER t = {}`] THEN
    MATCH_MP_TAC(SET_RULE `!b. a SUBSET b /\ b INTER c = {} ==> (a:real^3->bool) INTER c = {}`) THEN
    EXISTS_TAC `IMAGE (hh:real^3->real^3) (cc (w:real^3))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (hh:real^3->real^3) (closure (cc (w:real^3) DIFF ss))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      USE_THEN "hdis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e x. (e:real^3->bool) IN ed
          ==> ((av:(real^3->bool)->real^3) e = (v:real^3)
               ==> ~(x IN closure (IMAGE (hh:real^3->real^3) (cc (w:real^3) DIFF ss)) /\
                     x IN (uu1:(real^3->bool)->real^3->bool) e)) /\
              ((bv:(real^3->bool)->real^3) e = v
               ==> ~(x IN closure (IMAGE (hh:real^3->real^3) (cc (w:real^3) DIFF ss)) /\
                     x IN (uu2:(real^3->bool)->real^3->bool) e))`
  (LABEL_TAC "p23") THENL
   [MAP_EVERY X_GEN_TAC [`e:real^3->bool`; `x:real^3`] THEN DISCH_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `!y. y IN closure (cc (w:real^3) DIFF ss) /\
                      y IN IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab
                      ==> (w = (bv:(real^3->bool)->real^3) e ==>
                           y IN IMAGE (ps e) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}) /\
                          (w = (av:(real^3->bool)->real^3) e ==>
                           y IN IMAGE (ps e) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}) /\
                          (w = av e \/ w = bv e)` (LABEL_TAC "yy") THENL
     [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
         `closure ((cc:real^3->real^3->bool) ((bv:(real^3->bool)->real^3) e) DIFF
                   IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) INTER
          IMAGE (ps e) moi_s35_slab SUBSET
          IMAGE (ps e) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}`)) THEN
        ASM_REWRITE_TAC[IN_INTER] THEN
        MP_TAC(ISPECL [`(cc:real^3->real^3->bool) ((bv:(real^3->bool)->real^3) e) DIFF ss`;
                       `(cc:real^3->real^3->bool) ((bv:(real^3->bool)->real^3) e) DIFF
                        IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab`]
          SUBSET_CLOSURE) THEN
        USE_THEN "sss" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
        UNDISCH_TAC `(y:real^3) IN closure ((cc:real^3->real^3->bool)
                       ((bv:(real^3->bool)->real^3) e) DIFF ss)` THEN SET_TAC[];
        DISCH_THEN SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
         `closure ((cc:real^3->real^3->bool) ((av:(real^3->bool)->real^3) e) DIFF
                   IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) INTER
          IMAGE (ps e) moi_s35_slab SUBSET
          IMAGE (ps e) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}`)) THEN
        ASM_REWRITE_TAC[IN_INTER] THEN
        MP_TAC(ISPECL [`(cc:real^3->real^3->bool) ((av:(real^3->bool)->real^3) e) DIFF ss`;
                       `(cc:real^3->real^3->bool) ((av:(real^3->bool)->real^3) e) DIFF
                        IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab`]
          SUBSET_CLOSURE) THEN
        USE_THEN "sss" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
        UNDISCH_TAC `(y:real^3) IN closure ((cc:real^3->real^3->bool)
                       ((av:(real^3->bool)->real^3) e) DIFF ss)` THEN SET_TAC[];
        ONCE_REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`] THEN DISCH_TAC THEN
        ASM_CASES_TAC `(w:real^3) = (bv:(real^3->bool)->real^3) e` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "dis" (MP_TAC o SPECL [`w:real^3`; `e:real^3->bool`]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `closure (cc (w:real^3) DIFF ss) SUBSET (cc:real^3->real^3->bool) w` THEN
        UNDISCH_TAC `(y:real^3) IN closure ((cc:real^3->real^3->bool) w DIFF ss)` THEN
        UNDISCH_TAC `(y:real^3) IN IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
    (SUBGOAL_THEN `?y:real^3. y IN closure ((cc:real^3->real^3->bool) w DIFF ss) /\
                              x = (hh:real^3->real^3) y` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `closure (IMAGE (hh:real^3->real^3) (cc (w:real^3) DIFF ss)) SUBSET
                    IMAGE hh (closure (cc w DIFF ss))` THEN
       UNDISCH_TAC `(x:real^3) IN closure (IMAGE (hh:real^3->real^3) (cc (w:real^3) DIFF ss))` THEN
       SET_TAC[];
       ALL_TAC]) THEN
    (SUBGOAL_THEN `(y:real^3) IN IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab`
     ASSUME_TAC THENL
      [MATCH_MP_TAC MOI_S3HD_INJ_IMAGE THEN
       MAP_EVERY EXISTS_TAC [`hh:real^3->real^3`; `tt:real^3->bool`] THEN
       REPEAT CONJ_TAC THENL
        [USE_THEN "inj" ACCEPT_TAC;
         USE_THEN "stt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
         UNDISCH_TAC `closure (cc (w:real^3) DIFF ss) SUBSET (cc:real^3->real^3->bool) w` THEN
         UNDISCH_TAC `(cc:real^3->real^3->bool) w SUBSET tt` THEN
         UNDISCH_TAC `(y:real^3) IN closure ((cc:real^3->real^3->bool) w DIFF ss)` THEN
         SET_TAC[];
         FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
           `(x:real^3) = (hh:real^3->real^3) y`)) THEN
         ASM SET_TAC[]];
       ALL_TAC]) THEN
    USE_THEN "yy" (MP_TAC o SPEC `y:real^3`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "y1") (CONJUNCTS_THEN2 (LABEL_TAC "y2")
      ASSUME_TAC)) THEN
    FIRST
     [FIRST_ASSUM(fun th -> if aconv (concl th)
        `(x:real^3) IN (uu1:(real^3->bool)->real^3->bool) e` then ALL_TAC else NO_TAC) THEN
      SUBGOAL_THEN `(w:real^3) = (bv:(real^3->bool)->real^3) e` ASSUME_TAC THENL
       [UNDISCH_TAC `(w:real^3) = (av:(real^3->bool)->real^3) e \/ w = bv e` THEN
        UNDISCH_TAC `(av:(real^3->bool)->real^3) e = v` THEN
        UNDISCH_TAC `~((v:real^3) = w)` THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN (uu2:(real^3->bool)->real^3->bool) e` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> aconv (concl th)
          `(x:real^3) = (hh:real^3->real^3) y`)) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
          `IMAGE (hh:real^3->real^3) (IMAGE ((ps:(real^3->bool)->real^3->real^3) e)
             {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}) SUBSET
           (uu2:(real^3->bool)->real^3->bool) e`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN USE_THEN "y1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `DISJOINT ((uu1:(real^3->bool)->real^3->bool) e)
                              ((uu2:(real^3->bool)->real^3->bool) e)` THEN
        UNDISCH_TAC `(x:real^3) IN (uu1:(real^3->bool)->real^3->bool) e` THEN SET_TAC[]];
      FIRST_ASSUM(fun th -> if aconv (concl th)
        `(x:real^3) IN (uu2:(real^3->bool)->real^3->bool) e` then ALL_TAC else NO_TAC) THEN
      SUBGOAL_THEN `(w:real^3) = (av:(real^3->bool)->real^3) e` ASSUME_TAC THENL
       [UNDISCH_TAC `(w:real^3) = (av:(real^3->bool)->real^3) e \/ w = bv e` THEN
        UNDISCH_TAC `(bv:(real^3->bool)->real^3) e = v` THEN
        UNDISCH_TAC `~((v:real^3) = w)` THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN (uu1:(real^3->bool)->real^3->bool) e` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> aconv (concl th)
          `(x:real^3) = (hh:real^3->real^3) y`)) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
          `IMAGE (hh:real^3->real^3) (IMAGE ((ps:(real^3->bool)->real^3->real^3) e)
             {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}) SUBSET
           (uu1:(real^3->bool)->real^3->bool) e`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN USE_THEN "y2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `DISJOINT ((uu1:(real^3->bool)->real^3->bool) e)
                              ((uu2:(real^3->bool)->real^3->bool) e)` THEN
        UNDISCH_TAC `(x:real^3) IN (uu2:(real^3->bool)->real^3->bool) e` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e x. (e:real^3->bool) IN ed
          ==> ~((x:real^3) IN closure ((uu1:(real^3->bool)->real^3->bool) e) /\
                x IN IMAGE (hh:real^3->real^3) (cc (v:real^3) DIFF ss)) /\
              ~(x IN closure ((uu2:(real^3->bool)->real^3->bool) e) /\
                x IN IMAGE hh (cc v DIFF ss))`
  (LABEL_TAC "p4") THENL
   [MAP_EVERY X_GEN_TAC [`e:real^3->bool`; `x:real^3`] THEN DISCH_TAC THEN
    USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    USE_THEN "hdis" (MP_TAC o SPECL
      [`IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab`;
       `(cc:real^3->real^3->bool) v DIFF ss`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "stt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(cc:real^3->real^3->bool) v SUBSET tt` THEN SET_TAC[];
        USE_THEN "sss" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `closure ((uu1:(real^3->bool)->real^3->bool) e) SUBSET
                 IMAGE (hh:real^3->real^3)
                   (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab)` THEN
    UNDISCH_TAC `closure ((uu2:(real^3->bool)->real^3->bool) e) SUBSET
                 IMAGE (hh:real^3->real^3)
                   (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e e' x. (e:real^3->bool) IN ed /\ e' IN ed /\ ~(e = e')
             ==> ~((x:real^3) IN closure ((uu1:(real^3->bool)->real^3->bool) e') /\
                   (x IN uu1 e \/ x IN (uu2:(real^3->bool)->real^3->bool) e)) /\
                 ~(x IN closure (uu2 e') /\ (x IN uu1 e \/ x IN uu2 e))`
  (LABEL_TAC "p5") THENL
   [MAP_EVERY X_GEN_TAC [`e:real^3->bool`; `e':real^3->bool`; `x:real^3`] THEN STRIP_TAC THEN
    USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
    USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e':real^3->bool) IN ed`)) THEN
    USE_THEN "sdj" (MP_TAC o SPECL [`e:real^3->bool`; `e':real^3->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`IMAGE (hh:real^3->real^3)
                (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab)`,
             `x1:real^3->bool`) THEN
    SPEC_TAC(`IMAGE (hh:real^3->real^3)
                (IMAGE ((ps:(real^3->bool)->real^3->real^3) e') moi_s35_slab)`,
             `x2:real^3->bool`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e x. (e:real^3->bool) IN ed
          ==> ~((x:real^3) IN closure ((uu1:(real^3->bool)->real^3->bool) e) /\
                x IN (uu2:(real^3->bool)->real^3->bool) e) /\
              ~(x IN closure (uu2 e) /\ x IN uu1 e)`
  (LABEL_TAC "p6") THENL
   [MAP_EVERY X_GEN_TAC [`e:real^3->bool`; `x:real^3`] THEN DISCH_TAC THEN
    USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
    SPEC_TAC(`IMAGE (hh:real^3->real^3)
                (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab)`,
             `x1:real^3->bool`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN
  USE_THEN "p1" (MP_TAC o SPEC `x:real^3`) THEN
  USE_THEN "p23" (MP_TAC o SPEC `x:real^3` o ONCE_REWRITE_RULE[SWAP_FORALL_THM]) THEN
  USE_THEN "p4" (MP_TAC o SPEC `x:real^3` o ONCE_REWRITE_RULE[SWAP_FORALL_THM]) THEN
  USE_THEN "p5" (MP_TAC o GEN `e:real^3->bool` o GEN `e':real^3->bool` o
                 SPECL [`e:real^3->bool`; `e':real^3->bool`; `x:real^3`]) THEN
  USE_THEN "p6" (MP_TAC o SPEC `x:real^3` o ONCE_REWRITE_RULE[SWAP_FORALL_THM]) THEN
  UNDISCH_TAC `~((v:real^3) = w)` THEN
  MESON_TAC[]);;

let MOI_S3HD_Q_CONN = prove
 (`!vv ed cc av bv ps tt hh ee uu1 uu2.
     moi_s3hd_ctx vv ed cc av bv ps tt hh ee uu1 uu2
     ==> !v. v IN vv
             ==> (hh:real^3->real^3) v IN moi_s3hd_q ed cc av bv ps hh uu1 uu2 v /\
                 connected (moi_s3hd_q ed cc av bv ps hh uu1 uu2 v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_CTX_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "se") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dis")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "clh") STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_SIDES) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sd") (LABEL_TAC "sdj")) THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s3hd_q] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s3hd_ctx]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cv") (CONJUNCTS_THEN2 (LABEL_TAC "ce")
    (CONJUNCTS_THEN2 (LABEL_TAC "dj") (CONJUNCTS_THEN2 (LABEL_TAC "cm")
    (CONJUNCTS_THEN2 (LABEL_TAC "va") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))))))))) THEN
  ABBREV_TAC `ss = moi_s3hd_ss ed (ps:(real^3->bool)->real^3->real^3)` THEN
  SUBGOAL_THEN `!e. e IN ed ==> IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab
                                SUBSET ss` (LABEL_TAC "sss") THENL
   [EXPAND_TAC "ss" THEN REWRITE_TAC[moi_s3hd_ss] THEN SET_TAC[]; ALL_TAC] THEN
  USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN vv`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((v:real^3) IN ss)` ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN REWRITE_TAC[moi_s3hd_ss; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
    USE_THEN "va" (MP_TAC o SPECL [`v:real^3`; `e:real^3->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  ABBREV_TAC `pp = \e. if (av:(real^3->bool)->real^3) e = v
                       then (ps:(real^3->bool)->real^3->real^3) e
                       else ps e o (\x:real^3. x - (&2 * x$3) % basis 3)` THEN
  ABBREV_TAC `ev = {e | e IN ed /\ ((av:(real^3->bool)->real^3) e = v \/
                                    (bv:(real^3->bool)->real^3) e = v)}` THEN
  SUBGOAL_THEN
   `!e. e IN ev
        ==> ((pp:(real^3->bool)->real^3->real^3) e) continuous_on moi_s35_lower /\
            (!x y. x IN moi_s35_lower /\ y IN moi_s35_lower /\ pp e x = pp e y ==> x = y) /\
            IMAGE (pp e) moi_s35_lower = (cc:real^3->real^3->bool) v /\
            IMAGE (pp e) moi_s32_slab_lo =
            IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab INTER cc v /\
            IMAGE (pp e) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} =
            (if (av:(real^3->bool)->real^3) e = v
             then IMAGE (ps e) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}
             else IMAGE (ps e) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8})`
  (LABEL_TAC "ppf") THENL
   [X_GEN_TAC `e:real^3->bool` THEN EXPAND_TAC "ev" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    EXPAND_TAC "pp" THEN REWRITE_TAC[] THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
        ASM_REWRITE_TAC[MOI_S3HD_LOWER_FACTS];
        REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> aconv (concl th)
          `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                 (ps:(real^3->bool)->real^3->real^3) e x = ps e y ==> x = y`)) THEN
        ASM_REWRITE_TAC[] THEN MP_TAC MOI_S3HD_LOWER_FACTS THEN ASM SET_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
          `IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab INTER
           (cc:real^3->real^3->bool) ((av:(real^3->bool)->real^3) e) =
           IMAGE (ps e) moi_s32_slab_lo`)) THEN
        ASM_REWRITE_TAC[]];
      ASM_CASES_TAC `(av:(real^3->bool)->real^3) e = v` THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `(ps:(real^3->bool)->real^3->real^3) e` MOI_S3HD_REFL_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
        `IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab INTER
         (cc:real^3->real^3->bool) ((bv:(real^3->bool)->real^3) e) =
         IMAGE (ps e) moi_s32_slab_hi`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (ev:(real^3->bool)->bool) /\ ev SUBSET ed` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ev" THEN CONJ_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT]; SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`pp:(real^3->bool)->real^3->real^3`; `(cc:real^3->real^3->bool) v`]
    MOI_S3HD_COLLARS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `ev:(real^3->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
      USE_THEN "ppf" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ev`)) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      MAP_EVERY X_GEN_TAC [`e:real^3->bool`; `e':real^3->bool`] THEN STRIP_TAC THEN
      USE_THEN "ppf" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ev`)) THEN
      USE_THEN "ppf" (MP_TAC o C MATCH_MP (ASSUME `(e':real^3->bool) IN ev`)) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)))))) THEN
      USE_THEN "dj" (MP_TAC o SPECL [`e:real^3->bool`; `e':real^3->bool`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(cc:real^3->real^3->bool) v DIFF
                UNIONS {IMAGE ((pp:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo | e IN ev} =
                cc v DIFF ss` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(x:real^3) IN cc (v:real^3)` THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(e:real^3->bool) IN ed` ASSUME_TAC THENL
       [UNDISCH_TAC `(ev:(real^3->bool)->bool) SUBSET ed` THEN
        UNDISCH_TAC `(e:real^3->bool) IN ev` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "ppf" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        C MATCH_MP (ASSUME `(e:real^3->bool) IN ev`)) THEN
      DISCH_THEN(fun th -> UNDISCH_TAC `(x:real^3) IN IMAGE
        ((pp:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo` THEN REWRITE_TAC[th]) THEN
      USE_THEN "sss" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
      SET_TAC[];
      EXPAND_TAC "ss" THEN REWRITE_TAC[moi_s3hd_ss; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real^3->bool` THEN
      SUBGOAL_THEN `(e:real^3->bool) IN ev` ASSUME_TAC THENL
       [EXPAND_TAC "ev" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`] THEN DISCH_TAC THEN
        ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
        USE_THEN "dis" (MP_TAC o SPECL [`v:real^3`; `e:real^3->bool`]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:real^3) IN cc (v:real^3)` THEN
        UNDISCH_TAC `(x:real^3) IN IMAGE ((ps:(real^3->bool)->real^3->real^3) e)
                       moi_s35_slab` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "ppf" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        C MATCH_MP (ASSUME `(e:real^3->bool) IN ev`)) THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fc")) THEN
  ABBREV_TAC `kk = (cc:real^3->real^3->bool) v DIFF ss` THEN
  SUBGOAL_THEN `(kk:real^3->bool) SUBSET tt` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN UNDISCH_TAC `(cc:real^3->real^3->bool) v SUBSET tt` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (hh:real^3->real^3) kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `tt:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(hh:real^3->real^3) v IN IMAGE hh kk` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (hh:real^3->real^3) (closure kk) SUBSET closure (IMAGE hh kk)`
  ASSUME_TAC THENL
   [USE_THEN "clh" (MP_TAC o SPEC `kk:real^3->bool`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC MOI_S3HD_FACES THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY])
    (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) (K ALL_TAC))))))) THEN
  DISCH_THEN(X_CHOOSE_TAC `p1:real^3`) THEN DISCH_THEN(X_CHOOSE_TAC `p0:real^3`) THEN
  SUBGOAL_THEN
   `!e. e IN ed /\ (av:(real^3->bool)->real^3) e = v
        ==> connected (IMAGE (hh:real^3->real^3) kk UNION
                       (uu1:(real^3->bool)->real^3->bool) e)` ASSUME_TAC THENL
   [X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^3->bool) IN ev` ASSUME_TAC THENL
     [EXPAND_TAC "ev" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_UNION_STRONG THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(hh:real^3->real^3) ((ps:(real^3->bool)->real^3->real^3) e p0)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
        `IMAGE (hh:real^3->real^3) (closure kk) SUBSET closure (IMAGE hh kk)`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      USE_THEN "fc" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ev`)) THEN
      USE_THEN "ppf" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        C MATCH_MP (ASSUME `(e:real^3->bool) IN ev`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
        `IMAGE (hh:real^3->real^3) (IMAGE ((ps:(real^3->bool)->real^3->real^3) e)
           {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}) SUBSET
         (uu1:(real^3->bool)->real^3->bool) e`)) THEN
      REPEAT(MATCH_MP_TAC FUN_IN_IMAGE) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN ed /\ (bv:(real^3->bool)->real^3) e = v
        ==> connected (IMAGE (hh:real^3->real^3) kk UNION
                       (uu2:(real^3->bool)->real^3->bool) e)` ASSUME_TAC THENL
   [X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^3->bool) IN ev` ASSUME_TAC THENL
     [EXPAND_TAC "ev" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "sd" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((av:(real^3->bool)->real^3) e = v)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_UNION_STRONG THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(hh:real^3->real^3) ((ps:(real^3->bool)->real^3->real^3) e p1)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
        `IMAGE (hh:real^3->real^3) (closure kk) SUBSET closure (IMAGE hh kk)`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      USE_THEN "fc" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ev`)) THEN
      USE_THEN "ppf" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        C MATCH_MP (ASSUME `(e:real^3->bool) IN ev`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> aconv (concl th)
        `IMAGE (hh:real^3->real^3) (IMAGE ((ps:(real^3->bool)->real^3->real^3) e)
           {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}) SUBSET
         (uu2:(real^3->bool)->real^3->bool) e`)) THEN
      REPEAT(MATCH_MP_TAC FUN_IN_IMAGE) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (hh:real^3->real^3) kk UNION
    (UNIONS {(uu1:(real^3->bool)->real^3->bool) e | e IN ed /\
                                                   (av:(real^3->bool)->real^3) e = (v:real^3)} UNION
     UNIONS {(uu2:(real^3->bool)->real^3->bool) e | e IN ed /\
                                                   (bv:(real^3->bool)->real^3) e = v}) =
    UNIONS ({IMAGE hh kk} UNION
            {IMAGE hh kk UNION uu1 e | e | e IN ed /\ av e = v} UNION
            {IMAGE hh kk UNION uu2 e | e | e IN ed /\ bv e = v})` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_SING] THEN MESON_TAC[IN_UNION];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_SING; IN_ELIM_THM] THEN X_GEN_TAC `t:real^3->bool` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTERS; IN_UNION; IN_SING; IN_ELIM_THM] THEN
    EXISTS_TAC `(hh:real^3->real^3) v` THEN X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_UNION]]);;

let MOI_S3HD_Q_COMPONENT = prove
 (`!vv ed cc av bv ps tt hh ee uu1 uu2.
     moi_s3hd_ctx vv ed cc av bv ps tt hh ee uu1 uu2
     ==> !v. v IN vv
             ==> connected_component (moi_s3hd_y vv ed cc hh ee) (hh v) =
                 moi_s3hd_q ed cc av bv ps hh uu1 uu2 v`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_Q_IN_Y) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "qy") (LABEL_TAC "cov")) THEN
  FIRST_ASSUM(LABEL_TAC "sep" o MATCH_MP MOI_S3HD_Q_SEP) THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^3` o MATCH_MP MOI_S3HD_Q_CONN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s3hd_ctx]) THEN DISCH_TAC THEN
  ABBREV_TAC `yy = moi_s3hd_y vv ed cc (hh:real^3->real^3) ee` THEN
  ABBREV_TAC `q = moi_s3hd_q ed cc (av:(real^3->bool)->real^3) bv ps (hh:real^3->real^3) uu1 uu2` THEN
  SUBGOAL_THEN `(q:real^3->real^3->bool) v SUBSET yy` ASSUME_TAC THENL
   [USE_THEN "qy" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN yy ==> ?w. w IN vv /\ x IN (q:real^3->real^3->bool) w`
  (LABEL_TAC "cv2") THENL
   [UNDISCH_TAC `yy SUBSET UNIONS {(q:real^3->real^3->bool) v | v IN vv}` THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean yy) ((q:real^3->real^3->bool) v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      USE_THEN "cv2" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN yy`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `w:real^3 = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "sep" (MP_TAC o SPECL [`w:real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      MP_TAC(ISPEC `(q:real^3->real^3->bool) v` CLOSURE_SUBSET) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean yy) ((q:real^3->real^3->bool) v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `(:real^3) DIFF
                UNIONS {closure ((q:real^3->real^3->bool) w) | w | w IN vv /\ ~(w = v)}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC; CLOSED_CLOSURE] THEN
      ONCE_REWRITE_TAC[SET_RULE `{(f:real^3->real^3->bool) w | w | w IN s /\ P w} =
                                 IMAGE f {w | w IN s /\ P w}`] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_RESTRICT];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      EQ_TAC THENL
       [DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
        USE_THEN "sep" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ASM SET_TAC[];
        STRIP_TAC THEN USE_THEN "cv2" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN yy`)) THEN
        DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `w:real^3 = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `(q:real^3->real^3->bool) w` CLOSURE_SUBSET) THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN EXISTS_TAC `yy:real^3->bool` THEN
    ASM_REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; CONNECTED_COMPONENT_SUBSET] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `(hh:real^3->real^3) v` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]]);;

let MOI_S3HD_PAIR = prove
 (`!a b v w:real^3.
     ~(a = b) /\ ~(v = w) /\ (a = v \/ b = v) /\ (a = w \/ b = w) ==> {a,b} = {v,w}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INSERT_COMM]);;

let MOI_S3HD_Q_MEET = prove
 (`!vv ed cc av bv ps tt hh ee uu1 uu2.
     moi_s3hd_ctx vv ed cc av bv ps tt hh ee uu1 uu2
     ==> (!v. v IN vv
              ==> closure (moi_s3hd_q ed cc av bv ps hh uu1 uu2 v) SUBSET
                  IMAGE hh (cc v) UNION
                  UNIONS {IMAGE hh (IMAGE (ps e) moi_s35_slab) | e |
                          e IN ed /\ (av e = v \/ bv e = v)}) /\
         (!e. e IN ed
              ==> ee e SUBSET
                  closure (moi_s3hd_q ed cc av bv ps hh uu1 uu2 (av e)) INTER
                  closure (moi_s3hd_q ed cc av bv ps hh uu1 uu2 (bv e))) /\
         (!v w. v IN vv /\ w IN vv /\ ~(v = w)
                ==> closure (moi_s3hd_q ed cc av bv ps hh uu1 uu2 v) INTER
                    closure (moi_s3hd_q ed cc av bv ps hh uu1 uu2 w) =
                    UNIONS {ee e | e | e IN ed /\ {av e,bv e} = {v,w}})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_CTX_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "se") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dis")
    (CONJUNCTS_THEN2 (LABEL_TAC "chc") (CONJUNCTS_THEN2 (LABEL_TAC "clh")
    STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_SIDES) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sd") (LABEL_TAC "sdj")) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3HD_Q_IN_Y) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "qy") (LABEL_TAC "cov")) THEN
  FIRST_ASSUM(LABEL_TAC "sep" o MATCH_MP MOI_S3HD_Q_SEP) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s3hd_ctx]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cv") (CONJUNCTS_THEN2 (LABEL_TAC "ce")
    (CONJUNCTS_THEN2 (LABEL_TAC "dj") (CONJUNCTS_THEN2 (LABEL_TAC "cm")
    (CONJUNCTS_THEN2 (LABEL_TAC "va") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))))))))) THEN
  ABBREV_TAC `q = moi_s3hd_q ed cc (av:(real^3->bool)->real^3) bv ps (hh:real^3->real^3) uu1 uu2` THEN
  SUBGOAL_THEN
   `!v. v IN vv
        ==> closure ((q:real^3->real^3->bool) v) SUBSET
            IMAGE (hh:real^3->real^3) (cc v) UNION
            UNIONS {IMAGE hh (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab) | e |
                    e IN ed /\ ((av:(real^3->bool)->real^3) e = v \/
                                (bv:(real^3->bool)->real^3) e = v)}`
  (LABEL_TAC "c2") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC[moi_s3hd_q; UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (s:real^3->bool) SUBSET t UNION u`) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^3->bool` THEN
        STRIP_TAC THEN
        USE_THEN "sd" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
        MATCH_MP_TAC(SET_RULE `t SUBSET u ==> (s:real^3->bool) SUBSET t DIFF x ==> s SUBSET v UNION u`) THEN
        MATCH_MP_TAC(SET_RULE `(s:real^3->bool) IN f ==> s SUBSET UNIONS f`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^3->bool` THEN
        STRIP_TAC THEN
        USE_THEN "sd" (MP_TAC o CONJUNCT1 o CONJUNCT2 o C MATCH_MP
          (ASSUME `(e:real^3->bool) IN ed`)) THEN
        MATCH_MP_TAC(SET_RULE `t SUBSET u ==> (s:real^3->bool) SUBSET t DIFF x ==> s SUBSET v UNION u`) THEN
        MATCH_MP_TAC(SET_RULE `(s:real^3->bool) IN f ==> s SUBSET UNIONS f`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN USE_THEN "chc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CLOSED_UNIONS THEN
        ONCE_REWRITE_TAC[SET_RULE `{(f:(real^3->bool)->real^3->bool) e | e | e IN s /\ P e} =
                                   IMAGE f {e | e IN s /\ P e}`] THEN
        ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        USE_THEN "se" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN ed
        ==> (ee:(real^3->bool)->real^3->bool) e SUBSET
            closure ((q:real^3->real^3->bool) ((av:(real^3->bool)->real^3) e)) INTER
            closure (q ((bv:(real^3->bool)->real^3) e))`
  (LABEL_TAC "c5") THENL
   [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(uu1:(real^3->bool)->real^3->bool) e SUBSET
                  (q:real^3->real^3->bool) ((av:(real^3->bool)->real^3) e) /\
                  (uu2:(real^3->bool)->real^3->bool) e SUBSET q ((bv:(real^3->bool)->real^3) e)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC[moi_s3hd_q] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `(s:real^3->bool) IN f ==> s SUBSET a UNION (UNIONS f UNION b)`);
        MATCH_MP_TAC(SET_RULE `(s:real^3->bool) IN f ==> s SUBSET a UNION (b UNION UNIONS f)`)] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `closure ((uu1:(real^3->bool)->real^3->bool) e)`;
      EXISTS_TAC `closure ((uu2:(real^3->bool)->real^3->bool) e)`] THEN
    ASM_SIMP_TAC[SUBSET_CLOSURE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^3->bool` THEN
    STRIP_TAC THEN
    USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `((av:(real^3->bool)->real^3) e = v /\ (bv:(real^3->bool)->real^3) e = w) \/
                  (av e = w /\ bv e = v)` MP_TAC THENL
     [UNDISCH_TAC `{(av:(real^3->bool)->real^3) e,(bv:(real^3->bool)->real^3) e} = {v,w}` THEN
      DISCH_THEN(ACCEPT_TAC o MATCH_MP (SET_RULE
        `{a:real^3,b} = {c,d} ==> a = c /\ b = d \/ a = d /\ b = c`));
      ALL_TAC] THEN
    USE_THEN "c5" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
    STRIP_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `closure:(real^3->bool)->real^3->bool`)) (concl th) &&
      can (find_term ((=) `ee:(real^3->bool)->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER] THEN
  STRIP_TAC THEN
  ABBREV_TAC `yy = moi_s3hd_y vv ed cc (hh:real^3->real^3) ee` THEN
  SUBGOAL_THEN `~((x:real^3) IN yy)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `yy SUBSET UNIONS {(q:real^3->real^3->bool) v | v IN vv}` THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `u:real^3 = v` THENL
     [USE_THEN "sep" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN (q:real^3->real^3->bool) u` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN closure ((q:real^3->real^3->bool) w)` THEN SET_TAC[];
      USE_THEN "sep" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN (q:real^3->real^3->bool) u` THEN
      UNDISCH_TAC `(x:real^3) IN closure ((q:real^3->real^3->bool) v)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (hh:real^3->real^3) (UNIONS {(cc:real^3->real^3->bool) v | v IN (vv:real^3->bool)})`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `closure ((q:real^3->real^3->bool) v) SUBSET
                  IMAGE (hh:real^3->real^3) (UNIONS {(cc:real^3->real^3->bool) v | v IN (vv:real^3->bool)})` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `yy:real^3->bool` THEN CONJ_TAC THENL
         [USE_THEN "qy" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          EXPAND_TAC "yy" THEN REWRITE_TAC[moi_s3hd_y] THEN SET_TAC[]];
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `tt:real^3->bool` THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `(x:real^3) IN closure ((q:real^3->real^3->bool) v)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e. e IN ed /\ (x:real^3) IN (ee:(real^3->bool)->real^3->bool) e`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~((x:real^3) IN yy)` THEN EXPAND_TAC "yy" THEN
    REWRITE_TAC[moi_s3hd_y; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "ce" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. u IN vv /\ (x:real^3) IN closure ((q:real^3->real^3->bool) u)
        ==> (av:(real^3->bool)->real^3) e = u \/ (bv:(real^3->bool)->real^3) e = u`
  (LABEL_TAC "at") THENL
   [X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
    USE_THEN "c2" (MP_TAC o C MATCH_MP (ASSUME `(u:real^3) IN vv`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e':real^3->bool`
      (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC))) THENL
     [ONCE_REWRITE_TAC[TAUT `p \/ q <=> ~(~p /\ ~q)`] THEN STRIP_TAC THEN
      USE_THEN "dis" (MP_TAC o SPECL [`u:real^3`; `e:real^3->bool`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`hh:real^3->real^3`; `(cc:real^3->real^3->bool) u`;
                     `IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab`;
                     `tt:real^3->bool`] MOI_S3HD_IMAGE_INTER) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "inj" ACCEPT_TAC;
          USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `(u:real^3) IN vv`)) THEN SIMP_TAC[];
          USE_THEN "se" (MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN SIMP_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
      UNDISCH_TAC `(ee:(real^3->bool)->real^3->bool) e SUBSET
                   IMAGE (hh:real^3->real^3)
                     (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab)` THEN
      UNDISCH_TAC `(x:real^3) IN (ee:(real^3->bool)->real^3->bool) e` THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE (hh:real^3->real^3) ((cc:real^3->real^3->bool) u)` THEN
      SET_TAC[];
      ASM_CASES_TAC `(e':real^3->bool) = e` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "sdj" (MP_TAC o SPECL [`e:real^3->bool`; `e':real^3->bool`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(ee:(real^3->bool)->real^3->bool) e SUBSET
                   IMAGE (hh:real^3->real^3)
                     (IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab)` THEN
      UNDISCH_TAC `(x:real^3) IN (ee:(real^3->bool)->real^3->bool) e` THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE (hh:real^3->real^3)
                     (IMAGE ((ps:(real^3->bool)->real^3->real^3) e') moi_s35_slab)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "at" (MP_TAC o SPEC `v:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "at" (MP_TAC o SPEC `w:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `e:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3HD_PAIR THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 9: the side facts of one edge from the edge facts of HANDLES        *)
(* (the far faces of the half slabs lie in their own sides).                *)
(* ------------------------------------------------------------------------- *)

(* A set k on the frontier of a closed set x and on the frontier of a      *)
(* component u of x minus ee lies in u, if k misses the part j of the      *)
(* frontier of x that meets the set ww containing ee.                      *)

let MOI_S3HD_FACE_SIDE = prove
 (`!(x:real^3->bool) ee ww j u k.
     closed x /\ ee SUBSET ww /\ ww INTER frontier x SUBSET j /\
     u IN components (x DIFF ee) /\
     k SUBSET frontier x /\ k SUBSET frontier u /\ DISJOINT k j
     ==> k SUBSET u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_COMPONENT) THEN
  REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN
  MP_TAC(ISPEC `x:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `frontier (u:real^3->bool) SUBSET closure u` MP_TAC THENL
   [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_S3HD_DISJ_IMAGE = prove
 (`!(f:real^3->real^3) t s1 s2.
     (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y) /\ s1 SUBSET t /\ s2 SUBSET t /\
     DISJOINT s1 s2 ==> DISJOINT (IMAGE f s1) (IMAGE f s2)`,
  SET_TAC[]);;

let MOI_S3HD_FACE_CUBE = prove
 (`{x:real^3 | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} SUBSET moi_s35_cube /\
   {x:real^3 | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} SUBSET moi_s35_cube /\
   moi_s35_mid SUBSET moi_s35_cube`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_S3HD_SETS_IN; MOI_S3HD_CUBE_IN] THEN
  REAL_ARITH_TAC);;

let MOI_S3HD_EDGE_SIDES = prove
 (`!(ps:real^3->real^3) q ca cb fr (a:real^3) b (tt:real^3->bool) (h:real^3->real^3)
    ww ee u1 u2.
     pl_homeomorphism (moi_s35_cube,ca UNION cb) (ps,q) /\
     IMAGE ps moi_s35_lower = ca /\ IMAGE ps moi_s35_upper = cb /\
     ps (vec 0) = midpoint(a,b) /\
     IMAGE ps {x | x IN moi_s35_slab /\ moi_s35_n x = &1} SUBSET fr /\
     interior(ca UNION cb) INTER fr = {} /\
     ca UNION cb SUBSET tt /\ compact tt /\ h continuous_on tt /\
     (!x y. x IN tt /\ y IN tt /\ h x = h y ==> x = y) /\
     ww SUBSET IMAGE h (IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi) /\
     ww INTER frontier (IMAGE h (IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi)) =
     IMAGE h (ca INTER cb INTER fr) /\
     pseudo_cell ee (IMAGE h (ca INTER cb INTER fr)) (h(midpoint(a,b))) /\
     ee SUBSET ww /\
     components (IMAGE h (IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi) DIFF ee) =
     {u1,u2} /\
     ee SUBSET frontier u1 /\ ee SUBSET frontier u2 /\
     IMAGE h (frontier (IMAGE ps moi_s32_slab_lo) DIFF
              ((ca INTER cb) DIFF (ca INTER cb INTER fr))) SUBSET frontier u1 /\
     IMAGE h (frontier (IMAGE ps moi_s32_slab_hi) DIFF
              ((ca INTER cb) DIFF (ca INTER cb INTER fr))) SUBSET frontier u2
     ==> closed ee /\ ee SUBSET IMAGE h (IMAGE ps moi_s35_slab) /\
         ee SUBSET closure u1 /\ ee SUBSET closure u2 /\
         components (IMAGE h (IMAGE ps moi_s35_slab) DIFF ee) = {u1,u2} /\
         IMAGE h (IMAGE ps {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}) SUBSET u1 /\
         IMAGE h (IMAGE ps {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}) SUBSET u2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ps:real^3->real^3`; `q:real^3->real^3`; `ca:real^3->bool`;
                 `cb:real^3->bool`; `fr:real^3->bool`; `a:real^3`; `b:real^3`]
    MOI_S3HD_SLAB_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`ps:real^3->real^3`; `q:real^3->real^3`; `ca:real^3->bool`;
                 `cb:real^3->bool`] MOI_S3HD_EDGE_GEOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC MOI_S3HD_BOX_BALLS THEN STRIP_TAC THEN
  MP_TAC MOI_S3HD_FACES THEN STRIP_TAC THEN
  MP_TAC MOI_S3HD_FACE_CUBE THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi =
                IMAGE ps moi_s35_slab`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `xx = IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) moi_s35_slab)` THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_cube SUBSET tt` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_slab SUBSET tt /\
                compact (IMAGE (ps:real^3->real^3) moi_s35_slab)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (ps:real^3->real^3) moi_s35_cube` THEN
      CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
                      FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (xx:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "xx" THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `tt:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (xx:real^3->bool) =
                IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) (frontier moi_s35_slab))`
  (LABEL_TAC "frx") THENL
   [EXPAND_TAC "xx" THEN
    MP_TAC(ISPECL [`h:real^3->real^3`; `tt:real^3->bool`;
                   `IMAGE (ps:real^3->real^3) moi_s35_slab`] MOI_S3HD_EMBED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (ee:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `pseudo_cell ee (IMAGE (h:real^3->real^3) (ca INTER cb INTER fr))
                   (h(midpoint(a:real^3,b)))` THEN
    REWRITE_TAC[pseudo_cell] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC
      [GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))))]) THEN
    REWRITE_TAC[CLOSED_CLOSURE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ee:real^3->bool) SUBSET closure u1 /\ ee SUBSET closure u2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `frontier (u1:real^3->bool) SUBSET closure u1 /\
                  frontier (u2:real^3->bool) SUBSET closure u2` MP_TAC THENL
     [REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(ee:real^3->bool) SUBSET frontier u1` THEN
    UNDISCH_TAC `(ee:real^3->bool) SUBSET frontier u2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ee:real^3->bool) SUBSET xx` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ww:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (ps:real^3->real^3)
                           {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}) (ca INTER cb) /\
                DISJOINT (IMAGE (ps:real^3->real^3)
                           {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}) (ca INTER cb)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC(ISPECL [`ps:real^3->real^3`; `moi_s35_cube`] MOI_S3HD_DISJ_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ca INTER cb:real^3->bool) SUBSET tt /\
                IMAGE (ps:real^3->real^3)
                  {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} SUBSET tt /\
                IMAGE (ps:real^3->real^3)
                  {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} SUBSET tt`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ca UNION cb SUBSET (tt:real^3->bool)` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (ps:real^3->real^3) moi_s35_cube` THEN
      CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
                      FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (ps:real^3->real^3) moi_s35_cube` THEN
      CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
                      FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ww:real^3->bool) INTER frontier xx SUBSET
                IMAGE (h:real^3->real^3) (ca INTER cb)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
       aconv (lhs (concl th)) `(ww:real^3->bool) INTER frontier xx`
       then SUBST1_TAC th else NO_TAC) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u1:real^3->bool) IN components (xx DIFF ee) /\
                (u2:real^3->bool) IN components (xx DIFF ee)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}) SUBSET frontier xx /\
                IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}) SUBSET frontier xx`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "frx" SUBST1_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC IMAGE_SUBSET THENL
     [UNDISCH_TAC `{x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} SUBSET frontier moi_s32_slab_lo INTER frontier moi_s35_slab`;
      UNDISCH_TAC `{x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} SUBSET frontier moi_s32_slab_hi INTER frontier moi_s35_slab`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}) SUBSET frontier u1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^3->real^3)
                  (frontier (IMAGE (ps:real^3->real^3) moi_s32_slab_lo) DIFF
                   ((ca INTER cb) DIFF (ca INTER cb INTER fr)))` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    SUBGOAL_THEN `IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} SUBSET frontier (IMAGE ps moi_s32_slab_lo)`
    MP_TAC THENL
     [REWRITE_TAC[ASSUME `frontier (IMAGE (ps:real^3->real^3) moi_s32_slab_lo) =
                          IMAGE ps (frontier moi_s32_slab_lo)`] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `{x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} SUBSET frontier moi_s32_slab_lo INTER frontier moi_s35_slab` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}) (ca INTER cb)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}) SUBSET frontier u2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^3->real^3)
                  (frontier (IMAGE (ps:real^3->real^3) moi_s32_slab_hi) DIFF
                   ((ca INTER cb) DIFF (ca INTER cb INTER fr)))` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    SUBGOAL_THEN `IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} SUBSET frontier (IMAGE ps moi_s32_slab_hi)`
    MP_TAC THENL
     [REWRITE_TAC[ASSUME `frontier (IMAGE (ps:real^3->real^3) moi_s32_slab_hi) =
                          IMAGE ps (frontier moi_s32_slab_hi)`] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `{x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} SUBSET frontier moi_s32_slab_hi INTER frontier moi_s35_slab` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}) (ca INTER cb)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}))
                         (IMAGE h (ca INTER cb)) /\
                DISJOINT (IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}))
                         (IMAGE h (ca INTER cb))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(ISPECL [`h:real^3->real^3`; `tt:real^3->bool`] MOI_S3HD_DISJ_IMAGE) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC MOI_S3HD_FACE_SIDE THEN
  MAP_EVERY EXISTS_TAC [`xx:real^3->bool`; `ee:real^3->bool`; `ww:real^3->bool`;
                        `IMAGE (h:real^3->real^3) (ca INTER cb)`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 10: the abstract handle setting holds under the hypotheses of       *)
(* MOI_S32_HANDLES_2 (tube facts, per-edge facts, the context).             *)
(* ------------------------------------------------------------------------- *)

(* Parts of MOI_S32_HANDLES_2: antecedent (library facts), variables, inner *)
(* hypothesis, conclusion; statements with the same hypotheses.             *)

let moi_s3hd_h2_parts =
  let a,b = dest_imp MOI_S32_HANDLES_2 in
  let vs,body = strip_forall b in
  let hy,c = dest_imp body in
  a,vs,hy,c;;

let moi_s3hd_ante = let a,_,_,_ = moi_s3hd_h2_parts in a;;

let moi_s3hd_hyps_imp c1 =
  let a,vs,hy,_ = moi_s3hd_h2_parts in
  let tm = mk_imp(a,list_mk_forall(vs,mk_imp(hy,c1))) in
  if frees tm = [] then tm else failwith "moi_s3hd_hyps_imp: free variables";;

let moi_s3hd_h2_concl i =
  let _,_,_,c = moi_s3hd_h2_parts in List.nth (conjuncts c) i;;

let MOI_S3HD_CELL_CC = prove
 (`!n (d:real^3->bool) j. pl_cell_with_boundary n d j ==> compact d /\ connected d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check
    (fun th -> is_eq (concl th) && rand(concl th) = `d:real^3->bool`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED]]);;

(* The tube facts used below, from the antecedent of HANDLES_2.             *)

let MOI_S3HD_TUBE_FACTS = prove
 (mk_imp(moi_s3hd_ante,
  `!(t:(real^3->bool)->bool) l.
     FINITE t /\ graph_in_complex t l
     ==> FINITE l /\ l SUBSET t /\ compact (UNIONS t) /\
         lf_simplicial_complex t /\ simplicial_subcomplex l t /\
         compact (derived_nbhd t l) /\ derived_nbhd t l SUBSET UNIONS t /\
         frontier (derived_nbhd t l) = derived_frontier t l /\
         derived_nbhd t l = UNIONS {derived_dual_cell t l v | v | {v} IN l} /\
         (!v. {v} IN l
              ==> compact (derived_dual_cell t l v) /\ connected (derived_dual_cell t l v) /\
                  v IN derived_dual_cell t l v /\
                  derived_dual_cell t l v SUBSET UNIONS t /\
                  derived_dual_cell t l v SUBSET derived_nbhd t l /\ v IN UNIONS t /\
                  (!w. {w} IN l /\ w IN derived_dual_cell t l v ==> w = v)) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
                ==> derived_dual_cell t l u INTER derived_dual_cell t l v = {})`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tube") (CONJUNCTS_THEN2 (LABEL_TAC "fr3")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "basic")))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^3->bool)->bool) /\ simplicial_subcomplex l t /\
                l SUBSET t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `graph_in_complex (t:(real^3->bool)->bool) l` THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS (t:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lf_simplicial_complex (t:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  USE_THEN "basic" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (MP_TAC o C MP (ASSUME `FINITE (l:(real^3->bool)->bool)`)))))))) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  USE_THEN "fr3" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  USE_THEN "tube" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nu") (CONJUNCTS_THEN2 (LABEL_TAC "tv")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "tn")))) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "tv" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o MATCH_MP MOI_S3HD_CELL_CC)))) THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `{v:real^3} IN t` ASSUME_TAC THENL
     [UNDISCH_TAC `{v:real^3} IN l` THEN UNDISCH_TAC `l SUBSET (t:(real^3->bool)->bool)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^3) IN derived_dual_cell t l v` ASSUME_TAC THENL
     [UNDISCH_TAC `{w:real^3 | {w} IN t /\ w IN derived_dual_cell t l v} = {v}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `derived_dual_cell t l (v:real^3) SUBSET UNIONS {s | s IN t /\ v IN s}` THEN
      SET_TAC[];
      USE_THEN "nu" SUBST1_TAC THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^3}` THEN ASM_REWRITE_TAC[IN_SING];
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `{w:real^3} IN t` ASSUME_TAC THENL
       [UNDISCH_TAC `{w:real^3} IN l` THEN UNDISCH_TAC `l SUBSET (t:(real^3->bool)->bool)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `{w:real^3 | {w} IN t /\ w IN derived_dual_cell t l v} = {v}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[]]);;

let MOI_S3HD_FR_STEP = prove
 (`!a w x hh k fx j:real^3->bool.
     a SUBSET w /\ a SUBSET x /\ k = x INTER hh /\ k SUBSET fx /\ w INTER fx = j
     ==> a INTER hh SUBSET j`,
  SET_TAC[]);;

(* One edge: from its chart and its edge facts, the per-edge clauses of the *)
(* abstract context and the facts used in the assembly of HANDLES.          *)

let MOI_S3HD_EDGE_CTX = prove
 (`!(ps:real^3->real^3) ca cb fr nn gl (a:real^3) b (tt:real^3->bool) (h:real^3->real^3)
    ww ee u1 u2.
     (?q. pl_homeomorphism (moi_s35_cube,ca UNION cb) (ps,q)) /\
     IMAGE ps moi_s35_lower = ca /\ IMAGE ps moi_s35_upper = cb /\
     ps (vec 0) = midpoint(a,b) /\
     IMAGE ps {x | x IN moi_s35_slab /\ moi_s35_n x = &1} SUBSET fr /\
     ca UNION cb SUBSET nn /\ frontier nn = fr /\ closed nn /\ nn SUBSET tt /\
     compact tt /\ h continuous_on tt /\
     (!x y. x IN tt /\ y IN tt /\ h x = h y ==> x = y) /\
     ww SUBSET IMAGE h (IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi) /\
     ww INTER frontier (IMAGE h (IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi)) =
     IMAGE h (ca INTER cb INTER fr) /\
     ww INTER IMAGE h gl = {h(midpoint(a,b))} /\
     pseudo_cell ee (IMAGE h (ca INTER cb INTER fr)) (h(midpoint(a,b))) /\
     ee SUBSET ww /\
     components (IMAGE h (IMAGE ps moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi) DIFF ee) =
     {u1,u2} /\
     ee SUBSET frontier u1 /\ ee SUBSET frontier u2 /\
     IMAGE h (frontier (IMAGE ps moi_s32_slab_lo) DIFF
              ((ca INTER cb) DIFF (ca INTER cb INTER fr))) SUBSET frontier u1 /\
     IMAGE h (frontier (IMAGE ps moi_s32_slab_hi) DIFF
              ((ca INTER cb) DIFF (ca INTER cb INTER fr))) SUBSET frontier u2
     ==> ps continuous_on moi_s35_cube /\
         (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\ ps x = ps y ==> x = y) /\
         IMAGE ps moi_s35_slab INTER ca = IMAGE ps moi_s32_slab_lo /\
         IMAGE ps moi_s35_slab INTER cb = IMAGE ps moi_s32_slab_hi /\
         closure (ca DIFF IMAGE ps moi_s35_slab) INTER IMAGE ps moi_s35_slab SUBSET
         IMAGE ps {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} /\
         closure (cb DIFF IMAGE ps moi_s35_slab) INTER IMAGE ps moi_s35_slab SUBSET
         IMAGE ps {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} /\
         components (IMAGE h (IMAGE ps moi_s35_slab) DIFF ee) = {u1,u2} /\
         closed ee /\ ee SUBSET IMAGE h (IMAGE ps moi_s35_slab) /\
         ee SUBSET closure u1 /\ ee SUBSET closure u2 /\
         IMAGE h (IMAGE ps {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)}) SUBSET u1 /\
         IMAGE h (IMAGE ps {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8}) SUBSET u2 /\
         IMAGE ps moi_s35_slab SUBSET ca UNION cb /\
         IMAGE ps moi_s35_mid = ca INTER cb /\
         IMAGE ps moi_s35_slab SUBSET tt /\
         ee INTER IMAGE h gl = {h(midpoint(a,b))} /\
         ee INTER IMAGE h fr = IMAGE h (ca INTER cb INTER fr)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^3->real^3`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ca UNION cb SUBSET (tt:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `nn:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (ca UNION cb:real^3->bool) INTER fr = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ca UNION cb:real^3->bool`; `nn:real^3->bool`] SUBSET_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> concl th = `frontier (nn:real^3->bool) = fr`)) THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ps:real^3->real^3`; `q:real^3->real^3`; `ca:real^3->bool`;
                 `cb:real^3->bool`; `fr:real^3->bool`; `a:real^3`; `b:real^3`;
                 `tt:real^3->bool`; `h:real^3->real^3`; `ww:real^3->bool`;
                 `ee:real^3->bool`; `u1:real^3->bool`; `u2:real^3->bool`]
    MOI_S3HD_EDGE_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`ps:real^3->real^3`; `q:real^3->real^3`; `ca:real^3->bool`;
                 `cb:real^3->bool`] MOI_S3HD_EDGE_GEOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`ps:real^3->real^3`; `q:real^3->real^3`; `ca:real^3->bool`;
                 `cb:real^3->bool`; `fr:real^3->bool`; `a:real^3`; `b:real^3`]
    MOI_S3HD_SLAB_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_slab SUBSET ca UNION cb` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (ps:real^3->real^3) moi_s35_cube = ca UNION cb`)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MP_TAC MOI_S3HD_BOX_BALLS THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_slab SUBSET tt` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ca UNION cb:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (ps:real^3->real^3) moi_s35_slab)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[] THEN MP_TAC MOI_S3HD_BOX_BALLS THEN SIMP_TAC[];
      MP_TAC MOI_S3HD_BOX_BALLS THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) (midpoint(a,b)) IN ee` ASSUME_TAC THENL
   [UNDISCH_TAC `pseudo_cell ee (IMAGE (h:real^3->real^3) (ca INTER cb INTER fr))
                   (h(midpoint(a:real^3,b)))` THEN
    REWRITE_TAC[pseudo_cell; IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ee INTER IMAGE (h:real^3->real^3) gl = {h(midpoint(a:real^3,b))}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ww INTER IMAGE (h:real^3->real^3) gl = {h(midpoint(a:real^3,b))}` THEN
    UNDISCH_TAC `(ee:real^3->bool) SUBSET ww` THEN
    UNDISCH_TAC `(h:real^3->real^3) (midpoint(a,b)) IN ee` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(fr:real^3->bool) SUBSET tt` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> concl th = `frontier (nn:real^3->bool) = fr`)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `nn:real^3->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_slab INTER fr SUBSET
                frontier (IMAGE ps moi_s35_slab)` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (ps:real^3->real^3) moi_s35_slab SUBSET nn` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ca UNION cb:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
    MP_TAC(ISPEC `IMAGE (ps:real^3->real^3) moi_s35_slab` CLOSURE_SUBSET) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> concl th = `frontier (nn:real^3->bool) = fr`)) THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) moi_s35_slab)) =
                IMAGE h (frontier (IMAGE ps moi_s35_slab))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real^3->real^3`; `tt:real^3->bool`;
                   `IMAGE (ps:real^3->real^3) moi_s35_slab`] MOI_S3HD_EMBED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) moi_s35_slab INTER fr) =
                IMAGE h (IMAGE ps moi_s35_slab) INTER IMAGE h fr` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3HD_IMAGE_INTER THEN EXISTS_TAC `tt:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ww INTER frontier (IMAGE (h:real^3->real^3)
                  (IMAGE (ps:real^3->real^3) moi_s35_slab)) =
                IMAGE h (ca INTER cb INTER fr)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if aconv (concl th)
      `IMAGE (ps:real^3->real^3) moi_s32_slab_lo UNION IMAGE ps moi_s32_slab_hi =
       IMAGE ps moi_s35_slab` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ee INTER IMAGE (h:real^3->real^3) fr = IMAGE h (ca INTER cb INTER fr)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3HD_FR_STEP THEN
      MAP_EVERY EXISTS_TAC
       [`ww:real^3->bool`;
        `IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) moi_s35_slab)`;
        `IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) moi_s35_slab INTER fr)`;
        `frontier (IMAGE (h:real^3->real^3) (IMAGE (ps:real^3->real^3) moi_s35_slab))`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REWRITE_TAC[ASSUME `frontier (IMAGE (h:real^3->real^3)
                           (IMAGE (ps:real^3->real^3) moi_s35_slab)) =
                          IMAGE h (frontier (IMAGE ps moi_s35_slab))`] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `pseudo_cell ee (IMAGE (h:real^3->real^3) (ca INTER cb INTER fr))
                     (h(midpoint(a:real^3,b)))` THEN
      REWRITE_TAC[pseudo_cell] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST_ASSUM(ACCEPT_TAC o SYM o check (fun th ->
    concl th = `ca INTER cb = IMAGE (ps:real^3->real^3) moi_s35_mid`)));;

(* The per-edge facts under the hypotheses of HANDLES_2.                    *)

let MOI_S3HD_H_EDGES = prove
 (moi_s3hd_hyps_imp
   `!e. moi_s35_edge (l:(real^3->bool)->bool) e
        ==> {(av:(real^3->bool)->real^3) e} IN l /\ {(bv:(real^3->bool)->real^3) e} IN l /\
            ~(av e = bv e) /\ segment[av e,bv e] = e /\
            IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s35_slab SUBSET
            (g:real^3->real^3->bool) (av e) INTER g (bv e) /\
            psi e continuous_on moi_s35_cube /\
            (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\ psi e x = psi e y ==> x = y) /\
            IMAGE (psi e) moi_s35_lower = derived_dual_cell (t:(real^3->bool)->bool) l (av e) /\
            IMAGE (psi e) moi_s35_upper = derived_dual_cell t l (bv e) /\
            IMAGE (psi e) moi_s35_slab INTER derived_dual_cell t l (av e) =
            IMAGE (psi e) moi_s32_slab_lo /\
            IMAGE (psi e) moi_s35_slab INTER derived_dual_cell t l (bv e) =
            IMAGE (psi e) moi_s32_slab_hi /\
            closure (derived_dual_cell t l (av e) DIFF IMAGE (psi e) moi_s35_slab) INTER
            IMAGE (psi e) moi_s35_slab SUBSET
            IMAGE (psi e) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)} /\
            closure (derived_dual_cell t l (bv e) DIFF IMAGE (psi e) moi_s35_slab) INTER
            IMAGE (psi e) moi_s35_slab SUBSET
            IMAGE (psi e) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8} /\
            components (IMAGE (h:real^3->real^3) (IMAGE (psi e) moi_s35_slab) DIFF
                        (ee:(real^3->bool)->real^3->bool) e) =
            {(uu1:(real^3->bool)->real^3->bool) e, (uu2:(real^3->bool)->real^3->bool) e} /\
            ~(uu1 e = uu2 e) /\
            closed (ee e) /\ ee e SUBSET IMAGE h (IMAGE (psi e) moi_s35_slab) /\
            ee e SUBSET closure (uu1 e) /\ ee e SUBSET closure (uu2 e) /\
            IMAGE h (IMAGE (psi e) {x | x IN moi_s32_slab_lo /\ x$3 = --(&1 / &8)})
            SUBSET uu1 e /\
            IMAGE h (IMAGE (psi e) {x | x IN moi_s32_slab_hi /\ x$3 = &1 / &8})
            SUBSET uu2 e /\
            IMAGE (psi e) moi_s35_slab SUBSET
            derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e) /\
            IMAGE (psi e) moi_s35_mid =
            derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) /\
            IMAGE (psi e) moi_s35_slab SUBSET UNIONS t /\
            pseudo_cell (ee e)
              (IMAGE h (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) INTER
                        derived_frontier t l))
              (h(midpoint(av e,bv e))) /\
            ee e INTER IMAGE h (UNIONS l) = {h(midpoint(av e,bv e))} /\
            ee e INTER IMAGE h (derived_frontier t l) =
            IMAGE h (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) INTER
                     derived_frontier t l)`,
  DISCH_THEN(LABEL_TAC "ante") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "charts") (CONJUNCTS_THEN2 (LABEL_TAC "ef") (K ALL_TAC))))) THEN
  USE_THEN "ante" (fun a -> MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    (MATCH_MP MOI_S3HD_TUBE_FACTS a))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "tv") (K ALL_TAC))))))))))) THEN
  X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
  USE_THEN "charts" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge (l:(real^3->bool)->bool) e`) o
    CONJUNCT1 o REWRITE_RULE[moi_s35_charts]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))))) THEN
  USE_THEN "ef" (STRIP_ASSUME_TAC o C MATCH_MP
    (ASSUME `moi_s35_edge (l:(real^3->bool)->bool) e`)) THEN
  SUBGOAL_THEN `derived_dual_cell t l ((av:(real^3->bool)->real^3) e) UNION
                derived_dual_cell t l ((bv:(real^3->bool)->real^3) e) SUBSET derived_nbhd t l`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [USE_THEN "tv" (MP_TAC o C MATCH_MP (ASSUME `{(av:(real^3->bool)->real^3) e} IN l`));
      USE_THEN "tv" (MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^3->bool)->real^3) e} IN l`))] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (derived_nbhd (t:(real^3->bool)->bool) l)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(psi:(real^3->bool)->real^3->real^3) e`;
                 `derived_dual_cell t l ((av:(real^3->bool)->real^3) e)`;
                 `derived_dual_cell t l ((bv:(real^3->bool)->real^3) e)`;
                 `derived_frontier (t:(real^3->bool)->bool) l`;
                 `derived_nbhd (t:(real^3->bool)->bool) l`;
                 `UNIONS (l:(real^3->bool)->bool)`;
                 `(av:(real^3->bool)->real^3) e`; `(bv:(real^3->bool)->real^3) e`;
                 `UNIONS (t:(real^3->bool)->bool)`; `h:real^3->real^3`;
                 `(ww:(real^3->bool)->real^3->bool) e`; `(ee:(real^3->bool)->real^3->bool) e`;
                 `(uu1:(real^3->bool)->real^3->bool) e`; `(uu2:(real^3->bool)->real^3->bool) e`]
    MOI_S3HD_EDGE_CTX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The abstract context holds under the hypotheses of HANDLES_2.  The       *)
(* vertex condition keeps the vertices out of the slabs.                    *)

let MOI_S3HD_H_CTX = prove
 (moi_s3hd_hyps_imp
   `moi_s3hd_ctx {v | {v} IN l} {e | moi_s35_edge l e} (derived_dual_cell t l) av bv psi
                 (UNIONS t) h ee uu1 uu2`,
  DISCH_THEN(fun a -> REPEAT GEN_TAC THEN DISCH_THEN(fun hy ->
    MP_TAC (MATCH_MP (MATCH_MP MOI_S3HD_H_EDGES a) hy) THEN
    MP_TAC (MATCH_MP (MATCH_MP MOI_S3HD_TUBE_FACTS a)
      (CONJ (CONJUNCT1 (CONJUNCT1 hy)) (CONJUNCT1 (CONJUNCT2 (CONJUNCT1 hy))))) THEN
    MP_TAC hy)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gdef")
    (CONJUNCTS_THEN2 (LABEL_TAC "charts") (CONJUNCTS_THEN2 (K ALL_TAC)
    (LABEL_TAC "vsep"))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "tv")
    (LABEL_TAC "tn"))))))))))) THEN
  DISCH_THEN(LABEL_TAC "edg") THEN
  REWRITE_TAC[moi_s3hd_ctx; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MP_TAC(ISPECL [`\v:real^3. {v}`; `l:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SET_TAC[]; DISCH_THEN ACCEPT_TAC];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s35_edge] THEN MESON_TAC[];
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "tv" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN SIMP_TAC[];
    X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "edg" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge (l:(real^3->bool)->bool) e`)) THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "charts" (ACCEPT_TAC o CONJUNCT2 o REWRITE_RULE[moi_s35_charts]);
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `segment[u:real^3,v] IN l` THENL
     [ALL_TAC;
      SUBGOAL_THEN `derived_dual_cell t l u INTER derived_dual_cell t l (v:real^3) = {}`
        SUBST1_TAC THENL
       [USE_THEN "tn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REWRITE_TAC[EMPTY_SUBSET]]] THEN
    SUBGOAL_THEN `moi_s35_edge l (segment[u:real^3,v])` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_s35_edge; AFF_DIM_SEGMENT]; ALL_TAC] THEN
    USE_THEN "edg" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (segment[u:real^3,v])`)) THEN
    ABBREV_TAC `e = segment[u:real^3,v]` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{(av:(real^3->bool)->real^3) e,bv e} = {u,v}` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT1 SEGMENT_EQ)] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s35_slab` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `derived_dual_cell t l u INTER derived_dual_cell t l (v:real^3) =
                    IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s35_mid`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN (SUBST1_TAC o SYM)) o
          MATCH_MP (SET_RULE `{a:real^3,b} = {c,d} ==> a = c /\ b = d \/ a = d /\ b = c`)) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[INTER_COMM];
        MATCH_MP_TAC IMAGE_SUBSET THEN MP_TAC MOI_S3HD_BOX_BALLS THEN SIMP_TAC[]];
      MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`v:real^3`; `e:real^3->bool`] THEN STRIP_TAC THEN
    USE_THEN "edg" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge (l:(real^3->bool)->bool) e`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^3->real^3) v IN nb ((av:(real^3->bool)->real^3) e) /\
                  h v IN nb ((bv:(real^3->bool)->real^3) e)` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(v:real^3) IN (g:real^3->real^3->bool) ((av:(real^3->bool)->real^3) e) /\
                    v IN g ((bv:(real^3->bool)->real^3) e)` MP_TAC THENL
       [UNDISCH_TAC `IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s35_slab SUBSET
                     (g:real^3->real^3->bool) ((av:(real^3->bool)->real^3) e) INTER
                     g ((bv:(real^3->bool)->real^3) e)` THEN
        UNDISCH_TAC `(v:real^3) IN IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s35_slab` THEN
        SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "gdef" (fun th -> REWRITE_TAC[
        MATCH_MP th (ASSUME `{(av:(real^3->bool)->real^3) e} IN l`);
        MATCH_MP th (ASSUME `{(bv:(real^3->bool)->real^3) e} IN l`)]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((h:real^3->real^3) v IN nb ((av:(real^3->bool)->real^3) e)) \/
                  ~(h v IN nb ((bv:(real^3->bool)->real^3) e))` MP_TAC THENL
     [ASM_CASES_TAC `v = (av:(real^3->bool)->real^3) e` THENL
       [DISJ2_TAC THEN USE_THEN "vsep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~((av:(real^3->bool)->real^3) e = bv e)` THEN MESON_TAC[];
        DISJ1_TAC THEN USE_THEN "vsep" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 11: the assembly of HANDLES : |- MOI_S32_HANDLES_2.  The            *)
(* pieces of 32.3 are the closures of the abstract pieces q v; (7)-(11).    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3HD_CTX_PROJ = prove
 (`!vv ed cc av bv ps tt hh ee uu1 uu2.
     moi_s3hd_ctx vv ed cc av bv ps tt hh ee uu1 uu2
     ==> DISJOINT vv (moi_s3hd_ss ed ps) /\
         (!e. e IN ed ==> ee e SUBSET IMAGE hh (IMAGE (ps e) moi_s35_slab))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3hd_ctx; moi_s3hd_ss] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `!v e. v IN vv /\ e IN ed
                       ==> ~(v IN IMAGE ((ps:(real^3->bool)->real^3->real^3) e) moi_s35_slab)` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(e:real^3->bool) IN ed`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S3HD_SLABS_SS = prove
 (`!ed (ps:(real^3->bool)->real^3->real^3) (hh:real^3->real^3) (pp:(real^3->bool)->bool).
     (!e. pp e ==> e IN ed)
     ==> UNIONS {IMAGE hh (IMAGE (ps e) moi_s35_slab) | e | pp e} SUBSET
         IMAGE hh (moi_s3hd_ss ed ps)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^3->bool` THEN
  DISCH_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[moi_s3hd_ss] THEN
  MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `e:real^3->bool` THEN ASM_SIMP_TAC[]);;

let MOI_S3HD_VERTEX_ONLY = prove
 (`!(hh:real^3->real^3) tt cv ss vs v k.
     (!x y. x IN tt /\ y IN tt /\ hh x = hh y ==> x = y) /\
     cv SUBSET tt /\ ss SUBSET tt /\ vs SUBSET tt /\ v IN vs /\
     (!w. w IN vs /\ w IN cv ==> w = v) /\ DISJOINT vs ss /\
     k SUBSET IMAGE hh cv UNION IMAGE hh ss /\ hh v IN k
     ==> k INTER IMAGE hh vs = {hh v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_SING] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (hh:real^3->real^3) cv UNION IMAGE hh ss` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `c:real^3` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
  ASM_MESON_TAC[]);;

(* The pieces of 32.3 are the closures of the pieces q v.                   *)

let MOI_S3HD_H_PC = prove
 (moi_s3hd_hyps_imp
   `(!v. {v} IN l
         ==> closure (connected_component
                       (IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF
                        UNIONS {(ee:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})
                       (h v)) =
             closure (moi_s3hd_q {e | moi_s35_edge l e} (derived_dual_cell t l) av bv psi h
                                 uu1 uu2 v)) /\
    {closure (connected_component
               (IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF
                UNIONS {(ee:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})
               (h v)) | v | {v} IN l} =
    {closure (moi_s3hd_q {e | moi_s35_edge l e} (derived_dual_cell t l) av bv psi h
                         uu1 uu2 v) | v | {v} IN l} /\
    IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF
    UNIONS {(ee:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1} =
    moi_s3hd_y {v | {v} IN l} {e | moi_s35_edge l e} (derived_dual_cell t l) h ee`,
  DISCH_THEN(fun a -> REPEAT GEN_TAC THEN DISCH_THEN(fun hy ->
    LABEL_TAC "ctx" (MATCH_MP (MATCH_MP MOI_S3HD_H_CTX a) hy) THEN
    MP_TAC (MATCH_MP (MATCH_MP MOI_S3HD_TUBE_FACTS a)
      (CONJ (CONJUNCT1 (CONJUNCT1 hy)) (CONJUNCT1 (CONJUNCT2 (CONJUNCT1 hy))))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "nu") (K ALL_TAC)))))))))) THEN
  SUBGOAL_THEN
   `IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF
    UNIONS {(ee:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1} =
    moi_s3hd_y {v | {v} IN l} {e | moi_s35_edge l e} (derived_dual_cell t l) h ee`
  (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [REWRITE_TAC[moi_s3hd_y] THEN USE_THEN "nu" SUBST1_TAC THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; IN_IMAGE; IN_ELIM_THM; moi_s35_edge] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    USE_THEN "ctx" (MP_TAC o SPEC `v:real^3` o MATCH_MP MOI_S3HD_Q_COMPONENT) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `s:real^3->bool` THEN
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^3` THEN ASM_SIMP_TAC[]]);;

(* Common start of the parts (7)-(11): the context, the per-edge facts, the *)
(* pieces, the tube facts and the hypotheses of 32.3 as assumptions.        *)

let MOI_S3HD_PRE_TAC =
  DISCH_THEN(fun a -> REPEAT GEN_TAC THEN DISCH_THEN(fun hy ->
    LABEL_TAC "ctx" (MATCH_MP (MATCH_MP MOI_S3HD_H_CTX a) hy) THEN
    LABEL_TAC "edg" (MATCH_MP (MATCH_MP MOI_S3HD_H_EDGES a) hy) THEN
    LABEL_TAC "pc" (MATCH_MP (MATCH_MP MOI_S3HD_H_PC a) hy) THEN
    MP_TAC (MATCH_MP (MATCH_MP MOI_S3HD_TUBE_FACTS a)
      (CONJ (CONJUNCT1 (CONJUNCT1 hy)) (CONJUNCT1 (CONJUNCT2 (CONJUNCT1 hy))))) THEN
    MP_TAC hy)) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nbh")))))
    (CONJUNCTS_THEN2 (LABEL_TAC "gdef") (K ALL_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "tv")
    (LABEL_TAC "tn")))))))))));;

(* (7): the pseudo-cells of the edges.                                       *)

let MOI_S3HD_H_7 = prove
 (moi_s3hd_hyps_imp (moi_s3hd_h2_concl 0),
  MOI_S3HD_PRE_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l)) =
                IMAGE h (derived_frontier t l)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`h:real^3->real^3`; `UNIONS t:real^3->bool`;
                   `derived_nbhd t l:real^3->bool`] MOI_S3HD_EMBED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_edge l (segment[u:real^3,v])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s35_edge; AFF_DIM_SEGMENT]; ALL_TAC] THEN
  USE_THEN "edg" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (segment[u:real^3,v])`)) THEN
  ABBREV_TAC `e = segment[u:real^3,v]` THEN STRIP_TAC THEN
  SUBGOAL_THEN `{(av:(real^3->bool)->real^3) e,bv e} = {u,v}` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT1 SEGMENT_EQ)] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_dual_cell t l u INTER derived_dual_cell t l v INTER frontier (derived_nbhd t l) =
    derived_dual_cell t l ((av:(real^3->bool)->real^3) e) INTER
    derived_dual_cell t l ((bv:(real^3->bool)->real^3) e) INTER derived_frontier t l /\
    midpoint(u:real^3,v) = midpoint(av e,bv e)` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN (SUBST1_TAC o SYM)) o
      MATCH_MP (SET_RULE `{a:real^3,b} = {c,d} ==> a = c /\ b = d \/ a = d /\ b = c`)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; MATCH_ACCEPT_TAC MIDPOINT_SYM];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* (8): the pseudo-cells of distinct edges are disjoint.                     *)

let MOI_S3HD_H_8 = prove
 (moi_s3hd_hyps_imp (moi_s3hd_h2_concl 1),
  MOI_S3HD_PRE_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `s':real^3->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_edge l (s:real^3->bool) /\ moi_s35_edge l (s':real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[moi_s35_edge]; ALL_TAC] THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`s:real^3->bool`; `s':real^3->bool`] o CONJUNCT2 o
    MATCH_MP MOI_S3HD_SIDES) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "ctx" (MP_TAC o CONJUNCT2 o MATCH_MP MOI_S3HD_CTX_PROJ) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(fun th ->
    MP_TAC(MATCH_MP th (ASSUME `moi_s35_edge l (s:real^3->bool)`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `moi_s35_edge l (s':real^3->bool)`))) THEN
  UNDISCH_TAC `DISJOINT (IMAGE (h:real^3->real^3)
                 (IMAGE ((psi:(real^3->bool)->real^3->real^3) s) moi_s35_slab))
                (IMAGE h (IMAGE (psi s') moi_s35_slab))` THEN
  SET_TAC[]);;

(* (9): each piece meets the image of the vertex set only in h v and lies   *)
(* in nb v.                                                                 *)

let MOI_S3HD_H_9 = prove
 (moi_s3hd_hyps_imp (moi_s3hd_h2_concl 2),
  MOI_S3HD_PRE_TAC THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  USE_THEN "pc" (fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 th) (ASSUME `{v:real^3} IN l`)]) THEN
  USE_THEN "ctx" (MP_TAC o SPEC `v:real^3` o CONJUNCT1 o MATCH_MP MOI_S3HD_Q_MEET) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [USE_THEN "tv" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
    USE_THEN "ctx" (STRIP_ASSUME_TAC o MATCH_MP MOI_S3HD_CTX_PROJ) THEN
    USE_THEN "ctx" (MP_TAC o MATCH_MP MOI_S3HD_CTX_FACTS) THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    SUBGOAL_THEN `{w:real^3 | {w} IN l} SUBSET UNIONS t` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "tv" (MP_TAC o C MATCH_MP (ASSUME `{w:real^3} IN l`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^3->real^3) v IN
                  closure (moi_s3hd_q {e | moi_s35_edge l e} (derived_dual_cell t l) av bv psi h
                                      uu1 uu2 v)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      USE_THEN "ctx" (MP_TAC o SPEC `v:real^3` o MATCH_MP MOI_S3HD_Q_CONN) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `closure (moi_s3hd_q {e | moi_s35_edge l e} (derived_dual_cell t l) av bv psi h
                          uu1 uu2 v) SUBSET
      IMAGE (h:real^3->real^3) (derived_dual_cell t l v) UNION
      IMAGE h (moi_s3hd_ss {e | moi_s35_edge l e} psi)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `(k:real^3->bool) SUBSET a UNION b ==> b SUBSET c ==> k SUBSET a UNION c`) o
        check (fun th -> is_binary "SUBSET" (concl th) &&
                         is_comb (lhand (concl th)) &&
                         fst(dest_comb(lhand(concl th))) = `closure:(real^3->bool)->real^3->bool`)) THEN
      MATCH_MP_TAC MOI_S3HD_SLABS_SS THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3HD_VERTEX_ONLY THEN
    MAP_EVERY EXISTS_TAC [`UNIONS t:real^3->bool`; `derived_dual_cell t l (v:real^3)`;
                          `moi_s3hd_ss {e | moi_s35_edge l e}
                             (psi:(real^3->bool)->real^3->real^3)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^3->real^3) (derived_dual_cell t l v) UNION
                UNIONS {IMAGE h (IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s35_slab) |
                        e | moi_s35_edge l e /\
                            ((av:(real^3->bool)->real^3) e = v \/
                             (bv:(real^3->bool)->real^3) e = v)}` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [USE_THEN "nbh" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `e:real^3->bool` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s35_slab SUBSET
                  (g:real^3->real^3->bool) v` MP_TAC THENL
     [USE_THEN "edg" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge (l:(real^3->bool)->bool) e`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      UNDISCH_TAC `(av:(real^3->bool)->real^3) e = v \/ (bv:(real^3->bool)->real^3) e = v` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "gdef" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `{v:real^3} IN l`)]) THEN
    SET_TAC[]]);;

(* (10): the pieces cover h N.                                               *)

let MOI_S3HD_H_10 = prove
 (moi_s3hd_hyps_imp (moi_s3hd_h2_concl 3),
  MOI_S3HD_PRE_TAC THEN
  USE_THEN "pc" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (h:real^3->real^3) (derived_nbhd t l) SUBSET
                  moi_s3hd_y {v | {v} IN l} {e | moi_s35_edge l e} (derived_dual_cell t l) h ee
                  UNION
                  UNIONS {(ee:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1}`
    MP_TAC THENL
     [USE_THEN "pc" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET c /\ b SUBSET c
                           ==> (x SUBSET a UNION b ==> x SUBSET c)`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {moi_s3hd_q {e | moi_s35_edge l e} (derived_dual_cell t l) av bv psi h
                                     uu1 uu2 v | v | v IN {v | {v} IN l}}` THEN
      CONJ_TAC THENL
       [USE_THEN "ctx" (ACCEPT_TAC o CONJUNCT2 o MATCH_MP MOI_S3HD_Q_IN_Y); ALL_TAC] THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure (moi_s3hd_q {e | moi_s35_edge l e} (derived_dual_cell t l) av bv psi h
                                      uu1 uu2 v)` THEN
      REWRITE_TAC[CLOSURE_SUBSET] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `e:real^3->bool` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `moi_s35_edge l (e:real^3->bool)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[moi_s35_edge]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure (moi_s3hd_q {e | moi_s35_edge l e} (derived_dual_cell t l) av bv psi h
                                      uu1 uu2 ((av:(real^3->bool)->real^3) e))` THEN
      CONJ_TAC THENL
       [USE_THEN "ctx" (MP_TAC o SPEC `e:real^3->bool` o CONJUNCT1 o CONJUNCT2 o
          MATCH_MP MOI_S3HD_Q_MEET) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `(av:(real^3->bool)->real^3) e` THEN
        REWRITE_TAC[] THEN
        USE_THEN "edg" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^3->bool)`)) THEN
        DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "ctx" (MP_TAC o SPEC `v:real^3` o CONJUNCT1 o MATCH_MP MOI_S3HD_Q_MEET) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(b:real^3->bool) SUBSET c ==> (a SUBSET b ==> a SUBSET c)`) THEN
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      USE_THEN "tv" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
      STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `e:real^3->bool` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    USE_THEN "edg" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `moi_s35_edge (l:(real^3->bool)->bool) e`)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `derived_dual_cell t l ((av:(real^3->bool)->real^3) e) UNION
                derived_dual_cell t l ((bv:(real^3->bool)->real^3) e)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[UNION_SUBSET]] THEN
    CONJ_TAC THENL
     [USE_THEN "tv" (MP_TAC o C MATCH_MP (ASSUME `{(av:(real^3->bool)->real^3) e} IN l`));
      USE_THEN "tv" (MP_TAC o C MATCH_MP (ASSUME `{(bv:(real^3->bool)->real^3) e} IN l`))] THEN
    STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* (11): two pieces meet in the pseudo-cell of the edge joining them.       *)

let MOI_S3HD_GSPEC_EQ1 = prove
 (`!(f:(real^3->bool)->real^3->bool) a. {f e | e | e = a} = {f a}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING; UNWIND_THM2]);;

let MOI_S3HD_GSPEC_F = prove
 (`!(f:(real^3->bool)->real^3->bool). {f e | e | F} = {}`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY]);;

let MOI_S3HD_H_11 = prove
 (moi_s3hd_hyps_imp (moi_s3hd_h2_concl 4),
  MOI_S3HD_PRE_TAC THEN
  MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  USE_THEN "pc" (fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 th) (ASSUME `{v:real^3} IN l`);
                                       MATCH_MP (CONJUNCT1 th) (ASSUME `{w:real^3} IN l`)]) THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`v:real^3`; `w:real^3`] o CONJUNCT2 o CONJUNCT2 o
    MATCH_MP MOI_S3HD_Q_MEET) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!e. moi_s35_edge l e /\ {(av:(real^3->bool)->real^3) e,bv e} = {v,w} <=>
                    segment[v,w] IN l /\ e = segment[v:real^3,w]`
    (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `e:real^3->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `segment[v:real^3,w] = e` ASSUME_TAC THENL
       [USE_THEN "edg" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^3->bool)`)) THEN
        DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
        REWRITE_TAC[CONJUNCT1 SEGMENT_EQ] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_s35_edge l (e:real^3->bool)` THEN SIMP_TAC[moi_s35_edge];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      SUBGOAL_THEN `moi_s35_edge l (segment[v:real^3,w])` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[moi_s35_edge; AFF_DIM_SEGMENT]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "edg" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (segment[v:real^3,w])`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[CONJUNCT1 SEGMENT_EQ]];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[MOI_S3HD_GSPEC_EQ1; UNIONS_1];
    REWRITE_TAC[MOI_S3HD_GSPEC_F; UNIONS_0]]);;

(* HANDLES : |- MOI_S32_HANDLES_2.                                           *)

let HANDLES = prove
 (MOI_S32_HANDLES_2,
  DISCH_THEN(fun a -> REPEAT GEN_TAC THEN DISCH_THEN(fun hy ->
    REPEAT CONJ_TAC THENL
     (map (fun th -> ACCEPT_TAC (MATCH_MP (MATCH_MP th a) hy))
          [MOI_S3HD_H_7; MOI_S3HD_H_8; MOI_S3HD_H_9; MOI_S3HD_H_10; MOI_S3HD_H_11]))));;

