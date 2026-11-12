(* ========================================================================= *)
(* pc_moi_s30_tor_b: Moise GTM 47 p.218 (30.7 Case 2,                       *)
(* "exactly as in the proof of Theorem 28.1").  Main theorem                *)
(* HANDLE_SOLID_TORUS : |- MOI_S30_HANDLE_SOLID_TORUS: two PL 3-balls of    *)
(* real^3 meeting exactly in two disjoint PL 2-cells of both frontiers form *)
(* a PL solid torus.                                                        *)
(* Route: the model solid torus M3 (square annulus x [-1,1]) is cut by the  *)
(* plane x1 = 0 into two U-prisms P1, P2 meeting in two rectangles E1, E2. *)
(* ONE_DISK_EXT maps P1 onto b; affine local extensions at flat points of   *)
(* E1 and E2 (the two sides of a flat disk point, ext2's CHART_FLAT and    *)
(* FLAT_ORIENT) carry the same orientation by ext2's LOCAL_D0 and          *)
(* LOCAL_SIGN (the orientability of the handle in real^3, the gap of        *)
(* p.218); TWO_DISK_EXT then maps P2 onto hb compatibly, and the two maps   *)
(* glue.                                                                    *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s35_ext2.ml";;
needs "src/pc_moi_s35_cells.ml";;
needs "src/pc_moi_s35_approx.ml";;
needs "src/pc_moi_fnd_plst.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: the model in real^3.  M3 = square annulus x [-1,1] (the          *)
(* image of moi_fps_m under the coordinate map k), its halves P1 (x1 <= 0)  *)
(* and P2 (x1 >= 0), the two rectangles E1, E2 of the cut (images of the    *)
(* standard square under the affine maps moi_s3tb_sq), the boxes of the     *)
(* halves, and the frontier and half-space facts.                          *)
(* ------------------------------------------------------------------------- *)

let moi_s3tb_m3 = new_definition
 `moi_s3tb_m3 =
    {x:real^3 | &1 <= max (abs(x$1)) (abs(x$2)) /\ max (abs(x$1)) (abs(x$2)) <= &2 /\
                abs(x$3) <= &1}`;;

let moi_s3tb_p1 = new_definition
 `moi_s3tb_p1 = {x:real^3 | x IN moi_s3tb_m3 /\ x$1 <= &0}`;;

let moi_s3tb_p2 = new_definition
 `moi_s3tb_p2 = {x:real^3 | x IN moi_s3tb_m3 /\ &0 <= x$1}`;;

let moi_s3tb_sq = new_definition
 `moi_s3tb_sq (c:real) (s:real) (z:real^2) = vector[c; s + z$1 / &2; z$2]:real^3`;;

let moi_s3tb_e1 = new_definition
 `moi_s3tb_e1 =
    IMAGE (moi_s3tb_sq (&0) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`;;

let moi_s3tb_e2 = new_definition
 `moi_s3tb_e2 =
    IMAGE (moi_s3tb_sq (&0) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`;;

let moi_s3tb_k = new_definition
 `moi_s3tb_k (z:real^(2,1)finite_sum) =
    vector[(fstcart z)$1; (fstcart z)$2; (sndcart z)$1]:real^3`;;

let moi_s3tb_kinv = new_definition
 `moi_s3tb_kinv (x:real^3) =
    pastecart (vector[x$1; x$2]:real^2) (lift(x$3)):real^(2,1)finite_sum`;;

let MOI_S3TB_IN_Q = prove
 (`!z:real^2. z IN interval[--vector[&1;&1],vector[&1;&1]] <=>
              abs(z$1) <= &1 /\ abs(z$2) <= &1`,
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_S3TB_SQ_IMAGE = prove
 (`!c s (x:real^3).
     x IN IMAGE (moi_s3tb_sq c s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) <=>
     x$1 = c /\ abs(x$2 - s) <= &1 / &2 /\ abs(x$3) <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE; MOI_S3TB_IN_Q; moi_s3tb_sq] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_3] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `vector[&2 * ((x:real^3)$2 - s); x$3]:real^2` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S3TB_E12 = prove
 (`(!x:real^3. x IN moi_s3tb_e1 <=> x$1 = &0 /\ &1 <= x$2 /\ x$2 <= &2 /\ abs(x$3) <= &1) /\
   (!x:real^3. x IN moi_s3tb_e2 <=>
               x$1 = &0 /\ -- &2 <= x$2 /\ x$2 <= -- &1 /\ abs(x$3) <= &1)`,
  REWRITE_TAC[moi_s3tb_e1; moi_s3tb_e2; MOI_S3TB_SQ_IMAGE] THEN REAL_ARITH_TAC);;

let MOI_S3TB_MODEL_SETS = prove
 (`moi_s3tb_p1 UNION moi_s3tb_p2 = moi_s3tb_m3 /\
   moi_s3tb_p1 INTER moi_s3tb_p2 = moi_s3tb_e1 UNION moi_s3tb_e2 /\
   DISJOINT moi_s3tb_e1 moi_s3tb_e2 /\
   moi_s3tb_p1 SUBSET {x:real^3 | x$1 <= &0} /\ moi_s3tb_p2 SUBSET {x:real^3 | &0 <= x$1} /\
   moi_s3tb_p1 INTER {x:real^3 | x$1 = &0} = moi_s3tb_e1 UNION moi_s3tb_e2 /\
   moi_s3tb_p2 INTER {x:real^3 | x$1 = &0} = moi_s3tb_e1 UNION moi_s3tb_e2 /\
   moi_s3tb_e1 UNION moi_s3tb_e2 SUBSET moi_s3tb_p1 /\
   moi_s3tb_e1 UNION moi_s3tb_e2 SUBSET moi_s3tb_p2`,
  REWRITE_TAC[EXTENSION; SUBSET; DISJOINT; IN_UNION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY;
              moi_s3tb_p1; moi_s3tb_p2; moi_s3tb_m3; MOI_S3TB_E12] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

(* The boxes of the two halves and the faces where they meet.              *)

let MOI_S3TB_P1_BOXES = prove
 (`moi_s3tb_p1 =
   (interval[vector[-- &2; -- &2; -- &1],vector[-- &1; &2; &1]] UNION
    interval[vector[-- &1; &1; -- &1],vector[&0; &2; &1]]) UNION
   interval[vector[-- &1; -- &2; -- &1],vector[&0; -- &1; &1]]`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3;
              moi_s3tb_p1; moi_s3tb_m3; IN_ELIM_THM] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3TB_P2_BOXES = prove
 (`moi_s3tb_p2 =
   (interval[vector[&1; -- &2; -- &1],vector[&2; &2; &1]] UNION
    interval[vector[&0; &1; -- &1],vector[&1; &2; &1]]) UNION
   interval[vector[&0; -- &2; -- &1],vector[&1; -- &1; &1]]`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3;
              moi_s3tb_p2; moi_s3tb_m3; IN_ELIM_THM] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3TB_FACES = prove
 (`interval[vector[-- &2; -- &2; -- &1],vector[-- &1; &2; &1]] INTER
   interval[vector[-- &1; &1; -- &1],vector[&0; &2; &1]] =
   IMAGE (moi_s3tb_sq (-- &1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
   (interval[vector[-- &2; -- &2; -- &1],vector[-- &1; &2; &1]] UNION
    interval[vector[-- &1; &1; -- &1],vector[&0; &2; &1]]) INTER
   interval[vector[-- &1; -- &2; -- &1],vector[&0; -- &1; &1]] =
   IMAGE (moi_s3tb_sq (-- &1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
   interval[vector[&1; -- &2; -- &1],vector[&2; &2; &1]] INTER
   interval[vector[&0; &1; -- &1],vector[&1; &2; &1]] =
   IMAGE (moi_s3tb_sq (&1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
   (interval[vector[&1; -- &2; -- &1],vector[&2; &2; &1]] UNION
    interval[vector[&0; &1; -- &1],vector[&1; &2; &1]]) INTER
   interval[vector[&0; -- &2; -- &1],vector[&1; -- &1; &1]] =
   IMAGE (moi_s3tb_sq (&1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3;
              MOI_S3TB_SQ_IMAGE] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3TB_E12_INTERVAL = prove
 (`moi_s3tb_e1 = interval[vector[&0; &1; -- &1],vector[&0; &2; &1]] /\
   moi_s3tb_e2 = interval[vector[&0; -- &2; -- &1],vector[&0; -- &1; &1]]`,
  REWRITE_TAC[EXTENSION; MOI_S3TB_E12; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3TB_CLOSED = prove
 (`compact moi_s3tb_m3 /\ compact moi_s3tb_p1 /\ compact moi_s3tb_p2 /\
   compact moi_s3tb_e1 /\ compact moi_s3tb_e2 /\
   polytope moi_s3tb_e1 /\ polytope moi_s3tb_e2`,
  REWRITE_TAC[GSYM(CONJUNCT1 MOI_S3TB_MODEL_SETS)] THEN
  REWRITE_TAC[MOI_S3TB_P1_BOXES; MOI_S3TB_P2_BOXES; MOI_S3TB_E12_INTERVAL] THEN
  SIMP_TAC[COMPACT_UNION; COMPACT_INTERVAL; POLYTOPE_INTERVAL]);;

(* Frontier facts: E1, E2 lie in the frontiers of both halves.             *)

let MOI_S3TB_FRONTIERS = prove
 (`moi_s3tb_e1 UNION moi_s3tb_e2 SUBSET frontier moi_s3tb_p1 /\
   moi_s3tb_e1 UNION moi_s3tb_e2 SUBSET frontier moi_s3tb_p2`,
  MP_TAC MOI_S3TB_MODEL_SETS THEN MP_TAC MOI_S3TB_CLOSED THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[]) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[]) THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `interior moi_s3tb_p1 SUBSET {x:real^3 | x$1 < &0}` MP_TAC THENL
     [REWRITE_TAC[GSYM INTERIOR_HALFSPACE_COMPONENT_LE] THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s3tb_e1 UNION moi_s3tb_e2 SUBSET moi_s3tb_p1` THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM; MOI_S3TB_E12] THEN
    MESON_TAC[REAL_LT_REFL];
    SUBGOAL_THEN `interior moi_s3tb_p2 SUBSET {x:real^3 | x$1 > &0}` MP_TAC THENL
     [REWRITE_TAC[GSYM INTERIOR_HALFSPACE_COMPONENT_GE] THEN
      MATCH_MP_TAC SUBSET_INTERIOR THEN
      UNDISCH_TAC `moi_s3tb_p2 SUBSET {x:real^3 | &0 <= x$1}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s3tb_e1 UNION moi_s3tb_e2 SUBSET moi_s3tb_p2` THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM; MOI_S3TB_E12; real_gt] THEN
    MESON_TAC[REAL_LT_REFL]]);;

(* The coordinate isomorphism from the model of pl_solid_torus onto M3.    *)

let MOI_S3TB_K_FACTS = prove
 (`linear moi_s3tb_k /\ linear moi_s3tb_kinv /\
   (!z. moi_s3tb_kinv (moi_s3tb_k z) = z) /\ (!x. moi_s3tb_k (moi_s3tb_kinv x) = x) /\
   IMAGE moi_s3tb_k moi_fps_m = moi_s3tb_m3`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; moi_s3tb_k; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; FSTCART_ADD; SNDCART_ADD;
                FSTCART_CMUL; SNDCART_CMUL];
    REWRITE_TAC[linear; moi_s3tb_kinv; PASTECART_ADD; GSYM PASTECART_CMUL; PASTECART_INJ] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT];
    GEN_TAC THEN REWRITE_TAC[moi_s3tb_k; moi_s3tb_kinv; VECTOR_3] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_INJ] THEN CONJ_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
      REWRITE_TAC[GSYM drop; LIFT_DROP]];
    GEN_TAC THEN REWRITE_TAC[moi_s3tb_k; moi_s3tb_kinv; FSTCART_PASTECART; SNDCART_PASTECART;
                             VECTOR_2; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_IMAGE; moi_fps_m; moi_s3tb_m3; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^(2,1)finite_sum` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[moi_s3tb_k; VECTOR_3] THEN
      UNDISCH_TAC `z IN moi_fps_ann PCROSS interval[--vec 1:real^1,vec 1]` THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; MOI_FPS_ANN; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
      REWRITE_TAC[drop] THEN REAL_ARITH_TAC;
      STRIP_TAC THEN EXISTS_TAC `moi_s3tb_kinv x` THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_s3tb_k; moi_s3tb_kinv; FSTCART_PASTECART; SNDCART_PASTECART;
                    VECTOR_2; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
        REWRITE_TAC[GSYM drop; LIFT_DROP];
        REWRITE_TAC[moi_s3tb_kinv; PASTECART_IN_PCROSS; MOI_FPS_ANN; IN_INTERVAL_1;
                    DROP_NEG; DROP_VEC; VECTOR_2; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: cells.  The rectangles moi_s3tb_sq c s (square) are PL           *)
(* 2-cells (affine image of the standard square, MOI_S5C_CELL_PLH); boxes   *)
(* are PL 3-cells (MOI_S5A_POLYTOPE_CELL); the halves P1, P2 are PL 3-cells *)
(* (three boxes glued twice, MOI_S5V_CELL_UNION); the coordinate map is a  *)
(* PL homeomorphism from the model of pl_solid_torus onto M3.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TB_SQ_AFFINE = prove
 (`!c s. (!z. moi_s3tb_sq c s z =
              (\z:real^2. vector[&0; z$1 / &2; z$2]:real^3) z + vector[c; s; &0]) /\
         linear (\z:real^2. vector[&0; z$1 / &2; z$2]:real^3) /\
         (!z w. moi_s3tb_sq c s z = moi_s3tb_sq c s w ==> z = w) /\
         (!z. (\x:real^3. vector[&2 * (x$2 - s); x$3]:real^2) (moi_s3tb_sq c s z) = z) /\
         (!x. (\x:real^3. vector[&2 * (x$2 - s); x$3]:real^2) x =
              (\x:real^3. vector[&2 * x$2; x$3]:real^2) x + vector[--(&2 * s); &0]) /\
         linear (\x:real^3. vector[&2 * x$2; x$3]:real^2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3tb_sq] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; DIMINDEX_2; FORALL_2] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_3] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC]);;

let MOI_S3TB_SIMPLEX2_R3 = prove
 (`?k:real^3->bool. &2 simplex k`,
  EXISTS_TAC `IMAGE (\z:real^2. vector[z$1; z$2; &0]:real^3)
                    (convex hull {vec 0:real^2,basis 1,basis 2})` THEN
  MP_TAC(ISPECL [`\z:real^2. vector[z$1; z$2; &0]:real^3`;
                 `convex hull {vec 0:real^2,basis 1,basis 2}`; `&2:int`]
    SIMPLEX_LINEAR_IMAGE_EQ) THEN
  REWRITE_TAC[MOI_S27_STD_SIMPLEX_2] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; DIMINDEX_2; FORALL_2] THEN
    REAL_ARITH_TAC]);;

let MOI_S3TB_SQ_INV = prove
 (`!c s (z:real^2). vector[&2 * ((moi_s3tb_sq c s z)$2 - s); (moi_s3tb_sq c s z)$3]:real^2 = z`,
  REWRITE_TAC[moi_s3tb_sq; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_3] THEN
  REAL_ARITH_TAC);;

let MOI_S3TB_SQ_PLH = prove
 (`!c s. pl_homeomorphism
           (interval[--vector[&1;&1]:real^2,vector[&1;&1]],
            IMAGE (moi_s3tb_sq c s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
           (moi_s3tb_sq c s,(\x:real^3. vector[&2 * (x$2 - s); x$3]:real^2))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] MOI_S3TB_SQ_AFFINE) THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
                       MAP_EVERY ASSUME_TAC [el 1 ths; el 2 ths; el 5 ths]) THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_S3TB_SQ_INV];
      SUBGOAL_THEN `moi_s3tb_sq c s =
                    (\z:real^2. (\z:real^2. vector[&0; z$1 / &2; z$2]:real^3) z +
                                vector[c; s; &0])` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; moi_s3tb_sq; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                    VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; MOI_S3TB_SQ_INV];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^2` THEN
      REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
        DISCH_THEN(X_CHOOSE_THEN `w:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
        REWRITE_TAC[MOI_S3TB_SQ_INV] THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN EXISTS_TAC `moi_s3tb_sq c s z` THEN
        REWRITE_TAC[MOI_S3TB_SQ_INV] THEN EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(\x:real^3. vector[&2 * (x$2 - s); x$3]:real^2) =
                    (\x:real^3. (\x:real^3. vector[&2 * x$2; x$3]:real^2) x +
                                vector[--(&2 * s); &0])` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                    VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^2. (\z:real^2. vector[&0; z$1 / &2; z$2]:real^3) z +
                           vector[c; s; &0]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[moi_s3tb_sq; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN REWRITE_TAC[POLYTOPE_INTERVAL]]);;

let MOI_S3TB_SQ_CELL = prove
 (`!c s. pl_cell_with_boundary 2
           (IMAGE (moi_s3tb_sq c s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
           (IMAGE (moi_s3tb_sq c s)
                  (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_S5C_CELL_PLH THEN
  EXISTS_TAC `interval[--vector[&1;&1]:real^2,vector[&1;&1]]` THEN
  EXISTS_TAC `(\x:real^3. vector[&2 * (x$2 - s); x$3]:real^2)` THEN
  REWRITE_TAC[MOI_S3TB_SQ_PLH; MOI_S5T_Q1_CELL; MOI_S3TB_SIMPLEX2_R3]);;

let MOI_S3TB_CELL_BALL = prove
 (`!n (s:real^N->bool) b. pl_cell_with_boundary n s b ==> pl_ball n s`,
  REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]);;

let MOI_S3TB_BOX_CELL = prove
 (`!a b:real^3.
     a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3
     ==> pl_cell_with_boundary 3 (interval[a,b]) (frontier(interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5A_POLYTOPE_CELL THEN
  REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_3; FORALL_3] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3TB_THREE_CELLS = prove
 (`!x y z g1 j1 g2 j2:real^3->bool.
     pl_cell_with_boundary 3 x (frontier x) /\ pl_cell_with_boundary 3 y (frontier y) /\
     pl_cell_with_boundary 3 z (frontier z) /\
     x INTER y = g1 /\ pl_cell_with_boundary 2 g1 j1 /\ g1 SUBSET frontier x /\
     g1 SUBSET frontier y /\
     (x UNION y) INTER z = g2 /\ pl_cell_with_boundary 2 g2 j2 /\ g2 SUBSET frontier x /\
     g2 SUBSET frontier z /\ DISJOINT g1 g2
     ==> pl_ball 3 ((x UNION y) UNION z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3TB_CELL_BALL THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `frontier x:real^3->bool`; `y:real^3->bool`;
                 `frontier y:real^3->bool`; `g1:real^3->bool`; `j1:real^3->bool`]
    MOI_S5V_CELL_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x UNION y:real^3->bool`;
                 `(frontier x UNION frontier y) DIFF (g1 DIFF j1):real^3->bool`;
                 `z:real^3->bool`; `frontier z:real^3->bool`; `g2:real^3->bool`;
                 `j2:real^3->bool`] MOI_S5V_CELL_UNION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[]]);;

let MOI_S3TB_FACES_FR = prove
 (`IMAGE (moi_s3tb_sq (-- &1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
    SUBSET frontier(interval[vector[-- &2; -- &2; -- &1],vector[-- &1; &2; &1]]) /\
   IMAGE (moi_s3tb_sq (-- &1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
    SUBSET frontier(interval[vector[-- &1; &1; -- &1],vector[&0; &2; &1]]) /\
   IMAGE (moi_s3tb_sq (-- &1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
    SUBSET frontier(interval[vector[-- &2; -- &2; -- &1],vector[-- &1; &2; &1]]) /\
   IMAGE (moi_s3tb_sq (-- &1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
    SUBSET frontier(interval[vector[-- &1; -- &2; -- &1],vector[&0; -- &1; &1]]) /\
   DISJOINT
    (IMAGE (moi_s3tb_sq (-- &1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
    (IMAGE (moi_s3tb_sq (-- &1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
   IMAGE (moi_s3tb_sq (&1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
    SUBSET frontier(interval[vector[&1; -- &2; -- &1],vector[&2; &2; &1]]) /\
   IMAGE (moi_s3tb_sq (&1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
    SUBSET frontier(interval[vector[&0; &1; -- &1],vector[&1; &2; &1]]) /\
   IMAGE (moi_s3tb_sq (&1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
    SUBSET frontier(interval[vector[&1; -- &2; -- &1],vector[&2; &2; &1]]) /\
   IMAGE (moi_s3tb_sq (&1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
    SUBSET frontier(interval[vector[&0; -- &2; -- &1],vector[&1; -- &1; &1]]) /\
   DISJOINT
    (IMAGE (moi_s3tb_sq (&1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
    (IMAGE (moi_s3tb_sq (&1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`,
  REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; SUBSET; DISJOINT; EXTENSION; IN_DIFF; IN_INTER;
              NOT_IN_EMPTY; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; MOI_S3TB_SQ_IMAGE] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

(* The two halves are PL 3-balls.                                         *)

let MOI_S3TB_HALVES_BALLS = prove
 (`pl_ball 3 moi_s3tb_p1 /\ pl_ball 3 moi_s3tb_p2`,
  MP_TAC MOI_S3TB_FACES THEN MP_TAC MOI_S3TB_FACES_FR THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[MOI_S3TB_P1_BOXES] THEN MATCH_MP_TAC MOI_S3TB_THREE_CELLS THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (moi_s3tb_sq (-- &1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`;
      `IMAGE (moi_s3tb_sq (-- &1) (&3 / &2))
             (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`;
      `IMAGE (moi_s3tb_sq (-- &1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`;
      `IMAGE (moi_s3tb_sq (-- &1) (--(&3 / &2)))
             (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`];
    REWRITE_TAC[MOI_S3TB_P2_BOXES] THEN MATCH_MP_TAC MOI_S3TB_THREE_CELLS THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (moi_s3tb_sq (&1) (&3 / &2)) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`;
      `IMAGE (moi_s3tb_sq (&1) (&3 / &2))
             (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`;
      `IMAGE (moi_s3tb_sq (&1) (--(&3 / &2))) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`;
      `IMAGE (moi_s3tb_sq (&1) (--(&3 / &2)))
             (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`]] THEN
  ASM_REWRITE_TAC[MOI_S3TB_SQ_CELL] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC MOI_S3TB_BOX_CELL THEN REWRITE_TAC[VECTOR_3] THEN REAL_ARITH_TAC);;

(* The coordinate map is a PL homeomorphism from the model onto M3.        *)

let MOI_S3TB_K_PLH = prove
 (`pl_homeomorphism (moi_fps_m,moi_s3tb_m3) (moi_s3tb_k,moi_s3tb_kinv)`,
  MP_TAC MOI_S3TB_K_FACTS THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    ASM_REWRITE_TAC[o_DEF; IMAGE_ID];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\z. moi_s3tb_k z + vec 0` THEN
    CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    REWRITE_TAC[MOI_FPS_M_PL_POLYHEDRON]]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: a PL map on a rectangle moi_s3tb_sq c s (square) is affine      *)
(* with injective linear part on a small ball of the open square (chart     *)
(* moi_s3tb_sq c s, MOI_S5T_PL_AFFINE_BALL, MOI_S5T_AFFINE_INJ).            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TB_AFF_PT = prove
 (`!c s (g:real^3->real^3).
     pl_map_on (IMAGE (moi_s3tb_sq c s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) g /\
     (!x x'. x IN IMAGE (moi_s3tb_sq c s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
             x' IN IMAGE (moi_s3tb_sq c s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
             g x = g x' ==> x = x')
     ==> ?z0 rho (l:real^2->real^3) y.
           &0 < rho /\ ball(z0,rho) SUBSET interval(--vector[&1;&1],vector[&1;&1]) /\
           linear l /\ (!v. l v = vec 0 ==> v = vec 0) /\
           !z. z IN ball(z0,rho) ==> g(moi_s3tb_sq c s z) = l z + y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] MOI_S3TB_SQ_PLH) THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_map_on (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
                          ((g:real^3->real^3) o moi_s3tb_sq c s)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `IMAGE (moi_s3tb_sq c s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:real^3->real^3) o moi_s3tb_sq c s`;
                 `interval[--vector[&1;&1]:real^2,vector[&1;&1]]`;
                 `interval(--vector[&1;&1]:real^2,vector[&1;&1])`] MOI_S5T_PL_AFFINE_BALL) THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN ANTS_TAC THENL
   [REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^2` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`z0:real^2`; `rho:real`; `l:real^2->real^3`; `y:real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5T_AFFINE_INJ THEN
    MAP_EVERY EXISTS_TAC [`(g:real^3->real^3) o moi_s3tb_sq c s`;
                          `interval[--vector[&1;&1]:real^2,vector[&1;&1]]`;
                          `y:real^3`; `z0:real^2`; `rho:real`] THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:real^2`; `z':real^2`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`c:real`; `s:real`] MOI_S3TB_SQ_AFFINE) THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "x")) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
      ASM_REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `y:real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[o_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: the two sides of a flat point of a disk shared by the            *)
(* frontiers of b and hb.  OPP_NORMALS: two open half-balls of a common     *)
(* point that do not meet have opposite normals.  LOCAL_EXT: at a point     *)
(* where the disk is the flat image of an injective affine chart, the       *)
(* affine continuation of the chart along the inner normal of hb maps the  *)
(* positive side into the interior of hb and the negative side into the    *)
(* interior of b (CHART_FLAT and FLAT_ORIENT for both balls).              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TB_OPP_NORMALS = prove
 (`!(u:real^3) v q r.
     ~(u = vec 0) /\ ~(v = vec 0) /\ &0 < r /\
     (!x. x IN ball(q,r) ==> ~(&0 < u dot (x - q) /\ &0 < v dot (x - q)))
     ==> ?c. &0 < c /\ v = --(c % u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(u:real^3) /\ &0 < norm(v:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `a:real^3 = inv(norm u) % u + inv(norm v) % v` THEN
  ABBREV_TAC `sg = ((u:real^3) dot v) / (norm u * norm v)` THEN
  SUBGOAL_THEN `(u:real^3) dot a = norm u * (&1 + sg) /\ (v:real^3) dot a = norm v * (&1 + sg) /\
                a dot a = &2 * (&1 + sg)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "sg"] THEN
    REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_SQUARE_NORM] THEN
    REWRITE_TAC[DOT_SYM] THEN
    UNDISCH_TAC `&0 < norm(u:real^3)` THEN UNDISCH_TAC `&0 < norm(v:real^3)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^3 = vec 0` THENL
   [EXISTS_TAC `norm(v:real^3) / norm(u:real^3)` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
    UNDISCH_TAC `inv(norm u) % u + inv(norm v) % v = (a:real^3)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(v:real^3) % (inv(norm u) % u + inv(norm v) % v) = vec 0` MP_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; real_div] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + sg` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (a:real^3) dot a` MP_TAC THENL
     [ASM_REWRITE_TAC[DOT_POS_LT]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(a:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q + (r / (&2 * norm(a:real^3))) % a`) THEN
  REWRITE_TAC[IN_BALL; NORM_ARITH `dist(q:real^3,q + y) = norm y`;
              VECTOR_ARITH `(q + y) - q:real^3 = y`; DOT_RMUL; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_MUL; REAL_ABS_NORM;
               REAL_LT_IMP_LE; REAL_ARITH `&0 < r ==> abs r = r`] THEN
  MATCH_MP_TAC(TAUT `p /\ q /\ r ==> (p ==> ~(q /\ r)) ==> s`) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `r / (&2 * norm(a:real^3)) * norm a = r / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < norm(a:real^3)` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &2`]]);;

let MOI_S3TB_LOCAL_EXT = prove
 (`!(b:real^3->bool) hb d (l:real^2->real^3) y z0 rho w0 w1.
     pl_ball 3 b /\ pl_ball 3 hb /\ DISJOINT (interior b) (interior hb) /\
     d SUBSET frontier b /\ d SUBSET frontier hb /\
     linear l /\ (!v. l v = vec 0 ==> v = vec 0) /\ &0 < rho /\
     (!z. z IN ball(z0,rho) ==> l z + y IN d) /\
     w0 IN frontier b /\ ~(w0 IN d) /\ w1 IN frontier hb /\ ~(w1 IN d)
     ==> ?wv r. &0 < r /\ (!v t. l v + t % wv = vec 0 ==> t = &0) /\
                !v t. dist(v,z0) < r /\ abs t < r
                      ==> (&0 < t ==> l v + y + t % wv IN interior hb) /\
                          (t < &0 ==> l v + y + t % wv IN interior b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `b:real^3->bool` MOI_S5T_BALL_SIDES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `hb:real^3->bool` MOI_S5T_BALL_SIDES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\z:real^2. (l:real^2->real^3) z + y) (ball(z0,rho)) SUBSET d`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^2->real^3) z0 + y IN d` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "z")) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier b:real^3->bool`; `\z:real^2. (l:real^2->real^3) z + y`;
                 `z0:real^2`; `rho:real`; `l:real^2->real^3`; `y:real^3`; `w0:real^3`]
    MOI_S5T_CHART_FLAT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (\z:real^2. (l:real^2->real^3) z + y) (ball(z0,rho)) SUBSET d` THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET frontier b` THEN UNDISCH_TAC `~((w0:real^3) IN d)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:real^3` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`frontier hb:real^3->bool`; `\z:real^2. (l:real^2->real^3) z + y`;
                 `z0:real^2`; `rho:real`; `l:real^2->real^3`; `y:real^3`; `w1:real^3`]
    MOI_S5T_CHART_FLAT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (\z:real^2. (l:real^2->real^3) z + y) (ball(z0,rho)) SUBSET d` THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET frontier hb` THEN UNDISCH_TAC `~((w1:real^3) IN d)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:real^3` (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `q = (l:real^2->real^3) z0 + y` THEN
  SUBGOAL_THEN `(q:real^3) IN frontier b /\ q IN frontier hb` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^3) IN d` THEN UNDISCH_TAC `(d:real^3->bool) SUBSET frontier b` THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET frontier hb` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `q:real^3`; `n1:real^3`; `r1:real`] MOI_S5T_FLAT_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nb:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sb"))) THEN
  MP_TAC(ISPECL [`hb:real^3->bool`; `q:real^3`; `n2:real^3`; `r2:real`] MOI_S5T_FLAT_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nh:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh"))) THEN
  SUBGOAL_THEN `~(nb:real^3 = vec 0) /\ ~(nh:real^3 = vec 0) /\
                (!v. nb dot (l:real^2->real^3) v = &0) /\ (!v. nh dot (l:real^2->real^3) v = &0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
        is_disj(concl th) && can (find_term (fun t -> t = `nb:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[VECTOR_NEG_EQ_0];
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
        is_disj(concl th) && can (find_term (fun t -> t = `nh:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[VECTOR_NEG_EQ_0];
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
        is_disj(concl th) && can (find_term (fun t -> t = `nb:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[DOT_LNEG; REAL_NEG_0];
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
        is_disj(concl th) && can (find_term (fun t -> t = `nh:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[DOT_LNEG; REAL_NEG_0]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nb:real^3`; `nh:real^3`; `q:real^3`; `min r1 r2`] MOI_S3TB_OPP_NORMALS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN STRIP_TAC THEN
    REMOVE_THEN "sb" (MP_TAC o SPEC `x:real^3`) THEN
    REMOVE_THEN "sh" (MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `DISJOINT (interior b) (interior hb:real^3->bool)` THEN
    REWRITE_TAC[IN_DISJOINT] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (fun th -> ASSUME_TAC(REWRITE_RULE[DOT_RNEG; DOT_RMUL]
                 (AP_TERM `(dot) (nb:real^3)` th))))) THEN
  MP_TAC(ISPEC `l:real^2->real^3` LINEAR_BOUNDED_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (nh:real^3) dot nh /\ &0 < (nb:real^3) dot nb` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `nh:real^3` THEN
  EXISTS_TAC `min r1 r2 / (bb + norm(nh:real^3) + &1)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    MP_TAC(ISPEC `nh:real^3` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`v:real^2`; `t:real`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(nh:real^3) dot ((l:real^2->real^3) v + t % nh) = &0` MP_TAC THENL
     [ASM_REWRITE_TAC[DOT_RZERO]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_ADD_LID; REAL_ENTIRE] THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^2`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((l:real^2->real^3) v + y + t % nh) - q = l(v - z0) + t % nh` ASSUME_TAC THENL
   [SUBGOAL_THEN `(l:real^2->real^3)(v - z0) = l v - l z0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[LINEAR_SUB]; ALL_TAC] THEN
    EXPAND_TAC "q" THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^2->real^3) v + y + t % nh IN ball(q,r1) /\
                l v + y + t % nh IN ball(q,r2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    REWRITE_TAC[dist] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `!w. x <= w /\ w < min a b ==> x < a /\ x < b`) THEN
    EXISTS_TAC `bb * norm(v - z0:real^2) + abs t * norm(nh:real^3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH `norm(a:real^3) <= x /\ norm(b:real^3) <= y ==> norm(a + b) <= x + y`) THEN
      ASM_REWRITE_TAC[NORM_MUL; REAL_LE_REFL];
      SUBGOAL_THEN `norm(v - z0:real^2) < min r1 r2 / (bb + norm(nh:real^3) + &1)` ASSUME_TAC THENL
       [UNDISCH_TAC `dist(v:real^2,z0) < min r1 r2 / (bb + norm(nh:real^3) + &1)` THEN
        REWRITE_TAC[dist];
        ALL_TAC] THEN
      ABBREV_TAC `rr = min r1 r2 / (bb + norm(nh:real^3) + &1)` THEN
      SUBGOAL_THEN `min r1 r2 = rr * (bb + norm(nh:real^3) + &1)` SUBST1_TAC THENL
       [EXPAND_TAC "rr" THEN MP_TAC(ISPEC `nh:real^3` NORM_POS_LE) THEN
        UNDISCH_TAC `&0 < bb` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < rr` ASSUME_TAC THENL
       [MP_TAC(ISPEC `v - z0:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `bb * x <= bb * rr /\ t * n <= rr * n /\ &0 < rr ==> bb * x + t * n < rr * (bb + n + &1)`) THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_IMP_LE; REAL_LE_RMUL; NORM_POS_LE]];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [REMOVE_THEN "sh" (MP_TAC o SPEC `(l:real^2->real^3) v + y + t % nh`) THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_ADD_LID] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "sb" (MP_TAC o SPEC `(l:real^2->real^3) v + y + t % nh`) THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_ADD_LID] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_MUL_RNEG; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: the orientation (the gap of p.218).  Two local extensions        *)
(* gg0, gg1 of a PL homeomorphism ff: u -> w across two disjoint disks of   *)
(* frontier u, each mapping the u-side into w, have the sign of ff at some  *)
(* interior point (ext2's LOCAL_D0); ff has one sign on the connected      *)
(* interior of u, and each gg one sign on its ball (LOCAL_SIGN); hence     *)
(* gg0 and gg1 have the same orientation.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TB_SIGN_TRANS = prove
 (`!a b c. &0 < a * b /\ &0 < b * c ==> &0 < a * c`,
  REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC);;

let MOI_S3TB_ORIENT = prove
 (mk_imp(MOI_S35_LOCAL_SIGN,
  `!(u:real^3->bool) w d0 j0 d1 j1 e0 i0 e1 i1 (g0:real^3->real^3) g0'
     (g1:real^3->real^3) g1' (ff:real^3->real^3) ff' (gg0:real^3->real^3) gg1
     x0 r0 x1 r1.
     pl_ball 3 u /\ pl_ball 3 w /\
     pl_cell_with_boundary 2 d0 j0 /\ pl_cell_with_boundary 2 d1 j1 /\
     d0 SUBSET frontier u /\ d1 SUBSET frontier u /\ DISJOINT d0 d1 /\
     pl_cell_with_boundary 2 e0 i0 /\ pl_cell_with_boundary 2 e1 i1 /\
     e0 SUBSET frontier w /\ e1 SUBSET frontier w /\ DISJOINT e0 e1 /\
     pl_homeomorphism (d0,e0) (g0,g0') /\ pl_homeomorphism (d1,e1) (g1,g1') /\
     pl_homeomorphism (u,w) (ff,ff') /\
     (!x. x IN d0 ==> ff x = g0 x) /\ (!x. x IN d1 ==> ff x = g1 x) /\
     ~(ball(x0,r0) INTER (d0 DIFF j0) = {}) /\
     pl_map_on (ball(x0,r0)) gg0 /\
     (!x y. x IN ball(x0,r0) /\ y IN ball(x0,r0) /\ gg0 x = gg0 y ==> x = y) /\
     (!x. x IN ball(x0,r0) INTER d0 ==> gg0 x = g0 x) /\
     IMAGE gg0 (ball(x0,r0) INTER u) SUBSET w /\
     ~(ball(x1,r1) INTER (d1 DIFF j1) = {}) /\
     pl_map_on (ball(x1,r1)) gg1 /\
     (!x y. x IN ball(x1,r1) /\ y IN ball(x1,r1) /\ gg1 x = gg1 y ==> x = y) /\
     (!x. x IN ball(x1,r1) INTER d1 ==> gg1 x = g1 x) /\
     IMAGE gg1 (ball(x1,r1) INTER u) SUBSET w
     ==> moi_s35_same_orient gg0 (ball(x0,r0)) gg1 (ball(x1,r1))`),
  DISCH_THEN(LABEL_TAC "sign") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `w:real^3->bool`; `d0:real^3->bool`; `j0:real^3->bool`;
                 `d1:real^3->bool`; `j1:real^3->bool`; `e0:real^3->bool`; `i0:real^3->bool`;
                 `e1:real^3->bool`; `i1:real^3->bool`; `g0:real^3->real^3`;
                 `g0':real^3->real^3`; `ball(x0:real^3,r0)`; `gg0:real^3->real^3`;
                 `ff:real^3->real^3`; `ff':real^3->real^3`] MOI_S5T_LOCAL_D0) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `xa:real^3` (X_CHOOSE_THEN `ma:real^3->real^3`
    (X_CHOOSE_THEN `ya:real^3` (X_CHOOSE_THEN `mma:real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `w:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`;
                 `d0:real^3->bool`; `j0:real^3->bool`; `e1:real^3->bool`; `i1:real^3->bool`;
                 `e0:real^3->bool`; `i0:real^3->bool`; `g1:real^3->real^3`;
                 `g1':real^3->real^3`; `ball(x1:real^3,r1)`; `gg1:real^3->real^3`;
                 `ff:real^3->real^3`; `ff':real^3->real^3`] MOI_S5T_LOCAL_D0) THEN
  ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `xb:real^3` (X_CHOOSE_THEN `mb:real^3->real^3`
    (X_CHOOSE_THEN `yb:real^3` (X_CHOOSE_THEN `mmb:real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `connected(interior u:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `u:real^3->bool` MOI_S5T_BALL_SIDES) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(matrix(ma:real^3->real^3)) * det(matrix(mb:real^3->real^3))`
  ASSUME_TAC THENL
   [USE_THEN "sign" MATCH_MP_TAC THEN
    EXISTS_TAC `ff:real^3->real^3` THEN EXISTS_TAC `interior u:real^3->bool` THEN
    MAP_EVERY EXISTS_TAC [`xa:real^3`; `xb:real^3`] THEN ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
    UNDISCH_TAC `pl_homeomorphism (u,w) (ff:real^3->real^3,ff')` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      MP_TAC(ISPEC `u:real^3->bool` INTERIOR_SUBSET) THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_same_orient] THEN
  MAP_EVERY X_GEN_TAC [`p:real^3`; `p':real^3`; `m0:real^3->real^3`; `m1:real^3->real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < det(matrix(m0:real^3->real^3)) * det(matrix(mma:real^3->real^3)) /\
                &0 < det(matrix(mmb:real^3->real^3)) * det(matrix(m1:real^3->real^3))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "sign" MATCH_MP_TAC THENL
     [EXISTS_TAC `gg0:real^3->real^3` THEN EXISTS_TAC `ball(x0:real^3,r0)` THEN
      MAP_EVERY EXISTS_TAC [`p:real^3`; `ya:real^3`];
      EXISTS_TAC `gg1:real^3->real^3` THEN EXISTS_TAC `ball(x1:real^3,r1)` THEN
      MAP_EVERY EXISTS_TAC [`yb:real^3`; `p':real^3`]] THEN
    ASM_SIMP_TAC[OPEN_BALL; CONNECTED_BALL; PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3TB_SIGN_TRANS THEN
  EXISTS_TAC `det(matrix(mmb:real^3->real^3))` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3TB_SIGN_TRANS THEN
  EXISTS_TAC `det(matrix(mb:real^3->real^3))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MOI_S3TB_SIGN_TRANS THEN
  EXISTS_TAC `det(matrix(ma:real^3->real^3))` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3TB_SIGN_TRANS THEN
  EXISTS_TAC `det(matrix(mma:real^3->real^3))` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: two PL n-cells are PL homeomorphic (CELL_PLH2); the local        *)
(* extension at one rectangle moi_s3tb_sq 0 s (square) of a PL             *)
(* homeomorphism g onto a disk d shared by frontier b and frontier hb (GG):  *)
(* an affine map on a small ball around a point of the open rectangle that *)
(* agrees with g on the rectangle and maps x1 > 0 into interior hb and      *)
(* x1 < 0 into interior b.                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TB_CELL_PLH2 = prove
 (`!n (a:real^N->bool) ja (c:real^N->bool) jc.
     pl_cell_with_boundary n a ja /\ pl_cell_with_boundary n c jc
     ==> ?f g. pl_homeomorphism (a,c) (f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k1:real^N->bool` (X_CHOOSE_THEN `f1:real^N->real^N`
      (X_CHOOSE_THEN `g1:real^N->real^N` STRIP_ASSUME_TAC)))
    (X_CHOOSE_THEN `k2:real^N->bool` (X_CHOOSE_THEN `f2:real^N->real^N`
      (X_CHOOSE_THEN `g2:real^N->real^N` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k1:real^N->bool`; `k2:real^N->bool`; `&n:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^N` (X_CHOOSE_THEN `q:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  ASM_MESON_TAC[PL_HOMEOMORPHISM_COMPOSE; PL_HOMEOMORPHISM_SYM]);;

let MOI_S3TB_PI_BOUND = prove
 (`!s (x:real^3) x0.
     norm(vector[&2 * (x$2 - s); x$3] - vector[&2 * (x0$2 - s); x0$3]:real^2)
     <= &3 * norm(x - x0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `vector[&2 * ((x:real^3)$2 - s); x$3] -
                 vector[&2 * ((x0:real^3)$2 - s); x0$3]:real^2`
    NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
  MP_TAC(ISPECL [`x - x0:real^3`; `2`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`x - x0:real^3`; `3`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[DIMINDEX_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let MOI_S3TB_GG = prove
 (`!(b:real^3->bool) hb d w (g:real^3->real^3) g' s.
     pl_ball 3 b /\ pl_ball 3 hb /\ DISJOINT (interior b) (interior hb) /\
     d SUBSET frontier b /\ d SUBSET frontier hb /\
     w IN frontier b /\ w IN frontier hb /\ ~(w IN d) /\
     pl_homeomorphism
       (IMAGE (moi_s3tb_sq (&0) s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]),d) (g,g')
     ==> ?x0 r (gg:real^3->real^3).
           &0 < r /\ r <= &1 /\
           x0 IN IMAGE (moi_s3tb_sq (&0) s)
                       (interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\
           pl_map_on (ball(x0,r)) gg /\
           (!x y. x IN ball(x0,r) /\ y IN ball(x0,r) /\ gg x = gg y ==> x = y) /\
           (!x. x IN ball(x0,r) /\
                x IN IMAGE (moi_s3tb_sq (&0) s)
                           (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
                ==> gg x = g x) /\
           (!x. x IN ball(x0,r) /\ &0 < x$1 ==> gg x IN interior hb) /\
           (!x. x IN ball(x0,r) /\ x$1 < &0 ==> gg x IN interior b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`&0`; `s:real`; `g:real^3->real^3`] MOI_S3TB_AFF_PT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^2` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(z0,rho)
                           ==> moi_s3tb_sq (&0) s z IN
                               IMAGE (moi_s3tb_sq (&0) s)
                                     (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    MP_TAC(ISPECL [`--vector[&1;&1]:real^2`; `vector[&1;&1]:real^2`]
      INTERVAL_OPEN_SUBSET_CLOSED) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `hb:real^3->bool`; `d:real^3->bool`; `l:real^2->real^3`;
                 `y:real^3`; `z0:real^2`; `rho:real`; `w:real^3`; `w:real^3`]
    MOI_S3TB_LOCAL_EXT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `y:real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3)
                   (IMAGE (moi_s3tb_sq (&0) s)
                          (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = d` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `wv:real^3` (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `r = min (&1) (min (rho / &3) (r0 / &3))` THEN
  SUBGOAL_THEN `&0 < r /\ r <= &1 /\ &3 * r <= rho /\ &3 * r <= r0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN UNDISCH_TAC `&0 < rho` THEN UNDISCH_TAC `&0 < r0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x0 = moi_s3tb_sq (&0) s z0` THEN
  SUBGOAL_THEN `(x0:real^3)$1 = &0 /\ vector[&2 * (x0$2 - s); x0$3]:real^2 = z0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN REWRITE_TAC[MOI_S3TB_SQ_INV] THEN
    REWRITE_TAC[moi_s3tb_sq; VECTOR_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN ball(x0,r)
               ==> dist(vector[&2 * (x$2 - s); x$3]:real^2,z0) < rho /\
                   dist(vector[&2 * (x$2 - s); x$3]:real^2,z0) < r0 /\ abs(x$1) < r0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real`; `x:real^3`; `x0:real^3`] MOI_S3TB_PI_BOUND) THEN
    MP_TAC(ISPECL [`x - x0:real^3`; `1`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[dist] THEN
    UNDISCH_TAC `dist(x0:real^3,x) < r` THEN REWRITE_TAC[dist; NORM_SUB] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lm = \x:real^3. (l:real^2->real^3) (vector[&2 * x$2; x$3]:real^2) + x$1 % wv` THEN
  SUBGOAL_THEN `linear (lm:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "lm" THEN MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:real^3. (l:real^2->real^3) (vector[&2 * x$2; x$3]:real^2)) =
                    l o (\x:real^3. vector[&2 * x$2; x$3]:real^2)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. (l:real^2->real^3) (vector[&2 * (x$2 - s); x$3]) + y + x$1 % wv =
                           lm x + (y - l(vector[&2 * s; &0]))` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN EXPAND_TAC "lm" THEN
    SUBGOAL_THEN `vector[&2 * ((x:real^3)$2 - s); x$3]:real^2 =
                  vector[&2 * x$2; x$3] - vector[&2 * s; &0]` SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_SUB_COMPONENT] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`x0:real^3`; `r:real`;
    `\x:real^3. (l:real^2->real^3) (vector[&2 * (x$2 - s); x$3]) + y + x$1 % wv`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    EXPAND_TAC "x0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `ball(z0:real^2,rho) SUBSET interval(--vector[&1;&1],vector[&1;&1])` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. (lm:real^3->real^3) x +
                            (y - (l:real^2->real^3)(vector[&2 * s; &0]))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `x':real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(lm:real^3->real^3) (x - x') = vec 0` MP_TAC THENL
     [ASM_SIMP_TAC[LINEAR_SUB] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        can (find_term (fun t -> t = `x':real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "lm" THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x - x':real^3)$1 = &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && is_imp(snd(strip_forall(concl th))) &&
        can (find_term (fun t -> t = `vec 0:real^3`)) (concl th))) THEN
      EXISTS_TAC `vector[&2 * (x - x':real^3)$2; (x - x')$3]:real^2` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `vector[&2 * (x - x':real^3)$2; (x - x')$3]:real^2 = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && is_imp(snd(strip_forall(concl th))) &&
        fst(dest_var(fst(dest_forall(concl th)))) = "v")) THEN
      UNDISCH_TAC `(l:real^2->real^3) (vector[&2 * (x - x':real^3)$2; (x - x')$3]) +
                   (x - x')$1 % wv = vec 0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    UNDISCH_TAC `(x - x':real^3)$1 = &0` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT; DIMINDEX_3; FORALL_3;
                VECTOR_SUB_COMPONENT] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[MOI_S3TB_SQ_INV] THEN
    SUBGOAL_THEN `(moi_s3tb_sq (&0) s z)$1 = &0` SUBST1_TAC THENL
     [REWRITE_TAC[moi_s3tb_sq; VECTOR_3]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `y:real^3`)) (concl th) &&
      can (find_term (fun t -> t = `rho:real`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `moi_s3tb_sq (&0) s z` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `r0:real`)) (concl th) &&
      can (find_term (fun t -> t = `rho:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[MOI_S3TB_SQ_INV] THEN REWRITE_TAC[IN_BALL] THEN SIMP_TAC[DIST_SYM];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `r0:real`)) (concl th) &&
      can (find_term (fun t -> t = `rho:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vector[&2 * ((x:real^3)$2 - s); x$3]:real^2`; `(x:real^3)$1`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `interior hb:real^3->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `r0:real`)) (concl th) &&
      can (find_term (fun t -> t = `rho:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vector[&2 * ((x:real^3)$2 - s); x$3]:real^2`; `(x:real^3)$1`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `interior hb:real^3->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 7: gluing and the main theorem.  GLUE: PL homeomorphisms of the two *)
(* halves onto b and hb that agree on E1 UNION E2, with b INTER hb the      *)
(* image of E1 UNION E2, glue to a PL homeomorphism of M3 onto b UNION hb;  *)
(* with the coordinate map, b UNION hb is a PL solid torus.                 *)
(* HANDLE_SOLID_TORUS: ONE_DISK_EXT on the first half, the local extensions *)
(* at both disks, the orientation, TWO_DISK_EXT on the second half, and     *)
(* GLUE.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3TB_GLUE = prove
 (`!(b:real^3->bool) hb d1 d2 (f1:real^3->real^3) f1' f2 f2'.
     pl_homeomorphism (moi_s3tb_p1,b) (f1,f1') /\ pl_homeomorphism (moi_s3tb_p2,hb) (f2,f2') /\
     (!x. x IN moi_s3tb_e1 UNION moi_s3tb_e2 ==> f2 x = f1 x) /\
     IMAGE f1 (moi_s3tb_e1 UNION moi_s3tb_e2) = d1 UNION d2 /\
     b INTER hb = d1 UNION d2
     ==> pl_solid_torus (b UNION hb)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  MP_TAC MOI_S3TB_MODEL_SETS THEN MP_TAC MOI_S3TB_CLOSED THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[]) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[]) THEN
  ABBREV_TAC `ff = \x:real^3. if x$1 <= &0 then (f1:real^3->real^3) x else f2 x` THEN
  SUBGOAL_THEN `(!x:real^3. x IN moi_s3tb_p1 ==> ff x = (f1:real^3->real^3) x) /\
                (!x:real^3. x IN moi_s3tb_p2 ==> ff x = (f2:real^3->real^3) x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [ASM SET_TAC[];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `moi_s3tb_p2 INTER {x:real^3 | x$1 = &0} = moi_s3tb_e1 UNION moi_s3tb_e2` THEN
      UNDISCH_TAC `moi_s3tb_p2 SUBSET {x:real^3 | &0 <= x$1}` THEN
      UNDISCH_TAC `(x:real^3)$1 <= &0` THEN UNDISCH_TAC `(x:real^3) IN moi_s3tb_p2` THEN
      REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_ELIM_THM] THEN
      MESON_TAC[REAL_LE_ANTISYM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on moi_s3tb_m3 (ff:real^3->real^3)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SYM(CONJUNCT1 MOI_S3TB_MODEL_SETS)] THEN
    MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `f1:real^3->real^3` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `f2:real^3->real^3` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBSET_UNION];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBSET_UNION]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ff:real^3->real^3) moi_s3tb_m3 = b UNION hb` ASSUME_TAC THENL
   [REWRITE_TAC[SYM(CONJUNCT1 MOI_S3TB_MODEL_SETS)] THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    SUBGOAL_THEN `IMAGE (ff:real^3->real^3) moi_s3tb_p1 = IMAGE f1 moi_s3tb_p1 /\
                  IMAGE (ff:real^3->real^3) moi_s3tb_p2 = IMAGE f2 moi_s3tb_p2`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^3. x IN moi_s3tb_m3 /\ y IN moi_s3tb_m3 /\
                             (ff:real^3->real^3) x = ff y ==> x = y`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `!x y:real^3. x IN moi_s3tb_p1 /\ y IN moi_s3tb_p2 /\
                               (f1:real^3->real^3) x = f2 y ==> x = y` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(f1:real^3->real^3) x IN d1 UNION d2` ASSUME_TAC THENL
       [UNDISCH_TAC `b INTER hb = (d1:real^3->bool) UNION d2` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN moi_s3tb_e1 UNION moi_s3tb_e2 /\
                    (y:real^3) IN moi_s3tb_e1 UNION moi_s3tb_e2` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `(f1:real^3->real^3) x IN d1 UNION d2` THEN
          UNDISCH_TAC `IMAGE (f1:real^3->real^3) (moi_s3tb_e1 UNION moi_s3tb_e2) = d1 UNION d2` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
          DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `(x:real^3) = x'` (fun th -> ASM_REWRITE_TAC[th]) THEN
          FIRST_X_ASSUM(fun th -> MP_TAC(AP_TERM `f1':real^3->real^3` th)) THEN
          ASM_SIMP_TAC[] THEN ASM SET_TAC[];
          UNDISCH_TAC `(f1:real^3->real^3) x IN d1 UNION d2` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `IMAGE (f1:real^3->real^3) (moi_s3tb_e1 UNION moi_s3tb_e2) = d1 UNION d2` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
          DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `(y:real^3) = y'` (fun th -> ASM_REWRITE_TAC[th]) THEN
          SUBGOAL_THEN `(f2:real^3->real^3) y = f2 y'` MP_TAC THENL
           [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC[];
            DISCH_THEN(MP_TAC o AP_TERM `f2':real^3->real^3`) THEN ASM_SIMP_TAC[] THEN
            ASM SET_TAC[]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f1:real^3->real^3) x = f1 y` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(MP_TAC o AP_TERM `f1':real^3->real^3`) THEN ASM_SIMP_TAC[] THEN
        ASM SET_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `((x:real^3) IN moi_s3tb_p1 \/ x IN moi_s3tb_p2) /\
                  ((y:real^3) IN moi_s3tb_p1 \/ y IN moi_s3tb_p2)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `(ff:real^3->real^3) x = ff y` THEN ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `f1':real^3->real^3`) THEN ASM_SIMP_TAC[];
      UNDISCH_TAC `(ff:real^3->real^3) x = ff y` THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `(ff:real^3->real^3) x = ff y` THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `(ff:real^3->real^3) x = ff y` THEN ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `f2':real^3->real^3`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s3tb_m3`; `ff:real^3->real^3`; `b UNION hb:real^3->bool`]
    HOMEOMORPHISM_COMPACT) THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `gg:real^3->real^3`) THEN
  SUBGOAL_THEN `pl_homeomorphism (moi_s3tb_m3,b UNION hb) (ff:real^3->real^3,gg)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pl_solid_torus] THEN
  EXISTS_TAC `(ff:real^3->real^3) o moi_s3tb_k` THEN
  EXISTS_TAC `moi_s3tb_kinv o (gg:real^3->real^3)` THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s3tb_m3` THEN
  ASM_REWRITE_TAC[REWRITE_RULE[moi_fps_m; moi_fps_ann] MOI_S3TB_K_PLH]);;

let MOI_S3TB_SQ_IMAGE_OPEN = prove
 (`!c s (x:real^3).
     x IN IMAGE (moi_s3tb_sq c s) (interval(--vector[&1;&1]:real^2,vector[&1;&1])) <=>
     x$1 = c /\ abs(x$2 - s) < &1 / &2 /\ abs(x$3) < &1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT; VECTOR_2;
              moi_s3tb_sq] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_3] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `vector[&2 * ((x:real^3)$2 - s); x$3]:real^2` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S3TB_OPEN_RIM = prove
 (`!c s (x:real^3).
     x IN IMAGE (moi_s3tb_sq c s) (interval(--vector[&1;&1]:real^2,vector[&1;&1]))
     ==> x IN IMAGE (moi_s3tb_sq c s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
         ~(x IN IMAGE (moi_s3tb_sq c s)
                  (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`--vector[&1;&1]:real^2`; `vector[&1;&1]:real^2`]
      INTERVAL_OPEN_SUBSET_CLOSED) THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z':real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^2) = z'` SUBST_ALL_TAC THENL
     [MP_TAC(SPECL [`c:real`; `s:real`] MOI_S3TB_SQ_AFFINE) THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC MOI_S5T_Q1_CELL THEN STRIP_TAC THEN
    UNDISCH_TAC `(z':real^2) IN interval(--vector[&1;&1],vector[&1;&1])` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT; VECTOR_2] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z':real^2` o check (fun th ->
      is_forall(concl th) && is_iff(snd(dest_forall(concl th))))) THEN
    SUBGOAL_THEN `(z':real^2) IN interval[--vector[&1;&1],vector[&1;&1]]` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S3TB_NEAR_E = prove
 (`!s x0 r (x:real^3).
     (s = &3 / &2 \/ s = --(&3 / &2)) /\
     x0 IN IMAGE (moi_s3tb_sq (&0) s) (interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\
     r <= &1 /\ x IN ball(x0,r)
     ==> (x IN moi_s3tb_p1
          ==> x$1 < &0 \/
              x IN IMAGE (moi_s3tb_sq (&0) s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
         (x IN moi_s3tb_p2
          ==> &0 < x$1 \/
              x IN IMAGE (moi_s3tb_sq (&0) s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S3TB_SQ_IMAGE_OPEN; MOI_S3TB_SQ_IMAGE; IN_BALL] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`x0 - x:real^3`; `2`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[DIMINDEX_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `dist(x0:real^3,x) < r` THEN REWRITE_TAC[dist] THEN
  REWRITE_TAC[moi_s3tb_p1; moi_s3tb_p2; moi_s3tb_m3; IN_ELIM_THM] THEN
  REPEAT DISCH_TAC THEN CONJ_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S3TB_CELL_NONEMPTY = prove
 (`!(s:real^N->bool) b. pl_cell_with_boundary 2 s b ==> ~(s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN UNDISCH_TAC `IMAGE (f:real^N->real^N) k = s` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM AFF_DIM_POS_LE] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN INT_ARITH_TAC);;

let MOI_S3TB_GG_SIDES = prove
 (`!(b:real^3->bool) hb d s x0 r (gg:real^3->real^3) (g:real^3->real^3).
     (s = &3 / &2 \/ s = --(&3 / &2)) /\
     x0 IN IMAGE (moi_s3tb_sq (&0) s) (interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\
     r <= &1 /\
     (!x. x IN ball(x0,r) /\
          x IN IMAGE (moi_s3tb_sq (&0) s) (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
          ==> gg x = g x) /\
     (!x. x IN ball(x0,r) /\ &0 < x$1 ==> gg x IN interior hb) /\
     (!x. x IN ball(x0,r) /\ x$1 < &0 ==> gg x IN interior b) /\
     IMAGE g (IMAGE (moi_s3tb_sq (&0) s)
                    (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = d /\
     d SUBSET b /\ d SUBSET hb
     ==> IMAGE gg (ball(x0,r) INTER moi_s3tb_p1) SUBSET b /\
         IMAGE gg (ball(x0,r) INTER moi_s3tb_p2) SUBSET hb`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
  ABBREV_TAC `e = IMAGE (moi_s3tb_sq (&0) s)
                        (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `x0:real^3`; `r:real`; `x:real^3`] MOI_S3TB_NEAR_E) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(DISJ_CASES_TAC o CONJUNCT1); DISCH_THEN(DISJ_CASES_TAC o CONJUNCT2)] THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(gg:real^3->real^3) x = g x` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN e` THEN UNDISCH_TAC `IMAGE (g:real^3->real^3) e = d` THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET b` THEN SET_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(gg:real^3->real^3) x = g x` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN e` THEN UNDISCH_TAC `IMAGE (g:real^3->real^3) e = d` THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET hb` THEN SET_TAC[]]);;

let HANDLE_SOLID_TORUS = prove
 (MOI_S30_HANDLE_SOLID_TORUS,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sign")
    (CONJUNCTS_THEN2 (LABEL_TAC "one") (LABEL_TAC "two"))) THEN
  MAP_EVERY X_GEN_TAC [`b:real^3->bool`; `hb:real^3->bool`; `d1:real^3->bool`;
                       `j1:real^3->bool`; `d2:real^3->bool`; `j2:real^3->bool`] THEN
  REWRITE_TAC[UNION_SUBSET] THEN STRIP_TAC THEN
  MP_TAC MOI_S3TB_MODEL_SETS THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[UNION_SUBSET]) THEN
  MP_TAC MOI_S3TB_FRONTIERS THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[UNION_SUBSET]) THEN
  MP_TAC MOI_S3TB_HALVES_BALLS THEN STRIP_TAC THEN
  MP_TAC MOI_S3TB_CLOSED THEN STRIP_TAC THEN
  ABBREV_TAC `je1 = IMAGE (moi_s3tb_sq (&0) (&3 / &2))
                          (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
  ABBREV_TAC `je2 = IMAGE (moi_s3tb_sq (&0) (--(&3 / &2)))
                          (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 moi_s3tb_e1 je1 /\
                pl_cell_with_boundary 2 moi_s3tb_e2 je2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["je1"; "je2"] THEN
    REWRITE_TAC[moi_s3tb_e1; moi_s3tb_e2; MOI_S3TB_SQ_CELL];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (interior b) (interior hb:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `b:real^3->bool` MOI_S5T_BALL_SIDES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `b:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `hb:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `b INTER hb = (d1:real^3->bool) UNION d2` THEN
    UNDISCH_TAC `(d1:real^3->bool) SUBSET frontier b` THEN
    UNDISCH_TAC `(d2:real^3->bool) SUBSET frontier b` THEN
    UNDISCH_TAC `frontier b INTER interior b = ({}:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d1:real^3->bool) SUBSET b /\ d2 SUBSET b /\ d1 SUBSET hb /\ d2 SUBSET hb`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `b INTER hb = (d1:real^3->bool) UNION d2` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?w1:real^3. w1 IN d1` (X_CHOOSE_TAC `w1:real^3`) THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MOI_S3TB_CELL_NONEMPTY THEN
    EXISTS_TAC `j1:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w2:real^3. w2 IN d2` (X_CHOOSE_TAC `w2:real^3`) THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MOI_S3TB_CELL_NONEMPTY THEN
    EXISTS_TAC `j2:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w2:real^3) IN frontier b /\ w2 IN frontier hb /\ ~(w2 IN d1) /\
                (w1:real^3) IN frontier b /\ w1 IN frontier hb /\ ~(w1 IN d2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w1:real^3) IN d1` THEN UNDISCH_TAC `(w2:real^3) IN d2` THEN
    UNDISCH_TAC `DISJOINT (d1:real^3->bool) d2` THEN
    UNDISCH_TAC `(d1:real^3->bool) SUBSET frontier b` THEN
    UNDISCH_TAC `(d2:real^3->bool) SUBSET frontier b` THEN
    UNDISCH_TAC `(d1:real^3->bool) SUBSET frontier hb` THEN
    UNDISCH_TAC `(d2:real^3->bool) SUBSET frontier hb` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `moi_s3tb_e1`; `je1:real^3->bool`; `d1:real^3->bool`;
                 `j1:real^3->bool`] MOI_S3TB_CELL_PLH2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^3->real^3` (X_CHOOSE_TAC `g0':real^3->real^3`)) THEN
  USE_THEN "one" (MP_TAC o SPECL
   [`moi_s3tb_p1`; `b:real^3->bool`; `moi_s3tb_e1`; `je1:real^3->bool`; `moi_s3tb_e2`;
    `je2:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`; `d2:real^3->bool`;
    `j2:real^3->bool`; `g0:real^3->real^3`; `g0':real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^3->real^3` (X_CHOOSE_THEN `f1':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism (moi_s3tb_e2,d2) (f1:real^3->real^3,f1')` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5T_RESTRICT_GEN THEN
    MAP_EVERY EXISTS_TAC [`moi_s3tb_p1`; `b:real^3->bool`] THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `hb:real^3->bool`; `d1:real^3->bool`; `w2:real^3`;
                 `g0:real^3->real^3`; `g0':real^3->real^3`; `&3 / &2`] MOI_S3TB_GG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM moi_s3tb_e1]; ALL_TAC] THEN
  REWRITE_TAC[GSYM moi_s3tb_e1] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `r0:real`
    (X_CHOOSE_THEN `gg0:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `hb:real^3->bool`; `d2:real^3->bool`; `w1:real^3`;
                 `f1:real^3->real^3`; `f1':real^3->real^3`; `--(&3 / &2)`] MOI_S3TB_GG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM moi_s3tb_e2]; ALL_TAC] THEN
  REWRITE_TAC[GSYM moi_s3tb_e2] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^3` (X_CHOOSE_THEN `r1:real`
    (X_CHOOSE_THEN `gg1:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `IMAGE (g0:real^3->real^3) moi_s3tb_e1 = d1` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_s3tb_e1,d1) (g0:real^3->real^3,g0')` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN ball(x0,r0) INTER moi_s3tb_e1 ==> (gg0:real^3->real^3) x = g0 x) /\
    (!x. x IN ball(x1,r1) INTER moi_s3tb_e2 ==> (gg1:real^3->real^3) x = f1 x) /\
    ~(ball(x0:real^3,r0) INTER (moi_s3tb_e1 DIFF je1) = {}) /\
    ~(ball(x1:real^3,r1) INTER (moi_s3tb_e2 DIFF je2) = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[IN_INTER] THEN
    MP_TAC(SPECL [`&0`; `&3 / &2`; `x0:real^3`] MOI_S3TB_OPEN_RIM) THEN
    MP_TAC(SPECL [`&0`; `--(&3 / &2)`; `x1:real^3`] MOI_S3TB_OPEN_RIM) THEN
    ASM_REWRITE_TAC[GSYM moi_s3tb_e1; GSYM moi_s3tb_e2] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    REPEAT STRIP_TAC THENL
     [EXISTS_TAC `x0:real^3`; EXISTS_TAC `x1:real^3`] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF; CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `hb:real^3->bool`; `d1:real^3->bool`; `&3 / &2`;
                 `x0:real^3`; `r0:real`; `gg0:real^3->real^3`; `g0:real^3->real^3`]
    MOI_S3TB_GG_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM moi_s3tb_e1]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `hb:real^3->bool`; `d2:real^3->bool`; `--(&3 / &2)`;
                 `x1:real^3`; `r1:real`; `gg1:real^3->real^3`; `f1:real^3->real^3`]
    MOI_S3TB_GG_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM moi_s3tb_e2]; STRIP_TAC] THEN
  USE_THEN "sign" (MP_TAC o MATCH_MP MOI_S3TB_ORIENT) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`moi_s3tb_p1`; `b:real^3->bool`; `moi_s3tb_e1`; `je1:real^3->bool`; `moi_s3tb_e2`;
    `je2:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`; `d2:real^3->bool`;
    `j2:real^3->bool`; `g0:real^3->real^3`; `g0':real^3->real^3`; `f1:real^3->real^3`;
    `f1':real^3->real^3`; `f1:real^3->real^3`; `f1':real^3->real^3`; `gg0:real^3->real^3`;
    `gg1:real^3->real^3`; `x0:real^3`; `r0:real`; `x1:real^3`; `r1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "two" (MP_TAC o SPECL
   [`moi_s3tb_p2`; `hb:real^3->bool`; `moi_s3tb_e1`; `je1:real^3->bool`; `moi_s3tb_e2`;
    `je2:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`; `d2:real^3->bool`;
    `j2:real^3->bool`; `g0:real^3->real^3`; `g0':real^3->real^3`; `f1:real^3->real^3`;
    `f1':real^3->real^3`; `ball(x0:real^3,r0)`; `ball(x1:real^3,r1)`; `gg0:real^3->real^3`;
    `gg1:real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^3->real^3` (X_CHOOSE_THEN `f2':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_S3TB_GLUE THEN
  MAP_EVERY EXISTS_TAC [`d1:real^3->bool`; `d2:real^3->bool`; `f1:real^3->real^3`;
                        `f1':real^3->real^3`; `f2:real^3->real^3`; `f2':real^3->real^3`] THEN
  ASM_REWRITE_TAC[IMAGE_UNION] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `IMAGE (g0:real^3->real^3) moi_s3tb_e1 = d1` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]]);;

