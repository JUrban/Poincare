(* ========================================================================= *)
(* pc_moi_s30_cut_b: the cut and cap of Moise 30.3 (GTM 47, printed p.215),  *)
(* main theorem                                                              *)
(*   CUTCAP |- MOI_S30_CUTCAP                                                *)
(* (PL_SCHOENFLIES_3 /\ ANNULUS_2D' /\ DISK_CHART' ==> MOISE_303_STATEMENT,  *)
(* the primes marking consequents; PL_SCHOENFLIES_3 is not used).  Route:    *)
(* chart the cut disk d1 by DISK_CHART' (the cube meets d1 in its middle     *)
(* square, the inner square onto a); the collar of a in d2 (ANNULUS_2D') is  *)
(* on one side of the middle square, after a reflection in x3 the upper      *)
(* side; a small square S_r around the inner square and a small pyramid P    *)
(* below it give the annulus a1 (ANNULUS_2D' for psi(S_r) and a), the cap    *)
(* delta1 (the lateral surface of P) and the new set c'; c' separates h from *)
(* k by explicit open sets: the pocket psi(interior P) joins the side of     *)
(* the half balls above the removed open annulus.                            *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_sch3_slab.ml";;    (* MOI_SSL_POLYGON3_CELL *)
needs "src/pc_moi_s34_frame.ml";;    (* MOI_S4K_CELL_IMAGE *)
needs "src/pc_moi_s35_cells.ml";;    (* MOI_S5V_RF_MID *)
needs "src/pc_moi_s30sep.ml";;       (* separation basics *)
needs "src/pc_moi_s34_tinf.ml";;     (* MOI_S4L_PL_CELL_FACTS *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The model pieces in real^3 (n = moi_s35_n, the max norm of                *)
(* the first two coordinates).  moi_s3cb_sq r: the square n <= r of the      *)
(* plane x3 = 0 (the inner square is r = 1/2, the middle square r = 1);     *)
(* moi_s3cb_ring r: the open annulus 1/2 < n < r of that plane.             *)
(* ========================================================================= *)

let moi_s3cb_sq = new_definition
 `moi_s3cb_sq r = {x:real^3 | x$3 = &0 /\ moi_s35_n x <= r}`;;

let moi_s3cb_ring = new_definition
 `moi_s3cb_ring r =
    {x:real^3 | x$3 = &0 /\ &1 / &2 < moi_s35_n x /\ moi_s35_n x < r}`;;

let MOI_S3CB_N_CMUL = prove
 (`!c x:real^3. &0 <= c ==> moi_s35_n (c % x) = c * moi_s35_n x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s35_n; VECTOR_MUL_COMPONENT; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`] THEN
  ASM_CASES_TAC `c = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MAX_ACI]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_max] THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let MOI_S3CB_N_COMPONENTS = prove
 (`!x:real^3 r. moi_s35_n x <= r <=> abs(x$1) <= r /\ abs(x$2) <= r`,
  REWRITE_TAC[moi_s35_n; REAL_MAX_LE]);;

let MOI_S3CB_MID_SQ = prove
 (`moi_s35_mid = moi_s3cb_sq (&1)`,
  REWRITE_TAC[moi_s35_mid; moi_s35_cube; moi_s3cb_sq; MOI_S3CB_N_COMPONENTS;
              EXTENSION; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3;
              VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3CB_INNER_SQ = prove
 (`moi_s30_inner = moi_s3cb_sq (&1 / &2)`,
  REWRITE_TAC[moi_s30_inner; moi_s35_mid; moi_s35_cube; moi_s3cb_sq;
              MOI_S3CB_N_COMPONENTS; EXTENSION; IN_ELIM_THM; IN_INTERVAL;
              DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3CB_IN_SCALE = prove
 (`!r (x:real^3) s.
     &0 < r ==> (x IN IMAGE (\y. r % y) s <=> inv r % x IN s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                 VECTOR_MUL_LID];
    DISCH_TAC THEN EXISTS_TAC `inv r % x:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                 VECTOR_MUL_LID]]);;

let MOI_S3CB_SCALE_N_X3 = prove
 (`!r (x:real^3) P.
     &0 < r
     ==> (x IN IMAGE (\y. r % y) {y | y$3 = &0 /\ P (moi_s35_n y)} <=>
          x$3 = &0 /\ P (moi_s35_n x / r))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_S3CB_IN_SCALE; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[MOI_S3CB_N_CMUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_ENTIRE; REAL_INV_EQ_0] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN REWRITE_TAC[real_div; REAL_MUL_SYM]);;

let MOI_S3CB_SQ_IMAGE = prove
 (`!r. &0 < r ==> moi_s3cb_sq r = IMAGE (\x:real^3. r % x) moi_s35_mid`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_S3CB_MID_SQ; moi_s3cb_sq] THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  ASM_SIMP_TAC[MOI_S3CB_SCALE_N_X3] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID]);;

let MOI_S3CB_SQ_RF = prove
 (`!r. &0 < r
       ==> relative_frontier (moi_s3cb_sq r) =
           {x:real^3 | x$3 = &0 /\ moi_s35_n x = r}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_S3CB_SQ_IMAGE] THEN
  SUBGOAL_THEN `linear (\x:real^3. r % x) /\
                (!x y:real^3. r % x = r % y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LINEAR_SCALING] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. r % x`; `moi_s35_mid`]
    RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MOI_S5V_RF_MID] THEN
  SUBGOAL_THEN `{x | x IN moi_s35_mid /\ moi_s35_n x = &1} =
                {x:real^3 | x$3 = &0 /\ (\m. m = &1) (moi_s35_n x)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[MOI_S3CB_MID_SQ; moi_s3cb_sq; EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  ASM_SIMP_TAC[MOI_S3CB_SCALE_N_X3] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_MUL_LID]);;

let MOI_S3CB_SQ_CELL = prove
 (`!r. &0 < r
       ==> polytope (moi_s3cb_sq r) /\ compact (moi_s3cb_sq r) /\
           pl_cell_with_boundary 2 (moi_s3cb_sq r)
                                   (relative_frontier (moi_s3cb_sq r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[MOI_S3CB_SQ_IMAGE] THEN
  STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  SUBGOAL_THEN `linear (\x:real^3. r % x) /\
                (!x y:real^3. r % x = r % y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LINEAR_SCALING] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (IMAGE (\x:real^3. r % x) moi_s35_mid)` ASSUME_TAC THENL
   [MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT] THEN
  MATCH_MP_TAC MOI_SSL_POLYGON3_CELL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x:real^3. r % x`; `moi_s35_mid`]
    AFF_DIM_INJECTIVE_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3CB_SQ_SUBSET = prove
 (`!r s. r <= s ==> moi_s3cb_sq r SUBSET moi_s3cb_sq s`,
  REWRITE_TAC[moi_s3cb_sq; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let MOI_S3CB_MID_CUBE = prove
 (`moi_s35_mid SUBSET moi_s35_cube`,
  REWRITE_TAC[moi_s35_mid; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Open square bands a < n < b are connected (four open boxes in real^2);    *)
(* the open annulus of the model plane is their image in real^3.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CB_BAND2_CONNECTED = prove
 (`!a b. &0 < a /\ a < b
         ==> connected {y:real^2 | a < max (abs(y$1)) (abs(y$2)) /\
                                   max (abs(y$1)) (abs(y$2)) < b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{y:real^2 | a < max (abs(y$1)) (abs(y$2)) /\ max (abs(y$1)) (abs(y$2)) < b} =
    ((interval(vector[a; --b],vector[b; b]) UNION
      interval(vector[--b; a],vector[b; b])) UNION
     interval(vector[--b; --b],vector[--a; b])) UNION
    interval(vector[--b; --b],vector[b; --a])`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL; IN_ELIM_THM; DIMINDEX_2;
                FORALL_2; VECTOR_2; REAL_LT_MAX; REAL_MAX_LT] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = (a + b) / &2` THEN
  SUBGOAL_THEN `a < m /\ m < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC) THEN
  REWRITE_TAC[CONNECTED_INTERVAL] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION; IN_INTERVAL;
              DIMINDEX_2; FORALL_2; VECTOR_2] THENL
   [EXISTS_TAC `vector[m; m]:real^2`;
    EXISTS_TAC `vector[--m; m]:real^2`;
    EXISTS_TAC `vector[--m; --m]:real^2`] THEN
  REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CB_RING_CONNECTED = prove
 (`!r. &1 / &2 < r ==> connected (moi_s3cb_ring r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s3cb_ring r =
    IMAGE (\y:real^2. vector[y$1; y$2; &0]:real^3)
          {y:real^2 | &1 / &2 < max (abs(y$1)) (abs(y$2)) /\
                      max (abs(y$1)) (abs(y$2)) < r}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; moi_s3cb_ring; IN_ELIM_THM; moi_s35_n] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `vector[(x:real^3)$1; x$2]:real^2` THEN
      ASM_REWRITE_TAC[VECTOR_2; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3];
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_3]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_S3CB_BAND2_CONNECTED THEN ASM_REAL_ARITH_TAC]);;

let MOI_S3CB_RING_EQ = prove
 (`!r. &1 / &2 < r
       ==> moi_s3cb_ring r =
           (moi_s3cb_sq r DIFF moi_s30_inner) DIFF
           relative_frontier (moi_s3cb_sq r)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_S3CB_SQ_RF; REAL_ARITH `&1 / &2 < r ==> &0 < r`] THEN
  REWRITE_TAC[MOI_S3CB_INNER_SQ; moi_s3cb_ring; moi_s3cb_sq; EXTENSION;
              IN_DIFF; IN_ELIM_THM] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The capping frustum below sq r: moi_s3cb_pyr r t (closed, depth t, slope  *)
(* 1), moi_s3cb_pyro r t (its open part) and the map moi_s3cb_lat r t of     *)
(* sq r onto the bottom and lateral faces (x3 becomes max(-t, n x - r)).     *)
(* ------------------------------------------------------------------------- *)

let moi_s3cb_pyr = new_definition
 `moi_s3cb_pyr r t =
    {x:real^3 | --t <= x$3 /\ x$3 <= &0 /\ moi_s35_n x <= r + x$3}`;;

let moi_s3cb_pyro = new_definition
 `moi_s3cb_pyro r t =
    {x:real^3 | --t < x$3 /\ x$3 < &0 /\ moi_s35_n x < r + x$3}`;;

let moi_s3cb_lat = new_definition
 `moi_s3cb_lat r t (x:real^3) = x + max (--t) (moi_s35_n x - r) % basis 3`;;

let MOI_S3CB_LAT_COMPONENTS = prove
 (`!r t x:real^3.
     (moi_s3cb_lat r t x)$1 = x$1 /\ (moi_s3cb_lat r t x)$2 = x$2 /\
     (moi_s3cb_lat r t x)$3 = x$3 + max (--t) (moi_s35_n x - r) /\
     moi_s35_n (moi_s3cb_lat r t x) = moi_s35_n x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s3cb_lat; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID] THEN
  REWRITE_TAC[moi_s35_n; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID]);;

let MOI_S3CB_LAT_PL = prove
 (`!r t. pl_map_on (:real^3) (moi_s3cb_lat r t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `locally_polyhedral (:real^3)` ASSUME_TAC THENL
   [SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (:real^3) (\x. lift(max (--t) (moi_s35_n x - r)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_n] THEN
    REPEAT(MATCH_MP_TAC MOI_S5V_PL_LIFT_SUB ORELSE
           MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX ORELSE
           MATCH_MP_TAC MOI_S5V_PL_LIFT_ABS ORELSE CONJ_TAC) THEN
    ASM_SIMP_TAC[MOI_S5V_PL_LIFT_COMPONENT; MOI_PTR_PL_LIFT_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s3cb_lat r t = (\x. x + max (--t) (moi_s35_n x - r) % basis 3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s3cb_lat]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_ADD THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. max (--t) (moi_s35_n x - r) % basis 3:real^3) =
    (\z:real^1. drop z % basis 3) o (\x. lift(max (--t) (moi_s35_n x - r)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\z:real^1. drop z % basis 3:real^3`;
                 `vec 0:real^3`] PL_MAP_ON_AFFINE) THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; VECTOR_ADD_RID; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
  VECTOR_ARITH_TAC);;

let MOI_S3CB_OPEN_LIN3 = prove
 (`!a b c d. open {x:real^3 | a * x$1 + b * x$2 + c * x$3 < d}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:real^3 | a * x$1 + b * x$2 + c * x$3 < d} =
                {x | vector[a; b; c] dot x < d}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_3; VECTOR_3];
    REWRITE_TAC[OPEN_HALFSPACE_LT]]);;

let MOI_S3CB_CLOSED_LIN3 = prove
 (`!a b c d. closed {x:real^3 | a * x$1 + b * x$2 + c * x$3 <= d}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:real^3 | a * x$1 + b * x$2 + c * x$3 <= d} =
                {x | vector[a; b; c] dot x <= d}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_3; VECTOR_3];
    REWRITE_TAC[CLOSED_HALFSPACE_LE]]);;

let MOI_S3CB_PYRO_OPEN = prove
 (`!r t. open (moi_s3cb_pyro r t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `moi_s3cb_pyro r t =
    {x:real^3 | &0 * x$1 + &0 * x$2 + &1 * x$3 < &0} INTER
    {x | &0 * x$1 + &0 * x$2 + -- &1 * x$3 < t} INTER
    {x | &1 * x$1 + &0 * x$2 + -- &1 * x$3 < r} INTER
    {x | -- &1 * x$1 + &0 * x$2 + -- &1 * x$3 < r} INTER
    {x | &0 * x$1 + &1 * x$2 + -- &1 * x$3 < r} INTER
    {x | &0 * x$1 + -- &1 * x$2 + -- &1 * x$3 < r}`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_s3cb_pyro; moi_s35_n; EXTENSION; IN_INTER; IN_ELIM_THM;
                REAL_MAX_LT] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[MOI_S3CB_OPEN_LIN3]]);;

let MOI_S3CB_PYR_CLOSED = prove
 (`!r t. closed (moi_s3cb_pyr r t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `moi_s3cb_pyr r t =
    {x:real^3 | &0 * x$1 + &0 * x$2 + &1 * x$3 <= &0} INTER
    {x | &0 * x$1 + &0 * x$2 + -- &1 * x$3 <= t} INTER
    {x | &1 * x$1 + &0 * x$2 + -- &1 * x$3 <= r} INTER
    {x | -- &1 * x$1 + &0 * x$2 + -- &1 * x$3 <= r} INTER
    {x | &0 * x$1 + &1 * x$2 + -- &1 * x$3 <= r} INTER
    {x | &0 * x$1 + -- &1 * x$2 + -- &1 * x$3 <= r}`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_s3cb_pyr; moi_s35_n; EXTENSION; IN_INTER; IN_ELIM_THM;
                REAL_MAX_LE] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[MOI_S3CB_CLOSED_LIN3]]);;

let MOI_S3CB_PYR_FACTS = prove
 (`!r t. &0 < t /\ t < r /\ r <= &1
         ==> moi_s3cb_pyr r t SUBSET moi_s35_cube /\
             compact (moi_s3cb_pyr r t) /\
             moi_s3cb_pyro r t SUBSET moi_s3cb_pyr r t /\
             moi_s3cb_sq r SUBSET moi_s3cb_pyr r t /\
             (!x. x IN moi_s3cb_pyr r t
                  ==> x$3 <= &0 /\ --t <= x$3 /\ moi_s35_n x <= r) /\
             (!x. x IN moi_s3cb_pyro r t ==> x$3 < &0) /\
             (!x. x IN moi_s3cb_pyr r t /\ x$3 = &0 ==> x IN moi_s3cb_sq r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) /\ c ==> a /\ b /\ c`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; moi_s3cb_pyr; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL;
                DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT;
                moi_s35_n; REAL_MAX_LE] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; MOI_S3CB_PYR_CLOSED] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
    ASM_REWRITE_TAC[moi_s35_cube; BOUNDED_INTERVAL];
    REWRITE_TAC[SUBSET; moi_s3cb_pyr; moi_s3cb_pyro; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; moi_s3cb_pyr; moi_s3cb_sq; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[moi_s3cb_pyr; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[moi_s3cb_pyro; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[moi_s3cb_pyr; moi_s3cb_sq; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_S3CB_LAT_FACTS = prove
 (`!r t. &0 < t /\ t < r /\ r <= &1
         ==> pl_map_on (moi_s3cb_sq r) (moi_s3cb_lat r t) /\
             (!x y. x IN moi_s3cb_sq r /\ y IN moi_s3cb_sq r /\
                    moi_s3cb_lat r t x = moi_s3cb_lat r t y ==> x = y) /\
             IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) SUBSET moi_s3cb_pyr r t /\
             DISJOINT (moi_s3cb_pyro r t)
                      (IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r)) /\
             moi_s3cb_pyr r t =
               (moi_s3cb_pyro r t UNION moi_s3cb_sq r) UNION
               IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) /\
             IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) INTER moi_s3cb_sq r =
               relative_frontier (moi_s3cb_sq r) /\
             IMAGE (moi_s3cb_lat r t) (relative_frontier (moi_s3cb_sq r)) =
               relative_frontier (moi_s3cb_sq r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3CB_SQ_RF] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[MOI_S3CB_LAT_PL; SUBSET_UNIV] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
    ASM_SIMP_TAC[MOI_S3CB_SQ_CELL];
    REWRITE_TAC[moi_s3cb_sq; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(AP_TERM `\v:real^3. v$1` th) THEN
      MP_TAC(AP_TERM `\v:real^3. v$2` th)) THEN
    REWRITE_TAC[MOI_S3CB_LAT_COMPONENTS] THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_s3cb_sq; moi_s3cb_pyr;
                IN_ELIM_THM; MOI_S3CB_LAT_COMPONENTS] THEN
    GEN_TAC THEN REWRITE_TAC[REAL_LE_MAX; REAL_MAX_LE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> q ==> ~p`; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC[moi_s3cb_sq; moi_s3cb_pyro; IN_ELIM_THM;
                MOI_S3CB_LAT_COMPONENTS] THEN
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[moi_s3cb_pyr; moi_s3cb_pyro; moi_s3cb_sq; IN_ELIM_THM] THEN
      STRIP_TAC THEN
      ASM_CASES_TAC `--t < (x:real^3)$3 /\ x$3 < &0 /\ moi_s35_n x < r + x$3` THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(x:real^3)$3 = &0` THEN ASM_REWRITE_TAC[] THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `vector[(x:real^3)$1; x$2; &0]:real^3` THEN
      SUBGOAL_THEN `moi_s35_n (vector[(x:real^3)$1; x$2; &0]:real^3) =
                    moi_s35_n x` ASSUME_TAC THENL
       [REWRITE_TAC[moi_s35_n; VECTOR_3]; ALL_TAC] THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_S3CB_LAT_COMPONENTS] THEN
      ASM_REWRITE_TAC[VECTOR_3; REAL_ADD_LID] THEN
      REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; moi_s3cb_pyr; moi_s3cb_pyro; IN_ELIM_THM] THEN
        GEN_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; moi_s3cb_pyr; moi_s3cb_sq; IN_ELIM_THM] THEN
        GEN_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_s3cb_sq; moi_s3cb_pyr;
                    IN_ELIM_THM; MOI_S3CB_LAT_COMPONENTS] THEN
        GEN_TAC THEN REWRITE_TAC[REAL_LE_MAX; REAL_MAX_LE] THEN
        ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
        MP_TAC) THEN
      UNDISCH_TAC `(y:real^3) IN moi_s3cb_sq r` THEN
      ASM_REWRITE_TAC[moi_s3cb_sq; IN_ELIM_THM; MOI_S3CB_LAT_COMPONENTS] THEN
      REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[moi_s3cb_sq; IN_ELIM_THM; REAL_LE_REFL] THEN
        REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_S3CB_LAT_COMPONENTS] THEN
        ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
        REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[moi_s3cb_sq; IN_ELIM_THM; REAL_LE_REFL]]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[MOI_S3CB_LAT_COMPONENTS; REAL_SUB_REFL] THEN
      REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_S3CB_LAT_COMPONENTS] THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
      REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]]);;

let MOI_S3CB_N_FACTS = prove
 (`!x:real^3. abs(x$1) <= moi_s35_n x /\ abs(x$2) <= moi_s35_n x /\
              (moi_s35_n x = abs(x$1) \/ moi_s35_n x = abs(x$2))`,
  GEN_TAC THEN REWRITE_TAC[moi_s35_n] THEN REAL_ARITH_TAC);;

let MOI_S3CB_RING_LOCAL = prove
 (`!r t x0:real^3.
     &1 / &2 < r /\ r < &1 /\ &0 < t /\ x0 IN moi_s3cb_ring r
     ==> ?e. &0 < e /\ ball(x0,e) SUBSET moi_s35_cube /\
             (!x. x IN ball(x0,e) /\ x$3 = &0 ==> x IN moi_s3cb_ring r) /\
             (!x. x IN ball(x0,e) /\ x$3 < &0 ==> x IN moi_s3cb_pyro r t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3cb_ring; IN_ELIM_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `min (min (moi_s35_n (x0:real^3) - &1 / &2)
                       ((r - moi_s35_n x0) / &2))
                  (min t (&1 - r))` THEN
  REWRITE_TAC[REAL_LT_MIN] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN ball(x0,min (min (moi_s35_n x0 - &1 / &2)
                                      ((r - moi_s35_n x0) / &2))
                                 (min t (&1 - r)))
               ==> abs(x$1 - x0$1) < moi_s35_n x0 - &1 / &2 /\
                   abs(x$1 - x0$1) < (r - moi_s35_n x0) / &2 /\
                   abs(x$1 - x0$1) < t /\ abs(x$1 - x0$1) < &1 - r /\
                   abs(x$2 - x0$2) < moi_s35_n x0 - &1 / &2 /\
                   abs(x$2 - x0$2) < (r - moi_s35_n x0) / &2 /\
                   abs(x$2 - x0$2) < t /\ abs(x$2 - x0$2) < &1 - r /\
                   abs(x$3 - x0$3) < moi_s35_n x0 - &1 / &2 /\
                   abs(x$3 - x0$3) < (r - moi_s35_n x0) / &2 /\
                   abs(x$3 - x0$3) < t /\ abs(x$3 - x0$3) < &1 - r`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN; dist] THEN
    SUBGOAL_THEN `abs((x:real^3)$1 - x0$1) <= norm(x0 - x) /\
                  abs(x$2 - x0$2) <= norm(x0 - x) /\
                  abs(x$3 - x0$3) <= norm(x0 - x)`
    MP_TAC THENL
     [REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      SIMP_TAC[COMPONENT_LE_NORM; DIMINDEX_3; ARITH];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `x0:real^3` MOI_S3CB_N_FACTS) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; moi_s35_cube; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_THEN(fun th ->
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `x:real^3` MOI_S3CB_N_FACTS) THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s3cb_pyro; IN_ELIM_THM] THEN
    MP_TAC(ISPEC `x:real^3` MOI_S3CB_N_FACTS) THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Chart transfer.  A positive continuous function on a compact              *)
(* set has a positive lower bound; a cube chart maps open subsets of the     *)
(* cube onto open sets (INVARIANCE_OF_DOMAIN); the reflection in x3 turns a  *)
(* chart into a chart with the same images of cube, middle square and inner *)
(* square (the WLOG step for the side of d2); and a compact set missing the *)
(* image of the inner square misses the image of a small frustum.            *)
(* ========================================================================= *)

let MOI_S3CB_COMPACT_GAP = prove
 (`!(f:real^N->real) k.
     compact k /\ (lift o f) continuous_on k /\ (!x. x IN k ==> &0 < f x)
     ==> ?e. &0 < e /\ !x. x IN k ==> e <= f x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:real^N->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01];
    MP_TAC(ISPECL [`f:real^N->real`; `k:real^N->bool`] CONTINUOUS_ATTAINS_INF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(f:real^N->real) x0` THEN ASM_SIMP_TAC[]]);;

let MOI_S3CB_CHART_OPEN = prove
 (`!(psi:real^3->real^3) phi z s.
     homeomorphism (moi_s35_cube,z) (psi,phi) /\ s SUBSET moi_s35_cube /\ open s
     ==> open (IMAGE psi s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM_MESON_TAC[SUBSET]]);;

let MOI_S3CB_CHART_INJ = prove
 (`!(psi:real^3->real^3) phi z s t.
     homeomorphism (moi_s35_cube,z) (psi,phi) /\ s SUBSET moi_s35_cube /\
     t SUBSET moi_s35_cube
     ==> IMAGE psi s INTER IMAGE psi t = IMAGE psi (s INTER t) /\
         IMAGE psi s DIFF IMAGE psi t = IMAGE psi (s DIFF t) /\
         (IMAGE psi s SUBSET IMAGE psi t <=> s SUBSET t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

let moi_s3cb_refl = new_definition
 `moi_s3cb_refl (x:real^3) = vector[x$1; x$2; --(x$3)]:real^3`;;

let MOI_S3CB_REFL_FACTS = prove
 (`(!x. moi_s3cb_refl (moi_s3cb_refl x) = x) /\
   (!x. (moi_s3cb_refl x)$1 = x$1 /\ (moi_s3cb_refl x)$2 = x$2 /\
        (moi_s3cb_refl x)$3 = --(x$3)) /\
   linear moi_s3cb_refl /\
   IMAGE moi_s3cb_refl moi_s35_cube = moi_s35_cube /\
   IMAGE moi_s3cb_refl moi_s35_mid = moi_s35_mid /\
   IMAGE moi_s3cb_refl moi_s30_inner = moi_s30_inner /\
   IMAGE moi_s3cb_refl {x | x IN interval(--vec 1,vec 1) /\ x$3 < &0} =
     {x | x IN interval(--vec 1,vec 1) /\ &0 < x$3}`,
  SUBGOAL_THEN `(!x. moi_s3cb_refl (moi_s3cb_refl x) = x) /\
                (!x. (moi_s3cb_refl x)$1 = x$1 /\ (moi_s3cb_refl x)$2 = x$2 /\
                     (moi_s3cb_refl x)$3 = --(x$3))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3cb_refl; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s:real^3->bool. (!x. x IN s ==> moi_s3cb_refl x IN s)
                     ==> IMAGE moi_s3cb_refl s = s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[moi_s35_cube; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                    VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[moi_s35_mid; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL;
                    DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[moi_s30_inner; moi_s35_mid; moi_s35_cube; IN_ELIM_THM;
                    IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                    VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(x:real^3) IN interval(--vec 1,vec 1)` THEN
      ASM_REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                      VECTOR_NEG_COMPONENT] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN EXISTS_TAC `moi_s3cb_refl y` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN interval(--vec 1,vec 1)` THEN
      ASM_REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                      VECTOR_NEG_COMPONENT] THEN
      ASM_REAL_ARITH_TAC]]);;

let MOI_S3CB_REFL_PLH = prove
 (`pl_homeomorphism (moi_s35_cube,moi_s35_cube) (moi_s3cb_refl,moi_s3cb_refl)`,
  STRIP_ASSUME_TAC MOI_S3CB_REFL_FACTS THEN
  SUBGOAL_THEN `locally_polyhedral moi_s35_cube` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
    REWRITE_TAC[moi_s35_cube; POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on moi_s35_cube moi_s3cb_refl` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s35_cube`; `moi_s3cb_refl`; `vec 0:real^3`]
      PL_MAP_ON_AFFINE) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_RID; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]);;

let MOI_S3CB_REFLECT = prove
 (`!(psi:real^3->real^3) phi.
     pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi)
     ==> pl_homeomorphism
           (moi_s35_cube,IMAGE (psi o moi_s3cb_refl) moi_s35_cube)
           (psi o moi_s3cb_refl,moi_s3cb_refl o phi) /\
         IMAGE (psi o moi_s3cb_refl) moi_s35_cube = IMAGE psi moi_s35_cube /\
         IMAGE (psi o moi_s3cb_refl) moi_s35_mid = IMAGE psi moi_s35_mid /\
         IMAGE (psi o moi_s3cb_refl) moi_s30_inner = IMAGE psi moi_s30_inner /\
         IMAGE (psi o moi_s3cb_refl)
               {x | x IN interval(--vec 1,vec 1) /\ &0 < x$3} =
         IMAGE psi {x | x IN interval(--vec 1,vec 1) /\ x$3 < &0}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC MOI_S3CB_REFL_FACTS THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s35_cube` THEN
    ASM_REWRITE_TAC[MOI_S3CB_REFL_PLH];
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  ASM_REWRITE_TAC[o_DEF; IMAGE_ID; ETA_AX] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]);;

let MOI_S3CB_DELTA_PL = prove
 (`pl_map_on (:real^3) (\x. lift(max (moi_s35_n x - &1 / &2) (abs(x$3))))`,
  SUBGOAL_THEN `locally_polyhedral (:real^3)` ASSUME_TAC THENL
   [SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[moi_s35_n] THEN
  REPEAT(MATCH_MP_TAC MOI_S5V_PL_LIFT_SUB ORELSE
         MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX ORELSE
         MATCH_MP_TAC MOI_S5V_PL_LIFT_ABS ORELSE CONJ_TAC) THEN
  ASM_SIMP_TAC[MOI_S5V_PL_LIFT_COMPONENT; MOI_PTR_PL_LIFT_CONST]);;

let MOI_S3CB_CHART_SMALL = prove
 (`!(psi:real^3->real^3) phi z k.
     homeomorphism (moi_s35_cube,z) (psi,phi) /\ compact k /\
     DISJOINT (IMAGE psi moi_s30_inner) k
     ==> ?r t. &1 / &2 < r /\ r < &1 /\ &0 < t /\ t < &1 / &2 /\
               DISJOINT (IMAGE psi (moi_s3cb_pyr r t)) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ABBREV_TAC `kk = {x | x IN moi_s35_cube /\ (psi:real^3->real^3) x IN k}` THEN
  SUBGOAL_THEN `compact (kk:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      REWRITE_TAC[moi_s35_cube; BOUNDED_INTERVAL] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; moi_s35_cube; CLOSED_INTERVAL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. max (moi_s35_n x - &1 / &2) (abs(x$3))`;
                 `kk:real^3->bool`] MOI_S3CB_COMPACT_GAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV; o_DEF] THEN
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[MOI_S3CB_DELTA_PL];
      EXPAND_TAC "kk" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((x:real^3) IN moi_s30_inner)` MP_TAC THENL
       [UNDISCH_TAC `DISJOINT (IMAGE (psi:real^3->real^3) moi_s30_inner) k` THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `(psi:real^3->real^3) x`) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        REWRITE_TAC[MOI_S3CB_INNER_SQ; moi_s3cb_sq; IN_ELIM_THM] THEN
        REWRITE_TAC[REAL_LT_MAX] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?e1. &0 < e1 /\ e1 < e /\ e1 <= &1 / &8` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min e (&1 / &4) / &2` THEN
    MP_TAC(SPECL [`e:real`; `&1 / &4`] REAL_MIN_MIN) THEN
    MP_TAC(SPECL [`e:real`; `&1 / &4`] REAL_LE_MIN) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&1 / &2 + e1`; `e1:real`] THEN
  REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MP_TAC(SPECL [`&1 / &2 + e1`; `e1:real`] MOI_S3CB_PYR_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN kk` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `moi_s3cb_pyr (&1 / &2 + e1) e1 SUBSET moi_s35_cube` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN kk`)) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP
    (ASSUME `(x:real^3) IN moi_s3cb_pyr (&1 / &2 + e1) e1`)) THEN
  REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The side of the second sheet.  ANNULUS_2D' for d2 and a                  *)
(* gives the collar f of a in d2; a thin band of the model annulus maps     *)
(* into any given open neighbourhood of ja (compactness), so d2 is a, a     *)
(* connected near part tt inside the chart and a compact far part missing    *)
(* a.  A connected set inside the open cube image missing the middle square  *)
(* lies over one open half of the cube.                                      *)
(* ========================================================================= *)

let MOI_S3CB_CONNECTED_OPEN_SPLIT = prove
 (`!f u v:real^N->bool.
     connected f /\ open u /\ open v /\ DISJOINT u v /\ f SUBSET u UNION v
     ==> f SUBSET u \/ f SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONNECTED; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DISJOINT]) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_S3CB_SIDE = prove
 (`!(psi:real^3->real^3) phi z tt.
     homeomorphism (moi_s35_cube,z) (psi,phi) /\ connected tt /\
     tt SUBSET IMAGE psi (interval(--vec 1,vec 1)) /\
     DISJOINT tt (IMAGE psi moi_s35_mid)
     ==> tt SUBSET IMAGE psi {x | x IN interval(--vec 1,vec 1) /\ &0 < x$3} \/
         tt SUBSET IMAGE psi {x | x IN interval(--vec 1,vec 1) /\ x$3 < &0}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CB_CONNECTED_OPEN_SPLIT THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `interval(--vec 1,vec 1) SUBSET moi_s35_cube` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_cube; INTERVAL_OPEN_SUBSET_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN interval(--vec 1,vec 1) /\ &0 < x$3} =
    interval(--vec 1,vec 1) INTER {x:real^3 | x$3 > &0} /\
    {x | x IN interval(--vec 1,vec 1) /\ x$3 < &0} =
    interval(--vec 1,vec 1) INTER {x:real^3 | x$3 < &0}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3CB_CHART_OPEN THEN
    MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `z:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC OPEN_INTER THEN
      REWRITE_TAC[OPEN_INTERVAL; OPEN_HALFSPACE_COMPONENT_GT]];
    MATCH_MP_TAC MOI_S3CB_CHART_OPEN THEN
    MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `z:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC OPEN_INTER THEN
      REWRITE_TAC[OPEN_INTERVAL; OPEN_HALFSPACE_COMPONENT_LT]];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM;
                NOT_IN_EMPTY; real_gt] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `x2:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x1:real^3) IN moi_s35_cube /\ (x2:real^3) IN moi_s35_cube`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `x1:real^3 = x2` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `!x. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x` THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `x1:real^3` th) THEN
                           MP_TAC(SPEC `x2:real^3` th)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (psi:real^3->real^3) (interval(--vec 1,vec 1)) DIFF
                IMAGE psi moi_s35_mid` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_IMAGE; IN_INTER; IN_ELIM_THM;
                real_gt] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                               ASSUME_TAC) THEN
    ASM_CASES_TAC `(x:real^3)$3 = &0` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN ASM SET_TAC[];
      SUBGOAL_THEN `&0 < (x:real^3)$3 \/ x$3 < &0` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        DISJ1_TAC THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[]]]]);;

let MOI_S3CB_ANN_MODEL = prove
 (`interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
   interval(--vector[&1;&1]:real^2,vector[&1;&1]) =
   {y:real^2 | &1 <= max (abs(y$1)) (abs(y$2)) /\
               max (abs(y$1)) (abs(y$2)) <= &2} /\
   relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) =
   {y:real^2 | max (abs(y$1)) (abs(y$2)) = &1}`,
  SUBGOAL_THEN
   `~(interior (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2;
                FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; FRONTIER_CLOSED_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTERVAL; IN_ELIM_THM; DIMINDEX_2;
              FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `m = &1 <=> m <= &1 /\ ~(m < &1)`;
              REAL_ARITH `&1 <= m <=> ~(m < &1)`; REAL_MAX_LE; REAL_MAX_LT] THEN
  CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3CB_N2_PL = prove
 (`!c. pl_map_on (:real^2) (\y. lift(max (abs(y$1)) (abs(y$2)) - c))`,
  GEN_TAC THEN
  SUBGOAL_THEN `locally_polyhedral (:real^2)` ASSUME_TAC THENL
   [SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MOI_S5V_PL_LIFT_SUB ORELSE
         MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX ORELSE
         MATCH_MP_TAC MOI_S5V_PL_LIFT_ABS ORELSE CONJ_TAC) THEN
  ASM_SIMP_TAC[MOI_S5V_PL_LIFT_COMPONENT; MOI_PTR_PL_LIFT_CONST]);;

let MOI_S3CB_N2_CLOSED_BAND = prove
 (`!b c. compact {y:real^2 | b <= max (abs(y$1)) (abs(y$2)) /\
                             max (abs(y$1)) (abs(y$2)) <= c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `interval[--vector[c;c]:real^2,vector[c;c]]` THEN
    REWRITE_TAC[BOUNDED_INTERVAL; SUBSET; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_2;
                FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT; REAL_MAX_LE] THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\y:real^2. lift(max (abs(y$1)) (abs(y$2)) - &0)`;
                   `interval[lift b,lift c]`] CONTINUOUS_CLOSED_PREIMAGE_UNIV) THEN
    REWRITE_TAC[CLOSED_INTERVAL; IN_INTERVAL_1; LIFT_DROP; REAL_SUB_RZERO] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPEC `&0` MOI_S3CB_N2_PL) THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o MATCH_MP PL_MAP_ON_IMP_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]]);;

let MOI_S3CB_COLLAR_SPLIT = prove
 (`!(d2:real^3->bool) a ja jd2 g.
     pl_annulus_with_ends ((d2 DIFF a) UNION ja) ja jd2 /\
     ja SUBSET a /\ a SUBSET d2 /\ open g /\ ja SUBSET g
     ==> ?tt ff. d2 = (a UNION tt) UNION ff /\ connected tt /\ tt SUBSET g /\
                 DISJOINT tt a /\ compact ff /\ DISJOINT ff a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism; homeomorphism;
              MOI_S3CB_ANN_MODEL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `h:real^3->real^2`
      STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `aa = {y:real^2 | &1 <= max (abs(y$1)) (abs(y$2)) /\
                               max (abs(y$1)) (abs(y$2)) <= &2}` THEN
  ABBREV_TAC `kk = {y | y IN aa /\ (f:real^2->real^3) y IN (:real^3) DIFF g}` THEN
  SUBGOAL_THEN `compact (kk:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `aa:real^2->bool` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      EXPAND_TAC "aa" THEN MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      REWRITE_TAC[MOI_S3CB_N2_CLOSED_BAND];
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
      EXPAND_TAC "aa" THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      REWRITE_TAC[MOI_S3CB_N2_CLOSED_BAND]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^2. max (abs(y$1)) (abs(y$2)) - &1`; `kk:real^2->bool`]
    MOI_S3CB_COMPACT_GAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV; o_DEF] THEN
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN REWRITE_TAC[MOI_S3CB_N2_PL];
      EXPAND_TAC "kk" THEN EXPAND_TAC "aa" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `y:real^2` THEN
      STRIP_TAC THEN
      ASM_CASES_TAC `max (abs((y:real^2)$1)) (abs(y$2)) = &1` THENL
       [SUBGOAL_THEN `(f:real^2->real^3) y IN ja` MP_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          ASM_REWRITE_TAC[IN_ELIM_THM];
          DISCH_TAC THEN UNDISCH_TAC `ja SUBSET (g:real^3->bool)` THEN
          UNDISCH_TAC `~((f:real^2->real^3) y IN g)` THEN
          UNDISCH_TAC `(f:real^2->real^3) y IN ja` THEN SET_TAC[]];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?eta. &0 < eta /\ eta < e /\ eta < &1` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min e (&1) / &2` THEN
    MP_TAC(SPECL [`e:real`; `&1`] REAL_MIN_MIN) THEN
    MP_TAC(SPECL [`e:real`; `&1`] REAL_LE_MIN) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `band = {y:real^2 | &1 < max (abs(y$1)) (abs(y$2)) /\
                                 max (abs(y$1)) (abs(y$2)) < &1 + eta}` THEN
  ABBREV_TAC `far = {y:real^2 | &1 + eta <= max (abs(y$1)) (abs(y$2)) /\
                                max (abs(y$1)) (abs(y$2)) <= &2}` THEN
  SUBGOAL_THEN
   `aa = {y:real^2 | max (abs(y$1)) (abs(y$2)) = &1} UNION band UNION far /\
    band SUBSET aa /\ far SUBSET aa`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["aa"; "band"; "far"] THEN
    REWRITE_TAC[EXTENSION; SUBSET; IN_UNION; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN band UNION far ==> ~((f:real^2->real^3) y IN a)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN aa` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^2) IN band UNION far` THEN
      UNDISCH_TAC `band SUBSET (aa:real^2->bool)` THEN
      UNDISCH_TAC `far SUBSET (aa:real^2->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^3) y IN ja` MP_TAC THENL
     [SUBGOAL_THEN `(f:real^2->real^3) y IN d2 DIFF a UNION ja` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (f:real^2->real^3) aa = d2 DIFF a UNION ja` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(f:real^2->real^3) y IN a` THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC
     `ja = IMAGE (f:real^2->real^3) {y | max (abs (y$1)) (abs (y$2)) = &1}` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y':real^2) IN aa` ASSUME_TAC THENL
     [UNDISCH_TAC
       `aa = {y:real^2 | max (abs (y$1)) (abs (y$2)) = &1} UNION band UNION far` THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `y':real^2 = y` SUBST_ALL_TAC THENL
     [UNDISCH_TAC
       `!x. x IN aa ==> (h:real^3->real^2) ((f:real^2->real^3) x) = x` THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `y:real^2` th) THEN
                           MP_TAC(SPEC `y':real^2` th)) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      UNDISCH_TAC `(y:real^2) IN band UNION far` THEN
      MAP_EVERY EXPAND_TAC ["band"; "far"] THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^2->real^3) aa = (ja UNION IMAGE f band) UNION IMAGE f far`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `aa = {y:real^2 | max (abs (y$1)) (abs (y$2)) = &1} UNION band UNION far` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    UNDISCH_TAC
     `ja = IMAGE (f:real^2->real^3) {y | max (abs (y$1)) (abs (y$2)) = &1}` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IMAGE_UNION] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^2->real^3) band`;
                        `IMAGE (f:real^2->real^3) far`] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC
     `IMAGE (f:real^2->real^3) aa = (ja UNION IMAGE f band) UNION IMAGE f far` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) aa = d2 DIFF a UNION ja` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `ja SUBSET (a:real^3->bool)` THEN
    UNDISCH_TAC `a SUBSET (d2:real^3->bool)` THEN
    SPEC_TAC(`IMAGE (f:real^2->real^3) band`,`fb:real^3->bool`) THEN
    SPEC_TAC(`IMAGE (f:real^2->real^3) far`,`ff:real^3->bool`) THEN
    SET_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `aa:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "band" THEN MATCH_MP_TAC MOI_S3CB_BAND2_CONNECTED THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN kk` ASSUME_TAC THENL
     [EXPAND_TAC "kk" THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^2) IN band` THEN
      UNDISCH_TAC `band SUBSET (aa:real^2->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN kk`)) THEN
    UNDISCH_TAC `(y:real^2) IN band` THEN EXPAND_TAC "band" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)
                               ASSUME_TAC) THEN
    UNDISCH_TAC `!y. y IN band UNION far ==> ~((f:real^2->real^3) y IN a)` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[IN_UNION] THEN
    UNDISCH_TAC `(z:real^3) IN a` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `aa:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "far" THEN REWRITE_TAC[MOI_S3CB_N2_CLOSED_BAND]];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)
                               ASSUME_TAC) THEN
    UNDISCH_TAC `!y. y IN band UNION far ==> ~((f:real^2->real^3) y IN a)` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[IN_UNION] THEN
    UNDISCH_TAC `(z:real^3) IN a` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The separation.  Abstract form (SEP_CORE): m DIFF c is the                *)
(* union of disjoint open U0, V0; the cut removes the set A0 of c and adds   *)
(* the cap D; the pocket P0 (open) lies in the compact P with P DIFF P0 in   *)
(* the union of D and c; every point of A0 has an open neighbourhood inside *)
(* (U0 DIFF D) UNION A0 UNION P0.  Then (U0 DIFF D) UNION A0 UNION P0 and    *)
(* V0 DIFF P separate the new set.  CUT_CLOSED: the new set is relatively    *)
(* closed when each point of A0 has an open neighbourhood meeting c only in *)
(* A0.                                                                       *)
(* ========================================================================= *)

let MOI_S3CB_SEP_CORE = prove
 (`!m c u0 v0 a0 p0 p (d:real^3->bool).
     open m /\ open u0 /\ open v0 /\ DISJOINT u0 v0 /\ u0 UNION v0 = m DIFF c /\
     open p0 /\ compact p /\ compact d /\ p SUBSET m /\ p0 SUBSET p /\
     d SUBSET p /\ a0 SUBSET p /\ p DIFF p0 SUBSET d UNION c /\
     a0 SUBSET c /\ DISJOINT p0 c /\ DISJOINT a0 d /\ DISJOINT p0 d /\
     (!x. x IN a0 ==> ?n. open n /\ x IN n /\
                          n SUBSET ((u0 DIFF d) UNION a0) UNION p0)
     ==> open (((u0 DIFF d) UNION a0) UNION p0) /\ open (v0 DIFF p) /\
         DISJOINT (((u0 DIFF d) UNION a0) UNION p0) (v0 DIFF p) /\
         (((u0 DIFF d) UNION a0) UNION p0) UNION (v0 DIFF p) =
         m DIFF ((c DIFF a0) UNION d) /\
         u0 DIFF p SUBSET ((u0 DIFF d) UNION a0) UNION p0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (d:real^3->bool) /\ closed (p:real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [EXISTS_TAC `u0 DIFF (d:real^3->bool)` THEN ASM_SIMP_TAC[OPEN_DIFF] THEN
      SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN a0`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `n:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `n:real^3->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `p0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ASM_SIMP_TAC[OPEN_DIFF];
    UNDISCH_TAC `DISJOINT (u0:real^3->bool) v0` THEN
    UNDISCH_TAC `(p0:real^3->bool) SUBSET p` THEN
    UNDISCH_TAC `(a0:real^3->bool) SUBSET p` THEN SET_TAC[];
    UNDISCH_TAC `(u0:real^3->bool) UNION v0 = m DIFF c` THEN
    UNDISCH_TAC `(p:real^3->bool) SUBSET m` THEN
    UNDISCH_TAC `(p0:real^3->bool) SUBSET p` THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET p` THEN
    UNDISCH_TAC `(a0:real^3->bool) SUBSET p` THEN
    UNDISCH_TAC `(p:real^3->bool) DIFF p0 SUBSET d UNION c` THEN
    UNDISCH_TAC `(a0:real^3->bool) SUBSET c` THEN
    UNDISCH_TAC `DISJOINT (p0:real^3->bool) c` THEN
    UNDISCH_TAC `DISJOINT (a0:real^3->bool) d` THEN
    UNDISCH_TAC `DISJOINT (p0:real^3->bool) d` THEN
    UNDISCH_TAC `DISJOINT (u0:real^3->bool) v0` THEN
    SET_TAC[];
    UNDISCH_TAC `(d:real^3->bool) SUBSET p` THEN SET_TAC[]]);;

let MOI_S3CB_CUT_CLOSED = prove
 (`!m c a0 (d:real^3->bool).
     closed_in (subtopology euclidean m) c /\ compact d /\ d SUBSET m /\
     (!x. x IN a0 ==> ?n. open n /\ x IN n /\ c INTER n SUBSET a0)
     ==> closed_in (subtopology euclidean m) ((c DIFF a0) UNION d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_IN_UNION THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]] THEN
  ABBREV_TAC `w = UNIONS {n:real^3->bool | open n /\ c INTER n SUBSET a0}` THEN
  SUBGOAL_THEN `open (w:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC OPEN_UNIONS THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET m` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) DIFF a0 = c DIFF (m INTER w)` SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; IN_UNIONS;
                                    IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `~((x:real^3) IN a0)` THEN
      UNDISCH_TAC `(c:real^3->bool) INTER t SUBSET a0` THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN UNDISCH_TAC `(x:real^3) IN c` THEN
      SET_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN a0`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `n:real^3->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~((x:real^3) IN m /\
                    (?t. (open t /\ c INTER t SUBSET a0) /\ x IN t))` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(c:real^3->bool) SUBSET m` THEN
        UNDISCH_TAC `(x:real^3) IN c` THEN SET_TAC[];
        EXISTS_TAC `n:real^3->bool` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The half balls above the removed open annulus: for a family of good radii *)
(* (downward closed, existing at every point of the model annulus), the     *)
(* images of the upper half balls all lie in u or all lie in v.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CB_SIDE_OPEN = prove
 (`!(psi:real^3->real^3) phi z r good u.
     homeomorphism (moi_s35_cube,z) (psi,phi) /\
     (!x0 e e'. good x0 e /\ &0 < e' /\ e' <= e ==> good x0 e') /\
     (!x0. x0 IN moi_s3cb_ring r ==> ?e. good x0 e) /\
     (!x0 e. good x0 e ==> &0 < e)
     ==> open_in (subtopology euclidean (moi_s3cb_ring r))
           {x0 | x0 IN moi_s3cb_ring r /\
                 ?e. good x0 e /\
                     IMAGE psi {x | x IN ball(x0,e) /\ &0 < x$3} SUBSET u}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mono")
    (CONJUNCTS_THEN2 (LABEL_TAC "ex") (LABEL_TAC "pos")))) THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `x0:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [USE_THEN "pos" MATCH_MP_TAC THEN EXISTS_TAC `x0:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `moi_s3cb_ring r INTER ball(x0:real^3,e / &2)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x1:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ex" (MP_TAC o C MATCH_MP
      (ASSUME `(x1:real^3) IN moi_s3cb_ring r`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `e1:real`) THEN
    SUBGOAL_THEN `&0 < e1` ASSUME_TAC THENL
     [USE_THEN "pos" MATCH_MP_TAC THEN EXISTS_TAC `x1:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `min e1 (e / &2)` THEN CONJ_TAC THENL
     [USE_THEN "mono" MATCH_MP_TAC THEN EXISTS_TAC `e1:real` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (psi:real^3->real^3) {x | x IN ball(x0,e) /\ &0 < x$3}` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL] THEN X_GEN_TAC `x:real^3` THEN
      UNDISCH_TAC `(x1:real^3) IN ball(x0,e / &2)` THEN REWRITE_TAC[IN_BALL] THEN
      REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC NORM_ARITH]]);;

let MOI_S3CB_UPPER_CONNECTED = prove
 (`!(psi:real^3->real^3) phi z x0 e.
     homeomorphism (moi_s35_cube,z) (psi,phi) /\ ball(x0,e) SUBSET moi_s35_cube
     ==> connected (IMAGE psi {x | x IN ball(x0,e) /\ &0 < x$3})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ball(x0:real^3,e) SUBSET moi_s35_cube` THEN
    SET_TAC[];
    MATCH_MP_TAC CONVEX_CONNECTED THEN
    SUBGOAL_THEN `{x | x IN ball(x0,e) /\ &0 < x$3} =
                  ball(x0:real^3,e) INTER {x | basis 3 dot x > &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_GT]]]);;

let MOI_S3CB_SIDE_CONST = prove
 (`!(psi:real^3->real^3) phi z r good u v.
     homeomorphism (moi_s35_cube,z) (psi,phi) /\ &1 / &2 < r /\
     open u /\ open v /\ DISJOINT u v /\
     (!x0 e e'. good x0 e /\ &0 < e' /\ e' <= e ==> good x0 e') /\
     (!x0. x0 IN moi_s3cb_ring r ==> ?e. good x0 e) /\
     (!x0 e. good x0 e
             ==> &0 < e /\ ball(x0,e) SUBSET moi_s35_cube /\
                 IMAGE psi {x | x IN ball(x0,e) /\ &0 < x$3} SUBSET u UNION v)
     ==> (!x0. x0 IN moi_s3cb_ring r
               ==> ?e. good x0 e /\
                       IMAGE psi {x | x IN ball(x0,e) /\ &0 < x$3} SUBSET u) \/
         (!x0. x0 IN moi_s3cb_ring r
               ==> ?e. good x0 e /\
                       IMAGE psi {x | x IN ball(x0,e) /\ &0 < x$3} SUBSET v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mono")
   (CONJUNCTS_THEN2 (LABEL_TAC "ex") (LABEL_TAC "good")))))))) THEN
  SUBGOAL_THEN
   `!x0 e. good x0 e
           ==> IMAGE (psi:real^3->real^3) {x | x IN ball(x0,e) /\ &0 < x$3}
                 SUBSET u \/
               IMAGE psi {x | x IN ball(x0,e) /\ &0 < x$3} SUBSET v`
  (LABEL_TAC "split") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "good" (MP_TAC o C MATCH_MP (ASSUME `(good:real^3->real->bool) x0 e`)) THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_S3CB_CONNECTED_OPEN_SPLIT THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CB_UPPER_CONNECTED THEN
    MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `z:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `su = {x0 | x0 IN moi_s3cb_ring r /\
               ?e. (good:real^3->real->bool) x0 e /\
                   IMAGE (psi:real^3->real^3) {x | x IN ball(x0,e) /\ &0 < x$3}
                     SUBSET u}` THEN
  ABBREV_TAC
   `sv = {x0 | x0 IN moi_s3cb_ring r /\
               ?e. (good:real^3->real->bool) x0 e /\
                   IMAGE (psi:real^3->real^3) {x | x IN ball(x0,e) /\ &0 < x$3}
                     SUBSET v}` THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (moi_s3cb_ring r)) su /\
    open_in (subtopology euclidean (moi_s3cb_ring r)) sv`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["su"; "sv"] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S3CB_SIDE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `z:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "good" (MP_TAC o C MATCH_MP (ASSUME `(good:real^3->real->bool) x0 e`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3cb_ring r SUBSET su UNION sv` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["su"; "sv"] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x0:real^3` THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ex" (MP_TAC o C MATCH_MP (ASSUME `(x0:real^3) IN moi_s3cb_ring r`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `e:real`) THEN
    USE_THEN "split" (MP_TAC o C MATCH_MP (ASSUME `(good:real^3->real->bool) x0 e`)) THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `su INTER sv:real^3->bool = {}` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["su"; "sv"] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x0:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `&0 < e1 /\ &0 < e2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "good" (MP_TAC o C MATCH_MP
        (ASSUME `(good:real^3->real->bool) x0 e1`)) THEN
      TRY(USE_THEN "good" (MP_TAC o C MATCH_MP
        (ASSUME `(good:real^3->real->bool) x0 e2`))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `y:real^3 = x0 + (min e1 e2 / &2) % basis 3` THEN
    SUBGOAL_THEN
     `(y:real^3) IN {x | x IN ball(x0,e1) /\ &0 < x$3} /\
      y IN {x | x IN ball(x0,e2) /\ &0 < x$3}`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x0:real^3) IN moi_s3cb_ring r` THEN
      REWRITE_TAC[moi_s3cb_ring; IN_ELIM_THM; IN_BALL; dist] THEN
      EXPAND_TAC "y" THEN
      REWRITE_TAC[VECTOR_ARITH `x - (x + c % b):real^3 = --(c % b)`;
                  NORM_NEG; NORM_MUL; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[NORM_BASIS; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      MP_TAC(SPECL [`e1:real`; `e2:real`] REAL_MIN_MIN) THEN
      MP_TAC(SPECL [`e1:real`; `e2:real`] REAL_LE_MIN) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN
    UNDISCH_TAC `IMAGE (psi:real^3->real^3) {x | x IN ball(x0,e1) /\ &0 < x$3}
                 SUBSET u` THEN
    UNDISCH_TAC `IMAGE (psi:real^3->real^3) {x | x IN ball(x0,e2) /\ &0 < x$3}
                 SUBSET v` THEN
    UNDISCH_TAC `(y:real^3) IN {x | x IN ball(x0,e1) /\ &0 < x$3}` THEN
    UNDISCH_TAC `(y:real^3) IN {x | x IN ball(x0,e2) /\ &0 < x$3}` THEN
    SPEC_TAC(`{x | x IN ball(x0:real^3,e1) /\ &0 < x$3}`,`b1:real^3->bool`) THEN
    SPEC_TAC(`{x | x IN ball(x0:real^3,e2) /\ &0 < x$3}`,`b2:real^3->bool`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `moi_s3cb_ring r` CONNECTED_OPEN_IN) THEN
  ASM_SIMP_TAC[MOI_S3CB_RING_CONNECTED] THEN
  DISCH_THEN(MP_TAC o SPECL [`su:real^3->bool`; `sv:real^3->bool`] o
             REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM]) THENL
   [DISJ2_TAC; DISJ1_TAC] THEN
  (X_GEN_TAC `x0:real^3` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(x0:real^3) IN su UNION sv` MP_TAC THENL
    [UNDISCH_TAC `moi_s3cb_ring r SUBSET su UNION sv` THEN
     UNDISCH_TAC `(x0:real^3) IN moi_s3cb_ring r` THEN SET_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[IN_UNION; NOT_IN_EMPTY] THEN
   MAP_EVERY EXPAND_TAC ["su"; "sv"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
   SIMP_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* The separation in the chart: with the cut along psi(ring r) and the cap  *)
(* psi(lat(sq r)), the new set is closed in m and separates h from k.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CB_GOOD = prove
 (`!(m:real^3->bool) c (psi:real^3->real^3) phi x0 e.
     homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
     IMAGE psi moi_s35_cube SUBSET m /\
     &0 < e /\ ball(x0,e) SUBSET moi_s35_cube /\
     c INTER IMAGE psi (ball(x0,e)) SUBSET IMAGE psi moi_s35_mid
     ==> IMAGE psi {x | x IN ball(x0,e) /\ &0 < x$3} SUBSET m DIFF c /\
         c INTER IMAGE psi (ball(x0,e)) SUBSET
           IMAGE psi {x | x IN ball(x0,e) /\ x$3 = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
          (psi:real^3->real^3) x = psi y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!x. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^3` th) THEN
                         MP_TAC(SPEC `y:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET m` THEN
      UNDISCH_TAC `ball(x0:real^3,e) SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `(x:real^3) IN ball(x0,e)` THEN SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(psi:real^3->real^3) x IN IMAGE psi moi_s35_mid` MP_TAC THENL
       [UNDISCH_TAC `c INTER IMAGE (psi:real^3->real^3) (ball(x0,e)) SUBSET
                     IMAGE psi moi_s35_mid` THEN
        UNDISCH_TAC `(x:real^3) IN ball(x0,e)` THEN
        UNDISCH_TAC `(psi:real^3->real^3) x IN c` THEN SET_TAC[];
        REWRITE_TAC[IN_IMAGE; moi_s35_mid; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `x:real^3 = y` SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `ball(x0:real^3,e) SUBSET moi_s35_cube` THEN
          UNDISCH_TAC `(x:real^3) IN ball(x0,e)` THEN SET_TAC[];
          ASM_REAL_ARITH_TAC]]];
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `p:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^3->real^3) x IN IMAGE psi moi_s35_mid` MP_TAC THENL
     [UNDISCH_TAC `c INTER IMAGE (psi:real^3->real^3) (ball(x0,e)) SUBSET
                   IMAGE psi moi_s35_mid` THEN
      UNDISCH_TAC `(x:real^3) IN ball(x0,e)` THEN
      UNDISCH_TAC `(psi:real^3->real^3) x IN c` THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE; moi_s35_mid; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^3 = y` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `ball(x0:real^3,e) SUBSET moi_s35_cube` THEN
        UNDISCH_TAC `(x:real^3) IN ball(x0,e)` THEN SET_TAC[];
        ASM_REWRITE_TAC[]]]]);;

let MOI_S3CB_SEPARATE = prove
 (`!(m:real^3->bool) c h k (psi:real^3->real^3) phi r t.
     open m /\ closed_in (subtopology euclidean m) c /\ separates_in m c h k /\
     homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
     IMAGE psi moi_s35_cube SUBSET m /\
     &1 / &2 < r /\ r < &1 /\ &0 < t /\ t < &1 / &2 /\
     c INTER IMAGE psi (moi_s3cb_pyr r t) = IMAGE psi (moi_s3cb_sq r) /\
     (!x0. x0 IN moi_s3cb_ring r
           ==> ?e. &0 < e /\
                   c INTER IMAGE psi (ball(x0,e) INTER moi_s35_cube) SUBSET
                   IMAGE psi moi_s35_mid) /\
     DISJOINT (h UNION k) (IMAGE psi (moi_s3cb_pyr r t))
     ==> closed_in (subtopology euclidean m)
           ((c DIFF IMAGE psi (moi_s3cb_ring r)) UNION
            IMAGE psi (IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r))) /\
         separates_in m
           ((c DIFF IMAGE psi (moi_s3cb_ring r)) UNION
            IMAGE psi (IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r))) h k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
          (psi:real^3->real^3) x = psi y ==> x = y`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!x. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^3` th) THEN
                         MP_TAC(SPEC `y:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`r:real`; `t:real`] MOI_S3CB_PYR_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`r:real`; `t:real`] MOI_S3CB_LAT_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `a0 = IMAGE (psi:real^3->real^3) (moi_s3cb_ring r)` THEN
  ABBREV_TAC `p0 = IMAGE (psi:real^3->real^3) (moi_s3cb_pyro r t)` THEN
  ABBREV_TAC `pp = IMAGE (psi:real^3->real^3) (moi_s3cb_pyr r t)` THEN
  ABBREV_TAC
   `dd = IMAGE (psi:real^3->real^3) (IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r))` THEN
  SUBGOAL_THEN `moi_s3cb_ring r SUBSET moi_s3cb_sq r /\
                moi_s3cb_ring r INTER relative_frontier (moi_s3cb_sq r) = {} /\
                moi_s3cb_pyro r t INTER moi_s3cb_sq r = {} /\
                IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) SUBSET moi_s35_cube /\
                moi_s3cb_sq r SUBSET moi_s35_cube /\
                moi_s3cb_pyro r t SUBSET moi_s35_cube /\
                moi_s3cb_ring r SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S3CB_SQ_RF; REAL_ARITH `&1 / &2 < r ==> &0 < r`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; moi_s3cb_ring; moi_s3cb_sq; IN_ELIM_THM] THEN
      GEN_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[EXTENSION; IN_INTER; moi_s3cb_ring; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      GEN_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[moi_s3cb_sq; IN_ELIM_THM] THEN
      UNDISCH_TAC `!x. x IN moi_s3cb_pyro r t ==> x$3 < &0` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN MESON_TAC[REAL_LT_REFL];
      UNDISCH_TAC `IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) SUBSET moi_s3cb_pyr r t` THEN
      UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN SET_TAC[];
      UNDISCH_TAC `moi_s3cb_sq r SUBSET moi_s3cb_pyr r t` THEN
      UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN SET_TAC[];
      UNDISCH_TAC `moi_s3cb_pyro r t SUBSET moi_s3cb_pyr r t` THEN
      UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s3cb_sq r` THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; moi_s3cb_ring; moi_s3cb_sq; IN_ELIM_THM] THEN
        GEN_TAC THEN REAL_ARITH_TAC;
        UNDISCH_TAC `moi_s3cb_sq r SUBSET moi_s3cb_pyr r t` THEN
        UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (p0:real^3->bool) /\ compact (pp:real^3->bool) /\
    compact (dd:real^3->bool) /\
    pp SUBSET m /\ p0 SUBSET pp /\ dd SUBSET pp /\ a0 SUBSET pp /\
    pp DIFF p0 SUBSET dd UNION c /\ a0 SUBSET c /\ DISJOINT p0 c /\
    DISJOINT a0 dd /\ DISJOINT p0 dd`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a0"; "p0"; "pp"; "dd"] THEN
    SUBGOAL_THEN
     `!s t. s SUBSET moi_s35_cube /\ t SUBSET moi_s35_cube
            ==> IMAGE (psi:real^3->real^3) s INTER IMAGE psi t =
                IMAGE psi (s INTER t) /\
                IMAGE psi s DIFF IMAGE psi t = IMAGE psi (s DIFF t)`
    (LABEL_TAC "img") THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`psi:real^3->real^3`; `phi:real^3->real^3`;
                     `IMAGE (psi:real^3->real^3) moi_s35_cube`;
                     `s:real^3->bool`; `t':real^3->bool`] MOI_S3CB_CHART_INJ) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(psi:real^3->real^3) continuous_on moi_s3cb_pyr r t`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3CB_CHART_OPEN THEN
      MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`;
                            `IMAGE (psi:real^3->real^3) moi_s35_cube`] THEN
      ASM_REWRITE_TAC[MOI_S3CB_PYRO_OPEN];
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `moi_s3cb_pyr r t` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        ASM_SIMP_TAC[MOI_S3CB_SQ_CELL; REAL_ARITH `&1 / &2 < r ==> &0 < r`] THEN
        MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET m` THEN
      UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN SET_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `moi_s3cb_ring r SUBSET moi_s3cb_sq r` THEN
      UNDISCH_TAC `moi_s3cb_sq r SUBSET moi_s3cb_pyr r t` THEN SET_TAC[];
      USE_THEN "img" (fun th -> MP_TAC(MATCH_MP
        (SPECL [`moi_s3cb_pyr r t`; `moi_s3cb_pyro r t`] th)
        (CONJ (ASSUME `moi_s3cb_pyr r t SUBSET moi_s35_cube`)
              (ASSUME `moi_s3cb_pyro r t SUBSET moi_s35_cube`)))) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (psi:real^3->real^3) (moi_s3cb_sq r) UNION
                  IMAGE psi (IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        UNDISCH_TAC `moi_s3cb_pyr r t =
                     (moi_s3cb_pyro r t UNION moi_s3cb_sq r) UNION
                     IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r)` THEN
        SPEC_TAC(`IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r)`,`ll:real^3->bool`) THEN
        SET_TAC[];
        UNDISCH_TAC `c INTER pp = IMAGE (psi:real^3->real^3) (moi_s3cb_sq r)` THEN
        SET_TAC[]];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (psi:real^3->real^3) (moi_s3cb_sq r)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `c INTER pp = IMAGE (psi:real^3->real^3) (moi_s3cb_sq r)` THEN
        SET_TAC[]];
      SUBGOAL_THEN `IMAGE (psi:real^3->real^3) (moi_s3cb_pyro r t) INTER
                    IMAGE psi (moi_s3cb_sq r) = {}` ASSUME_TAC THENL
       [USE_THEN "img" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP
          (SPECL [`moi_s3cb_pyro r t`; `moi_s3cb_sq r`] th)
          (CONJ (ASSUME `moi_s3cb_pyro r t SUBSET moi_s35_cube`)
                (ASSUME `moi_s3cb_sq r SUBSET moi_s35_cube`)))]) THEN
        ASM_REWRITE_TAC[IMAGE_CLAUSES];
        ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (psi:real^3->real^3) (moi_s3cb_pyro r t) SUBSET pp`
      ASSUME_TAC THENL
       [EXPAND_TAC "pp" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `c INTER pp = IMAGE (psi:real^3->real^3) (moi_s3cb_sq r)` THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) (moi_s3cb_pyro r t) INTER
                   IMAGE psi (moi_s3cb_sq r) = {}` THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) (moi_s3cb_pyro r t) SUBSET pp` THEN
      SPEC_TAC(`IMAGE (psi:real^3->real^3) (moi_s3cb_pyro r t)`,`q0:real^3->bool`) THEN
      SPEC_TAC(`IMAGE (psi:real^3->real^3) (moi_s3cb_sq r)`,`ss:real^3->bool`) THEN
      SET_TAC[];
      REWRITE_TAC[DISJOINT] THEN
      USE_THEN "img" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP
          (SPECL [`moi_s3cb_ring r`; `IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r)`] th)
          (CONJ (ASSUME `moi_s3cb_ring r SUBSET moi_s35_cube`)
                (ASSUME `IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) SUBSET
                         moi_s35_cube`)))]) THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      UNDISCH_TAC `IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) INTER moi_s3cb_sq r =
                   relative_frontier (moi_s3cb_sq r)` THEN
      UNDISCH_TAC `moi_s3cb_ring r INTER relative_frontier (moi_s3cb_sq r) = {}` THEN
      UNDISCH_TAC `moi_s3cb_ring r SUBSET moi_s3cb_sq r` THEN
      SPEC_TAC(`IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r)`,`ll:real^3->bool`) THEN
      SPEC_TAC(`relative_frontier (moi_s3cb_sq r)`,`rf:real^3->bool`) THEN SET_TAC[];
      REWRITE_TAC[DISJOINT] THEN
      USE_THEN "img" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP
          (SPECL [`moi_s3cb_pyro r t`; `IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r)`] th)
          (CONJ (ASSUME `moi_s3cb_pyro r t SUBSET moi_s35_cube`)
                (ASSUME `IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) SUBSET
                         moi_s35_cube`)))]) THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      UNDISCH_TAC `DISJOINT (moi_s3cb_pyro r t)
                            (IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r))` THEN
      REWRITE_TAC[DISJOINT]];
    ALL_TAC] THEN
  ABBREV_TAC
   `good = \x0:real^3 e. &0 < e /\ ball(x0,e) SUBSET moi_s35_cube /\
       (!x. x IN ball(x0,e) /\ x$3 = &0 ==> x IN moi_s3cb_ring r) /\
       (!x. x IN ball(x0,e) /\ x$3 < &0 ==> x IN moi_s3cb_pyro r t) /\
       c INTER IMAGE (psi:real^3->real^3) (ball(x0,e)) SUBSET IMAGE psi moi_s35_mid` THEN
  SUBGOAL_THEN `!x0 e e'. good x0 e /\ &0 < e' /\ e' <= e ==> (good:real^3->real->bool) x0 e'`
  (LABEL_TAC "mono") THENL
   [EXPAND_TAC "good" THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ball(x0:real^3,e') SUBSET ball(x0,e)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ball(x0:real^3,e) SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `ball(x0:real^3,e') SUBSET ball(x0,e)` THEN SET_TAC[];
      UNDISCH_TAC `!x. x IN ball(x0:real^3,e) /\ x$3 = &0 ==> x IN moi_s3cb_ring r` THEN
      UNDISCH_TAC `ball(x0:real^3,e') SUBSET ball(x0,e)` THEN SET_TAC[];
      UNDISCH_TAC `!x. x IN ball(x0:real^3,e) /\ x$3 < &0 ==> x IN moi_s3cb_pyro r t` THEN
      UNDISCH_TAC `ball(x0:real^3,e') SUBSET ball(x0,e)` THEN SET_TAC[];
      UNDISCH_TAC `c INTER IMAGE (psi:real^3->real^3) (ball(x0,e)) SUBSET IMAGE psi moi_s35_mid` THEN
      UNDISCH_TAC `ball(x0:real^3,e') SUBSET ball(x0,e)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x0. x0 IN moi_s3cb_ring r ==> ?e. (good:real^3->real->bool) x0 e`
  (LABEL_TAC "ex") THENL
   [X_GEN_TAC `x0:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`r:real`; `t:real`; `x0:real^3`] MOI_S3CB_RING_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `!x0. x0 IN moi_s3cb_ring r
                      ==> ?e. &0 < e /\
                              c INTER IMAGE (psi:real^3->real^3) (ball(x0,e) INTER moi_s35_cube)
                              SUBSET IMAGE psi moi_s35_mid` THEN
    DISCH_THEN(MP_TAC o SPEC `x0:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e1 e2` THEN EXPAND_TAC "good" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `ball(x0:real^3,min e1 e2) SUBSET ball(x0,e1) /\
                  ball(x0:real^3,min e1 e2) SUBSET ball(x0,e2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ball(x0:real^3,e1) SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `ball(x0:real^3,min e1 e2) SUBSET ball(x0,e1)` THEN SET_TAC[];
      UNDISCH_TAC `!x. x IN ball(x0:real^3,e1) /\ x$3 = &0 ==> x IN moi_s3cb_ring r` THEN
      UNDISCH_TAC `ball(x0:real^3,min e1 e2) SUBSET ball(x0,e1)` THEN SET_TAC[];
      UNDISCH_TAC `!x. x IN ball(x0:real^3,e1) /\ x$3 < &0 ==> x IN moi_s3cb_pyro r t` THEN
      UNDISCH_TAC `ball(x0:real^3,min e1 e2) SUBSET ball(x0,e1)` THEN SET_TAC[];
      UNDISCH_TAC `c INTER IMAGE (psi:real^3->real^3) (ball(x0,e2) INTER moi_s35_cube)
                   SUBSET IMAGE psi moi_s35_mid` THEN
      UNDISCH_TAC `ball(x0:real^3,e1) SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `ball(x0:real^3,min e1 e2) SUBSET ball(x0,e1)` THEN
      UNDISCH_TAC `ball(x0:real^3,min e1 e2) SUBSET ball(x0,e2)` THEN
      SPEC_TAC(`ball(x0:real^3,min e1 e2)`,`b:real^3->bool`) THEN
      SPEC_TAC(`ball(x0:real^3,e1)`,`b1:real^3->bool`) THEN
      SPEC_TAC(`ball(x0:real^3,e2)`,`b2:real^3->bool`) THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `separates_in m c (h:real^3->bool) k` THEN REWRITE_TAC[separates_in] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open (u:real^3->bool) /\ open (v:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `m:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x0 e. (good:real^3->real->bool) x0 e
           ==> &0 < e /\ ball(x0,e) SUBSET moi_s35_cube /\
               IMAGE (psi:real^3->real^3) {x | x IN ball(x0,e) /\ &0 < x$3}
                 SUBSET u UNION v`
  (LABEL_TAC "gfacts") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "good" THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:real^3->bool`; `c:real^3->bool`; `psi:real^3->real^3`;
                   `phi:real^3->real^3`; `x0:real^3`; `e:real`] MOI_S3CB_GOOD) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `phi:real^3->real^3`;
                 `IMAGE (psi:real^3->real^3) moi_s35_cube`; `r:real`;
                 `good:real^3->real->bool`; `u:real^3->bool`; `v:real^3->bool`]
    MOI_S3CB_SIDE_CONST) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean m) ((c DIFF a0) UNION dd:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3CB_CUT_CLOSED THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(pp:real^3->bool) SUBSET m` THEN
      UNDISCH_TAC `(dd:real^3->bool) SUBSET pp` THEN SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "a0" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x0:real^3` THEN
    DISCH_TAC THEN
    USE_THEN "ex" (MP_TAC o C MATCH_MP (ASSUME `(x0:real^3) IN moi_s3cb_ring r`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `e:real`) THEN
    UNDISCH_TAC `(good:real^3->real->bool) x0 e` THEN EXPAND_TAC "good" THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `IMAGE (psi:real^3->real^3) (ball(x0,e))` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3CB_CHART_OPEN THEN
      MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `IMAGE (psi:real^3->real^3) moi_s35_cube`] THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      MP_TAC(ISPECL [`m:real^3->bool`; `c:real^3->bool`; `psi:real^3->real^3`;
                     `phi:real^3->real^3`; `x0:real^3`; `e:real`] MOI_S3CB_GOOD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC(SET_RULE `!a1 b1 c1:real^3->bool. b1 SUBSET a1 ==> c1 SUBSET b1 ==> c1 SUBSET a1`) THEN
      EXPAND_TAC "a0" THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u0:real^3->bool.
      (!x0. x0 IN moi_s3cb_ring r
            ==> ?e. good x0 e /\
                    IMAGE (psi:real^3->real^3) {x | x IN ball(x0,e) /\ &0 < x$3}
                      SUBSET u0)
      ==> !x. x IN a0
              ==> ?n. open n /\ x IN n /\ n SUBSET ((u0 DIFF dd) UNION a0) UNION p0`
  (LABEL_TAC "nbhd") THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "a0" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x0:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x0:real^3) IN moi_s3cb_ring r`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(good:real^3->real->bool) x0 e` THEN EXPAND_TAC "good" THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `IMAGE (psi:real^3->real^3) (ball(x0,e))` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3CB_CHART_OPEN THEN
      MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `IMAGE (psi:real^3->real^3) moi_s35_cube`] THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_UNION; IN_DIFF] THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s35_cube` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(x0:real^3,e) SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `(y:real^3) IN ball(x0,e)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 < (y:real^3)$3` THENL
     [DISJ1_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (psi:real^3->real^3) {x | x IN ball(x0,e) /\ &0 < x$3}
                     SUBSET u0` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "dd" THEN REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `x':real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
        SUBGOAL_THEN `moi_s3cb_lat r t x' IN moi_s3cb_pyr r t` ASSUME_TAC THENL
         [UNDISCH_TAC `IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) SUBSET moi_s3cb_pyr r t` THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `x':real^3`) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `y = moi_s3cb_lat r t x'` SUBST_ALL_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN
          UNDISCH_TAC `moi_s3cb_lat r t x' IN moi_s3cb_pyr r t` THEN SET_TAC[];
          UNDISCH_TAC `!x. x IN moi_s3cb_pyr r t
                           ==> x$3 <= &0 /\ --t <= x$3 /\ moi_s35_n x <= r` THEN
          DISCH_THEN(MP_TAC o SPEC `moi_s3cb_lat r t x'`) THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC]];
      ASM_CASES_TAC `(y:real^3)$3 = &0` THENL
       [DISJ1_TAC THEN DISJ2_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `!x. x IN ball(x0:real^3,e) /\ x$3 = &0 ==> x IN moi_s3cb_ring r` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXPAND_TAC "p0" THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `!x. x IN ball(x0:real^3,e) /\ x$3 < &0 ==> x IN moi_s3cb_pyro r t` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN (LABEL_TAC "side")) THENL
   [MP_TAC(ISPECL [`m:real^3->bool`; `c:real^3->bool`; `u:real^3->bool`; `v:real^3->bool`;
                   `a0:real^3->bool`; `p0:real^3->bool`; `pp:real^3->bool`;
                   `dd:real^3->bool`] MOI_S3CB_SEP_CORE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "nbhd" MATCH_MP_TAC THEN USE_THEN "side" ACCEPT_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`((u DIFF dd) UNION a0) UNION p0:real^3->bool`;
                          `v DIFF pp:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(((u DIFF dd) UNION a0) UNION p0) UNION (v DIFF pp) =
                   m DIFF ((c DIFF a0) UNION dd:real^3->bool)` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(((u DIFF dd) UNION a0) UNION p0) UNION (v DIFF pp) =
                   m DIFF ((c DIFF a0) UNION dd:real^3->bool)` THEN SET_TAC[];
      UNDISCH_TAC `(u:real^3->bool) DIFF pp SUBSET ((u DIFF dd) UNION a0) UNION p0` THEN
      UNDISCH_TAC `DISJOINT (h UNION k) (pp:real^3->bool)` THEN
      UNDISCH_TAC `(h:real^3->bool) SUBSET u` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT (h UNION k) (pp:real^3->bool)` THEN
      UNDISCH_TAC `(k:real^3->bool) SUBSET v` THEN SET_TAC[]];
    MP_TAC(ISPECL [`m:real^3->bool`; `c:real^3->bool`; `v:real^3->bool`; `u:real^3->bool`;
                   `a0:real^3->bool`; `p0:real^3->bool`; `pp:real^3->bool`;
                   `dd:real^3->bool`] MOI_S3CB_SEP_CORE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN SET_TAC[];
        CONJ_TAC THENL
         [UNDISCH_TAC `(u:real^3->bool) UNION v = m DIFF c` THEN SET_TAC[];
          USE_THEN "nbhd" MATCH_MP_TAC THEN USE_THEN "side" ACCEPT_TAC]];
      ALL_TAC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`u DIFF pp:real^3->bool`;
                          `((v DIFF dd) UNION a0) UNION p0:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(((v DIFF dd) UNION a0) UNION p0) UNION (u DIFF pp) =
                   m DIFF ((c DIFF a0) UNION dd:real^3->bool)` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(((v DIFF dd) UNION a0) UNION p0) UNION (u DIFF pp) =
                   m DIFF ((c DIFF a0) UNION dd:real^3->bool)` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT (((v DIFF dd) UNION a0) UNION p0) (u DIFF pp:real^3->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `(((v DIFF dd) UNION a0) UNION p0) UNION (u DIFF pp) =
                   m DIFF ((c DIFF a0) UNION dd:real^3->bool)` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT (h UNION k) (pp:real^3->bool)` THEN
      UNDISCH_TAC `(h:real^3->bool) SUBSET u` THEN SET_TAC[];
      UNDISCH_TAC `(v:real^3->bool) DIFF pp SUBSET ((v DIFF dd) UNION a0) UNION p0` THEN
      UNDISCH_TAC `DISJOINT (h UNION k) (pp:real^3->bool)` THEN
      UNDISCH_TAC `(k:real^3->bool) SUBSET v` THEN SET_TAC[]]]);;

(* ========================================================================= *)
(* The assembly.  An open set oo around a in which c is d1                  *)
(* union d2; the chart of d1 inside w INTER oo with d2's collar above the   *)
(* middle square (after the reflection); the small frustum; the trace of c  *)
(* on it; the local structure of c near the removed annulus; then           *)
(* MOI_S3CB_SEPARATE and the cell and annulus facts give MOISE_303.         *)
(* ========================================================================= *)

let MOI_S3CB_OPEN_NBHD = prove
 (`!c s a:real^3->bool.
     a SUBSET (subtopology euclidean c) interior_of s
     ==> ?oo. open oo /\ a SUBSET oo /\ c INTER oo SUBSET s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (c:real^3->bool)`; `s:real^3->bool`]
    OPEN_IN_INTERIOR_OF) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `oo:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology euclidean (c:real^3->bool)`; `s:real^3->bool`]
    INTERIOR_OF_SUBSET) THEN
  UNDISCH_TAC `a SUBSET (subtopology euclidean c) interior_of (s:real^3->bool)` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S3CB_INNER_OPEN_CUBE = prove
 (`moi_s30_inner SUBSET interval(--vec 1,vec 1:real^3) /\
   interval(--vec 1,vec 1:real^3) SUBSET moi_s35_cube /\
   open (interval(--vec 1,vec 1:real^3))`,
  REWRITE_TAC[OPEN_INTERVAL; moi_s35_cube; INTERVAL_OPEN_SUBSET_CLOSED] THEN
  REWRITE_TAC[MOI_S3CB_INNER_SQ; moi_s3cb_sq; SUBSET; IN_ELIM_THM; IN_INTERVAL;
              DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_NEG_COMPONENT;
              MOI_S3CB_N_COMPONENTS] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3CB_CHART_SIDE = prove
 (`!(d1:real^3->bool) jd1 d2 jd2 a ja v.
     (!d jd a ja:real^3->bool.
        pl_cell_with_boundary 2 d jd /\ pl_cell_with_boundary 2 a ja /\
        a SUBSET d /\ DISJOINT a jd
        ==> pl_annulus_with_ends ((d DIFF a) UNION ja) ja jd) /\
     (!d jd a ja v:real^3->bool.
        pl_cell_with_boundary 2 d jd /\ pl_cell_with_boundary 2 a ja /\
        a SUBSET d /\ DISJOINT a jd /\ open v /\ a SUBSET v
        ==> ?(psi:real^3->real^3) phi.
              pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
              IMAGE psi moi_s35_cube SUBSET v /\
              IMAGE psi moi_s35_cube INTER d = IMAGE psi moi_s35_mid /\
              IMAGE psi moi_s30_inner = a) /\
     pl_cell_with_boundary 2 d1 jd1 /\ pl_cell_with_boundary 2 d2 jd2 /\
     pl_cell_with_boundary 2 a ja /\ d1 INTER d2 = a /\
     DISJOINT a jd1 /\ DISJOINT a jd2 /\ open v /\ a SUBSET v
     ==> ?(psi:real^3->real^3) phi tt ff.
           pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
           IMAGE psi moi_s35_cube SUBSET v /\
           IMAGE psi moi_s35_cube INTER d1 = IMAGE psi moi_s35_mid /\
           IMAGE psi moi_s30_inner = a /\
           d2 = (a UNION tt) UNION ff /\
           tt SUBSET IMAGE psi {x | x IN interval(--vec 1,vec 1) /\ &0 < x$3} /\
           compact ff /\ DISJOINT ff a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ann") (CONJUNCTS_THEN2 (LABEL_TAC "chart")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET d1 /\ a SUBSET d2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(d1:real^3->bool) INTER d2 = a` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(ja:real^3->bool) SUBSET a` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ALL_TAC] THEN
  REMOVE_THEN "chart" (MP_TAC o SPECL [`d1:real^3->bool`; `jd1:real^3->bool`;
                                    `a:real^3->bool`; `ja:real^3->bool`;
                                    `v:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi0:real^3->real^3` (X_CHOOSE_THEN `phi0:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism (moi_s35_cube,IMAGE psi0 moi_s35_cube)
                  ((psi0:real^3->real^3),(phi0:real^3->real^3))` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  STRIP_ASSUME_TAC MOI_S3CB_INNER_OPEN_CUBE THEN
  MP_TAC(ISPECL [`d2:real^3->bool`; `a:real^3->bool`; `ja:real^3->bool`; `jd2:real^3->bool`;
                 `IMAGE (psi0:real^3->real^3) (interval(--vec 1,vec 1))`]
    MOI_S3CB_COLLAR_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "ann" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3CB_CHART_OPEN THEN
      MAP_EVERY EXISTS_TAC [`phi0:real^3->real^3`;
                            `IMAGE (psi0:real^3->real^3) moi_s35_cube`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (psi0:real^3->real^3) moi_s30_inner = a` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:real^3->bool` (X_CHOOSE_THEN `ff:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`psi0:real^3->real^3`; `phi0:real^3->real^3`;
                 `IMAGE (psi0:real^3->real^3) moi_s35_cube`; `tt:real^3->bool`]
    MOI_S3CB_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (psi0:real^3->real^3) moi_s35_cube INTER d1 =
                 IMAGE psi0 moi_s35_mid` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `DISJOINT (tt:real^3->bool) a` THEN
    UNDISCH_TAC `(d1:real^3->bool) INTER d2 = a` THEN
    UNDISCH_TAC `d2:real^3->bool = (a UNION tt) UNION ff` THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`psi0:real^3->real^3`; `phi0:real^3->real^3`;
                          `tt:real^3->bool`; `ff:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`psi0:real^3->real^3`; `phi0:real^3->real^3`] MOI_S3CB_REFLECT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(psi0:real^3->real^3) o moi_s3cb_refl`;
                          `moi_s3cb_refl o (phi0:real^3->real^3)`;
                          `tt:real^3->bool`; `ff:real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3CB_PYR_TRACE = prove
 (`!(psi:real^3->real^3) phi c d1 d2 a tt ff oo r t.
     homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
     IMAGE psi moi_s35_cube SUBSET oo /\ c INTER oo SUBSET d1 UNION d2 /\
     IMAGE psi moi_s35_cube INTER d1 = IMAGE psi moi_s35_mid /\
     IMAGE psi moi_s30_inner = a /\ d1 UNION d2 SUBSET c /\
     d2 = (a UNION tt) UNION ff /\
     tt SUBSET IMAGE psi {x | x IN interval(--vec 1,vec 1) /\ &0 < x$3} /\
     DISJOINT (IMAGE psi (moi_s3cb_pyr r t)) ff /\
     &1 / &2 < r /\ r < &1 /\ &0 < t /\ t < &1 / &2
     ==> c INTER IMAGE psi (moi_s3cb_pyr r t) = IMAGE psi (moi_s3cb_sq r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
          (psi:real^3->real^3) x = psi y ==> x = y`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!x. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^3` th) THEN
                         MP_TAC(SPEC `y:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`r:real`; `t:real`] MOI_S3CB_PYR_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `moi_s3cb_sq r SUBSET moi_s35_mid /\
                moi_s30_inner SUBSET moi_s3cb_sq r` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3CB_MID_SQ; MOI_S3CB_INNER_SQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S3CB_SQ_SUBSET THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `d1:real^3->bool` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (psi:real^3->real^3) moi_s35_mid` THEN CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube INTER d1 =
                       IMAGE psi moi_s35_mid` THEN SET_TAC[]];
        UNDISCH_TAC `(d1:real^3->bool) UNION d2 SUBSET c` THEN SET_TAC[]];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `p:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
             REWRITE_RULE[IN_IMAGE]) THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s35_cube` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s3cb_pyr r t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real^3) y IN d1 UNION d2` MP_TAC THENL
   [UNDISCH_TAC `c INTER oo SUBSET (d1:real^3->bool) UNION d2` THEN
    UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET oo` THEN
    UNDISCH_TAC `(psi:real^3->real^3) y IN c` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_cube` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(psi:real^3->real^3) y IN IMAGE psi moi_s35_mid` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube INTER d1 =
                   IMAGE psi moi_s35_mid` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
    SUBGOAL_THEN `y:real^3 = y'` SUBST_ALL_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y':real^3) IN moi_s35_mid` THEN
      REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `!x. x IN moi_s3cb_pyr r t /\ x$3 = &0 ==> x IN moi_s3cb_sq r` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y':real^3) IN moi_s35_mid` THEN
    REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(psi:real^3->real^3) y IN d2` THEN
  UNDISCH_TAC `d2:real^3->bool = (a UNION tt) UNION ff` THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [UNDISCH_TAC `(psi:real^3->real^3) y IN a` THEN
    UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s30_inner = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
    SUBGOAL_THEN `y:real^3 = y'` SUBST_ALL_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y':real^3) IN moi_s30_inner` THEN
      UNDISCH_TAC `moi_s30_inner SUBSET moi_s3cb_sq r` THEN
      UNDISCH_TAC `moi_s3cb_sq r SUBSET moi_s35_mid` THEN
      MP_TAC MOI_S3CB_MID_CUBE THEN SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(y':real^3) IN moi_s30_inner` THEN
      UNDISCH_TAC `moi_s30_inner SUBSET moi_s3cb_sq r` THEN SET_TAC[]];
    UNDISCH_TAC `(psi:real^3->real^3) y IN tt` THEN
    UNDISCH_TAC `tt SUBSET IMAGE (psi:real^3->real^3)
                   {x | x IN interval(--vec 1,vec 1) /\ &0 < x$3}` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC o
               REWRITE_RULE[IN_IMAGE; IN_ELIM_THM]) THEN
    SUBGOAL_THEN `y:real^3 = z` SUBST_ALL_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC MOI_S3CB_INNER_OPEN_CUBE THEN
      UNDISCH_TAC `(z:real^3) IN interval(--vec 1,vec 1)` THEN SET_TAC[];
      UNDISCH_TAC `!x. x IN moi_s3cb_pyr r t
                       ==> x$3 <= &0 /\ --t <= x$3 /\ moi_s35_n x <= r` THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `DISJOINT (IMAGE (psi:real^3->real^3) (moi_s3cb_pyr r t)) ff` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(psi:real^3->real^3) y`) THEN
    SUBGOAL_THEN `(psi:real^3->real^3) y IN IMAGE psi (moi_s3cb_pyr r t)`
      (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]);;

let MOI_S3CB_RING_NEAR = prove
 (`!(psi:real^3->real^3) phi c d1 d2 a oo r.
     homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
     IMAGE psi moi_s35_cube SUBSET oo /\ c INTER oo SUBSET d1 UNION d2 /\
     IMAGE psi moi_s35_cube INTER d1 = IMAGE psi moi_s35_mid /\
     IMAGE psi moi_s30_inner = a /\ d1 INTER d2 = a /\ compact d2 /\
     &1 / &2 < r /\ r < &1
     ==> !x0. x0 IN moi_s3cb_ring r
              ==> ?e. &0 < e /\
                      c INTER IMAGE psi (ball(x0,e) INTER moi_s35_cube) SUBSET
                      IMAGE psi moi_s35_mid`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x0:real^3` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
          (psi:real^3->real^3) x = psi y ==> x = y`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!x. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^3` th) THEN
                         MP_TAC(SPEC `y:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN moi_s35_mid` ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^3) IN moi_s3cb_ring r` THEN
    REWRITE_TAC[MOI_S3CB_MID_SQ; moi_s3cb_ring; moi_s3cb_sq; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN moi_s35_cube` ASSUME_TAC THENL
   [MP_TAC MOI_S3CB_MID_CUBE THEN UNDISCH_TAC `(x0:real^3) IN moi_s35_mid` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((psi:real^3->real^3) x0 IN d2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(psi:real^3->real^3) x0 IN a` MP_TAC THENL
     [UNDISCH_TAC `(d1:real^3->bool) INTER d2 = a` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube INTER d1 =
                   IMAGE psi moi_s35_mid` THEN
      MATCH_MP_TAC(SET_RULE `!z:real^3 s1 s2 s3. z IN s3 ==> s1 INTER s2 = s3 ==> z IN s2`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s30_inner = a` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x0:real^3 = y` SUBST_ALL_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC MOI_S3CB_INNER_OPEN_CUBE THEN
        UNDISCH_TAC `(y:real^3) IN moi_s30_inner` THEN SET_TAC[];
        UNDISCH_TAC `(y:real^3) IN moi_s3cb_ring r` THEN
        UNDISCH_TAC `(y:real^3) IN moi_s30_inner` THEN
        REWRITE_TAC[MOI_S3CB_INNER_SQ; moi_s3cb_ring; moi_s3cb_sq; IN_ELIM_THM] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `kk = {x | x IN moi_s35_cube /\ (psi:real^3->real^3) x IN d2}` THEN
  SUBGOAL_THEN `closed (kk:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; moi_s35_cube; CLOSED_INTERVAL] THEN
    ASM_MESON_TAC[moi_s35_cube];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^3) DIFF kk` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN DISCH_THEN(MP_TAC o SPEC `x0:real^3`) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "kk" THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `p:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) o
     REWRITE_RULE[IN_IMAGE; IN_INTER])) THEN
  SUBGOAL_THEN `~((psi:real^3->real^3) y IN d2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `ball(x0:real^3,e) SUBSET (:real^3) DIFF kk` THEN
    EXPAND_TAC "kk" THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real^3) y IN d1` ASSUME_TAC THENL
   [UNDISCH_TAC `c INTER oo SUBSET (d1:real^3->bool) UNION d2` THEN
    UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET oo` THEN
    UNDISCH_TAC `~((psi:real^3->real^3) y IN d2)` THEN
    UNDISCH_TAC `(psi:real^3->real^3) y IN c` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_cube` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube INTER d1 =
               IMAGE psi moi_s35_mid` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

let CUTCAP = prove
 (MOI_S30_CUTCAP,
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "ann") (LABEL_TAC "chart"))) THEN
  REWRITE_TAC[MOISE_303_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`m:real^3->bool`; `h:real^3->bool`; `k:real^3->bool`;
                       `c:real^3->bool`; `a:real^3->bool`; `ja:real^3->bool`;
                       `d1:real^3->bool`; `jd1:real^3->bool`; `d2:real^3->bool`;
                       `jd2:real^3->bool`; `w:real^3->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `d1 UNION d2:real^3->bool`; `a:real^3->bool`]
    MOI_S3CB_OPEN_NBHD) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `jd1:real^3->bool`; `d2:real^3->bool`;
                 `jd2:real^3->bool`; `a:real^3->bool`; `ja:real^3->bool`;
                 `w INTER oo:real^3->bool`] MOI_S3CB_CHART_SIDE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SUBSET_INTER]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `phi:real^3->real^3`
    (X_CHOOSE_THEN `tt:real^3->bool` (X_CHOOSE_THEN `ff:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube)
                  ((psi:real^3->real^3),(phi:real^3->real^3)) /\
                pl_map_on moi_s35_cube psi`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
          (psi:real^3->real^3) x = psi y ==> x = y`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!x. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^3` th) THEN
                         MP_TAC(SPEC `y:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET m /\
                IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET oo /\
                IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET w`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET w INTER oo` THEN
    UNDISCH_TAC `(w:real^3->bool) SUBSET m` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (d2:real^3->bool) /\ (ja:real^3->bool) SUBSET a`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `phi:real^3->real^3`;
                 `IMAGE (psi:real^3->real^3) moi_s35_cube`; `ff:real^3->bool`]
    MOI_S3CB_CHART_SMALL) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `DISJOINT (ff:real^3->bool) a` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`r:real`; `t:real`] MOI_S3CB_PYR_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`r:real`; `t:real`] MOI_S3CB_LAT_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `moi_s3cb_sq r SUBSET moi_s35_cube /\ moi_s3cb_sq r SUBSET moi_s35_mid /\
    moi_s30_inner SUBSET moi_s3cb_sq r /\
    relative_frontier (moi_s3cb_sq r) SUBSET moi_s3cb_sq r /\
    moi_s30_inner INTER relative_frontier (moi_s3cb_sq r) = {} /\
    moi_s3cb_ring r INTER moi_s30_inner = {} /\
    moi_s3cb_ring r SUBSET moi_s3cb_sq r /\
    IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S3CB_SQ_RF; REAL_ARITH `&1 / &2 < r ==> &0 < r`] THEN
    REWRITE_TAC[MOI_S3CB_MID_SQ; MOI_S3CB_INNER_SQ] THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY; moi_s3cb_sq;
                moi_s3cb_ring; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN ASM_REAL_ARITH_TAC) THENL
     [UNDISCH_TAC `moi_s3cb_sq r SUBSET moi_s3cb_pyr r t` THEN
      UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN
      REWRITE_TAC[SUBSET; moi_s3cb_sq; IN_ELIM_THM] THEN MESON_TAC[];
      UNDISCH_TAC `IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) SUBSET moi_s3cb_pyr r t` THEN
      UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN
      REWRITE_TAC[SUBSET; moi_s3cb_sq] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `ss = IMAGE (psi:real^3->real^3) (moi_s3cb_sq r)` THEN
  ABBREV_TAC `j1 = IMAGE (psi:real^3->real^3) (relative_frontier (moi_s3cb_sq r))` THEN
  ABBREV_TAC `a1 = ((ss:real^3->bool) DIFF a) UNION ja` THEN
  ABBREV_TAC `delta1 = IMAGE (psi:real^3->real^3)
                         (IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r))` THEN
  SUBGOAL_THEN `a1 DIFF (ja UNION j1) = IMAGE (psi:real^3->real^3) (moi_s3cb_ring r)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `a1 DIFF (ja UNION j1) = ((ss:real^3->bool) DIFF a) DIFF j1`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a1"] THEN
      UNDISCH_TAC `(ja:real^3->bool) SUBSET a` THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["ss"; "j1"] THEN
    UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s30_inner = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `phi:real^3->real^3`;
                   `IMAGE (psi:real^3->real^3) moi_s35_cube`;
                   `moi_s3cb_sq r`; `moi_s30_inner`] MOI_S3CB_CHART_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC MOI_S3CB_INNER_OPEN_CUBE THEN SET_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)])] THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `phi:real^3->real^3`;
                   `IMAGE (psi:real^3->real^3) moi_s35_cube`;
                   `moi_s3cb_sq r DIFF moi_s30_inner`;
                   `relative_frontier (moi_s3cb_sq r)`] MOI_S3CB_CHART_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `relative_frontier (moi_s3cb_sq r) SUBSET moi_s3cb_sq r` THEN
      UNDISCH_TAC `moi_s3cb_sq r SUBSET moi_s35_cube` THEN SET_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)])] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S3CB_RING_EQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^3->bool`; `c:real^3->bool`; `h:real^3->bool`; `k:real^3->bool`;
                 `psi:real^3->real^3`; `phi:real^3->real^3`; `r:real`; `t:real`]
    MOI_S3CB_SEPARATE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC MOI_S3CB_PYR_TRACE THEN
      MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `d1:real^3->bool`;
                            `d2:real^3->bool`; `a:real^3->bool`;
                            `tt:real^3->bool`; `ff:real^3->bool`; `oo:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3CB_RING_NEAR THEN
      MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `d1:real^3->bool`;
                            `d2:real^3->bool`; `a:real^3->bool`;
                            `oo:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `DISJOINT (w:real^3->bool) (h UNION k)` THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET w` THEN
      UNDISCH_TAC `moi_s3cb_pyr r t SUBSET moi_s35_cube` THEN
      SPEC_TAC(`moi_s3cb_pyr r t`,`pyr:real^3->bool`) THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `a1 DIFF (ja UNION j1) = IMAGE (psi:real^3->real^3) (moi_s3cb_ring r)` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th] THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(c DIFF (a1 DIFF (ja UNION j1))) UNION delta1:real^3->bool`;
                        `a1:real^3->bool`; `j1:real^3->bool`; `delta1:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (psi:real^3->real^3) (moi_s3cb_ring r) SUBSET IMAGE psi moi_s35_mid /\
    IMAGE (psi:real^3->real^3) (moi_s3cb_ring r) INTER a = {} /\
    IMAGE (psi:real^3->real^3) (moi_s3cb_ring r) SUBSET IMAGE psi moi_s35_cube /\
    delta1 SUBSET IMAGE (psi:real^3->real^3) moi_s35_cube /\
    ss SUBSET IMAGE (psi:real^3->real^3) moi_s35_cube /\
    ss SUBSET IMAGE (psi:real^3->real^3) moi_s35_mid /\
    a SUBSET ss /\ j1 SUBSET ss /\
    IMAGE (psi:real^3->real^3) moi_s35_mid SUBSET d1 /\
    a INTER j1 = {} /\ delta1 INTER ss = j1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!s t. s SUBSET moi_s35_cube /\ t SUBSET moi_s35_cube
            ==> IMAGE (psi:real^3->real^3) s INTER IMAGE psi t =
                IMAGE psi (s INTER t)`
    (LABEL_TAC "img") THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`psi:real^3->real^3`; `phi:real^3->real^3`;
                     `IMAGE (psi:real^3->real^3) moi_s35_cube`;
                     `s:real^3->bool`; `t':real^3->bool`] MOI_S3CB_CHART_INJ) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["ss"; "j1"; "delta1"] THEN
    UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s30_inner = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    STRIP_ASSUME_TAC MOI_S3CB_INNER_OPEN_CUBE THEN
    SUBGOAL_THEN `moi_s30_inner SUBSET moi_s35_cube /\
                  moi_s3cb_ring r SUBSET moi_s35_cube /\
                  relative_frontier (moi_s3cb_sq r) SUBSET moi_s35_cube`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s30_inner SUBSET interval(--vec 1,vec 1:real^3)` THEN
      UNDISCH_TAC `interval(--vec 1,vec 1:real^3) SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `moi_s3cb_ring r SUBSET moi_s3cb_sq r` THEN
      UNDISCH_TAC `relative_frontier (moi_s3cb_sq r) SUBSET moi_s3cb_sq r` THEN
      UNDISCH_TAC `moi_s3cb_sq r SUBSET moi_s35_cube` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `moi_s3cb_ring r SUBSET moi_s3cb_sq r` THEN
      UNDISCH_TAC `moi_s3cb_sq r SUBSET moi_s35_mid` THEN SET_TAC[];
      USE_THEN "img" (fun th -> REWRITE_TAC[MATCH_MP th
        (CONJ (ASSUME `moi_s3cb_ring r SUBSET moi_s35_cube`)
              (ASSUME `moi_s30_inner SUBSET moi_s35_cube`))]) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube INTER d1 =
                   IMAGE psi moi_s35_mid` THEN SET_TAC[];
      USE_THEN "img" (fun th -> REWRITE_TAC[MATCH_MP th
        (CONJ (ASSUME `moi_s30_inner SUBSET moi_s35_cube`)
              (ASSUME `relative_frontier (moi_s3cb_sq r) SUBSET moi_s35_cube`))]) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES];
      USE_THEN "img" (fun th -> REWRITE_TAC[MATCH_MP th
        (CONJ (ASSUME `IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r) SUBSET moi_s35_cube`)
              (ASSUME `moi_s3cb_sq r SUBSET moi_s35_cube`))]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(UNDISCH_TAC `IMAGE (psi:real^3->real^3) (moi_s3cb_ring r) SUBSET IMAGE psi moi_s35_cube` THEN
  UNDISCH_TAC `delta1 SUBSET IMAGE (psi:real^3->real^3) moi_s35_cube` THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET w` THEN
  SPEC_TAC(`IMAGE (psi:real^3->real^3) (moi_s3cb_ring r)`,`aa0:real^3->bool`) THEN
  SPEC_TAC(`IMAGE (psi:real^3->real^3) moi_s35_cube`,`zz:real^3->bool`) THEN SET_TAC[]);
    (UNDISCH_TAC `d2 = (a UNION tt) UNION (ff:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) (moi_s3cb_ring r) SUBSET IMAGE psi moi_s35_mid` THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_mid SUBSET d1` THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) (moi_s3cb_ring r) INTER a = {}` THEN
  UNDISCH_TAC `(d1:real^3->bool) INTER d2 = a` THEN
  UNDISCH_TAC `(d1:real^3->bool) UNION d2 SUBSET c` THEN
  SPEC_TAC(`IMAGE (psi:real^3->real^3) (moi_s3cb_ring r)`,`aa0:real^3->bool`) THEN
  SPEC_TAC(`IMAGE (psi:real^3->real^3) moi_s35_mid`,`mm:real^3->bool`) THEN SET_TAC[]);
    (EXPAND_TAC "a1" THEN USE_THEN "ann" MATCH_MP_TAC THEN ASM_REWRITE_TAC[DISJOINT] THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) (relative_frontier (moi_s3cb_sq r)) = j1` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) (moi_s3cb_sq r) = ss` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_S4K_CELL_IMAGE THEN
  EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_SIMP_TAC[MOI_S3CB_SQ_CELL; REAL_ARITH `&1 / &2 < r ==> &0 < r`]);
    (EXPAND_TAC "a1" THEN
  UNDISCH_TAC `ss SUBSET IMAGE (psi:real^3->real^3) moi_s35_mid` THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_mid SUBSET d1` THEN
  UNDISCH_TAC `ss SUBSET IMAGE (psi:real^3->real^3) moi_s35_cube` THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET w` THEN
  UNDISCH_TAC `(ja:real^3->bool) SUBSET a` THEN
  UNDISCH_TAC `(a:real^3->bool) SUBSET ss` THEN
  SPEC_TAC(`IMAGE (psi:real^3->real^3) moi_s35_mid`,`mm:real^3->bool`) THEN
  SPEC_TAC(`IMAGE (psi:real^3->real^3) moi_s35_cube`,`zz:real^3->bool`) THEN SET_TAC[]);
    (EXPAND_TAC "a1" THEN UNDISCH_TAC `(ja:real^3->bool) SUBSET a` THEN SET_TAC[]);
    (UNDISCH_TAC `IMAGE (psi:real^3->real^3) (IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r)) =
               delta1` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) (relative_frontier (moi_s3cb_sq r)) = j1` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `IMAGE (moi_s3cb_lat r t) (relative_frontier (moi_s3cb_sq r)) =
               relative_frontier (moi_s3cb_sq r)` THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  MATCH_MP_TAC MOI_S4K_CELL_IMAGE THEN EXISTS_TAC `moi_s35_cube` THEN
  ASM_REWRITE_TAC[ARITH] THEN
  MATCH_MP_TAC MOI_S4K_CELL_IMAGE THEN EXISTS_TAC `moi_s3cb_sq r` THEN
  ASM_REWRITE_TAC[ARITH; SUBSET_REFL] THEN
  ASM_SIMP_TAC[MOI_S3CB_SQ_CELL; REAL_ARITH `&1 / &2 < r ==> &0 < r`]);
    (UNDISCH_TAC `delta1 SUBSET IMAGE (psi:real^3->real^3) moi_s35_cube` THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET w` THEN SET_TAC[]);
    (SUBGOAL_THEN `c INTER IMAGE (psi:real^3->real^3) (moi_s3cb_pyr r t) =
                IMAGE psi (moi_s3cb_sq r)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3CB_PYR_TRACE THEN
    MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `d1:real^3->bool`;
                          `d2:real^3->bool`; `a:real^3->bool`;
                          `tt:real^3->bool`; `ff:real^3->bool`; `oo:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta1 SUBSET IMAGE (psi:real^3->real^3) (moi_s3cb_pyr r t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (psi:real^3->real^3) (IMAGE (moi_s3cb_lat r t) (moi_s3cb_sq r)) =
                 delta1` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `c INTER IMAGE (psi:real^3->real^3) (moi_s3cb_pyr r t) =
               IMAGE psi (moi_s3cb_sq r)` THEN
  UNDISCH_TAC `IMAGE (psi:real^3->real^3) (moi_s3cb_sq r) = ss` THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `delta1 SUBSET IMAGE (psi:real^3->real^3) (moi_s3cb_pyr r t)` THEN
  UNDISCH_TAC `delta1 INTER ss = (j1:real^3->bool)` THEN
  SPEC_TAC(`IMAGE (psi:real^3->real^3) (moi_s3cb_pyr r t)`,`pp:real^3->bool`) THEN
  SET_TAC[])]);;

