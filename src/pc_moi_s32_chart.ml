needs "src/pc_moi_s32_gfacts.ml";;
needs "src/pc_moi_s34_scella.ml";;
needs "src/pc_moi_sch3_push.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_fnd_m3a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s32_chart: Moise GTM 47, Sec 32 (p.224), the chart of a ball split *)
(* by a proper disk onto the model cylinder (CHART), and the model set v     *)
(* (MODEL_V).  Main theorems CHART and MODEL_V (the statements               *)
(* MOI_S32_CHART, MOI_S32_MODEL_V of pc_moi_s3032_stmt).  Route:             *)
(*   MODEL_V: v is the open cylinder meeting the preimage of interior w,    *)
(*     minus the axis and the two segments joining qlo to a1, qhi to a2.     *)
(*   CHART: a fixed chart theta of the cylinder onto the double cube (it    *)
(*     keeps x2 and maps the circles x1^2 + x3^2 = r^2 onto the squares     *)
(*     max(abs x1, abs x3) = r); PL cells of the model; the cells of the    *)
(*     data (the disk lies in both ball frontiers by invariance of          *)
(*     dimension; complements by SCH3_DISK_COMPLEMENT); a PL chart of the   *)
(*     disk with the centre at p (a cone map); cell and ball extensions     *)
(*     (MOI_SPU_CELL_EXTEND, MOI_SCD_COR_EXTEND_BALL) and gluing             *)
(*     (MOI_PL2_PL_HOMEOMORPHISM_UNION).                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* MODEL_V: the open set v of the model and the two segments.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CH_PDISK = prove
 (`!x:real^3. x IN moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim) <=>
              x$2 = &0 /\ x$1 pow 2 + x$3 pow 2 < &1 /\ ~(x = vec 0)`,
  GEN_TAC THEN
  REWRITE_TAC[moi_s32_disk; moi_s32_rim; moi_s32_cyl; IN_DIFF; IN_INSERT; IN_ELIM_THM] THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:real^3)$2 = &0` THEN ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_POS] THEN
  REAL_ARITH_TAC);;

let MOI_S3CH_CENTRE_CLOSURE = prove
 (`vec 0 IN closure (moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim))`,
  REWRITE_TAC[CLOSURE_APPROACHABLE; MOI_S3CH_PDISK] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `m = min (e / &2) (&1 / &2)` THEN
  SUBGOAL_THEN `&0 < m /\ m < e /\ m pow 2 < &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < m /\ m < e /\ m <= &1 / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 / &2) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  EXISTS_TAC `m % basis 1:real^3` THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT; DIST_0; NORM_MUL; VECTOR_MUL_EQ_0] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; NORM_BASIS; BASIS_NONZERO] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CH_G0_IN_W = prove
 (`!(g:real^3->real^3) w.
     g continuous_on moi_s32_cyl /\ closed w /\
     IMAGE g (moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim)) SUBSET interior w
     ==> g (vec 0) IN w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim)`;
                 `w:real^3->bool`] IMAGE_CLOSURE_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      REWRITE_TAC[MOI_S3GF_CYL_CLOSED] THEN REWRITE_TAC[moi_s32_disk] THEN SET_TAC[];
      MP_TAC(ISPEC `w:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim))
                   SUBSET interior w` THEN
      SET_TAC[]];
    MP_TAC MOI_S3CH_CENTRE_CLOSURE THEN SET_TAC[]]);;

(* The segments from qlo to a point of the lower half off the disk stay in *)
(* the open lower half; the same above.                                     *)

let MOI_S3CH_SEG_LO = prove
 (`!(a:real^3) x.
     a IN moi_s32_lo DIFF moi_s32_disk /\ x IN segment[moi_s32_qlo,a]
     ==> x IN moi_s32_cyl /\ x$2 < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s32_lo; moi_s32_disk; moi_s32_cyl; IN_DIFF; IN_ELIM_THM; IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; moi_s32_qlo; VECTOR_3] THEN
  SUBGOAL_THEN `(a:real^3)$2 < &0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
  SUBGOAL_THEN `(u * (a:real^3)$1) pow 2 + (u * a$3) pow 2 =
                u pow 2 * (a$1 pow 2 + a$3 pow 2)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &1 pow 2 ==> x <= &1`) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u pow 2 /\ &0 <= (a:real^3)$1 pow 2 + a$3 pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `u * (a:real^3)$2 <= &0 /\ &0 <= u * (a$2 + &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= u * --x ==> u * x <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC;
    ASM_CASES_TAC `u = &1` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let MOI_S3CH_SEG_HI = prove
 (`!(a:real^3) x.
     a IN moi_s32_hi DIFF moi_s32_disk /\ x IN segment[moi_s32_qhi,a]
     ==> x IN moi_s32_cyl /\ &0 < x$2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s32_hi; moi_s32_disk; moi_s32_cyl; IN_DIFF; IN_ELIM_THM; IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; moi_s32_qhi; VECTOR_3] THEN
  SUBGOAL_THEN `&0 < (a:real^3)$2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
  SUBGOAL_THEN `(u * (a:real^3)$1) pow 2 + (u * a$3) pow 2 =
                u pow 2 * (a$1 pow 2 + a$3 pow 2)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &1 pow 2 ==> x <= &1`) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u pow 2 /\ &0 <= (a:real^3)$1 pow 2 + a$3 pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u * (a:real^3)$2 /\ &0 <= u * (&1 - a$2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC;
    ASM_CASES_TAC `u = &1` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let MOI_S3CH_AXIS_CLOSED = prove
 (`closed moi_s32_axis`,
  SUBGOAL_THEN `moi_s32_axis = {x:real^3 | x$1 = &0} INTER {x | x$3 = &0}` SUBST1_TAC THENL
   [REWRITE_TAC[moi_s32_axis; EXTENSION; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE]);;

let MOI_S3CH_PDISK_FACTS = prove
 (`!x:real^3. x IN moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim)
              ==> x IN interior moi_s32_cyl /\ ~(x IN moi_s32_axis) /\ x$2 = &0`,
  X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[MOI_S3CH_PDISK; MOI_S3GF_INTERIOR_CYL; moi_s32_axis; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_NUM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  STRIP_TAC THEN UNDISCH_TAC `~(x:real^3 = vec 0)` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN ASM_REWRITE_TAC[]);;

let MOI_S3CH_RIM_2 = prove
 (`!x:real^3. x IN moi_s32_rim ==> x$2 = &0`,
  REWRITE_TAC[moi_s32_rim; moi_s32_disk; IN_ELIM_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The theorem MODEL_V.                                                       *)
(* ------------------------------------------------------------------------- *)

let MODEL_V = prove
 (MOI_S32_MODEL_V,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3CH_G0_IN_W THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN segment[moi_s32_qlo,a1] ==> x IN moi_s32_cyl /\ x$2 < &0`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_S3CH_SEG_LO]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN segment[moi_s32_qhi,a2] ==> x IN moi_s32_cyl /\ &0 < x$2`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_S3CH_SEG_HI]; ALL_TAC] THEN
  ABBREV_TAC `v = {x | x IN interior moi_s32_cyl /\ (g:real^3->real^3) x IN interior w} DIFF
                  (moi_s32_axis UNION segment[moi_s32_qlo,a1:real^3] UNION
                   segment[moi_s32_qhi,a2:real^3])` THEN
  SUBGOAL_THEN `open (v:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC OPEN_DIFF THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[OPEN_INTERIOR] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
      REWRITE_TAC[MOI_S3CH_AXIS_CLOSED; CLOSED_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3->bool) SUBSET interior moi_s32_cyl /\ DISJOINT v moi_s32_axis /\
                IMAGE (g:real^3->real^3) v SUBSET interior w`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "v" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim) SUBSET (v:real^3->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPEC `x:real^3` MOI_S3CH_PDISK_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXPAND_TAC "v" THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim))
                   SUBSET interior w` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim)` THEN
      SET_TAC[];
      ASM_MESON_TAC[REAL_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[moi_s32_qlo,a1:real^3] UNION segment[moi_s32_qhi,a2] SUBSET
                moi_s32_cyl DIFF (vec 0 INSERT (moi_s32_rim UNION v))` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF; IN_INSERT] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s32_cyl /\ ~(x$2 = &0)` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM DISJ_CASES_TAC THEN ASM_MESON_TAC[REAL_LT_IMP_NE]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~((x:real^3)$2 = &0)` THEN ASM_REWRITE_TAC[VEC_COMPONENT];
      ASM_MESON_TAC[MOI_S3CH_RIM_2];
      UNDISCH_TAC `(x:real^3) IN v` THEN EXPAND_TAC "v" THEN
      REWRITE_TAC[IN_DIFF; IN_UNION] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `segment[moi_s32_qlo,a1:real^3]`;
                        `segment[moi_s32_qhi,a2:real^3]`] THEN
  ASM_REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[moi_s32_model] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The fixed chart theta of the cylinder onto the double cube: it keeps x2  *)
(* and scales (x1,x3) by rad/sq, rad the Euclidean and sq the max norm of   *)
(* (x1,x3); HOL division by zero makes the axis case automatic.  thinv is   *)
(* its inverse.                                                              *)
(* ------------------------------------------------------------------------- *)

let moi_s3ch_rad = new_definition
 `moi_s3ch_rad (x:real^3) = sqrt(x$1 pow 2 + x$3 pow 2)`;;

let moi_s3ch_sq = new_definition
 `moi_s3ch_sq (x:real^3) = max (abs(x$1)) (abs(x$3))`;;

let moi_s3ch_theta = new_definition
 `moi_s3ch_theta (x:real^3) =
    vector[(moi_s3ch_rad x / moi_s3ch_sq x) * x$1; x$2;
           (moi_s3ch_rad x / moi_s3ch_sq x) * x$3]:real^3`;;

let moi_s3ch_thinv = new_definition
 `moi_s3ch_thinv (y:real^3) =
    vector[(moi_s3ch_sq y / moi_s3ch_rad y) * y$1; y$2;
           (moi_s3ch_sq y / moi_s3ch_rad y) * y$3]:real^3`;;

let MOI_S3CH_RAD_SQ = prove
 (`!x:real^3.
     &0 <= moi_s3ch_sq x /\ moi_s3ch_sq x <= moi_s3ch_rad x /\
     moi_s3ch_rad x <= &2 * moi_s3ch_sq x /\
     abs(x$1) <= moi_s3ch_sq x /\ abs(x$3) <= moi_s3ch_sq x /\
     (moi_s3ch_sq x = &0 <=> x$1 = &0 /\ x$3 = &0) /\
     (moi_s3ch_rad x = &0 <=> x$1 = &0 /\ x$3 = &0)`,
  GEN_TAC THEN REWRITE_TAC[moi_s3ch_sq; moi_s3ch_rad; SQRT_EQ_0; REAL_SOS_EQ_0] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN
    MP_TAC(SPEC `(x:real^3)$1` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `(x:real^3)$3` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3)$1 pow 2 <= (max (abs(x$1)) (abs(x$3))) pow 2 /\
                  (x:real^3)$3 pow 2 <= (max (abs(x$1)) (abs(x$3))) pow 2`
    MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN
      MP_TAC(SPEC `max (abs((x:real^3)$1)) (abs(x$3))` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC];
    REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let MOI_S3CH_MAX_LMUL = prove
 (`!c a b. &0 <= c ==> max (c * a) (c * b) = c * max a b`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_max] THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let MOI_S3CH_SCALE = prove
 (`!c (x:real^3) y.
     &0 <= c
     ==> moi_s3ch_sq (vector[c * x$1; y; c * x$3]) = c * moi_s3ch_sq x /\
         moi_s3ch_rad (vector[c * x$1; y; c * x$3]) = c * moi_s3ch_rad x /\
         (vector[c * x$1; y; c * x$3]:real^3)$2 = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3ch_sq; moi_s3ch_rad; VECTOR_3] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 <= c ==> abs c = c`; MOI_S3CH_MAX_LMUL];
    SUBGOAL_THEN `(c * (x:real^3)$1) pow 2 + (c * x$3) pow 2 =
                  c pow 2 * (x$1 pow 2 + x$3 pow 2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_MUL; POW_2_SQRT]]);;

let MOI_S3CH_THETA_SQ = prove
 (`!x:real^3.
     moi_s3ch_sq (moi_s3ch_theta x) = moi_s3ch_rad x /\
     moi_s3ch_rad (moi_s3ch_theta x) =
       (moi_s3ch_rad x / moi_s3ch_sq x) * moi_s3ch_rad x /\
     (moi_s3ch_theta x)$2 = x$2`,
  GEN_TAC THEN REWRITE_TAC[moi_s3ch_theta] THEN
  MP_TAC(SPEC `x:real^3` MOI_S3CH_RAD_SQ) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= moi_s3ch_rad x / moi_s3ch_sq x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3CH_SCALE] THEN
  ASM_CASES_TAC `moi_s3ch_sq x = &0` THENL
   [SUBGOAL_THEN `moi_s3ch_rad x = &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_DIV_RMUL THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S3CH_THINV_RAD = prove
 (`!y:real^3.
     moi_s3ch_rad (moi_s3ch_thinv y) = moi_s3ch_sq y /\
     moi_s3ch_sq (moi_s3ch_thinv y) =
       (moi_s3ch_sq y / moi_s3ch_rad y) * moi_s3ch_sq y /\
     (moi_s3ch_thinv y)$2 = y$2`,
  GEN_TAC THEN REWRITE_TAC[moi_s3ch_thinv] THEN
  MP_TAC(SPEC `y:real^3` MOI_S3CH_RAD_SQ) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= moi_s3ch_sq y / moi_s3ch_rad y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3CH_SCALE] THEN
  ASM_CASES_TAC `moi_s3ch_rad y = &0` THENL
   [SUBGOAL_THEN `moi_s3ch_sq y = &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_DIV_RMUL THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S3CH_THETA_INV = prove
 (`!x:real^3. moi_s3ch_thinv (moi_s3ch_theta x) = x /\
              moi_s3ch_theta (moi_s3ch_thinv x) = x`,
  GEN_TAC THEN
  SUBGOAL_THEN `&0 <= moi_s3ch_sq x /\ moi_s3ch_sq x <= moi_s3ch_rad x`
  STRIP_ASSUME_TAC THENL [MESON_TAC[MOI_S3CH_RAD_SQ]; ALL_TAC] THEN
  ASM_CASES_TAC `moi_s3ch_sq x = &0` THENL
   [SUBGOAL_THEN `(x:real^3)$1 = &0 /\ x$3 = &0` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_S3CH_RAD_SQ]; ALL_TAC] THEN
    REWRITE_TAC[moi_s3ch_thinv; moi_s3ch_theta] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s3ch_rad x = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_s3ch_thinv; MOI_S3CH_THETA_SQ] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; moi_s3ch_theta] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(r = &0) /\ ~(s = &0) ==> (r / ((r / s) * r)) * ((r / s) * a) = a`];
    REWRITE_TAC[moi_s3ch_theta; MOI_S3CH_THINV_RAD] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; moi_s3ch_thinv] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(r = &0) /\ ~(s = &0) ==> (s / ((s / r) * s)) * ((s / r) * a) = a`]]);;

let MOI_S3CH_IMAGE_EQ = prove
 (`!s t. (!x. x IN s ==> moi_s3ch_theta x IN t) /\
         (!y. y IN t ==> moi_s3ch_thinv y IN s)
         ==> IMAGE moi_s3ch_theta s = t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
  EQ_TAC THENL
   [ASM_MESON_TAC[];
    DISCH_TAC THEN EXISTS_TAC `moi_s3ch_thinv y` THEN ASM_SIMP_TAC[MOI_S3CH_THETA_INV]]);;

let MOI_S3CH_THETA_INJ = prove
 (`!x y. moi_s3ch_theta x = moi_s3ch_theta y ==> x = y`,
  MESON_TAC[MOI_S3CH_THETA_INV]);;

let MOI_S3CH_RAD_1 = prove
 (`!x:real^3. (moi_s3ch_rad x <= &1 <=> x$1 pow 2 + x$3 pow 2 <= &1) /\
              (moi_s3ch_rad x = &1 <=> x$1 pow 2 + x$3 pow 2 = &1)`,
  GEN_TAC THEN REWRITE_TAC[moi_s3ch_rad] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o RAND_CONV) [GSYM SQRT_1] THEN
  REWRITE_TAC[SQRT_MONO_LE_EQ; SQRT_INJ]);;

let MOI_S3CH_CYL_SETS = prove
 (`moi_s32_cyl = {x | moi_s3ch_rad x <= &1 /\ abs(x$2) <= &1} /\
   moi_s32_lo = {x | moi_s3ch_rad x <= &1 /\ abs(x$2) <= &1 /\ x$2 <= &0} /\
   moi_s32_hi = {x | moi_s3ch_rad x <= &1 /\ abs(x$2) <= &1 /\ &0 <= x$2} /\
   moi_s32_disk = {x | moi_s3ch_rad x <= &1 /\ x$2 = &0} /\
   moi_s32_rim = {x | moi_s3ch_rad x = &1 /\ x$2 = &0} /\
   moi_s32_lohemi = {x | moi_s3ch_rad x <= &1 /\ abs(x$2) <= &1 /\ x$2 <= &0 /\
                         (moi_s3ch_rad x = &1 \/ x$2 = -- &1)} /\
   moi_s32_hihemi = {x | moi_s3ch_rad x <= &1 /\ abs(x$2) <= &1 /\ &0 <= x$2 /\
                         (moi_s3ch_rad x = &1 \/ x$2 = &1)}`,
  REWRITE_TAC[moi_s32_cyl; moi_s32_lo; moi_s32_hi; moi_s32_disk; moi_s32_rim;
              moi_s32_lohemi; moi_s32_hihemi; EXTENSION; IN_ELIM_THM; MOI_S3CH_RAD_1] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3CH_MODEL_IMAGES = prove
 (`IMAGE moi_s3ch_theta moi_s32_cyl = {y | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1} /\
   IMAGE moi_s3ch_theta moi_s32_lo =
     {y | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1 /\ y$2 <= &0} /\
   IMAGE moi_s3ch_theta moi_s32_hi =
     {y | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1 /\ &0 <= y$2} /\
   IMAGE moi_s3ch_theta moi_s32_disk = {y | moi_s3ch_sq y <= &1 /\ y$2 = &0} /\
   IMAGE moi_s3ch_theta moi_s32_rim = {y | moi_s3ch_sq y = &1 /\ y$2 = &0} /\
   IMAGE moi_s3ch_theta moi_s32_lohemi =
     {y | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1 /\ y$2 <= &0 /\
          (moi_s3ch_sq y = &1 \/ y$2 = -- &1)} /\
   IMAGE moi_s3ch_theta moi_s32_hihemi =
     {y | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1 /\ &0 <= y$2 /\
          (moi_s3ch_sq y = &1 \/ y$2 = &1)} /\
   moi_s3ch_theta (vec 0) = vec 0`,
  REWRITE_TAC[MOI_S3CH_CYL_SETS] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC MOI_S3CH_IMAGE_EQ THEN
      REWRITE_TAC[IN_ELIM_THM; MOI_S3CH_THETA_SQ; MOI_S3CH_THINV_RAD] THEN
      MESON_TAC[]) THEN
  REWRITE_TAC[moi_s3ch_theta; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT;
              REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of theta and the homeomorphism of the cylinder onto the cube. *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CH_SQ_LIP = prove
 (`!x y:real^3. abs(moi_s3ch_sq x - moi_s3ch_sq y) <= &2 * norm(x - y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3ch_sq] THEN
  MP_TAC(ISPECL [`x - y:real^3`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`x - y:real^3`; `3`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC);;

let MOI_S3CH_RAD_NORM = prove
 (`!x:real^3. moi_s3ch_rad x = norm(vector[x$1; &0; x$3]:real^3)`,
  GEN_TAC THEN
  REWRITE_TAC[moi_s3ch_rad; vector_norm; dot; DIMINDEX_3; SUM_3; VECTOR_3; BETA_THM] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let MOI_S3CH_RAD_LIP = prove
 (`!x y:real^3. abs(moi_s3ch_rad x - moi_s3ch_rad y) <= &1 * norm(x - y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S3CH_RAD_NORM; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vector[(x:real^3)$1; &0; x$3] - vector[(y:real^3)$1; &0; y$3]:real^3)` THEN
  REWRITE_TAC[REAL_ABS_SUB_NORM] THEN
  REWRITE_TAC[vector_norm; dot; DIMINDEX_3; SUM_3; VECTOR_3; BETA_THM;
              VECTOR_SUB_COMPONENT] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  MP_TAC(SPEC `(x:real^3)$2 - (y:real^3)$2` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let MOI_S3CH_LIP_CONT = prove
 (`!(f:real^3->real) c a.
     &0 < c /\ (!x y. abs(f x - f y) <= c * norm(x - y))
     ==> (lift o f) continuous at a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_at; o_THM; DIST_LIFT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e / c` THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN X_GEN_TAC `x:real^3` THEN REWRITE_TAC[dist] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `c * norm(x - a:real^3)` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `norm(x - a:real^3) < e / c` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
  REAL_ARITH_TAC);;

let MOI_S3CH_THETA_BOUND = prove
 (`!x:real^3.
     abs((moi_s3ch_rad x / moi_s3ch_sq x) * x$1) <= moi_s3ch_rad x /\
     abs((moi_s3ch_rad x / moi_s3ch_sq x) * x$3) <= moi_s3ch_rad x`,
  GEN_TAC THEN MP_TAC(SPEC `x:real^3` MOI_S3CH_RAD_SQ) THEN STRIP_TAC THEN
  ASM_CASES_TAC `moi_s3ch_sq x = &0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_MUL_LZERO;
                    REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= moi_s3ch_rad x / moi_s3ch_sq x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(moi_s3ch_rad x / moi_s3ch_sq x) * moi_s3ch_sq x = moi_s3ch_rad x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`] THEN
  CONJ_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let MOI_S3CH_THETA_AXIS = prove
 (`!x:real^3. moi_s3ch_sq x = &0 ==> moi_s3ch_theta x = x`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3)$1 = &0 /\ x$3 = &0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3CH_RAD_SQ]; ALL_TAC] THEN
  REWRITE_TAC[moi_s3ch_theta; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

let MOI_S3CH_THETA_CONT = prove
 (`moi_s3ch_theta continuous_on (:real^3)`,
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `a:real^3` THEN
  DISCH_TAC THEN ASM_CASES_TAC `moi_s3ch_sq a = &0` THENL
   [REWRITE_TAC[continuous_at] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `e / &3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MOI_S3CH_THETA_AXIS] THEN
    SUBGOAL_THEN `moi_s3ch_rad a = &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_S3CH_RAD_SQ]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^3)$1 = &0 /\ a$3 = &0` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_S3CH_RAD_SQ]; ALL_TAC] THEN
    REWRITE_TAC[dist] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:3)) (\i. abs((moi_s3ch_theta x - a)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN
    REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT] THEN
    REWRITE_TAC[moi_s3ch_theta; VECTOR_3] THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    MP_TAC(SPEC `x:real^3` MOI_S3CH_THETA_BOUND) THEN
    MP_TAC(SPECL [`x:real^3`; `a:real^3`] MOI_S3CH_RAD_LIP) THEN
    MP_TAC(ISPECL [`x - a:real^3`; `2`] COMPONENT_LE_NORM) THEN
    UNDISCH_TAC `dist(x:real^3,a) < e / &3` THEN
    ASM_REWRITE_TAC[dist; VECTOR_SUB_COMPONENT; REAL_SUB_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o (\x:real^3. moi_s3ch_rad x / moi_s3ch_sq x)) continuous at a`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(lift o (\x:real^3. moi_s3ch_rad x / moi_s3ch_sq x)) =
                  (\x. moi_s3ch_rad x % (lift o inv o moi_s3ch_sq) x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; real_div; LIFT_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3CH_LIP_CONT THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[MOI_S3CH_RAD_LIP] THEN REAL_ARITH_TAC;
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_INV THEN ASM_REWRITE_TAC[NETLIMIT_AT] THEN
      MATCH_MP_TAC MOI_S3CH_LIP_CONT THEN EXISTS_TAC `&2` THEN
      REWRITE_TAC[MOI_S3CH_SQ_LIP] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; moi_s3ch_theta; VECTOR_3] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_AT_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_AT_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_AT_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The model: the double cube kk = k1 UNION k2, the middle square q = k1    *)
(* INTER k2 with boundary rq, and the outer halves l1, l2 of the frontiers  *)
(* of k1, k2; theta maps the cylinder sets onto them.                       *)
(* ------------------------------------------------------------------------- *)

let moi_s3ch_kk = new_definition
 `moi_s3ch_kk = {y:real^3 | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1}`;;

let moi_s3ch_k1 = new_definition
 `moi_s3ch_k1 = {y:real^3 | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1 /\ y$2 <= &0}`;;

let moi_s3ch_k2 = new_definition
 `moi_s3ch_k2 = {y:real^3 | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1 /\ &0 <= y$2}`;;

let moi_s3ch_q = new_definition
 `moi_s3ch_q = {y:real^3 | moi_s3ch_sq y <= &1 /\ y$2 = &0}`;;

let moi_s3ch_rq = new_definition
 `moi_s3ch_rq = {y:real^3 | moi_s3ch_sq y = &1 /\ y$2 = &0}`;;

let moi_s3ch_l1 = new_definition
 `moi_s3ch_l1 = {y:real^3 | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1 /\ y$2 <= &0 /\
                           (moi_s3ch_sq y = &1 \/ y$2 = -- &1)}`;;

let moi_s3ch_l2 = new_definition
 `moi_s3ch_l2 = {y:real^3 | moi_s3ch_sq y <= &1 /\ abs(y$2) <= &1 /\ &0 <= y$2 /\
                           (moi_s3ch_sq y = &1 \/ y$2 = &1)}`;;

let MOI_S3CH_IMAGES = prove
 (`IMAGE moi_s3ch_theta moi_s32_cyl = moi_s3ch_kk /\
   IMAGE moi_s3ch_theta moi_s32_lo = moi_s3ch_k1 /\
   IMAGE moi_s3ch_theta moi_s32_hi = moi_s3ch_k2 /\
   IMAGE moi_s3ch_theta moi_s32_disk = moi_s3ch_q /\
   IMAGE moi_s3ch_theta moi_s32_rim = moi_s3ch_rq /\
   IMAGE moi_s3ch_theta moi_s32_lohemi = moi_s3ch_l1 /\
   IMAGE moi_s3ch_theta moi_s32_hihemi = moi_s3ch_l2 /\
   moi_s3ch_theta (vec 0) = vec 0`,
  REWRITE_TAC[moi_s3ch_kk; moi_s3ch_k1; moi_s3ch_k2; moi_s3ch_q; moi_s3ch_rq;
              moi_s3ch_l1; moi_s3ch_l2; MOI_S3CH_MODEL_IMAGES]);;

let MOI_S3CH_THETA_HOMEO = prove
 (`?th'. homeomorphism (moi_s32_cyl,moi_s3ch_kk) (moi_s3ch_theta,th')`,
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  REWRITE_TAC[MOI_S3GF_CYL_COMPACT; MOI_S3CH_IMAGES] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[MOI_S3CH_THETA_CONT; SUBSET_UNIV];
    MESON_TAC[MOI_S3CH_THETA_INJ]]);;

let MOI_S3CH_K_INTERVALS = prove
 (`moi_s3ch_k1 = interval[vector[-- &1; -- &1; -- &1],vector[&1; &0; &1]] /\
   moi_s3ch_k2 = interval[vector[-- &1; &0; -- &1],vector[&1; &1; &1]] /\
   interval(vector[-- &1; -- &1; -- &1],vector[&1; &0; &1]) =
     {y:real^3 | abs(y$1) < &1 /\ -- &1 < y$2 /\ y$2 < &0 /\ abs(y$3) < &1} /\
   interval(vector[-- &1; &0; -- &1],vector[&1; &1; &1]) =
     {y:real^3 | abs(y$1) < &1 /\ &0 < y$2 /\ y$2 < &1 /\ abs(y$3) < &1}`,
  REWRITE_TAC[moi_s3ch_k1; moi_s3ch_k2; moi_s3ch_sq; EXTENSION; IN_ELIM_THM;
              IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3CH_MODEL_SETS = prove
 (`moi_s3ch_k1 UNION moi_s3ch_k2 = moi_s3ch_kk /\
   moi_s3ch_k1 INTER moi_s3ch_k2 = moi_s3ch_q /\
   moi_s3ch_rq SUBSET moi_s3ch_q /\
   vec 0 IN moi_s3ch_q /\ ~(vec 0 IN moi_s3ch_rq) /\
   moi_s3ch_q SUBSET frontier moi_s3ch_k1 /\ moi_s3ch_q SUBSET frontier moi_s3ch_k2 /\
   moi_s3ch_l1 = (frontier moi_s3ch_k1 DIFF moi_s3ch_q) UNION moi_s3ch_rq /\
   moi_s3ch_l2 = (frontier moi_s3ch_k2 DIFF moi_s3ch_q) UNION moi_s3ch_rq`,
  MP_TAC MOI_S3CH_K_INTERVALS THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    REWRITE_TAC[el 0 ths; el 1 ths; FRONTIER_CLOSED_INTERVAL] THEN
    REWRITE_TAC[GSYM(el 0 ths); GSYM(el 1 ths)] THEN REWRITE_TAC[el 2 ths; el 3 ths]) THEN
  REWRITE_TAC[moi_s3ch_k1; moi_s3ch_k2; moi_s3ch_kk; moi_s3ch_q; moi_s3ch_rq;
              moi_s3ch_l1; moi_s3ch_l2; moi_s3ch_sq; EXTENSION; SUBSET; IN_UNION;
              IN_INTER; IN_DIFF; IN_ELIM_THM; VEC_COMPONENT] THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* General facts on PL balls and cells in real^3.                            *)
(* ------------------------------------------------------------------------- *)

(* A PL 3-ball is compact, regular closed, with a PL 2-sphere as frontier   *)
(* (compare MOI_S4N_BALL_INTERIOR of pc_moi_s34_op1a, outside this closure). *)

let MOI_S3CH_BALL_FACTS = prove
 (`!c:real^3->bool.
     pl_ball 3 c
     ==> compact c /\ pl_sphere 2 (frontier c) /\ frontier c SUBSET c /\
         c SUBSET closure(interior c)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
    (X_CHOOSE_THEN `q:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_sphere 2 (frontier c:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[pl_sphere] THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `p:real^3->real^3`; `q:real^3->real^3`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOI_SCD_BALL_BOUNDARY_PLH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3->bool`; `p:real^3->real^3`;
                 `q:real^3->real^3`] MOI_SCD_BALL_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `homeomorphism (k,c) (p:real^3->real^3,q)` MP_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (k:real^3->bool) /\ convex k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (c:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier c SUBSET (c:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `k:real^3->bool` MOI_SCD_SIMPLEX_FILL) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(interior k:real^3->bool = {})` ASSUME_TAC THENL
   [SUBGOAL_THEN `affine hull (k:real^3->bool) = (:real^3)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN ASM_MESON_TAC[AFF_DIM_SIMPLEX];
      ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RELATIVE_INTERIOR_INTERIOR) THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `affine hull (k:real^3->bool) = (:real^3)` THEN
    ASM_REWRITE_TAC[AFFINE_HULL_EMPTY] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p:real^3->real^3) (interior k) = interior c` ASSUME_TAC THENL
   [SUBGOAL_THEN `interior (c:real^3->bool) = c DIFF frontier c` SUBST1_TAC THENL
     [REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
      MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `interior k = (k:real^3->bool) DIFF relative_frontier k` SUBST1_TAC THENL
     [UNDISCH_TAC `relative_frontier k = (k:real^3->bool) DIFF interior k` THEN
      MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^3->real^3`; `k:real^3->bool`; `relative_frontier k:real^3->bool`]
      IMAGE_DIFF_INJ_ALT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `!x. x IN k ==> (q:real^3->real^3) ((p:real^3->real^3) x) = x` THEN
        MESON_TAC[];
        UNDISCH_TAC `relative_frontier k = (k:real^3->bool) DIFF interior k` THEN SET_TAC[]];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ASSUME `IMAGE (p:real^3->real^3) k = c`;
                  ASSUME `IMAGE (p:real^3->real^3) (relative_frontier k) = frontier c`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(interior k) = (k:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^3->real^3`; `interior k:real^3->bool`;
                 `closure(interior c):real^3->bool`] IMAGE_CLOSURE_SUBSET) THEN
  ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET]);;

let MOI_S3CH_CELL_FACTS = prove
 (`!n d j:real^3->bool.
     pl_cell_with_boundary n d j ==> compact d /\ compact j /\ j SUBSET d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `homeomorphism (k,d) (f:real^3->real^3,g)` MP_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (k:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^3->bool) /\ compact (relative_frontier k)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED; COMPACT_RELATIVE_FRONTIER];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    EXPAND_TAC "d" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* PL facts of the model.                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CH_CELL_BALL = prove
 (`!n s b:real^N->bool. pl_cell_with_boundary n s b ==> pl_ball n s`,
  REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]);;

let MOI_S3CH_INTERVAL_BALL = prove
 (`!a b:real^3. (!i. 1 <= i /\ i <= 3 ==> a$i < b$i) ==> pl_ball 3 (interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interior(interval[a:real^3,b]) = {})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_3]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3CH_CELL_BALL THEN EXISTS_TAC `frontier(interval[a:real^3,b])` THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RELATIVE_FRONTIER_NONEMPTY_INTERIOR) THEN
  MATCH_MP_TAC MOI_S4A_POLY_CELL_3 THEN
  ASM_SIMP_TAC[POLYTOPE_INTERVAL; AFF_DIM_NONEMPTY_INTERIOR; DIMINDEX_3]);;

let MOI_S3CH_K_FACTS = prove
 (`pl_ball 3 moi_s3ch_k1 /\ pl_ball 3 moi_s3ch_k2 /\
   pl_sphere 2 (frontier moi_s3ch_k1) /\ pl_sphere 2 (frontier moi_s3ch_k2) /\
   compact moi_s3ch_k1 /\ compact moi_s3ch_k2`,
  SUBGOAL_THEN `pl_ball 3 moi_s3ch_k1 /\ pl_ball 3 moi_s3ch_k2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3CH_K_INTERVALS] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S3CH_INTERVAL_BALL THEN REWRITE_TAC[FORALL_3; VECTOR_3] THEN
    REAL_ARITH_TAC;
    ASM_MESON_TAC[MOI_S3CH_BALL_FACTS]]);;

(* The middle square as the image of the planar square.                     *)

let moi_s3ch_emb = new_definition
 `moi_s3ch_emb (z:real^2) = vector[z$1; &0; z$2]:real^3`;;

let MOI_S3CH_EMB = prove
 (`linear moi_s3ch_emb /\
   (!x y. moi_s3ch_emb x = moi_s3ch_emb y ==> x = y) /\
   (!s. IMAGE moi_s3ch_emb s = {y:real^3 | y$2 = &0 /\ (vector[y$1; y$3]:real^2) IN s})`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; moi_s3ch_emb; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s3ch_emb; CART_EQ; DIMINDEX_3; DIMINDEX_2; FORALL_3; FORALL_2;
                VECTOR_3] THEN MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; moi_s3ch_emb] THEN
    X_GEN_TAC `s:real^2->bool` THEN X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN
      SUBGOAL_THEN `vector[(z:real^2)$1; z$2]:real^2 = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
      STRIP_TAC THEN EXISTS_TAC `vector[(y:real^3)$1; y$3]:real^2` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_S3CH_Q_IMAGE = prove
 (`moi_s3ch_q = IMAGE moi_s3ch_emb (interval[--vector[&1;&1],vector[&1;&1]]) /\
   moi_s3ch_rq = IMAGE moi_s3ch_emb (interval[--vector[&1;&1],vector[&1;&1]] DIFF
                                     interval(--vector[&1;&1],vector[&1;&1])) /\
   vec 0 IN IMAGE moi_s3ch_emb (interval(--vector[&1;&1],vector[&1;&1]))`,
  REWRITE_TAC[MOI_S3CH_EMB] THEN
  REWRITE_TAC[moi_s3ch_q; moi_s3ch_rq; moi_s3ch_sq; EXTENSION; IN_ELIM_THM; IN_DIFF;
              IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT;
              VEC_COMPONENT] THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3CH_EMB_FACTS = prove
 (`(!s. relative_frontier (IMAGE moi_s3ch_emb s) =
        IMAGE moi_s3ch_emb (relative_frontier s)) /\
   (!s. relative_interior (IMAGE moi_s3ch_emb s) =
        IMAGE moi_s3ch_emb (relative_interior s)) /\
   (!s. aff_dim (IMAGE moi_s3ch_emb s) = aff_dim s) /\
   (!s. polytope s ==> polytope (IMAGE moi_s3ch_emb s))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN TRY DISCH_TAC THEN
  FIRST [MATCH_MP_TAC RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE;
         MATCH_MP_TAC RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE;
         MATCH_MP_TAC AFF_DIM_INJECTIVE_LINEAR_IMAGE;
         MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE] THEN
  ASM_MESON_TAC[MOI_S3CH_EMB]);;

let MOI_S3CH_Q_FACTS = prove
 (`pl_cell_with_boundary 2 moi_s3ch_q moi_s3ch_rq /\
   relative_frontier moi_s3ch_q = moi_s3ch_rq /\
   vec 0 IN relative_interior moi_s3ch_q /\
   convex moi_s3ch_q /\ compact moi_s3ch_q /\ polytope moi_s3ch_q`,
  SUBGOAL_THEN `~(interior(interval[--vector[&1;&1],vector[&1;&1]]):real^2->bool = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2;
                VECTOR_2; VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope moi_s3ch_q /\ relative_frontier moi_s3ch_q = moi_s3ch_rq /\
                vec 0 IN relative_interior moi_s3ch_q /\ aff_dim moi_s3ch_q = &2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3CH_Q_IMAGE; MOI_S3CH_EMB_FACTS] THEN
    ASM_SIMP_TAC[MOI_S3CH_EMB_FACTS; POLYTOPE_INTERVAL; RELATIVE_FRONTIER_NONEMPTY_INTERIOR;
                 RELATIVE_INTERIOR_NONEMPTY_INTERIOR; FRONTIER_CLOSED_INTERVAL;
                 INTERIOR_CLOSED_INTERVAL; AFF_DIM_NONEMPTY_INTERIOR; DIMINDEX_2;
                 MOI_S3CH_Q_IMAGE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT] THEN
  SUBST1_TAC(SYM(ASSUME `relative_frontier moi_s3ch_q = moi_s3ch_rq`)) THEN
  MP_TAC(ISPEC `moi_s3ch_q` (INST_TYPE [`:2`,`:M`] MOI_S4A_POLY_CELL)) THEN
  ASM_REWRITE_TAC[DIMINDEX_2]);;

let MOI_S3CH_L_CELLS = prove
 (mk_imp(MOI_SCH3_DISK_COMPLEMENT,
  `pl_cell_with_boundary 2 moi_s3ch_l1 moi_s3ch_rq /\
   pl_cell_with_boundary 2 moi_s3ch_l2 moi_s3ch_rq`),
  DISCH_TAC THEN REWRITE_TAC[MOI_S3CH_MODEL_SETS] THEN CONJ_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MOI_S3CH_K_FACTS; MOI_S3CH_Q_FACTS] THEN
  REWRITE_TAC[MOI_S3CH_MODEL_SETS]);;

(* ------------------------------------------------------------------------- *)
(* The data: the splitting disk lies in both ball frontiers (a PL 2-cell     *)
(* contains no ball, by invariance of dimension), and its complements in    *)
(* the two frontier spheres are PL 2-cells with the same boundary.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CH_NO_BALL = prove
 (`!(dd:real^3->bool) jj x r.
     pl_cell_with_boundary 2 dd jj /\ &0 < r ==> ~(ball(x,r) SUBSET dd)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
     (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `homeomorphism (t,dd) (f:real^3->real^3,g)` MP_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `ball(x:real^3,r)`; `t:real^3->bool`]
    INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN) THEN
  SUBGOAL_THEN `aff_dim (t:real^3->bool) = &2` SUBST1_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  ASM_REWRITE_TAC[CONVEX_BALL; AFF_DIM_BALL; DIMINDEX_3] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ALL_TAC; INT_ARITH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `dd:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^3->bool` THEN
    REWRITE_TAC[HULL_SUBSET] THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) dd = t` THEN
    UNDISCH_TAC `ball(x:real^3,r) SUBSET dd` THEN SET_TAC[];
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!y. y IN dd ==> (f:real^3->real^3) ((g:real^3->real^3) y) = y` THEN
    UNDISCH_TAC `(g:real^3->real^3) x' = g y` THEN
    UNDISCH_TAC `x' IN ball(x:real^3,r)` THEN UNDISCH_TAC `y IN ball(x:real^3,r)` THEN
    UNDISCH_TAC `ball(x:real^3,r) SUBSET dd` THEN MESON_TAC[SUBSET]]);;

let MOI_S3CH_DISK_IN_FRONTIER1 = prove
 (`!c1 c2 dd jj:real^3->bool.
     pl_ball 3 c1 /\ pl_ball 3 c2 /\ c1 INTER c2 = dd /\ pl_cell_with_boundary 2 dd jj
     ==> dd SUBSET frontier c1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `c1:real^3->bool` MOI_S3CH_BALL_FACTS) THEN
  MP_TAC(SPEC `c2:real^3->bool` MOI_S3CH_BALL_FACTS) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN dd` THEN UNDISCH_TAC `(c1:real^3->bool) INTER c2 = dd` THEN
    SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `~(interior c1 INTER interior c2:real^3->bool = {})` MP_TAC THENL
   [MP_TAC(ISPECL [`interior c1:real^3->bool`; `interior c2:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^3` THEN
    UNDISCH_TAC `(x:real^3) IN dd` THEN UNDISCH_TAC `(x:real^3) IN interior c1` THEN
    UNDISCH_TAC `(c1:real^3->bool) INTER c2 = dd` THEN
    UNDISCH_TAC `(c2:real^3->bool) SUBSET closure(interior c2)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN
  MP_TAC(ISPEC `interior c1 INTER interior c2:real^3->bool` OPEN_CONTAINS_BALL) THEN
  SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `jj:real^3->bool`; `y:real^3`; `e:real`]
    MOI_S3CH_NO_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `c1:real^3->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `c2:real^3->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `ball(y:real^3,e) SUBSET interior c1 INTER interior c2` THEN
  UNDISCH_TAC `(c1:real^3->bool) INTER c2 = dd` THEN SET_TAC[]);;

let MOI_S3CH_DISK_IN_FRONTIER = prove
 (`!c1 c2 dd jj:real^3->bool.
     pl_ball 3 c1 /\ pl_ball 3 c2 /\ c1 INTER c2 = dd /\ pl_cell_with_boundary 2 dd jj
     ==> dd SUBSET frontier c1 /\ dd SUBSET frontier c2`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_S3CH_DISK_IN_FRONTIER1 THEN
    MAP_EVERY EXISTS_TAC [`c2:real^3->bool`; `jj:real^3->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3CH_DISK_IN_FRONTIER1 THEN
    MAP_EVERY EXISTS_TAC [`c1:real^3->bool`; `jj:real^3->bool`] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]]);;

let MOI_S3CH_E_CELL = prove
 (mk_imp(MOI_SCH3_DISK_COMPLEMENT,
  `!c dd jj:real^3->bool.
     pl_ball 3 c /\ pl_cell_with_boundary 2 dd jj /\ dd SUBSET frontier c
     ==> pl_cell_with_boundary 2 ((frontier c DIFF dd) UNION jj) jj /\
         frontier c DIFF (dd DIFF jj) = (frontier c DIFF dd) UNION jj /\
         dd UNION ((frontier c DIFF dd) UNION jj) = frontier c /\
         dd INTER ((frontier c DIFF dd) UNION jj) = jj`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(jj:real^3->bool) SUBSET dd` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3CH_CELL_FACTS]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MOI_S3CH_BALL_FACTS];
    UNDISCH_TAC `(jj:real^3->bool) SUBSET dd` THEN
    UNDISCH_TAC `(dd:real^3->bool) SUBSET frontier c` THEN SET_TAC[];
    UNDISCH_TAC `(jj:real^3->bool) SUBSET dd` THEN
    UNDISCH_TAC `(dd:real^3->bool) SUBSET frontier c` THEN SET_TAC[];
    UNDISCH_TAC `(jj:real^3->bool) SUBSET dd` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A PL chart of the disk with the centre at the given point: the cone map  *)
(* from the apex 0 over rq to the apex g p over the boundary of a simplex.  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CH_RQ_FACTS = prove
 (`pl_polyhedron moi_s3ch_rq /\ ~(moi_s3ch_rq = {}) /\ ~(vec 0 IN moi_s3ch_rq) /\
   locally_polyhedral moi_s3ch_rq /\
   (!x y. x IN moi_s3ch_rq /\ y IN moi_s3ch_rq /\ y IN segment[vec 0,x] ==> y = x) /\
   UNIONS {segment[vec 0,x] | x IN moi_s3ch_rq} = moi_s3ch_q`,
  MP_TAC MOI_S3CH_Q_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron moi_s3ch_rq` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s3ch_rq = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 1:real^3` THEN
    SIMP_TAC[moi_s3ch_rq; moi_s3ch_sq; IN_ELIM_THM; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_S3CH_MODEL_SETS] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`moi_s3ch_q`; `vec 0:real^3`] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`moi_s3ch_q`; `vec 0:real^3`] MOI_CON_CONE_RF) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3CH_PHI = prove
 (`!dd jj (p:real^3).
     pl_cell_with_boundary 2 dd jj /\ p IN dd DIFF jj
     ==> ?phi phi'. pl_homeomorphism (moi_s3ch_q,dd) (phi,phi') /\
                    IMAGE phi moi_s3ch_rq = jj /\ phi (vec 0) = p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
     (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  MP_TAC(CONJUNCT1 MOI_S3CH_Q_FACTS) THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `tq:real^3->bool` (X_CHOOSE_THEN `fq:real^3->real^3`
     (X_CHOOSE_THEN `gq:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tq:real^3->bool`; `t:real^3->bool`; `&2:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^3->real^3` (X_CHOOSE_THEN `sg':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism (t,dd) (f:real^3->real^3,g)` MP_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (t:real^3->bool) /\ compact t /\ polytope t /\
                convex (tq:real^3->bool) /\ compact tq /\ polytope tq`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  ABBREV_TAC `p' = (g:real^3->real^3) p` THEN
  SUBGOAL_THEN `(p':real^3) IN relative_interior t /\ ~(p' IN relative_frontier t)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(p':real^3) IN t /\ ~(p' IN relative_frontier t)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "p'" THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (g:real^3->real^3) dd = t` THEN
        UNDISCH_TAC `(p:real^3) IN dd DIFF jj` THEN SET_TAC[];
        DISCH_TAC THEN
        SUBGOAL_THEN `(p:real^3) IN jj` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^3->real^3) p` THEN
          CONJ_TAC THENL
           [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
            UNDISCH_TAC `(p:real^3) IN dd DIFF jj` THEN SET_TAC[];
            FIRST_ASSUM ACCEPT_TAC];
          UNDISCH_TAC `(p:real^3) IN dd DIFF jj` THEN SET_TAC[]]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((p':real^3) IN relative_frontier t)` THEN
    UNDISCH_TAC `(p':real^3) IN t` THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (tq,moi_s3ch_q) (fq:real^3->real^3,gq)` MP_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (gq:real^3->real^3) moi_s3ch_rq = relative_frontier tq` ASSUME_TAC THENL
   [MP_TAC(ISPEC `tq:real^3->bool` RELATIVE_FRONTIER_SUBSET) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `moi_s3ch_rq = IMAGE (fq:real^3->real^3) (relative_frontier tq)` THEN
    UNDISCH_TAC `!x. x IN tq ==> (gq:real^3->real^3) ((fq:real^3->real^3) x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (moi_s3ch_rq,relative_frontier t)
                  ((sg:real^3->real^3) o (gq:real^3->real^3),
                   (fq:real^3->real^3) o (sg':real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier tq:real^3->bool` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> concl th = `IMAGE (gq:real^3->real^3) moi_s3ch_rq = relative_frontier tq`)) THEN
    MATCH_MP_TAC MOI_SCD_PLH_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`moi_s3ch_q`; `tq:real^3->bool`] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[MOI_S3CH_RQ_FACTS; MOI_S3CH_MODEL_SETS] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th =
    `moi_s3ch_rq = IMAGE (fq:real^3->real^3) (relative_frontier tq)`)) THEN
  MP_TAC MOI_S3CH_RQ_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS {segment[p',y] | y IN relative_frontier t} = (t:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CON_CONE_RF THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:real^3->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [INT_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s3ch_rq`; `relative_frontier t:real^3->bool`; `vec 0:real^3`;
                 `p':real^3`; `(sg:real^3->real^3) o (gq:real^3->real^3)`;
                 `(fq:real^3->real^3) o (sg':real^3->real^3)`] MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`t:real^3->bool`; `p':real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(f:real^3->real^3) o moi_con_conemap moi_s3ch_rq (vec 0) (p':real^3)
                            ((sg:real^3->real^3) o (gq:real^3->real^3))`;
    `moi_con_conemap (relative_frontier t) (p':real^3) (vec 0)
       ((fq:real^3->real^3) o (sg':real^3->real^3)) o (g:real^3->real^3)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (moi_con_conemap moi_s3ch_rq (vec 0) (p':real^3)
                     ((sg:real^3->real^3) o (gq:real^3->real^3))) moi_s3ch_rq =
                  relative_frontier t` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!(h:real^3->real^3) k s t.
         (!x. x IN s ==> h x = k x) /\ IMAGE k s = t ==> IMAGE h s = t`) THEN
      EXISTS_TAC `(sg:real^3->real^3) o (gq:real^3->real^3)` THEN
      CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `pl_homeomorphism (moi_s3ch_rq,relative_frontier t)
                       ((sg:real^3->real^3) o (gq:real^3->real^3),
                        (fq:real^3->real^3) o (sg':real^3->real^3))` THEN
        SIMP_TAC[pl_homeomorphism; homeomorphism]];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`moi_s3ch_rq`; `vec 0:real^3`; `p':real^3`;
                   `(sg:real^3->real^3) o (gq:real^3->real^3)`] MOI_CON_CONEMAP_APEX) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "p'" THEN
    MATCH_MP_TAC(ASSUME `!y. y IN dd ==> (f:real^3->real^3) ((g:real^3->real^3) y) = y`) THEN
    UNDISCH_TAC `(p:real^3) IN dd DIFF jj` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* One half: a PL homeomorphism of a model half-cube onto a data ball that  *)
(* is phi on the square and maps the outer half l onto the complement of    *)
(* the open disk in the ball frontier (cell extension, gluing, Alexander    *)
(* extension over the ball).                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CH_PLH_RESTRICT = prove
 (`!(f:real^3->real^3) g s t s'.
     pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ pl_polyhedron s'
     ==> pl_homeomorphism (s',IMAGE f s') (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCD_PLH_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `t:real^3->bool`] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^3->bool` THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN ASM_MESON_TAC[pl_homeomorphism]);;

let MOI_S3CH_HALF = prove
 (mk_imp(MOI_SCH3_DISK_COMPLEMENT,
  `!k l c dd jj (phi:real^3->real^3) phi'.
     pl_ball 3 k /\ frontier k = moi_s3ch_q UNION l /\
     moi_s3ch_q INTER l = moi_s3ch_rq /\ pl_cell_with_boundary 2 l moi_s3ch_rq /\
     pl_ball 3 c /\ pl_cell_with_boundary 2 dd jj /\ dd SUBSET frontier c /\
     pl_homeomorphism (moi_s3ch_q,dd) (phi,phi') /\ IMAGE phi moi_s3ch_rq = jj
     ==> ?h h'. pl_homeomorphism (k,c) (h,h') /\
                (!x. x IN moi_s3ch_q ==> h x = phi x) /\
                IMAGE h l = frontier c DIFF (dd DIFF jj)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^3->bool`; `dd:real^3->bool`; `jj:real^3->bool`]
    (UNDISCH MOI_S3CH_E_CELL)) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `e = (frontier c DIFF dd) UNION (jj:real^3->bool)` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_homeomorphism (moi_s3ch_rq,jj) (phi:real^3->real^3,phi')`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (phi:real^3->real^3) moi_s3ch_rq = jj`)) THEN
    MATCH_MP_TAC MOI_S3CH_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_s3ch_q`; `dd:real^3->bool`] THEN
    ASM_REWRITE_TAC[MOI_S3CH_RQ_FACTS; MOI_S3CH_MODEL_SETS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^3->bool`; `moi_s3ch_rq`; `e:real^3->bool`; `jj:real^3->bool`;
                 `phi:real^3->real^3`; `phi':real^3->real^3`] MOI_SPU_CELL_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3->real^3` (X_CHOOSE_THEN `e1':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `closed moi_s3ch_q /\ closed (l:real^3->bool) /\ closed (dd:real^3->bool) /\
                closed (e:real^3->bool)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    ASM_MESON_TAC[MOI_S3CH_CELL_FACTS; MOI_S3CH_Q_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s3ch_q`; `l:real^3->bool`; `dd:real^3->bool`; `e:real^3->bool`;
                 `phi:real^3->real^3`; `phi':real^3->real^3`;
                 `e1:real^3->real^3`; `e1':real^3->real^3`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `h0 = \x:real^3. if x IN moi_s3ch_q then (phi:real^3->real^3) x
                              else (e1:real^3->real^3) x` THEN
  ABBREV_TAC `h0' = \y:real^3. if y IN dd then (phi':real^3->real^3) y
                               else (e1':real^3->real^3) y` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3->bool`; `h0:real^3->real^3`;
                 `h0':real^3->real^3`] MOI_SCD_COR_EXTEND_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hh:real^3->real^3` (X_CHOOSE_THEN `hh':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`hh:real^3->real^3`; `hh':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[IN_UNION] THEN
    EXPAND_TAC "h0" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (hh:real^3->real^3) l = IMAGE (e1:real^3->real^3) l` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) g s. (!x. x IN s ==> f x = g x)
                            ==> IMAGE f s = IMAGE g s`) THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[IN_UNION] THEN
    EXPAND_TAC "h0" THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check
      (fun th -> try fst(dest_eq(snd(dest_imp(snd(strip_forall(concl th)))))) =
                     `(e1:real^3->real^3) x` with Failure _ -> false)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism (l,e) (e1:real^3->real^3,e1')` THEN
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

(* ------------------------------------------------------------------------- *)
(* The theorem CHART: glue the two halves over the square and precompose    *)
(* with the fixed chart theta.                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CH_IMAGE_EQ_ON = prove
 (`!(f:real^3->real^3) g s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`,
  SET_TAC[]);;

let CHART = prove
 (MOI_S32_CHART,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:real^3->bool`; `c2:real^3->bool`; `dd:real^3->bool`; `jj:real^3->bool`]
    MOI_S3CH_DISK_IN_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`dd:real^3->bool`; `jj:real^3->bool`; `p:real^3`] MOI_S3CH_PHI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^3` (X_CHOOSE_THEN `phi':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(UNDISCH MOI_S3CH_L_CELLS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier moi_s3ch_k1 = moi_s3ch_q UNION moi_s3ch_l1 /\
                moi_s3ch_q INTER moi_s3ch_l1 = moi_s3ch_rq /\
                frontier moi_s3ch_k2 = moi_s3ch_q UNION moi_s3ch_l2 /\
                moi_s3ch_q INTER moi_s3ch_l2 = moi_s3ch_rq`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3CH_MODEL_SETS] THEN
    MP_TAC MOI_S3CH_MODEL_SETS THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`moi_s3ch_k1`; `moi_s3ch_l1`; `c1:real^3->bool`; `dd:real^3->bool`;
                `jj:real^3->bool`; `phi:real^3->real^3`; `phi':real^3->real^3`]
    (UNDISCH MOI_S3CH_HALF)) THEN
  ASM_REWRITE_TAC[MOI_S3CH_K_FACTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^3->real^3` (X_CHOOSE_THEN `h1':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`moi_s3ch_k2`; `moi_s3ch_l2`; `c2:real^3->bool`; `dd:real^3->bool`;
                `jj:real^3->bool`; `phi:real^3->real^3`; `phi':real^3->real^3`]
    (UNDISCH MOI_S3CH_HALF)) THEN
  ASM_REWRITE_TAC[MOI_S3CH_K_FACTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^3->real^3` (X_CHOOSE_THEN `h2':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^3) moi_s3ch_q = dd` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_s3ch_q,dd) (phi:real^3->real^3,phi')` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s3ch_k1`; `moi_s3ch_k2`; `c1:real^3->bool`; `c2:real^3->bool`;
                 `h1:real^3->real^3`; `h1':real^3->real^3`;
                 `h2:real^3->real^3`; `h2':real^3->real^3`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S3CH_MODEL_SETS] THEN
    MP_TAC(SPEC `c1:real^3->bool` MOI_S3CH_BALL_FACTS) THEN
    MP_TAC(SPEC `c2:real^3->bool` MOI_S3CH_BALL_FACTS) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MOI_S3CH_K_FACTS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (phi:real^3->real^3) moi_s3ch_q` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOI_S3CH_IMAGE_EQ_ON THEN ASM_REWRITE_TAC[];
                    ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S3CH_MODEL_SETS] THEN
  ABBREV_TAC `hh = \x:real^3. if x IN moi_s3ch_k1 then (h1:real^3->real^3) x
                              else (h2:real^3->real^3) x` THEN
  ABBREV_TAC `hh' = \y:real^3. if y IN c1 then (h1':real^3->real^3) y
                               else (h2':real^3->real^3) y` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(!x. x IN moi_s3ch_k1 ==> (hh:real^3->real^3) x = h1 x) /\
                (!x. x IN moi_s3ch_k2 ==> hh x = h2 x)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "hh" THEN CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s3ch_q` (fun th -> ASM_SIMP_TAC[th]) THEN
    MP_TAC MOI_S3CH_MODEL_SETS THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_CHOOSE_TAC `th':real^3->real^3` MOI_S3CH_THETA_HOMEO THEN
  MAP_EVERY EXISTS_TAC [`(hh:real^3->real^3) o moi_s3ch_theta`;
                        `(th':real^3->real^3) o (hh':real^3->real^3)`] THEN
  REWRITE_TAC[IMAGE_o; o_THM; MOI_S3CH_IMAGES] THEN
  SUBGOAL_THEN `moi_s3ch_q SUBSET moi_s3ch_k1 /\ moi_s3ch_q SUBSET moi_s3ch_k2 /\
                moi_s3ch_rq SUBSET moi_s3ch_q /\ vec 0 IN moi_s3ch_q /\
                moi_s3ch_l1 SUBSET moi_s3ch_k1 /\ moi_s3ch_l2 SUBSET moi_s3ch_k2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `moi_s3ch_k1` MOI_S3CH_BALL_FACTS) THEN
    MP_TAC(SPEC `moi_s3ch_k2` MOI_S3CH_BALL_FACTS) THEN
    REWRITE_TAC[MOI_S3CH_K_FACTS] THEN MP_TAC MOI_S3CH_MODEL_SETS THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s3ch_kk` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pl_homeomorphism (moi_s3ch_kk,c1 UNION c2) (hh:real^3->real^3,hh')` THEN
    SIMP_TAC[pl_homeomorphism];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (h1:real^3->real^3) moi_s3ch_k1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3CH_IMAGE_EQ_ON THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `pl_homeomorphism (moi_s3ch_k1,c1) (h1:real^3->real^3,h1')` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism]];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (h2:real^3->real^3) moi_s3ch_k2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3CH_IMAGE_EQ_ON THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `pl_homeomorphism (moi_s3ch_k2,c2) (h2:real^3->real^3,h2')` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism]];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (phi:real^3->real^3) moi_s3ch_q` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC MOI_S3CH_IMAGE_EQ_ON THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s3ch_k1` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (phi:real^3->real^3) moi_s3ch_rq` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC MOI_S3CH_IMAGE_EQ_ON THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s3ch_k1 /\ x IN moi_s3ch_q`
      (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (h1:real^3->real^3) moi_s3ch_l1` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC MOI_S3CH_IMAGE_EQ_ON THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s3ch_k1` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (h2:real^3->real^3) moi_s3ch_l2` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC MOI_S3CH_IMAGE_EQ_ON THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s3ch_k2` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    SUBGOAL_THEN `vec 0 IN moi_s3ch_k1` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM SET_TAC[]]);;

