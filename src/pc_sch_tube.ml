(* ========================================================================= *)
(* pc_sch_tube: generic facts on collared spheres (sch_neck) in real^3 used  *)
(* by the surgery construction: derivatives along the unit sphere, transfer  *)
(* of critical points (sch_crit) and of horizontal Morse charts (sch_hchart) *)
(* between parametrizations that agree near a point, symmetries of the Morse *)
(* data (coordinate swap in the chart, reflection x3 -> -x3), and the tube   *)
(* lemma: a smooth embedding of the unit sphere extends to a collar          *)
(* (sch_neck) with the same values and tangential derivatives on the sphere. *)
(* Also the local saddle witness: the hyperboloid x2^2 + x3^2 = 1 + x1^2 has *)
(* an exact (1,-1) chart at (0,0,1).                                         *)
(* Main results: SCH5_TUBE_NECK (tube lemma), SCH5_NECK_FROM_TRANSVERSE     *)
(* (collars from maps transverse to an embedded sphere, used with a model    *)
(* collar near the caps), SCH5_CRIT_LOCAL_BALL, SCH5_HCHART_LOCAL,           *)
(* SCH5_HCHART_SWAP, SCH5_MAX_NOT_SADDLE, SCH5_MORSE_FLIP,                   *)
(* SCH5_SADDLES_FLIP, SCH5_LEVEL_FLIP, SCH5_HYP_SADDLE_HCHART, SCH5_HYP_CRIT. *)
(* ========================================================================= *)

needs "src/pc_sch_stmt.ml";;
needs "src/pc_sch_slab.ml";;
needs "src/pc_sch_isoext.ml";;
let sch5_saved_interface = !the_interface;;
needs "Multivariate/cross.ml";;
the_interface := sch5_saved_interface;;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The local saddle witness.  The hyperboloid                               *)
(* x2^2 + x3^2 = 1 + x1^2 has the exact horizontal chart with k = (1,-1) at *)
(* its top point (0,0,1): ph u = sqrt(2 + u1^2 - u2^2) u, with the inverse  *)
(* w / sqrt(1 + sqrt(1 + w1^2 - w2^2)); and its vertical parametrization    *)
(* x |-> (x1, x2, sqrt(1 + x1^2 - x2^2)) has a critical point (sch_crit) at *)
(* the north pole.  So exact saddle charts and critical points coexist.     *)
(* ------------------------------------------------------------------------- *)

let SCH5_HYPQ_SMOOTH = prove
 (`!s. open s ==> smooth_map_on s (\u:real^2. lift(u$1 pow 2 - u$2 pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. smooth_map_on s (\u:real^2. lift(u$k pow 2))` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `\u:real^2. lift(u$k)`; `2`] SMOOTH_MAP_ON_LIFT_POW) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `\u:real^2. u`; `k:num`] SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[]);;

let SCH5_HYPQ_BOUND = prove
 (`!u:real^2. abs(u$1 pow 2 - u$2 pow 2) <= norm u pow 2`,
  GEN_TAC THEN REWRITE_TAC[NORM_POW_2; DOT_2] THEN
  MP_TAC(SPEC `(u:real^2)$1` REAL_LE_SQUARE) THEN MP_TAC(SPEC `(u:real^2)$2` REAL_LE_SQUARE) THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let SCH5_HYP_CHART_SMOOTH = prove
 (`smooth_map_on (ball(vec 0:real^2,&1))
                 (\u. sqrt(&2 + (u$1 pow 2 - u$2 pow 2)) % u) /\
   smooth_map_on (ball(vec 0:real^2,&1 / &2))
                 (\w. inv(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))) % w)`,
  SUBGOAL_THEN `!u:real^2 r. u IN ball(vec 0,r) ==> norm u pow 2 < r pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`;
                   `\u:real^2. lift(sqrt(&2 + (u$1 pow 2 - u$2 pow 2)))`;
                   `\u:real^2. u`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_BALL; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\u:real^2. lift(&2 + (u$1 pow 2 - u$2 pow 2))`]
      SMOOTH_MAP_ON_LIFT_SQRT) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SCH5_HYPQ_SMOOTH THEN REWRITE_TAC[OPEN_BALL];
      X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^2`; `&1`]) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `u:real^2` SCH5_HYPQ_BOUND) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. w IN ball(vec 0,&1 / &2)
                           ==> &0 < &1 + (w$1 pow 2 - w$2 pow 2)` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^2`; `&1 / &2`]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(SPEC `w:real^2` SCH5_HYPQ_BOUND) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0:real^2,&1 / &2))
                  (\w. lift(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^2,&1 / &2)`;
                   `\w:real^2. lift(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))`]
      SMOOTH_MAP_ON_LIFT_SQRT) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
      MP_TAC(ISPECL [`ball(vec 0:real^2,&1 / &2)`;
                     `\w:real^2. lift(&1 + (w$1 pow 2 - w$2 pow 2))`]
        SMOOTH_MAP_ON_LIFT_SQRT) THEN
      REWRITE_TAC[LIFT_DROP; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SCH5_HYPQ_SMOOTH THEN REWRITE_TAC[OPEN_BALL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1 / &2)`;
                 `\w:real^2. lift(inv(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))))`;
                 `\w:real^2. w`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_BALL; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1 / &2)`;
                 `\w:real^2. lift(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2))))`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  ASM_REWRITE_TAC[LIFT_DROP; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN MATCH_MP_TAC SQRT_POS_LE THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let SCH5_HYP_INV1 = prove
 (`!u:real^2.
     norm u < &1 / &5
     ==> norm(sqrt(&2 + (u$1 pow 2 - u$2 pow 2)) % u) < &1 / &2 /\
         inv(sqrt(&1 + sqrt(&1 + ((sqrt(&2 + (u$1 pow 2 - u$2 pow 2)) % u)$1 pow 2 -
                                  (sqrt(&2 + (u$1 pow 2 - u$2 pow 2)) % u)$2 pow 2)))) %
         (sqrt(&2 + (u$1 pow 2 - u$2 pow 2)) % u) = u`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(u:real^2) pow 2 < (&1 / &5) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `u:real^2` SCH5_HYPQ_BOUND) THEN
  ABBREV_TAC `q = (u:real^2)$1 pow 2 - u$2 pow 2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs q < &1 / &25` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(u:real^2) pow 2 < (&1 / &5) pow 2` THEN
    UNDISCH_TAC `abs q <= norm(u:real^2) pow 2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2 + q) /\ sqrt(&2 + q) pow 2 = &2 + q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN
    UNDISCH_TAC `abs q < &1 / &25` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `l = sqrt(&2 + q)` THEN
  SUBGOAL_THEN `(l % (u:real^2))$1 pow 2 - (l % u)$2 pow 2 = l pow 2 * q` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN EXPAND_TAC "q" THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(&1 + (&2 + q) * q) = &1 + q` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
     [UNDISCH_TAC `abs q < &1 / &25` THEN REAL_ARITH_TAC; CONV_TAC REAL_RING];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 + &1 + q = &2 + q`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `l < &3 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_LT_FROM_SQ THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs q < &1 / &25` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
  SUBGOAL_THEN `norm(u:real^2) < &1 / &5` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `l * norm(u:real^2) <= &3 / &2 * norm u` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPEC `u:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC);;

let SCH5_HYP_INV2 = prove
 (`!w:real^2.
     norm w < &1 / &2
     ==> sqrt(&2 + ((inv(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))) % w)$1 pow 2 -
                    (inv(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))) % w)$2 pow 2)) %
         (inv(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))) % w) = w`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(w:real^2) pow 2 < (&1 / &2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `w:real^2` SCH5_HYPQ_BOUND) THEN
  ABBREV_TAC `p = (w:real^2)$1 pow 2 - w$2 pow 2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs p < &1 / &4` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(w:real^2) pow 2 < (&1 / &2) pow 2` THEN
    UNDISCH_TAC `abs p <= norm(w:real^2) pow 2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 + p) /\ sqrt(&1 + p) pow 2 = &1 + p` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN
    UNDISCH_TAC `abs p < &1 / &4` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `sg = sqrt(&1 + p)` THEN
  SUBGOAL_THEN `&0 < sqrt(&1 + sg) /\ sqrt(&1 + sg) pow 2 = &1 + sg` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN
    UNDISCH_TAC `&0 < sg` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = sqrt(&1 + sg)` THEN
  SUBGOAL_THEN `(inv m % (w:real^2))$1 pow 2 - (inv m % w)$2 pow 2 = sg - &1` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `(inv m * (w:real^2)$1) pow 2 - (inv m * w$2) pow 2 = inv(m pow 2) * p`
    SUBST1_TAC THENL
     [EXPAND_TAC "p" THEN REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p = sg pow 2 - &1` SUBST1_TAC THENL
     [UNDISCH_TAC `sg pow 2 = &1 + p` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&1 + sg = &0)` MP_TAC THENL
     [UNDISCH_TAC `&0 < sg` THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&2 + (sg - &1) = &1 + sg`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

let SCH5_HYP_CHART_DIFFEO = prove
 (`diffeomorphism_on (ball(vec 0:real^2,&1 / &5))
     (IMAGE (\u. sqrt(&2 + (u$1 pow 2 - u$2 pow 2)) % u) (ball(vec 0,&1 / &5)))
     (\u. sqrt(&2 + (u$1 pow 2 - u$2 pow 2)) % u)
     (\w. inv(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))) % w)`,
  ABBREV_TAC `ph = \u:real^2. sqrt(&2 + (u$1 pow 2 - u$2 pow 2)) % u` THEN
  ABBREV_TAC `ph' = \w:real^2. inv(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))) % w` THEN
  SUBGOAL_THEN `(!u:real^2. norm u < &1 / &5
                  ==> norm((ph:real^2->real^2) u) < &1 / &2 /\
                      (ph':real^2->real^2)(ph u) = u) /\
                (!w:real^2. norm w < &1 / &2 ==> (ph:real^2->real^2)(ph' w) = w)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ph"; "ph'"] THEN REWRITE_TAC[SCH5_HYP_INV1; SCH5_HYP_INV2];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0:real^2,&1)) (ph:real^2->real^2) /\
                smooth_map_on (ball(vec 0:real^2,&1 / &2)) (ph':real^2->real^2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ph"; "ph'"] THEN REWRITE_TAC[SCH5_HYP_CHART_SMOOTH]; ALL_TAC] THEN
  ABBREV_TAC `t = {w:real^2 | w IN ball(vec 0,&1 / &2) /\
                              (ph':real^2->real^2) w IN ball(vec 0,&1 / &5)}` THEN
  SUBGOAL_THEN `IMAGE (ph:real^2->real^2) (ball(vec 0,&1 / &5)) = t` SUBST1_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_BALL_0] THEN
    X_GEN_TAC `w:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      STRIP_TAC THEN EXISTS_TAC `(ph':real^2->real^2) w` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN REWRITE_TAC[OPEN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1 / &2)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN SET_TAC[];
    X_GEN_TAC `u:real^2` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL_0] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `w:real^2` THEN EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL_0] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* The local saddle witness: an exact (1,-1) chart of the hyperboloid. *)

let SCH5_HYP_SADDLE_HCHART = prove
 (`sch_hchart {x:real^3 | x$2 pow 2 + x$3 pow 2 = &1 + x$1 pow 2} (vector[&0; &0; &1])
              (&1) (-- &1)`,
  REWRITE_TAC[sch_hchart; VECTOR_3] THEN
  MAP_EVERY EXISTS_TAC
   [`&1 / &5`; `\u:real^2. sqrt(&2 + (u$1 pow 2 - u$2 pow 2)) % u`;
    `\w:real^2. inv(sqrt(&1 + sqrt(&1 + (w$1 pow 2 - w$2 pow 2)))) % w`] THEN
  REWRITE_TAC[SCH5_HYP_CHART_DIFFEO; VECTOR_MUL_RZERO; SCH_VECTOR2_00] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN REWRITE_TAC[IN_BALL_0; IN_ELIM_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[VECTOR_3; VECTOR_MUL_COMPONENT] THEN
  SUBGOAL_THEN `norm(u:real^2) pow 2 < (&1 / &5) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `u:real^2` SCH5_HYPQ_BOUND) THEN
  ABBREV_TAC `q = (u:real^2)$1 pow 2 - u$2 pow 2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs q < &1 / &25` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(u:real^2) pow 2 < (&1 / &5) pow 2` THEN
    UNDISCH_TAC `abs q <= norm(u:real^2) pow 2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 + q) pow 2 = &2 + q` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN UNDISCH_TAC `abs q < &1 / &25` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `l = sqrt(&2 + q)` THEN
  SUBGOAL_THEN `(l * (u:real^2)$1) pow 2 - (l * u$2) pow 2 = (&2 + q) * q` ASSUME_TAC THENL
   [UNDISCH_TAC `l pow 2 = &2 + q` THEN EXPAND_TAC "q" THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(l * (u:real^2)$2) pow 2 + z pow 2 = &1 + (l * u$1) pow 2 <=>
                (z - (&1 + q)) * (z + (&1 + q)) = &0` SUBST1_TAC THENL
   [UNDISCH_TAC `(l * (u:real^2)$1) pow 2 - (l * u$2) pow 2 = (&2 + q) * q` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_ARITH `&1 + &1 * a + -- &1 * b = &1 + (a - b)`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs(z - &1) < &1 / &5` THEN UNDISCH_TAC `abs q < &1 / &25` THEN
  REAL_ARITH_TAC);;

(* The vertical parametrization of the hyperboloid near its top point has a *)
(* critical point there.                                                     *)

let SCH5_LIFT_SQ_DERIV_AT_E3 = prove
 (`!k. k = 1 \/ k = 2
       ==> ((\x:real^3. x$k % lift(x$k)) has_derivative (\h. vec 0)) (at (basis 3))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x:real^3. x$k`; `\h:real^3. h$k`; `\x:real^3. lift(x$k)`;
                 `\h:real^3. lift(h$k)`; `basis 3:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[o_DEF; HAS_DERIVATIVE_LIFT_COMPONENT] THEN
  SUBGOAL_THEN `(basis 3:real^3)$k = &0` SUBST1_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_NUM; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_LID]);;

let SCH5_HYP_CRIT = prove
 (`sch_crit (\x:real^3. vector[x$1; x$2; sqrt(&1 + (x$1 pow 2 - x$2 pow 2))]:real^3)
            (basis 3) /\
   (\x:real^3. vector[x$1; x$2; sqrt(&1 + (x$1 pow 2 - x$2 pow 2))]:real^3) (basis 3) =
     vector[&0; &0; &1] /\
   (!x:real^3. x IN sphere(vec 0,&1)
               ==> (\x:real^3. vector[x$1; x$2; sqrt(&1 + (x$1 pow 2 - x$2 pow 2))]:real^3) x
                   IN {y:real^3 | y$2 pow 2 + y$3 pow 2 = &1 + y$1 pow 2})`,
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; BASIS_COMPONENT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_1];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_3; IN_ELIM_THM] THEN
    REWRITE_TAC[VECTOR_3] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(&1 + ((x:real^3)$1 pow 2 - x$2 pow 2)) pow 2 =
                  &1 + (x$1 pow 2 - x$2 pow 2)` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN
      MP_TAC(SPEC `(x:real^3)$1` REAL_LE_SQUARE) THEN MP_TAC(SPEC `(x:real^3)$3` REAL_LE_SQUARE) THEN
      UNDISCH_TAC `(x:real^3)$1 * x$1 + x$2 * x$2 + x$3 * x$3 = &1` THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC]] THEN
  REWRITE_TAC[sch_crit] THEN SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH] THEN
  SUBGOAL_THEN
   `((\x:real^3. vector[x$1; x$2; &0]:real^3) has_derivative
     (\x:real^3. vector[x$1; x$2; &0]:real^3)) (at (basis 3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x:real^3. lift(&1 + (x$1 pow 2 - x$2 pow 2))) has_derivative (\h. vec 0))
    (at (basis 3))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^3. lift(&1 + (x$1 pow 2 - x$2 pow 2))) =
                  (\x. lift(&1) + (x$1 % lift(x$1) - x$2 % lift(x$2)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_ADD; GSYM LIFT_SUB] THEN
      REWRITE_TAC[REAL_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\h:real^3. vec 0:real^1) = (\h. vec 0 + (vec 0 - vec 0))` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC SCH5_LIFT_SQ_DERIV_AT_E3 THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x:real^3. lift(sqrt(&1 + (x$1 pow 2 - x$2 pow 2)))) has_derivative (\h. vec 0))
    (at (basis 3))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^3. lift(sqrt(&1 + (x$1 pow 2 - x$2 pow 2)))) =
                  (lift o sqrt o drop) o (\x. lift(&1 + (x$1 pow 2 - x$2 pow 2)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN `(\h:real^3. vec 0:real^1) = (\h. inv(&2 * sqrt(&1)) % h) o (\h. vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_MUL_RZERO]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x:real^3. vector[x$1; x$2; sqrt(&1 + (x$1 pow 2 - x$2 pow 2))]:real^3) has_derivative
     (\h. vector[h$1; h$2; &0] + drop(vec 0:real^1) % basis 3)) (at (basis 3))`
  MP_TAC THENL
   [SUBGOAL_THEN
     `(\x:real^3. vector[x$1; x$2; sqrt(&1 + (x$1 pow 2 - x$2 pow 2))]:real^3) =
      (\x. vector[x$1; x$2; &0] + drop(lift(sqrt(&1 + (x$1 pow 2 - x$2 pow 2)))) % basis 3)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP] THEN X_GEN_TAC `x:real^3` THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_3]);;

(* ------------------------------------------------------------------------- *)
(* Derivatives along the unit sphere.  A map that is constant                *)
(* on the sphere near t has zero derivative in the tangent directions at t   *)
(* (great circles through t); so maps that agree on the sphere near t have   *)
(* the same tangential derivatives.                                          *)
(* ------------------------------------------------------------------------- *)

(* Chain rule for curves and the derivative of great circles (the statements *)
(* of SMT_CHAIN_VECTOR and SMT_CIRCLE_DERIV in pc_smt_cover.ml, proved again *)
(* here because this file does not load that one).                           *)

let SCH5_CHAIN_VECTOR = prove
 (`!(c:real^1->real^N) v (FF:real^N->real^P) FF' u.
        (c has_vector_derivative v) (at u) /\ (FF has_derivative FF') (at (c u))
        ==> ((FF o c) has_vector_derivative FF' v) (at u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^1. drop x % (FF':real^N->real^P) v) = FF' o (\x. drop x % v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `linear(FF':real^N->real^P)` MP_TAC THENL
     [UNDISCH_TAC `((FF:real^N->real^P) has_derivative FF') (at ((c:real^1->real^N) u))` THEN
      SIMP_TAC[has_derivative];
      SIMP_TAC[LINEAR_CMUL]];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]]);;

let SCH5_CIRCLE_DERIV = prove
 (`!(a:real^N) b s.
        ((\u. cos(drop u) % a + sin(drop u) % b) has_vector_derivative
         (--sin(drop s) % a + cos(drop s) % b)) (at s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MP_TAC(REAL_DIFF_CONV
   `((\t. cos t * (a:real^N)$i + sin t * (b:real^N)$i) has_real_derivative f)
    (atreal (drop s))`) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_DROP; o_DEF; REAL_MUL_LID]);;

let SCH5_SPHERE_TANGENT_ZERO = prove
 (`!(f:real^3->real^N) t r c.
     t IN sphere(vec 0,&1) /\ &0 < r /\ f differentiable (at t) /\
     (!x. x IN sphere(vec 0,&1) /\ dist(x,t) < r ==> f x = c)
     ==> !v. orthogonal t v ==> frechet_derivative f (at t) v = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  SUBGOAL_THEN `linear(frechet_derivative (f:real^3->real^N) (at t))` ASSUME_TAC THENL
   [UNDISCH_TAC `((f:real^3->real^N) has_derivative frechet_derivative f (at t)) (at t)` THEN
    SIMP_TAC[has_derivative];
    ALL_TAC] THEN
  ASM_CASES_TAC `v:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]);
    ALL_TAC] THEN
  ABBREV_TAC `w = inv(norm(v:real^3)) % v` THEN
  SUBGOAL_THEN `v = norm(v:real^3) % w` SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
  SUBGOAL_THEN `norm(w:real^3) = &1 /\ (t:real^3) dot w = &0 /\ norm(t:real^3) = &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[NORM_MUL; DOT_RMUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    UNDISCH_TAC `orthogonal (t:real^3) v` THEN UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[orthogonal; IN_SPHERE_0] THEN SIMP_TAC[REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  ABBREV_TAC `gam = \u:real^1. cos(drop u) % (t:real^3) + sin(drop u) % w` THEN
  SUBGOAL_THEN `(gam:real^1->real^3) (vec 0) = t /\
                (!u. gam u IN sphere(vec 0,&1)) /\
                (gam has_vector_derivative w) (at (vec 0))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gam" THEN REWRITE_TAC[DROP_VEC; COS_0; SIN_0; VECTOR_MUL_LID;
                                      VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN
      REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
      UNDISCH_TAC `norm(w:real^3) = &1` THEN UNDISCH_TAC `norm(t:real^3) = &1` THEN
      REWRITE_TAC[NORM_EQ_1] THEN REPEAT DISCH_TAC THEN
      ASM_REWRITE_TAC[DOT_SYM] THEN
      MP_TAC(SPEC `drop u` SIN_CIRCLE) THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`t:real^3`; `w:real^3`; `vec 0:real^1`] SCH5_CIRCLE_DERIV) THEN
      REWRITE_TAC[DROP_VEC; COS_0; SIN_0; REAL_NEG_0; VECTOR_MUL_LZERO; VECTOR_MUL_LID;
                  VECTOR_ADD_LID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gam:real^1->real^3`; `w:real^3`; `f:real^3->real^N`;
                 `frechet_derivative (f:real^3->real^N) (at t)`; `vec 0:real^1`]
    SCH5_CHAIN_VECTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((f:real^3->real^N) o (gam:real^1->real^3) has_vector_derivative vec 0)
                (at (vec 0))` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\u:real^1. (c:real^N)` THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    SUBGOAL_THEN `(gam:real^1->real^3) continuous (at (vec 0))` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\u:real^1. drop u % (w:real^3)` THEN
      ASM_REWRITE_TAC[GSYM has_vector_derivative];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `u:real^1` THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    UNDISCH_TAC `!x. x IN sphere(vec 0:real^3,&1) /\ dist(x,t) < r ==> (f:real^3->real^N) x = c` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "D" (fun th -> MP_TAC(MP (SPEC `u:real^1` th)
      (ASSUME `dist(u:real^1,vec 0) < d`))) THEN
    REWRITE_TAC[ASSUME `(gam:real^1->real^3) (vec 0) = t`];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`(f:real^3->real^N) o (gam:real^1->real^3)`; `vec 0:real^1`;
                       `frechet_derivative (f:real^3->real^N) (at t) w`; `vec 0:real^N`]
                VECTOR_DERIVATIVE_UNIQUE_AT) THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let SCH5_SPHERE_TANGENT_EQ = prove
 (`!(f:real^3->real^N) g t r.
     t IN sphere(vec 0,&1) /\ &0 < r /\ f differentiable (at t) /\ g differentiable (at t) /\
     (!x. x IN sphere(vec 0,&1) /\ dist(x,t) < r ==> f x = g x)
     ==> !v. orthogonal t v
             ==> frechet_derivative f (at t) v = frechet_derivative g (at t) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  SUBGOAL_THEN `((\x. (f:real^3->real^N) x - g x) has_derivative
                 (\h. frechet_derivative f (at t) h - frechet_derivative g (at t) h)) (at t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (f:real^3->real^N) x - g x`; `t:real^3`; `r:real`; `vec 0:real^N`]
    SCH5_SPHERE_TANGENT_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h. frechet_derivative (f:real^3->real^N) (at t) h -
                      frechet_derivative g (at t) h` THEN
      FIRST_ASSUM ACCEPT_TAC;
      ASM_SIMP_TAC[VECTOR_SUB_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Derivatives of collars, and critical points are intrinsic:               *)
(* two collars whose spheres agree near a common point have the same        *)
(* tangent plane there, so the same critical points.                         *)
(* ------------------------------------------------------------------------- *)

(* Restriction of a diffeomorphism to an open subset (the statement of       *)
(* SCH2_DIFFEO_RESTRICT in pc_sch_planar.ml, which this file does not load). *)

let SCH5_DIFFEO_RESTRICT = prove
 (`!s t (f:real^N->real^N) g s'.
        diffeomorphism_on s t f g /\ open s' /\ s' SUBSET s
        ==> diffeomorphism_on s' (IMAGE f s') f g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) s' = {y | y IN t /\ (g:real^N->real^N) y IN s'}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (f:real^N->real^N) s')` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* A collar and its inverse are differentiable with inverse derivatives.    *)

let SCH5_NECK_FACTS = prove
 (`!(g:real^3->real^3) g' x.
     sch_neck g g' /\ x IN annulus (&1 / &2) (&2)
     ==> open(IMAGE g (annulus (&1 / &2) (&2))) /\
         g x IN IMAGE g (annulus (&1 / &2) (&2)) /\ g'(g x) = x /\
         g differentiable (at x) /\ g' differentiable (at (g x)) /\
         (!h. frechet_derivative g' (at (g x)) (frechet_derivative g (at x) h) = h) /\
         (!k. frechet_derivative g (at x) (frechet_derivative g' (at (g x)) k) = k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_neck] THEN STRIP_TAC THEN
  ABBREV_TAC `A = annulus (&1 / &2) (&2):real^3->bool` THEN
  SUBGOAL_THEN `open(A:real^3->bool) /\ open(IMAGE (g:real^3->real^3) A) /\
                smooth_map_on A g /\ smooth_map_on (IMAGE g A) (g':real^3->real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on A (IMAGE g A) (g:real^3->real^3) g'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN A ==> (g':real^3->real^3)(g y) = y` (LABEL_TAC "LI") THENL
   [UNDISCH_TAC `diffeomorphism_on A (IMAGE g A) (g:real^3->real^3) g'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN IMAGE g A ==> (g:real^3->real^3)(g' y) = y`
  (LABEL_TAC "RI") THENL
   [UNDISCH_TAC `diffeomorphism_on A (IMAGE g A) (g:real^3->real^3) g'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) x IN IMAGE g A` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) differentiable (at x) /\
                (g':real^3->real^3) differentiable (at (g x))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `A:real^3->bool`; EXISTS_TAC `IMAGE (g:real^3->real^3) A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `((g':real^3->real^3) o (g:real^3->real^3) has_derivative
                 frechet_derivative g' (at (g x)) o frechet_derivative g (at x)) (at x) /\
                ((g:real^3->real^3) o (g':real^3->real^3) has_derivative
                 frechet_derivative g (at x) o frechet_derivative g' (at (g x))) (at (g x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    USE_THEN "LI" (fun th -> REWRITE_TAC[MP (SPEC `x:real^3` th) (ASSUME `(x:real^3) IN A`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((g':real^3->real^3) o (g:real^3->real^3) has_derivative (\h. h)) (at x) /\
                ((g:real^3->real^3) o (g':real^3->real^3) has_derivative (\h. h)) (at (g x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\y:real^3. y` THEN REWRITE_TAC[HAS_DERIVATIVE_ID] THENL
     [UNDISCH_TAC `open(A:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B"))) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "LI" MATCH_MP_TAC THEN
      USE_THEN "B" MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `open(IMAGE (g:real^3->real^3) A)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `(g:real^3->real^3) x`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B"))) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "RI" MATCH_MP_TAC THEN
      USE_THEN "B" MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THEN GEN_TAC THENL
   [MP_TAC(ISPECL [`(g':real^3->real^3) o (g:real^3->real^3)`;
                   `frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) x)) o
                    frechet_derivative g (at x)`; `\h:real^3. h`; `x:real^3`]
      FRECHET_DERIVATIVE_UNIQUE_AT);
    MP_TAC(ISPECL [`(g:real^3->real^3) o (g':real^3->real^3)`;
                   `frechet_derivative (g:real^3->real^3) (at x) o
                    frechet_derivative (g':real^3->real^3) (at (g x))`; `\h:real^3. h`;
                   `(g:real^3->real^3) x`]
      FRECHET_DERIVATIVE_UNIQUE_AT)] THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[]);;

let SCH5_SPHERE_IN_ANNULUS = prove
 (`!t:real^3. t IN sphere(vec 0,&1) ==> t IN annulus (&1 / &2) (&2)`,
  REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* The tangent plane of the image sphere at g t: w = Dg(v) with v tangent   *)
(* iff Dg'(w) is tangent.                                                    *)

let SCH5_NECK_TANGENT = prove
 (`!(g:real^3->real^3) g' t w.
     sch_neck g g' /\ t IN sphere(vec 0,&1)
     ==> ((?v. orthogonal t v /\ w = frechet_derivative g (at t) v) <=>
          orthogonal t (frechet_derivative g' (at (g t)) w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH5_SPHERE_IN_ANNULUS) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) t)) w` THEN
    ASM_REWRITE_TAC[]]);;

(* If g maps the sphere near t into the sphere of h, the tangent vectors of *)
(* the first are tangent to the second at h u = g t.                         *)

let SCH5_TANGENT_TRANSFER = prove
 (`!(g:real^3->real^3) g' h h' t u r.
     sch_neck g g' /\ sch_neck h h' /\ t IN sphere(vec 0,&1) /\ u IN sphere(vec 0,&1) /\
     g t = h u /\ &0 < r /\
     (!y. y IN sphere(vec 0,&1) /\ dist(y,t) < r ==> g y IN IMAGE h (sphere(vec 0,&1)))
     ==> !v. orthogonal t v
             ==> orthogonal u (frechet_derivative h' (at (h u))
                                 (frechet_derivative g (at t) v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5_NECK_FACTS) THEN
  ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^3->real^3`; `h':real^3->real^3`; `u:real^3`] SCH5_NECK_FACTS) THEN
  ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. lift(norm((h':real^3->real^3)((g:real^3->real^3) y)) pow 2)) has_derivative
     (\v. &2 % lift(u dot frechet_derivative h' (at (h u)) (frechet_derivative g (at t) v))))
    (at t)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. lift(norm((h':real^3->real^3)((g:real^3->real^3) y)) pow 2)) =
                  (\z:real^3. lift(norm z pow 2)) o ((h':real^3->real^3) o g)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. &2 % lift(u dot frechet_derivative (h':real^3->real^3) (at (h u))
                              (frechet_derivative (g:real^3->real^3) (at t) v))) =
      (\x:real^3. &2 % lift(u dot x)) o
      (frechet_derivative h' (at ((h:real^3->real^3) u)) o frechet_derivative g (at t))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `(g:real^3->real^3) t = (h:real^3->real^3) u`)) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. lift(norm((h':real^3->real^3)((g:real^3->real^3) y)) pow 2)`;
                 `t:real^3`; `r:real`; `lift(&1)`] SCH5_SPHERE_TANGENT_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN EXISTS_TAC
       `\v. &2 % lift(u dot frechet_derivative (h':real^3->real^3) (at (h u))
                                (frechet_derivative (g:real^3->real^3) (at t) v))` THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^3) y IN IMAGE (h:real^3->real^3) (sphere(vec 0,&1))`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:real^3->real^3`; `h':real^3->real^3`; `z:real^3`] SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&1)` THEN SIMP_TAC[IN_SPHERE_0] THEN
    REWRITE_TAC[REAL_POW_ONE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0] THEN REWRITE_TAC[GSYM LIFT_NUM] THEN
  REWRITE_TAC[LIFT_EQ; orthogonal] THEN REAL_ARITH_TAC);;

(* Critical points transfer between collars whose spheres agree near the    *)
(* common point.                                                             *)

let SCH5_CRIT_LOCAL = prove
 (`!(g:real^3->real^3) g' h h' t u r.
     sch_neck g g' /\ sch_neck h h' /\ t IN sphere(vec 0,&1) /\ u IN sphere(vec 0,&1) /\
     g t = h u /\ &0 < r /\
     (!y. y IN sphere(vec 0,&1) /\ dist(y,t) < r ==> g y IN IMAGE h (sphere(vec 0,&1))) /\
     sch_crit h u
     ==> sch_crit g t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[sch_crit] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `h:real^3->real^3`;
                 `h':real^3->real^3`; `t:real^3`; `u:real^3`; `r:real`]
    SCH5_TANGENT_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`h:real^3->real^3`; `h':real^3->real^3`; `u:real^3`] SCH5_NECK_FACTS) THEN
  ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN STRIP_TAC THEN
  UNDISCH_TAC `sch_crit (h:real^3->real^3) u` THEN REWRITE_TAC[sch_crit] THEN
  DISCH_THEN(MP_TAC o SPEC `frechet_derivative (h':real^3->real^3) (at ((h:real^3->real^3) u))
                              (frechet_derivative (g:real^3->real^3) (at t) v)` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

let SCH5_CRIT_LOCAL_BALL = prove
 (`!(g:real^3->real^3) g' h h' t u r.
     sch_neck g g' /\ sch_neck h h' /\ t IN sphere(vec 0,&1) /\ u IN sphere(vec 0,&1) /\
     g t = h u /\ &0 < r /\
     IMAGE g (sphere(vec 0,&1)) INTER ball(g t,r) =
     IMAGE h (sphere(vec 0,&1)) INTER ball(g t,r)
     ==> (sch_crit g t <=> sch_crit h u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!(f:real^3->real^3) f' s.
      sch_neck f f' /\ s IN sphere(vec 0,&1) /\ f s = (g:real^3->real^3) t
      ==> ?d. &0 < d /\
              !y. y IN sphere(vec 0,&1) /\ dist(y,s) < d ==> f y IN ball(g t,r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `s:real^3`] SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT o check (fun th ->
      concl th = `(f:real^3->real^3) differentiable (at s)`)) THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`h:real^3->real^3`; `h':real^3->real^3`; `u:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SCH5_CRIT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`h':real^3->real^3`; `g:real^3->real^3`; `g':real^3->real^3`;
                          `t:real^3`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^3->real^3) y IN IMAGE h (sphere(vec 0,&1)) INTER
                  ball((g:real^3->real^3) t,r)`
    MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM(ASSUME `IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER
                                    ball(g t,r) =
                                    IMAGE (h:real^3->real^3) (sphere(vec 0,&1)) INTER
                                    ball(g t,r)`)] THEN
      SIMP_TAC[IN_INTER]];
    FIRST_ASSUM(MP_TAC o SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SCH5_CRIT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `h:real^3->real^3`; `h':real^3->real^3`;
                          `u:real^3`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^3) y IN IMAGE g (sphere(vec 0,&1)) INTER
                  ball((g:real^3->real^3) t,r)`
    MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER]]]);;

(* ------------------------------------------------------------------------- *)
(* Horizontal Morse charts (sch_hchart) are local, can swap the              *)
(* two coordinates, reflect under x3 -> -x3, and a strict local maximum has  *)
(* no saddle chart.                                                          *)
(* ------------------------------------------------------------------------- *)

let SCH5_LINEAR_INVOLUTION_DIFFEO = prove
 (`!(l:real^N->real^N) s.
     linear l /\ (!x. l(l x) = x) /\ open s /\ IMAGE l s = s
     ==> diffeomorphism_on s s l l`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[diffeomorphism_on] THEN
  SUBGOAL_THEN `smooth_map_on s (l:real^N->real^N)` (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. x`; `l:real^N->real^N`]
    SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN REWRITE_TAC[o_DEF; ETA_AX]);;

let SCH5_HCHART_LOCAL = prove
 (`!s s' (p:real^3) k1 k2 r.
     sch_hchart s p k1 k2 /\ &0 < r /\ s INTER ball(p,r) = s' INTER ball(p,r)
     ==> sch_hchart s' p k1 k2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[sch_hchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `ph:real^2->real^2`
      (X_CHOOSE_THEN `ph':real^2->real^2` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(ph:real^2->real^2) continuous (at (vec 0))` MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^2,r0)` THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `diffeomorphism_on (ball(vec 0:real^2,r0)) (IMAGE ph (ball(vec 0,r0)))
                   (ph:real^2->real^2) ph'` THEN SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `r / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C"))) THEN
  EXISTS_TAC `min r0 (min d (r / &2))` THEN
  MAP_EVERY EXISTS_TAC [`ph:real^2->real^2`; `ph':real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SCH5_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^2,r0)`; `IMAGE (ph:real^2->real^2) (ball(vec 0,r0))`] THEN
    ASM_REWRITE_TAC[OPEN_BALL; SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN REWRITE_TAC[IN_BALL_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(vector[((ph:real^2->real^2) u)$1; (ph u)$2; z]:real^3) IN ball(p,r)`
  ASSUME_TAC THENL
   [USE_THEN "C" (MP_TAC o SPEC `u:real^2`) THEN
    ANTS_TAC THENL [REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[DIST_0] THEN REWRITE_TAC[dist; IN_BALL] THEN
    REWRITE_TAC[NORM_LT_SQUARE] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((ph:real^2->real^2) u - vector[(p:real^3)$1; p$2]) dot
                 (ph u - vector[p$1; p$2]) < (r / &2) pow 2` THEN
    SUBGOAL_THEN `(z - (p:real^3)$3) pow 2 < (r / &2) pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `abs(z - (p:real^3)$3) < min r0 (min d (r / &2))` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DOT_2; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_2; VECTOR_3] THEN
    SUBGOAL_THEN `&0 < r * r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(vector[((ph:real^2->real^2) u)$1; (ph u)$2; z]:real^3) IN s' <=>
                (vector[(ph u)$1; (ph u)$2; z]:real^3) IN s` SUBST1_TAC THENL
   [UNDISCH_TAC `s INTER ball(p:real^3,r) = s' INTER ball(p,r)` THEN
    UNDISCH_TAC `(vector[((ph:real^2->real^2) u)$1; (ph u)$2; z]:real^3) IN ball(p,r)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `s:real^3->bool`)) (concl th))) THEN
  REWRITE_TAC[IN_BALL_0] THEN
  UNDISCH_TAC `norm(u:real^2) < min r0 (min d (r / &2))` THEN
  UNDISCH_TAC `abs(z - (p:real^3)$3) < min r0 (min d (r / &2))` THEN REAL_ARITH_TAC);;

let SCH5_HCHART_SWAP = prove
 (`!s (p:real^3) k1 k2. sch_hchart s p k1 k2 ==> sch_hchart s p k2 k1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_hchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `ph:real^2->real^2`
      (X_CHOOSE_THEN `ph':real^2->real^2` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sw = \u:real^2. vector[u$2; u$1]:real^2` THEN
  SUBGOAL_THEN `linear (sw:real^2->real^2) /\ (!u. sw(sw u) = u) /\
                (!u. norm(sw u) = norm u) /\ (!u. (sw u)$1 = u$2 /\ (sw u)$2 = u$1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sw" THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; NORM_EQ; DOT_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (sw:real^2->real^2) (ball(vec 0,r0)) = ball(vec 0,r0)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `w:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(sw:real^2->real^2) w` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r0:real`; `(ph:real^2->real^2) o (sw:real^2->real^2)`;
                        `(sw:real^2->real^2) o (ph':real^2->real^2)`] THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `ball(vec 0:real^2,r0)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCH5_LINEAR_INVOLUTION_DIFFEO THEN ASM_REWRITE_TAC[OPEN_BALL];
    SUBGOAL_THEN `(sw:real^2->real^2) (vec 0) = vec 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[LINEAR_0]; ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN REWRITE_TAC[IN_BALL_0] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(sw:real^2->real^2) u`; `z:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `s:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL_0] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let SCH5_IN_IMAGE_FLIP3 = prove
 (`!s (y:real^3). y IN IMAGE sch_flip3 s <=> sch_flip3 y IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[SCH_FLIP3_INVOLUTION];
    DISCH_TAC THEN EXISTS_TAC `sch_flip3 (y:real^3)` THEN
    ASM_REWRITE_TAC[SCH_FLIP3_INVOLUTION]]);;

let SCH5_HCHART_FLIP = prove
 (`!s (p:real^3) k1 k2.
     sch_hchart s p k1 k2 ==> sch_hchart (IMAGE sch_flip3 s) (sch_flip3 p) (--k1) (--k2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_hchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `ph:real^2->real^2`
      (X_CHOOSE_THEN `ph':real^2->real^2` STRIP_ASSUME_TAC))))) THEN
  CONJ_TAC THENL [UNDISCH_TAC `k1 = &1 \/ k1 = -- &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [UNDISCH_TAC `k2 = &1 \/ k2 = -- &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r0:real`; `ph:real^2->real^2`; `ph':real^2->real^2`] THEN
  ASM_REWRITE_TAC[sch_flip3; VECTOR_3] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM sch_flip3; SCH5_IN_IMAGE_FLIP3] THEN REWRITE_TAC[sch_flip3; VECTOR_3] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^2`; `--z`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `s:real^3->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `abs(z - --((p:real^3)$3)) < r0` THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

(* A strict local maximum (chart k = (-1,-1)) has no chart with k1 = 1.     *)

let SCH5_MAX_NOT_SADDLE = prove
 (`!s (p:real^3) k2. sch_hchart s p (-- &1) (-- &1) ==> ~(sch_hchart s p (&1) k2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [sch_hchart]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `ph0:real^2->real^2`
      (X_CHOOSE_THEN `ph0':real^2->real^2` STRIP_ASSUME_TAC))))) THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [sch_hchart]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `ph1:real^2->real^2`
      (X_CHOOSE_THEN `ph1':real^2->real^2` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `?rho. &0 < rho /\
                      ball(vector[(p:real^3)$1; p$2]:real^2,rho) SUBSET
                      IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open(IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))) /\
                  vector[(p:real^3)$1; p$2]:real^2 IN IMAGE ph0 (ball(vec 0,r0))` MP_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `diffeomorphism_on (ball(vec 0:real^2,r0)) (IMAGE ph0 (ball(vec 0,r0)))
                       (ph0:real^2->real^2) ph0'` THEN SIMP_TAC[diffeomorphism_on];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL]];
      MESON_TAC[OPEN_CONTAINS_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ph1:real^2->real^2) continuous (at (vec 0))` MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^2,r1)` THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `diffeomorphism_on (ball(vec 0:real^2,r1)) (IMAGE ph1 (ball(vec 0,r1)))
                   (ph1:real^2->real^2) ph1'` THEN SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C"))) THEN
  ABBREV_TAC `e = min (d / &2) (min r0 r1 / &2)` THEN
  SUBGOAL_THEN `&0 < e /\ e < d /\ e < r1 /\ e < r0 /\ e <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `min (d / &2) (min r0 r1 / &2) = e` THEN
    UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 < r0` THEN UNDISCH_TAC `&0 < r1` THEN
    UNDISCH_TAC `r0 < &1` THEN UNDISCH_TAC `r1 < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e * e < r0 /\ e * e < r1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `e * e <= e * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `e < r0` THEN UNDISCH_TAC `e < r1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e * e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u = e % basis 1:real^2` THEN
  SUBGOAL_THEN `norm(u:real^2) = e /\ u$1 = e /\ u$2 = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(vector[((ph1:real^2->real^2) u)$1; (ph1 u)$2; (p:real^3)$3 + e * e]:real^3)
                IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^2`; `(p:real^3)$3 + e * e`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `ph1:real^2->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL_0] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ph1:real^2->real^2) u IN IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))`
  MP_TAC THENL
   [UNDISCH_TAC `ball(vector[(p:real^3)$1; p$2]:real^2,rho) SUBSET
                 IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    USE_THEN "C" MATCH_MP_TAC THEN REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:real^3)$3 + e * e =
                p$3 + -- &1 * (u':real^2)$1 pow 2 + -- &1 * u'$2 pow 2` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^2`; `(p:real^3)$3 + e * e`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `ph0:real^2->real^2`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_BALL_0] THEN UNDISCH_TAC `e * e < r0` THEN
      UNDISCH_TAC `&0 < e * e` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `(ph1:real^2->real^2) u = (ph0:real^2->real^2) u'`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `(u':real^2)$1` REAL_LE_SQUARE) THEN MP_TAC(SPEC `(u':real^2)$2` REAL_LE_SQUARE) THEN
  UNDISCH_TAC `&0 < e * e` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The reflection x3 -> -x3 (sch_flip3) of collars and of their              *)
(* Morse data: critical points, charts (k -> -k, a saddle stays a saddle     *)
(* after swapping the chart coordinates), saddles and levels (a -> -a).      *)
(* ------------------------------------------------------------------------- *)

let SCH5_FLIP3_FACTS = prove
 (`linear sch_flip3 /\ (!x:real^3. sch_flip3(sch_flip3 x) = x) /\
   (!x:real^3. norm(sch_flip3 x) = norm x) /\
   (!x y:real^3. sch_flip3 x dot sch_flip3 y = x dot y) /\
   (!x:real^3. (sch_flip3 x)$3 = --(x$3))`,
  REWRITE_TAC[sch_flip3; linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; NORM_EQ; DOT_3] THEN
  REAL_ARITH_TAC);;

let SCH5_FLIP3_IMAGE_NORM = prove
 (`!s:real^3->bool. (!x. x IN s <=> sch_flip3 x IN s) ==> IMAGE sch_flip3 s = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; SCH5_IN_IMAGE_FLIP3] THEN ASM_MESON_TAC[]);;

let SCH5_FLIP3_SPHERE_ANNULUS = prove
 (`IMAGE sch_flip3 (sphere(vec 0,&1)) = sphere(vec 0,&1) /\
   IMAGE sch_flip3 (annulus (&1 / &2) (&2)) = annulus (&1 / &2) (&2) /\
   (!t:real^3. sch_flip3 t IN sphere(vec 0,&1) <=> t IN sphere(vec 0,&1))`,
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SCH5_FLIP3_IMAGE_NORM) THEN
  REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM; SCH5_FLIP3_FACTS]);;

let SCH5_FLIP3_DIFFEO = prove
 (`!s:real^3->bool. open s ==> diffeomorphism_on s (IMAGE sch_flip3 s) sch_flip3 sch_flip3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH5_DIFFEO_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SCH5_LINEAR_INVOLUTION_DIFFEO THEN
  REWRITE_TAC[SCH5_FLIP3_FACTS; OPEN_UNIV] THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN MESON_TAC[SCH5_FLIP3_FACTS]);;

let SCH5_NECK_FLIP = prove
 (`!g g':real^3->real^3.
     sch_neck g g'
     ==> sch_neck (sch_flip3 o g o sch_flip3) (sch_flip3 o g' o sch_flip3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_neck] THEN DISCH_TAC THEN
  ABBREV_TAC `A = annulus (&1 / &2) (&2):real^3->bool` THEN
  SUBGOAL_THEN `open(A:real^3->bool) /\ open(IMAGE (g:real^3->real^3) A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on A (IMAGE g A) (g:real^3->real^3) g'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE sch_flip3 A = A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[SCH5_FLIP3_SPHERE_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (sch_flip3 o (g:real^3->real^3) o sch_flip3) A =
                IMAGE sch_flip3 (IMAGE g A)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  SUBGOAL_THEN `sch_flip3 o (g':real^3->real^3) o sch_flip3 = (sch_flip3 o g') o sch_flip3`
  SUBST1_TAC THENL [REWRITE_TAC[o_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `IMAGE (g:real^3->real^3) A` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `A:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE sch_flip3 A = A` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [GSYM th]) THEN
    MATCH_MP_TAC SCH5_FLIP3_DIFFEO THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCH5_FLIP3_DIFFEO THEN ASM_REWRITE_TAC[]]);;

let SCH5_CRIT_FLIP = prove
 (`!g g' t:real^3.
     sch_neck g g'
     ==> (sch_crit (sch_flip3 o g o sch_flip3) t <=> sch_crit g (sch_flip3 t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch_crit; SCH5_FLIP3_SPHERE_ANNULUS] THEN
  ASM_CASES_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sch_flip3 (t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5_SPHERE_IN_ANNULUS THEN ASM_REWRITE_TAC[SCH5_FLIP3_SPHERE_ANNULUS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `sch_flip3 t`] SCH5_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (sch_flip3 o (g:real^3->real^3) o sch_flip3) (at t) =
    sch_flip3 o frechet_derivative g (at (sch_flip3 t)) o sch_flip3`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[SCH5_FLIP3_FACTS]] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[SCH5_FLIP3_FACTS];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM; SCH5_FLIP3_FACTS; REAL_NEG_EQ_0] THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `sch_flip3 (v:real^3)`) THEN
    ASM_REWRITE_TAC[SCH5_FLIP3_FACTS] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `orthogonal (sch_flip3 (t:real^3)) v` THEN
    REWRITE_TAC[orthogonal] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM(CONJUNCT1(CONJUNCT2 SCH5_FLIP3_FACTS))] THEN
    REWRITE_TAC[SCH5_FLIP3_FACTS];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `orthogonal (t:real^3) v` THEN REWRITE_TAC[orthogonal; SCH5_FLIP3_FACTS]]);;

let SCH5_IMAGE_FLIP_NECK = prove
 (`!g:real^3->real^3.
     IMAGE (sch_flip3 o g o sch_flip3) (sphere(vec 0,&1)) =
     IMAGE sch_flip3 (IMAGE g (sphere(vec 0,&1)))`,
  REWRITE_TAC[IMAGE_o; SCH5_FLIP3_SPHERE_ANNULUS]);;

let SCH5_FLIP3_IMAGE_IMAGE = prove
 (`!s:real^3->bool. IMAGE sch_flip3 (IMAGE sch_flip3 s) = s`,
  REWRITE_TAC[EXTENSION; SCH5_IN_IMAGE_FLIP3; SCH5_FLIP3_FACTS]);;

let SCH5_HCHART_FLIP_NECK = prove
 (`!g:real^3->real^3 t k1 k2.
     sch_hchart (IMAGE (sch_flip3 o g o sch_flip3) (sphere(vec 0,&1)))
                ((sch_flip3 o g o sch_flip3) t) k1 k2 <=>
     sch_hchart (IMAGE g (sphere(vec 0,&1))) (g(sch_flip3 t)) (--k1) (--k2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SCH5_IMAGE_FLIP_NECK; o_THM] THEN EQ_TAC THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP SCH5_HCHART_FLIP) THEN
    REWRITE_TAC[SCH5_FLIP3_IMAGE_IMAGE; SCH5_FLIP3_FACTS];
    FIRST_ASSUM(MP_TAC o MATCH_MP SCH5_HCHART_FLIP) THEN REWRITE_TAC[REAL_NEG_NEG]]);;

let SCH5_MORSE_FLIP = prove
 (`!g g':real^3->real^3.
     sch_neck g g' /\ sch_morse g ==> sch_morse (sch_flip3 o g o sch_flip3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `sch_morse (g:real^3->real^3)` THEN REWRITE_TAC[sch_morse] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCH5_CRIT_FLIP th]) THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{t:real^3 | sch_crit g (sch_flip3 t)} =
                  IMAGE sch_flip3 {t | sch_crit (g:real^3->real^3) t}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; SCH5_IN_IMAGE_FLIP3]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[o_THM; SCH5_FLIP3_FACTS; REAL_EQ_NEG2] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `sch_flip3 (t:real^3) = sch_flip3 t'` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; MESON_TAC[SCH5_FLIP3_FACTS]];
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN REWRITE_TAC[SCH5_HCHART_FLIP_NECK] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sch_flip3 (t:real^3)` o check (fun th ->
      can (find_term ((=) `sch_hchart`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k1:real` (X_CHOOSE_TAC `k2:real`)) THEN
    MAP_EVERY EXISTS_TAC [`--k1:real`; `--k2:real`] THEN ASM_REWRITE_TAC[REAL_NEG_NEG]]);;

let SCH5_SADDLES_FLIP = prove
 (`!g g':real^3->real^3.
     sch_neck g g'
     ==> sch_saddles (sch_flip3 o g o sch_flip3) = IMAGE sch_flip3 (sch_saddles g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch_saddles; EXTENSION; IN_ELIM_THM; SCH5_IN_IMAGE_FLIP3] THEN
  X_GEN_TAC `t:real^3` THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCH5_CRIT_FLIP th]) THEN
  REWRITE_TAC[SCH5_HCHART_FLIP_NECK] THEN
  MESON_TAC[SCH5_HCHART_SWAP; REAL_NEG_NEG]);;

let SCH5_LEVEL_FLIP = prove
 (`!g:real^3->real^3 a.
     sch_level (sch_flip3 o g o sch_flip3) a = IMAGE sch_flip3 (sch_level g (--a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_level; SCH5_IMAGE_FLIP_NECK] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; SCH5_IN_IMAGE_FLIP3; SCH5_FLIP3_FACTS; REAL_EQ_NEG2]);;

let SCH5_COMPONENTS_FLIP = prove
 (`!s:real^3->bool.
     FINITE(components s)
     ==> FINITE(components(IMAGE sch_flip3 s)) /\
         CARD(components(IMAGE sch_flip3 s)) = CARD(components s)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `components(IMAGE sch_flip3 s) = IMAGE (IMAGE sch_flip3) (components s)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC COMPONENTS_LINEAR_IMAGE THEN REWRITE_TAC[SCH5_FLIP3_FACTS] THEN
    MESON_TAC[SCH5_FLIP3_FACTS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[SCH5_FLIP3_IMAGE_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* A smooth map near the unit sphere that is injective on the               *)
(* sphere and has invertible derivative there is a diffeomorphism on a thin *)
(* shell around the sphere (compactness: shells shrink to the sphere).      *)
(* ------------------------------------------------------------------------- *)

let SCH5_SHELL_IN_OPEN = prove
 (`!V:real^3->bool.
     open V /\ sphere(vec 0,&1) SUBSET V
     ==> ?eta. &0 < eta /\ eta < &1 /\ !x. abs(norm x - &1) < eta ==> x IN V`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^3,&1)`; `(:real^3) DIFF V`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[COMPACT_SPHERE; GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  EXISTS_TAC `min d (&1 / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^3) IN V` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(norm(x:real^3) - &1) < min d (&1 / &2)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm x) % (x:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(inv(norm x) % (x:real^3),x) = abs(norm x - &1)` ASSUME_TAC THENL
   [REWRITE_TAC[dist] THEN
    SUBGOAL_THEN `inv(norm x) % (x:real^3) - x = (inv(norm x) - &1) % x` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `(inv(norm(x:real^3)) - &1) * norm x = --(norm x - &1)` MP_TAC THENL
     [UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `abs`) THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < n ==> abs n = n`];
    ALL_TAC] THEN
  USE_THEN "D" (MP_TAC o SPECL [`inv(norm x) % (x:real^3)`; `x:real^3`]) THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; ASSUME `inv(norm x) % (x:real^3) IN sphere(vec 0,&1)`;
              ASSUME `~((x:real^3) IN V)`;
              ASSUME `dist(inv(norm x) % (x:real^3),x) = abs(norm x - &1)`] THEN
  UNDISCH_TAC `abs(norm(x:real^3) - &1) < min d (&1 / &2)` THEN REAL_ARITH_TAC);;

let SCH5_DET_DERIV_CONTINUOUS_ON = prove
 (`!(G:real^N->real^N) W.
     open W /\ smooth_map_on W G
     ==> (\x. lift(det(matrix(frechet_derivative G (at x))))) continuous_on W`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[matrix; LAMBDA_BETA] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `\x. frechet_derivative (G:real^N->real^N) (at x) (basis j)`;
                 `i:num`] SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN REWRITE_TAC[]);;

(* Injectivity on a shell from injectivity on the sphere and local          *)
(* injectivity at its points (sequences and compactness of S^2 x S^2).       *)

let SCH5_SHELL_SEQ_LIMIT = prove
 (`!(zs:num->real^3) (r:num->num) l.
     (!m n. m < n ==> r m < r n) /\
     (!n. abs(norm(zs n) - &1) < inv(&n + &1)) /\ (!n. ~(zs n = vec 0)) /\
     ((\n. inv(norm(zs(r n))) % zs(r n)) --> l) sequentially
     ==> ((\n. zs(r n)) --> l) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\n. (zs:num->real^3) ((r:num->num) n)) =
                (\n. inv(norm(zs(r n))) % zs(r n) + (&1 - inv(norm(zs(r n)))) % zs(r n))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `l:real^3 = l + vec 0` SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `&0 < norm((zs:num->real^3) ((r:num->num) n))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(&1 - inv(norm((zs:num->real^3) ((r:num->num) n)))) * norm(zs(r n)) =
                abs(norm(zs(r n)) - &1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `(&1 - inv(norm((zs:num->real^3) ((r:num->num) n)))) * norm(zs(r n)) =
                  norm(zs(r n)) - &1` MP_TAC THENL
     [UNDISCH_TAC `&0 < norm((zs:num->real^3) ((r:num->num) n))` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `abs`) THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < n ==> abs n = n`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&((r:num->num) n) + &1)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  SUBGOAL_THEN `N <= (r:num->num) n` MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `n:num` (MATCH_MP MONOTONE_BIGGER
      (ASSUME `!m n:num. m < n ==> (r:num->num) m < r n`))) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `~(N = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  MP_TAC(SPEC `N:num` REAL_POS) THEN REAL_ARITH_TAC);;

let SCH5_SHELL_INJ = prove
 (`!(G:real^3->real^3) W.
     open W /\ sphere(vec 0,&1) SUBSET W /\ G continuous_on W /\
     (!x y. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\ G x = G y ==> x = y) /\
     (!t. t IN sphere(vec 0,&1)
          ==> ?r. &0 < r /\
                  !x y. x IN ball(t,r) /\ y IN ball(t,r) /\ G x = G y ==> x = y)
     ==> ?eta. &0 < eta /\
               !x y. abs(norm x - &1) < eta /\ abs(norm y - &1) < eta /\ G x = G y
                     ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "loc"))))) THEN
  MP_TAC(ISPEC `W:real^3->bool` SCH5_SHELL_IN_OPEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?xs ys:num->real^3.
       (!n. abs(norm(xs n) - &1) < inv(&n + &1)) /\
       (!n. abs(norm(ys n) - &1) < inv(&n + &1)) /\
       (!n. abs(norm(xs n) - &1) < e1) /\
       (!n. (G:real^3->real^3) (xs n) = G (ys n)) /\
       (!n. ~(xs n = ys n))`
  MP_TAC THENL
   [REWRITE_TAC[GSYM FORALL_AND_THM; GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `min e1 (inv(&n + &1))`) THEN
    REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
    SUBGOAL_THEN `&0 < min e1 (inv(&n + &1))` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:num->real^3` (X_CHOOSE_THEN `ys:num->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "XB") (CONJUNCTS_THEN2 (LABEL_TAC "YB")
    (CONJUNCTS_THEN2 (LABEL_TAC "XE") (CONJUNCTS_THEN2 (LABEL_TAC "EQ") (LABEL_TAC "NE"))))))) THEN
  SUBGOAL_THEN `!n. ~((xs:num->real^3) n = vec 0) /\ ~((ys:num->real^3) n = vec 0)`
  (LABEL_TAC "NZ") THENL
   [GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "XB" (MP_TAC o SPEC `n:num`); USE_THEN "YB" (MP_TAC o SPEC `n:num`)] THEN
    (POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[NORM_0] THEN
     SUBGOAL_THEN `inv(&n + &1) <= &1` MP_TAC THENL
      [MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC; REAL_ARITH_TAC]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^3,&1)`; `sphere(vec 0:real^3,&1)`] COMPACT_PCROSS) THEN
  REWRITE_TAC[COMPACT_SPHERE; compact] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. pastecart (inv(norm((xs:num->real^3) n)) % xs n)
                                          (inv(norm((ys:num->real^3) n)) % ys n)`) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_SPHERE_0; NORM_MUL] THEN
    USE_THEN "NZ" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3` (X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `r:num->num`
    STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC
   `((\n. pastecart (inv(norm((xs:num->real^3) n)) % xs n)
                    (inv(norm((ys:num->real^3) n)) % ys n)) o r
     --> pastecart t u) sequentially` THEN
  REWRITE_TAC[o_DEF; LIM_PASTECART_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((\n. (xs:num->real^3) ((r:num->num) n)) --> t) sequentially /\
                ((\n. (ys:num->real^3) ((r:num->num) n)) --> u) sequentially`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SCH5_SHELL_SEQ_LIMIT THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "NZ" MP_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^3->real^3) continuous (at t) /\ G continuous (at u)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^3->real^3`; `W:real^3->bool`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^3->real^3) t = G u` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `(G:real^3->real^3) o (\n. (xs:num->real^3) ((r:num->num) n))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(G:real^3->real^3) continuous (at t)` THEN
      REWRITE_TAC[CONTINUOUS_AT_SEQUENTIALLY] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(G:real^3->real^3) o (\n. (xs:num->real^3) ((r:num->num) n)) =
                    G o (\n. (ys:num->real^3) (r n))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN USE_THEN "EQ" MATCH_ACCEPT_TAC;
        UNDISCH_TAC `(G:real^3->real^3) continuous (at u)` THEN
        REWRITE_TAC[CONTINUOUS_AT_SEQUENTIALLY] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t:real^3 = u` SUBST_ALL_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `u:real^3` th)
    (ASSUME `(u:real^3) IN sphere(vec 0,&1)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R"))) THEN
  SUBGOAL_THEN `?N. !n. N <= n ==> dist((xs:num->real^3) ((r:num->num) n),u) < rho /\
                                   dist((ys:num->real^3) (r n),u) < rho`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `((\n. (xs:num->real^3) ((r:num->num) n)) --> u) sequentially` THEN
    UNDISCH_TAC `((\n. (ys:num->real^3) ((r:num->num) n)) --> u) sequentially` THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "NE" (MP_TAC o SPEC `(r:num->num) N`) THEN REWRITE_TAC[] THEN
  USE_THEN "R" MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_SIMP_TAC[LE_REFL] THEN USE_THEN "EQ" MATCH_ACCEPT_TAC);;

let SCH5_IN_THIN_ANNULUS = prove
 (`!x:real^3 eta. x IN annulus (&1 - eta) (&1 + eta) <=> abs(norm x - &1) < eta`,
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let SCH5_NEAR_SPHERE_DIFFEO = prove
 (`!(G:real^3->real^3) W.
     open W /\ sphere(vec 0,&1) SUBSET W /\ smooth_map_on W G /\
     (!x y. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\ G x = G y ==> x = y) /\
     (!t. t IN sphere(vec 0,&1) ==> ~(det(matrix(frechet_derivative G (at t))) = &0))
     ==> ?eta G'. &0 < eta /\ eta < &1 /\
                  annulus (&1 - eta) (&1 + eta) SUBSET W /\
                  diffeomorphism_on (annulus (&1 - eta) (&1 + eta))
                                    (IMAGE G (annulus (&1 - eta) (&1 + eta))) G G'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "det"))))) THEN
  ABBREV_TAC `V = {x:real^3 | x IN W /\
                   lift(det(matrix(frechet_derivative (G:real^3->real^3) (at x)))) IN
                   (:real^1) DIFF {vec 0}}` THEN
  SUBGOAL_THEN `open(V:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SCH5_DET_DERIV_CONTINUOUS_ON; OPEN_DIFF; OPEN_UNIV; CLOSED_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; USE_THEN "det" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `V:real^3->bool` SCH5_SHELL_IN_OPEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `W:real^3->bool`] SCH5_SHELL_INJ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN CONJ_TAC THENL
     [USE_THEN "inj" ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:real^3->real^3`; `W:real^3->bool`; `t:real^3`]
      SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; USE_THEN "det" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Tt:real^3->bool` (X_CHOOSE_THEN `U:real^3->bool`
      (X_CHOOSE_THEN `H:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `open(Tt:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    UNDISCH_TAC `diffeomorphism_on Tt U (G:real^3->real^3) H` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `eta = min e1 e2` THEN
  SUBGOAL_THEN `&0 < eta /\ eta < &1 /\ eta <= e1 /\ eta <= e2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1 - eta) (&1 + eta) SUBSET (V:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; SCH5_IN_THIN_ANNULUS] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1 - eta) (&1 + eta) SUBSET (W:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `annulus (&1 - eta) (&1 + eta) SUBSET (V:real^3->bool)` THEN
    EXPAND_TAC "V" THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `annulus (&1 - eta) (&1 + eta):real^3->bool`]
    SCHI_INJ_DIFFEO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SCH5_IN_THIN_ANNULUS] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `G':real^3->real^3`) THEN
  MAP_EVERY EXISTS_TAC [`eta:real`; `G':real^3->real^3`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Invertibility of derivatives transverse to the sphere, and               *)
(* collars from diffeomorphisms of thin shells (radial compression of the    *)
(* standard shell 1/2 < |x| < 2 into 1 - k/2 < |x| < 1 + k).                 *)
(* ------------------------------------------------------------------------- *)

let SCH5_INJ_DET = prove
 (`!D:real^N->real^N.
     linear D /\ (!w. D w = vec 0 ==> w = vec 0) ==> ~(det(matrix D) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `matrix(D:real^N->real^N)` HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[]);;

let SCH5_TRANSVERSE_INJ = prove
 (`!(D:real^3->real^3) A t n.
     linear D /\ norm t = &1 /\
     (!v. orthogonal t v ==> D v = A v) /\
     (!v. orthogonal t v /\ A v = vec 0 ==> v = vec 0) /\
     (!v. orthogonal t v ==> n dot A v = &0) /\ ~(n dot D t = &0)
     ==> !w. D w = vec 0 ==> w = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  ABBREV_TAC `wt = w - (t dot w) % (t:real^3)` THEN
  SUBGOAL_THEN `orthogonal (t:real^3) wt` ASSUME_TAC THENL
   [EXPAND_TAC "wt" THEN REWRITE_TAC[orthogonal; DOT_RSUB; DOT_RMUL] THEN
    UNDISCH_TAC `norm(t:real^3) = &1` THEN REWRITE_TAC[NORM_EQ_1] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `w = wt + (t dot w) % (t:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "wt" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^3->real^3) wt + (t dot w) % (D:real^3->real^3) t = vec 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(D:real^3->real^3) wt = A wt` (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        is_eq(snd(dest_imp(snd(strip_forall(concl th))))) &&
        can (find_term ((=) `D:real^3->real^3`)) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th);
                                      GSYM(MATCH_MP LINEAR_ADD th)]) THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) o
      check (fun th -> concl th = `(D:real^3->real^3) w = vec 0`)) THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3) dot w = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(n:real^3) dot ((A:real^3->real^3) wt + (t dot w) % (D:real^3->real^3) t) = &0`
    MP_TAC THENL [ASM_REWRITE_TAC[DOT_RZERO]; ALL_TAC] THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    SUBGOAL_THEN `(n:real^3) dot (A:real^3->real^3) wt = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_ENTIRE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wt:real^3 = vec 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `vec 0:real^3`)) (concl th) &&
      can (find_term ((=) `A:real^3->real^3`)) (concl th) &&
      not(can (find_term ((=) `n:real^3`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(A:real^3->real^3) wt + (t dot w) % (D:real^3->real^3) t = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  UNDISCH_TAC `w = wt + (t dot w) % (t:real^3)` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID]);;

(* Radial compression of the standard shell. *)

let sch5_radial = new_definition
 `sch5_radial (k:real) (x:real^N) = ((&1 + k * (norm x - &1)) / norm x) % x`;;

let sch5_radinv = new_definition
 `sch5_radinv (k:real) (y:real^N) = ((&1 + (norm y - &1) / k) / norm y) % y`;;

let SCH5_RADIAL_FACTS = prove
 (`!k x:real^N.
     &0 < k /\ k < &1 /\ x IN annulus (&1 / &2) (&2)
     ==> norm(sch5_radial k x) = &1 + k * (norm x - &1) /\
         sch5_radial k x IN annulus (&1 - k / &2) (&1 + k) /\
         sch5_radinv k (sch5_radial k x) = x /\
         inv(norm(sch5_radial k x)) % sch5_radial k x = inv(norm x) % x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + k * (norm(x:real^N) - &1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `k * (norm(x:real^N) - &1) >= k * --(&1 / &2)` MP_TAC THENL
     [REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(sch5_radial k (x:real^N)) = &1 + k * (norm x - &1)` ASSUME_TAC THENL
   [REWRITE_TAC[sch5_radial; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `k * --(&1 / &2) < k * (norm(x:real^N) - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    SUBGOAL_THEN `k * (norm(x:real^N) - &1) < k * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    REWRITE_TAC[sch5_radinv] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[sch5_radial; VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < k` THEN UNDISCH_TAC `&0 < norm(x:real^N)` THEN
    UNDISCH_TAC `&0 < &1 + k * (norm(x:real^N) - &1)` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[sch5_radial; VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < norm(x:real^N)` THEN
    UNDISCH_TAC `&0 < &1 + k * (norm(x:real^N) - &1)` THEN CONV_TAC REAL_FIELD]);;

let SCH5_RADIAL_AFFINE_SMOOTH = prove
 (`!s a b. open s /\ s SUBSET {x:real^N | ~(x = vec 0)}
           ==> smooth_map_on s (\x:real^N. ((a + b * norm x) / norm x) % x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (\x:real^N. lift(norm x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_LIFT_NORM_NONZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift((a + b * norm x) / norm x)`;
                 `\x:real^N. x`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(a + b * norm x)`;
                 `\x:real^N. lift(norm x)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift a`; `\x:real^N. lift(b * norm x)`]
      SMOOTH_MAP_ON_LIFT_ADD) THEN
    REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `b:real`; `\x:real^N. lift(norm x)`]
      SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    UNDISCH_TAC `s SUBSET {x:real^N | ~(x = vec 0)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; NORM_EQ_0] THEN MESON_TAC[]]);;

let SCH5_RADIAL_DIFFEO = prove
 (`!k. &0 < k /\ k < &1
       ==> diffeomorphism_on (annulus (&1 / &2) (&2)) (annulus (&1 - k / &2) (&1 + k))
                             (sch5_radial k:real^N->real^N) (sch5_radinv k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN
  SUBGOAL_THEN `!r1 r2. &0 <= r1 ==> annulus r1 r2 SUBSET {x:real^N | ~(x = vec 0)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN UNDISCH_TAC `r1 < norm(vec 0:real^N)` THEN
    REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `sch5_radial k = (\x:real^N. (((&1 - k) + k * norm x) / norm x) % x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; sch5_radial] THEN GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SCH5_RADIAL_AFFINE_SMOOTH THEN REWRITE_TAC[OPEN_ANNULUS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `sch5_radinv k = (\y:real^N. (((&1 - inv k) + inv k * norm y) / norm y) % y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; sch5_radinv] THEN GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC SCH5_RADIAL_AFFINE_SMOOTH THEN REWRITE_TAC[OPEN_ANNULUS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:real`; `x:real^N`] SCH5_RADIAL_FACTS) THEN ASM_SIMP_TAC[];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 + (norm(y:real^N) - &1) / k` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `--(&1 / &2) < x ==> &0 < &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(sch5_radinv k (y:real^N)) = &1 + (norm y - &1) / k` ASSUME_TAC THENL
     [REWRITE_TAC[sch5_radinv; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `--(&1 / &2) < x ==> &1 / &2 < &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x < &1 ==> &1 + x < &2`) THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[sch5_radial] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[sch5_radinv; VECTOR_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < k` THEN UNDISCH_TAC `&0 < norm(y:real^N)` THEN
      UNDISCH_TAC `&0 < &1 + (norm(y:real^N) - &1) / k` THEN CONV_TAC REAL_FIELD]]);;

let SCH5_RADIAL_SPHERE = prove
 (`!k t:real^N. t IN sphere(vec 0,&1) ==> sch5_radial k t = t`,
  REWRITE_TAC[IN_SPHERE_0; sch5_radial] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID; REAL_DIV_1; VECTOR_MUL_LID]);;

let SCH5_NECK_FROM_THIN = prove
 (`!(G:real^3->real^3) G' eta.
     &0 < eta /\ eta < &1 /\
     diffeomorphism_on (annulus (&1 - eta) (&1 + eta))
                       (IMAGE G (annulus (&1 - eta) (&1 + eta))) G G'
     ==> sch_neck (G o sch5_radial (eta / &2)) (sch5_radinv (eta / &2) o G') /\
         (!t. t IN sphere(vec 0,&1) ==> (G o sch5_radial (eta / &2)) t = G t) /\
         (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
                ==> frechet_derivative (G o sch5_radial (eta / &2)) (at t) v =
                    frechet_derivative G (at t) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `k = eta / &2` THEN
  SUBGOAL_THEN `&0 < k /\ k < &1 /\ &1 - eta < &1 - k / &2 /\ &1 + k < &1 + eta`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1 - k / &2) (&1 + k) SUBSET annulus (&1 - eta) (&1 + eta):real^3->bool`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (annulus (&1 - k / &2) (&1 + k))
                  (IMAGE (G:real^3->real^3) (annulus (&1 - k / &2) (&1 + k))) G G'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 - eta) (&1 + eta):real^3->bool`;
                          `IMAGE (G:real^3->real^3) (annulus (&1 - eta) (&1 + eta))`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS];
    ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] (SPEC `k:real` SCH5_RADIAL_DIFFEO)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[sch_neck] THEN
    SUBGOAL_THEN `IMAGE ((G:real^3->real^3) o sch5_radial k) (annulus (&1 / &2) (&2)) =
                  IMAGE G (annulus (&1 - k / &2) (&1 + k))` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `diffeomorphism_on (annulus (&1 / &2) (&2)) (annulus (&1 - k / &2) (&1 + k))
                     (sch5_radial k:real^3->real^3) (sch5_radinv k)` THEN
      SIMP_TAC[diffeomorphism_on];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `annulus (&1 - k / &2) (&1 + k):real^3->bool` THEN ASM_REWRITE_TAC[];
    SIMP_TAC[o_THM; SCH5_RADIAL_SPHERE];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2) /\ t IN annulus (&1 - eta) (&1 + eta)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5_radial k differentiable (at (t:real^3)) /\
                (G:real^3->real^3) differentiable (at t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
      UNDISCH_TAC `diffeomorphism_on (annulus (&1 / &2) (&2)) (annulus (&1 - k / &2) (&1 + k))
                     (sch5_radial k:real^3->real^3) (sch5_radinv k)` THEN
      ASM_SIMP_TAC[diffeomorphism_on];
      EXISTS_TAC `annulus (&1 - eta) (&1 + eta):real^3->bool` THEN
      UNDISCH_TAC `diffeomorphism_on (annulus (&1 - eta) (&1 + eta))
                     (IMAGE G (annulus (&1 - eta) (&1 + eta))) (G:real^3->real^3) G'` THEN
      ASM_SIMP_TAC[diffeomorphism_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative ((G:real^3->real^3) o sch5_radial k) (at t) =
                frechet_derivative G (at t) o frechet_derivative (sch5_radial k) (at t)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[SCH5_RADIAL_SPHERE] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`sch5_radial k:real^3->real^3`; `\x:real^3. x`; `t:real^3`; `&1`]
    SCH5_SPHERE_TANGENT_EQ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SCH5_RADIAL_SPHERE; DIFFERENTIABLE_ID; REAL_LT_01];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `frechet_derivative (\x:real^3. x) (at t) = (\h. h)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Collars from transverse maps.  If G agrees with an embedded               *)
(* sphere s on S^2 and its radial derivative is transverse (not orthogonal   *)
(* to a normal field n of s), then G is a diffeomorphism on a thin shell and *)
(* G o (radial compression) is a collar with the values and the tangential   *)
(* derivatives of s on S^2.  The cofactor normal of s, and the tube lemma.   *)
(* ------------------------------------------------------------------------- *)

let SCH5_NECK_FROM_TRANSVERSE = prove
 (`!(G:real^3->real^3) (s:real^3->real^3) (n:real^3->real^3) W.
     open W /\ sphere(vec 0,&1) SUBSET W /\ smooth_map_on W G /\ smooth_map_on W s /\
     (!t. t IN sphere(vec 0,&1) ==> G t = s t) /\
     (!x y. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\ s x = s y ==> x = y) /\
     (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v /\ frechet_derivative s (at t) v = vec 0
            ==> v = vec 0) /\
     (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
            ==> n t dot frechet_derivative s (at t) v = &0) /\
     (!t. t IN sphere(vec 0,&1) ==> ~(n t dot frechet_derivative G (at t) t = &0))
     ==> ?eta G'. &0 < eta /\ eta < &1 /\ annulus (&1 - eta) (&1 + eta) SUBSET W /\
                  sch_neck (G o sch5_radial (eta / &2)) (sch5_radinv (eta / &2) o G') /\
                  (!t. t IN sphere(vec 0,&1) ==> (G o sch5_radial (eta / &2)) t = s t) /\
                  (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
                         ==> frechet_derivative (G o sch5_radial (eta / &2)) (at t) v =
                             frechet_derivative s (at t) v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "imm") (CONJUNCTS_THEN2 (LABEL_TAC "nor")
      (LABEL_TAC "tr"))))))))) THEN
  SUBGOAL_THEN
   `!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
          ==> frechet_derivative (G:real^3->real^3) (at t) v = frechet_derivative s (at t) v`
  (LABEL_TAC "tan") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^3->real^3`; `s:real^3->real^3`; `t:real^3`; `&1`]
      SCH5_SPHERE_TANGENT_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^3->bool` THEN
        ASM SET_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^3->bool` THEN
        ASM SET_TAC[];
        REPEAT STRIP_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `W:real^3->bool`] SCH5_NEAR_SPHERE_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
      UNDISCH_TAC `(G:real^3->real^3) x = G y` THEN
      USE_THEN "eq" (fun th -> ASM_SIMP_TAC[th]);
      ALL_TAC] THEN
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SCH5_INJ_DET THEN
    SUBGOAL_THEN `(G:real^3->real^3) differentiable (at t)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^3->bool` THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SCH5_TRANSVERSE_INJ THEN
    MAP_EVERY EXISTS_TAC [`frechet_derivative (s:real^3->real^3) (at t)`; `t:real^3`;
                          `(n:real^3->real^3) t`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0];
      REPEAT STRIP_TAC THEN USE_THEN "tan" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "imm" MATCH_MP_TAC THEN EXISTS_TAC `t:real^3` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "nor" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "tr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (X_CHOOSE_THEN `G':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `G':real^3->real^3`; `eta:real`] SCH5_NECK_FROM_THIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`eta:real`; `G':real^3->real^3`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN USE_THEN "eq" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN USE_THEN "tan" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* The cofactor normal of a map s: at x it is cof(Ds_x) x, written with     *)
(* cross products of the columns of the derivative.                          *)

let sch5_conormal = new_definition
 `sch5_conormal (s:real^3->real^3) (x:real^3) =
    x$1 % (frechet_derivative s (at x) (basis 2) cross frechet_derivative s (at x) (basis 3)) +
    x$2 % (frechet_derivative s (at x) (basis 3) cross frechet_derivative s (at x) (basis 1)) +
    x$3 % (frechet_derivative s (at x) (basis 1) cross frechet_derivative s (at x) (basis 2))`;;

let SCH5_CONORMAL_ALG1 = prove
 (`!a b c x v:real^3.
     (x$1 % (b cross c) + x$2 % (c cross a) + x$3 % (a cross b)) dot
     (v$1 % a + v$2 % b + v$3 % c) = (x dot v) * ((a cross b) dot c)`,
  REWRITE_TAC[DOT_3; CROSS_COMPONENTS; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

let SCH5_CONORMAL_ALG2 = prove
 (`!a b c u w:real^3.
     (u cross w)$1 % (b cross c) + (u cross w)$2 % (c cross a) + (u cross w)$3 % (a cross b) =
     (u$1 % a + u$2 % b + u$3 % c) cross (w$1 % a + w$2 % b + w$3 % c)`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; CROSS_COMPONENTS; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

let SCH5_LINEAR_BASIS3 = prove
 (`!(A:real^3->real^3) v.
     linear A ==> A v = v$1 % A(basis 1) + v$2 % A(basis 2) + v$3 % A(basis 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v:real^3 = v$1 % basis 1 + v$2 % basis 2 + v$3 % basis 3` MP_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]));;

let SCH5_CONORMAL_ORTH = prove
 (`!(s:real^3->real^3) t v.
     s differentiable (at t) /\ orthogonal t v
     ==> sch5_conormal s t dot frechet_derivative s (at t) v = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (s:real^3->real^3) (at t))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [SPEC `v:real^3` (MATCH_MP SCH5_LINEAR_BASIS3 th)]) THEN
  REWRITE_TAC[sch5_conormal; SCH5_CONORMAL_ALG1] THEN
  UNDISCH_TAC `orthogonal (t:real^3) v` THEN SIMP_TAC[orthogonal; REAL_MUL_LZERO]);;

let SCH5_CONORMAL_NZ = prove
 (`!(s:real^3->real^3) t.
     t IN sphere(vec 0,&1) /\ s differentiable (at t) /\
     (!v. orthogonal t v /\ frechet_derivative s (at t) v = vec 0 ==> v = vec 0)
     ==> ~(sch5_conormal s t = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (s:real^3->real^3) (at t))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `A = frechet_derivative (s:real^3->real^3) (at t)` THEN
  SUBGOAL_THEN `(t:real^3) dot t = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^3. ~(u = vec 0) /\ orthogonal t u` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(t:real^3) cross basis 1 = vec 0` THENL
     [EXISTS_TAC `(t:real^3) cross basis 2` THEN
      REWRITE_TAC[orthogonal; DOT_CROSS_SELF] THEN
      UNDISCH_TAC `(t:real^3) cross basis 1 = vec 0` THEN UNDISCH_TAC `(t:real^3) dot t = &1` THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; CROSS_COMPONENTS; DOT_3; BASIS_COMPONENT; ARITH;
               VEC_COMPONENT] THEN
      CONV_TAC REAL_RING;
      EXISTS_TAC `(t:real^3) cross basis 1` THEN ASM_REWRITE_TAC[orthogonal; DOT_CROSS_SELF]];
    ALL_TAC] THEN
  ABBREV_TAC `w = (t:real^3) cross u` THEN
  SUBGOAL_THEN `orthogonal (t:real^3) w /\ u cross w = (u dot u) % t /\ w dot u = &0 /\
                w dot w = u dot u` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN UNDISCH_TAC `orthogonal (t:real^3) u` THEN
    UNDISCH_TAC `(t:real^3) dot t = &1` THEN
    REWRITE_TAC[orthogonal; CART_EQ; DIMINDEX_3; FORALL_3; CROSS_COMPONENTS; DOT_3;
                VECTOR_MUL_COMPONENT] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (u:real^3) dot u` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sch5_conormal (s:real^3->real^3) t =
                inv((u:real^3) dot u) % ((A:real^3->real^3) u cross A w)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`(A:real^3->real^3) (basis 1)`; `(A:real^3->real^3) (basis 2)`;
                   `(A:real^3->real^3) (basis 3)`; `u:real^3`; `w:real^3`] SCH5_CONORMAL_ALG2) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP SCH5_LINEAR_BASIS3 th)]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[sch5_conormal; VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_ASSOC; REAL_MUL_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[CROSS_EQ_0; COLLINEAR_LEMMA] THEN STRIP_TAC THENL
   [UNDISCH_TAC `~(u:real^3 = vec 0)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `w:real^3 = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x dot x`) THEN ASM_REWRITE_TAC[DOT_LZERO] THEN
    UNDISCH_TAC `&0 < (u:real^3) dot u` THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `w - c % u:real^3 = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `orthogonal (t:real^3) w` THEN UNDISCH_TAC `orthogonal (t:real^3) u` THEN
        REWRITE_TAC[orthogonal; DOT_RSUB; DOT_RMUL] THEN
        REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL];
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th; MATCH_MP LINEAR_CMUL th]) THEN
        ASM_REWRITE_TAC[VECTOR_SUB_REFL]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x dot u`) THEN
    REWRITE_TAC[DOT_LSUB; DOT_LMUL; DOT_LZERO] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `c = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&0 - c * ((u:real^3) dot u) = &0` THEN
      UNDISCH_TAC `&0 < (u:real^3) dot u` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    UNDISCH_TAC `(A:real^3->real^3) w = &0 % A u` THEN
    REWRITE_TAC[VECTOR_MUL_LZERO] THEN DISCH_TAC THEN
    SUBGOAL_THEN `w:real^3 = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x dot x`) THEN ASM_REWRITE_TAC[DOT_LZERO] THEN
    UNDISCH_TAC `&0 < (u:real^3) dot u` THEN REAL_ARITH_TAC]);;

let SCH5_CONORMAL_SMOOTH = prove
 (`!(s:real^3->real^3) W. open W /\ smooth_map_on W s ==> smooth_map_on W (sch5_conormal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i j. smooth_map_on W
                  (\x. frechet_derivative (s:real^3->real^3) (at x) (basis i) cross
                       frechet_derivative s (at x) (basis j))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `(cross)`;
                   `\x. frechet_derivative (s:real^3->real^3) (at x) (basis i)`;
                   `\x. frechet_derivative (s:real^3->real^3) (at x) (basis j)`]
      SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_SIMP_TAC[BILINEAR_CROSS; SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. smooth_map_on W (\x:real^3. lift(x$k))` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`W:real^3->bool`; `\x:real^3. x`; `k:num`]
      SMOOTH_MAP_ON_LIFT_COMPONENT) THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j k. smooth_map_on W
              (\x:real^3. x$k % (frechet_derivative (s:real^3->real^3) (at x) (basis i) cross
                                 frechet_derivative s (at x) (basis j)))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `\x:real^3. lift(x$k)`;
                   `\x. frechet_derivative (s:real^3->real^3) (at x) (basis i) cross
                        frechet_derivative s (at x) (basis j)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5_conormal (s:real^3->real^3) =
     (\x. x$1 % (frechet_derivative s (at x) (basis 2) cross frechet_derivative s (at x) (basis 3)) +
          (x$2 % (frechet_derivative s (at x) (basis 3) cross frechet_derivative s (at x) (basis 1)) +
           x$3 % (frechet_derivative s (at x) (basis 1) cross frechet_derivative s (at x) (basis 2))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; sch5_conormal]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[]);;

let SCH5_RAY_DERIV = prove
 (`!(Fm:real^3->real^3) t d.
     Fm differentiable (at t) /\
     ((\u. Fm(drop u % t)) has_vector_derivative d) (at (lift(&1)))
     ==> frechet_derivative Fm (at t) t = d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\u:real^1. drop u % (t:real^3)) has_vector_derivative t) (at (lift(&1)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^1. drop u % (t:real^3)`; `t:real^3`; `Fm:real^3->real^3`;
                 `frechet_derivative (Fm:real^3->real^3) (at t)`; `lift(&1)`] SCH5_CHAIN_VECTOR) THEN
  ASM_REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`\u:real^1. (Fm:real^3->real^3) (drop u % t)`; `lift(&1)`;
                       `frechet_derivative (Fm:real^3->real^3) (at t) t`; `d:real^3`]
                VECTOR_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[]);;

(* The tube map x |-> s(x/|x|) + (|x| - 1) n(x/|x|) along the cofactor      *)
(* normal, and the tube lemma: an embedded sphere has a collar.              *)

let SCH5_TUBE_MAP_SMOOTH = prove
 (`!(s:real^3->real^3) W.
     open W /\ sphere(vec 0,&1) SUBSET W /\ smooth_map_on W s
     ==> smooth_map_on {x | ~(x = vec 0)}
           (\x. s(inv(norm x) % x) + (norm x - &1) % sch5_conormal s (inv(norm x) % x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^3 | ~(x = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_NONZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:real^3. inv(norm x) % x) {x | ~(x = vec 0)} SUBSET W` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h:real^3->real^3. smooth_map_on W h
                  ==> smooth_map_on {x:real^3 | ~(x = vec 0)} (\x. h(inv(norm x) % x))`
  (LABEL_TAC "comp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `W:real^3->bool`;
                   `\x:real^3. inv(norm x) % x`; `h:real^3->real^3`]
      SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE; o_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "comp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `\x:real^3. lift(norm x - &1)`;
                 `\x:real^3. sch5_conormal (s:real^3->real^3) (inv(norm x) % x)`]
    SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_LIFT_NORM_NONZERO];
    USE_THEN "comp" MATCH_MP_TAC THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SCH5_CONORMAL_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let SCH5_TUBE_NECK = prove
 (`!(s:real^3->real^3) W.
     open W /\ sphere(vec 0,&1) SUBSET W /\ smooth_map_on W s /\
     (!x y. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\ s x = s y ==> x = y) /\
     (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v /\ frechet_derivative s (at t) v = vec 0
            ==> v = vec 0)
     ==> ?g g'. sch_neck g g' /\
                (!t. t IN sphere(vec 0,&1) ==> g t = s t) /\
                (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
                       ==> frechet_derivative g (at t) v = frechet_derivative s (at t) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Ga = \x:real^3. (s:real^3->real^3)(inv(norm x) % x) +
                              (norm x - &1) % sch5_conormal s (inv(norm x) % x)` THEN
  ABBREV_TAC `W' = W INTER {x:real^3 | ~(x = vec 0)}` THEN
  SUBGOAL_THEN `open(W':real^3->bool) /\ sphere(vec 0,&1) SUBSET W'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W'" THEN SIMP_TAC[OPEN_INTER; OPEN_NONZERO; ASSUME `open(W:real^3->bool)`] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET W` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `vec 0 IN sphere(vec 0:real^3,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W' (Ga:real^3->real^3) /\ smooth_map_on W' (s:real^3->real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN CONJ_TAC THENL
       [EXPAND_TAC "W'" THEN SET_TAC[];
        EXPAND_TAC "Ga" THEN MATCH_MP_TAC SCH5_TUBE_MAP_SMOOTH THEN
        EXISTS_TAC `W:real^3->bool` THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `W:real^3->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "W'" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^3. t IN sphere(vec 0,&1) ==> (s:real^3->real^3) differentiable (at t) /\
                                                     (Ga:real^3->real^3) differentiable (at t)`
  (LABEL_TAC "diff") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W':real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET W'` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Ga:real^3->real^3`; `s:real^3->real^3`; `sch5_conormal (s:real^3->real^3)`;
                 `W':real^3->bool`] SCH5_NECK_FROM_TRANSVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Ga" THEN REWRITE_TAC[IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID; REAL_SUB_REFL; VECTOR_MUL_LZERO;
                      VECTOR_ADD_RID];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH5_CONORMAL_ORTH THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `frechet_derivative (Ga:real^3->real^3) (at t) t = sch5_conormal s t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SCH5_RAY_DERIV THEN CONJ_TAC THENL
       [USE_THEN "diff" (fun th -> ACCEPT_TAC(CONJUNCT2(MP (SPEC `t:real^3` th)
          (ASSUME `(t:real^3) IN sphere(vec 0,&1)`))));
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      EXISTS_TAC `\u:real^1. (s:real^3->real^3) t + (drop u - &1) % sch5_conormal s t` THEN
      EXISTS_TAC `&1 / &2` THEN REWRITE_TAC[REAL_ARITH `&0 < &1 / &2`] THEN CONJ_TAC THENL
       [X_GEN_TAC `u:real^1` THEN REWRITE_TAC[dist; NORM_1; DROP_SUB; LIFT_DROP] THEN
        DISCH_TAC THEN EXPAND_TAC "Ga" THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `norm(t:real^3) = &1` ASSUME_TAC THENL
         [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0];
          ALL_TAC] THEN
        SUBGOAL_THEN `&0 < drop u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[NORM_MUL; REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs x = x`;
                 ASSUME `norm(t:real^3) = &1`; ASSUME `&0 < drop(u:real^1)`] THEN
        SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 ASSUME `&0 < drop(u:real^1)`];
        ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV) [VECTOR_ADD_SYM] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_RID] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
      REWRITE_TAC[VECTOR_SUB_RDISTRIB] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_SUB_RZERO] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
      REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
      ALL_TAC] THEN
    REWRITE_TAC[DOT_EQ_0] THEN MATCH_MP_TAC SCH5_CONORMAL_NZ THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [USE_THEN "diff" (fun th -> ACCEPT_TAC(CONJUNCT1(MP (SPEC `t:real^3` th)
        (ASSUME `(t:real^3) IN sphere(vec 0,&1)`))));
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (X_CHOOSE_THEN `G':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(Ga:real^3->real^3) o sch5_radial (eta / &2)`;
                        `sch5_radinv (eta / &2) o (G':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[]);;

