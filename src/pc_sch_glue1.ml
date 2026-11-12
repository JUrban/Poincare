(* ========================================================================= *)
(* pc_sch_glue1: tools for the gluing step SCH_SLAB_GLUE of the smooth       *)
(* Schoenflies theorem in R^3 (pc_sch_glue.ml). Contents: monotonicity of    *)
(* the cap profile; the symmetric capsule (top dome sch_cap1, a cylinder,    *)
(* the mirror dome) as the image of the unit sphere under an explicit global *)
(* diffeomorphism sch6_gamma; the capsule collar (the model cap collar on    *)
(* the cone and its mirror image), a collared sphere whenever the model cap  *)
(* collar is a diffeomorphism on the cone; a ball chart of the capsule that  *)
(* follows the capsule collar (from SCH_COLLAR3_STATEMENT); conjugation of   *)
(* compactly supported diffeomorphisms by charts.                            *)
(* ========================================================================= *)

needs "src/pc_sch_slab.ml";;
needs "src/pc_sch_isoext.ml";;
needs "src/pc_sch_planar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Monotonicity of the cap profile; smooth functions of one                  *)
(* real variable; the squared horizontal scale sch6_capq of the capsule.     *)
(* ------------------------------------------------------------------------- *)

let SCH6_PROFILE_MONO = prove
 (`!s t. s <= t /\ t <= &3 / &2 ==> sch_cap_profile s <= sch_cap_profile t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch_cap_profile] THEN
  MP_TAC(SPECL [`&4 * s - &5 / &2`; `&4 * t - &5 / &2`] SMOOTH_STEP_MONO) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&4 * s - &5 / &2` SMOOTH_STEP_BOUNDS) THEN
  ABBREV_TAC `a = smooth_step(&4 * s - &5 / &2)` THEN
  ABBREV_TAC `b = smooth_step(&4 * t - &5 / &2)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (t - s) * (&1 - a) /\ &0 <= (b - a) * (&3 / &2 - t)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* A smooth real function of a smooth real-valued map. *)

let SCH6_REAL_COMPOSE = prove
 (`!s (f:real^N->real) (phi:real->real).
        open s /\ smooth_map_on s (\x. lift(f x)) /\
        smooth_map_on (:real^1) (lift o phi o drop)
        ==> smooth_map_on s (\x. lift(phi(f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. lift((phi:real->real)((f:real^N->real) x))) =
                (lift o phi o drop) o (\x. lift(f x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV]);;

let SCH6_AFFINE_1 = prove
 (`!a b. smooth_map_on (:real^1) (\x. lift(a + b * drop x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL; LIFT_DROP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]);;

(* The two smooth steps used by the capsule (from SMOOTH_STEP_AFFINE_SMOOTH). *)

let SCH6_SS_PAIR = prove
 (`smooth_map_on (:real^1) (\x. lift(smooth_step(&3 / &2 - &2 * drop x))) /\
   smooth_map_on (:real^1) (\x. lift(smooth_step(&3 / &2 + &2 * drop x)))`,
  MP_TAC(ISPECL [`--(&2)`; `--(&3 / &2)`] SMOOTH_STEP_AFFINE_SMOOTH) THEN
  MP_TAC(ISPECL [`&2`; `--(&3 / &2)`] SMOOTH_STEP_AFFINE_SMOOTH) THEN
  REWRITE_TAC[o_DEF] THEN
  REWRITE_TAC[REAL_ARITH `--(&2) * t - --(&3 / &2) = &3 / &2 - &2 * t`;
              REAL_ARITH `&2 * t - --(&3 / &2) = &3 / &2 + &2 * t`] THEN
  SIMP_TAC[]);;

(* Squared horizontal scale of the capsule: on the upper half it is         *)
(* sch_capq 0 (the model cap collar on the unit sphere), on the lower half   *)
(* its mirror image; the three terms never meet their singular points.       *)

let sch6_capq = new_definition
 `sch6_capq (t:real) =
    (&1 - smooth_step(&3 / &2 - &2 * t)) / (&2 * (&1 + t)) +
    (smooth_step(&3 / &2 - &2 * t) * smooth_step(&3 / &2 + &2 * t)) / (&1 - t pow 2) +
    (smooth_step(&3 / &2 - &2 * t) * (&1 - smooth_step(&3 / &2 + &2 * t))) /
    (&2 * (&1 - t))`;;

let SCH6_CAPQ_TOP = prove
 (`!t. --(&1 / &4) <= t
       ==> sch6_capq t = (&1 - smooth_step(&3 / &2 - &2 * t)) / (&2 * (&1 + t)) +
                         smooth_step(&3 / &2 - &2 * t) / (&1 - t pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch6_capq] THEN
  SUBGOAL_THEN `smooth_step(&3 / &2 + &2 * t) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_SUB_REFL; REAL_MUL_RZERO; real_div; REAL_MUL_LZERO;
              REAL_ADD_RID]);;

let SCH6_CAPQ_BOT = prove
 (`!t. t <= &1 / &4
       ==> sch6_capq t = smooth_step(&3 / &2 + &2 * t) / (&1 - t pow 2) +
                         (&1 - smooth_step(&3 / &2 + &2 * t)) / (&2 * (&1 - t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch6_capq] THEN
  SUBGOAL_THEN `smooth_step(&3 / &2 - &2 * t) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_LID]);;

let SCH6_CAPQ_NORTH = prove
 (`!t. &3 / &4 <= t ==> sch6_capq t = inv(&2 * (&1 + t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:real` SCH6_CAPQ_TOP) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `smooth_step(&3 / &2 - &2 * t) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; real_div; REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID]);;

let SCH6_CAPQ_SOUTH = prove
 (`!t. t <= --(&3 / &4) ==> sch6_capq t = inv(&2 * (&1 - t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:real` SCH6_CAPQ_BOT) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `smooth_step(&3 / &2 + &2 * t) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; real_div; REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_LID]);;

let SCH6_CONVEX_POS = prove
 (`!a d1 d2. &0 <= a /\ a <= &1 /\ &0 < d1 /\ &0 < d2 ==> &0 < (&1 - a) / d1 + a / d2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a = &1` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_LT_INV];
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]]);;

let SCH6_CAPQ_POS = prove
 (`!t. &0 < sch6_capq t`,
  GEN_TAC THEN ASM_CASES_TAC `&3 / &4 <= t` THENL
   [ASM_SIMP_TAC[SCH6_CAPQ_NORTH] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t <= --(&3 / &4)` THENL
   [ASM_SIMP_TAC[SCH6_CAPQ_SOUTH] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - t pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[REAL_ABS_POS; ARITH_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `--(&1 / &4) <= t` THENL
   [ASM_SIMP_TAC[SCH6_CAPQ_TOP] THEN MATCH_MP_TAC SCH6_CONVEX_POS THEN
    ASM_REWRITE_TAC[SMOOTH_STEP_BOUNDS] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `t:real` SCH6_CAPQ_BOT) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC SCH6_CONVEX_POS THEN
    ASM_REWRITE_TAC[SMOOTH_STEP_BOUNDS] THEN ASM_REAL_ARITH_TAC]);;

(* Smoothness of sch6_capq: by its formula on the open interval (-1,1), by   *)
(* the closed forms SCH6_CAPQ_NORTH and SCH6_CAPQ_SOUTH near the ends.       *)

let SCH6_CAPQ_SMOOTH_IN = prove
 (`smooth_map_on (ball(vec 0:real^1,&1)) (lift o sch6_capq o drop)`,
  ABBREV_TAC `s = ball(vec 0:real^1,&1)` THEN
  SUBGOAL_THEN `open(s:real^1->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^1. x IN s ==> abs(drop x) < &1` (LABEL_TAC "B") THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_BALL_0; NORM_1]; ALL_TAC] THEN
  MP_TAC SCH6_SS_PAIR THEN
  DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP SMOOTH_MAP_ON_SUBSET o
    CONJ (ISPEC `s:real^1->bool` SUBSET_UNIV))) THEN
  SUBGOAL_THEN `!c. smooth_map_on (s:real^1->bool) (\x. lift c)` ASSUME_TAC THENL
   [REWRITE_TAC[SMOOTH_MAP_ON_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. smooth_map_on (s:real^1->bool) (\x. lift(a + b * drop x))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN REWRITE_TAC[SUBSET_UNIV; SCH6_AFFINE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (s:real^1->bool)
                  (\x. lift(&1 - smooth_step(&3 / &2 + &2 * drop x)))` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; sch6_capq; LIFT_ADD] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^1->bool`;
                   `\x:real^1. lift(&1 - smooth_step(&3 / &2 - &2 * drop x))`;
                   `\x:real^1. lift(&2 * (&1 + drop x))`] SMOOTH_MAP_ON_LIFT_DIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ARITH `&2 * (&1 + t) = &2 + &2 * t`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      USE_THEN "B" (MP_TAC o C MATCH_MP (ASSUME `(x:real^1) IN s`)) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^1->bool`;
                   `\x:real^1. lift(smooth_step(&3 / &2 - &2 * drop x) *
                                    smooth_step(&3 / &2 + &2 * drop x))`;
                   `\x:real^1. lift(&1 - drop x pow 2)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. lift(smooth_step(&3 / &2 - &2 * drop x))`;
                     `\x:real^1. lift(smooth_step(&3 / &2 + &2 * drop x))`]
        SMOOTH_MAP_ON_LIFT_MUL) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. x`; `2`] SMOOTH_MAP_ON_LIFT_POW) THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN
      USE_THEN "B" (ACCEPT_TAC o C MATCH_MP (ASSUME `(x:real^1) IN s`))];
    MP_TAC(ISPECL [`s:real^1->bool`;
                   `\x:real^1. lift(smooth_step(&3 / &2 - &2 * drop x) *
                                    (&1 - smooth_step(&3 / &2 + &2 * drop x)))`;
                   `\x:real^1. lift(&2 * (&1 - drop x))`] SMOOTH_MAP_ON_LIFT_DIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. lift(smooth_step(&3 / &2 - &2 * drop x))`;
                     `\x:real^1. lift(&1 - smooth_step(&3 / &2 + &2 * drop x))`]
        SMOOTH_MAP_ON_LIFT_MUL) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ARITH `&2 * (&1 - t) = &2 + --(&2) * t`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      USE_THEN "B" (MP_TAC o C MATCH_MP (ASSUME `(x:real^1) IN s`)) THEN REAL_ARITH_TAC]]);;

let SCH6_CAPQ_SMOOTH = prove
 (`smooth_map_on (:real^1) (lift o sch6_capq o drop)`,
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `x0:real^1` THEN
  ASM_CASES_TAC `abs(drop x0) < &1` THENL
   [EXISTS_TAC `ball(vec 0:real^1,&1)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0; NORM_1; SCH6_CAPQ_SMOOTH_IN];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < drop x0` THENL
   [EXISTS_TAC `{x:real^1 | x$1 > &3 / &4}` THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(abs(drop x0) < &1)` THEN UNDISCH_TAC `&0 < drop x0` THEN
      REWRITE_TAC[drop] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^1. lift(inv(&2 * (&1 + drop x)))` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM; GSYM drop] THEN REPEAT STRIP_TAC THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH6_CAPQ_NORTH THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`{x:real^1 | x$1 > &3 / &4}`; `\x:real^1. lift(&2 * (&1 + drop x))`]
        SMOOTH_MAP_ON_LIFT_INV) THEN
      REWRITE_TAC[LIFT_DROP; OPEN_HALFSPACE_COMPONENT_GT] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `&2 * (&1 + t) = &2 + &2 * t`] THEN
        REWRITE_TAC[SCH6_AFFINE_1];
        REWRITE_TAC[IN_ELIM_THM; GSYM drop] THEN REAL_ARITH_TAC]];
    EXISTS_TAC `{x:real^1 | x$1 < --(&3 / &4)}` THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(abs(drop x0) < &1)` THEN UNDISCH_TAC `~(&0 < drop x0)` THEN
      REWRITE_TAC[drop] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^1. lift(inv(&2 * (&1 - drop x)))` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM; GSYM drop] THEN REPEAT STRIP_TAC THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH6_CAPQ_SOUTH THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`{x:real^1 | x$1 < --(&3 / &4)}`; `\x:real^1. lift(&2 * (&1 - drop x))`]
        SMOOTH_MAP_ON_LIFT_INV) THEN
      REWRITE_TAC[LIFT_DROP; OPEN_HALFSPACE_COMPONENT_LT] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `&2 * (&1 - t) = &2 + --(&2) * t`] THEN
        REWRITE_TAC[SCH6_AFFINE_1];
        REWRITE_TAC[IN_ELIM_THM; GSYM drop] THEN REAL_ARITH_TAC]]]);;

(* On the upper half sch6_capq is sch_capq 0, i.e. the model cap collar on   *)
(* the unit sphere; the lower half is the mirror image.                      *)

let SCH6_CAPQ_PROFILE = prove
 (`!t. --(&1 / &4) <= t /\ t < &1
       ==> sch6_capq t * (&1 - t pow 2) = sch_cap_profile(&1 - t / &2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SCH6_CAPQ_TOP] THEN
  REWRITE_TAC[sch_cap_profile; REAL_ARITH `&4 * (&1 - t / &2) - &5 / &2 = &3 / &2 - &2 * t`] THEN
  SUBGOAL_THEN `~(&1 + t = &0) /\ ~(&1 - t pow 2 = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `a = smooth_step(&3 / &2 - &2 * t)` THEN
  UNDISCH_TAC `~(&1 + t = &0)` THEN UNDISCH_TAC `~(&1 - t pow 2 = &0)` THEN
  CONV_TAC REAL_FIELD);;

let SCH6_CAPQ_PROFILE_BOT = prove
 (`!t. --(&1) < t /\ t <= &1 / &4
       ==> sch6_capq t * (&1 - t pow 2) = sch_cap_profile(&1 + t / &2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SCH6_CAPQ_BOT] THEN
  REWRITE_TAC[sch_cap_profile; REAL_ARITH `&4 * (&1 + t / &2) - &5 / &2 = &3 / &2 + &2 * t`] THEN
  SUBGOAL_THEN `~(&1 - t = &0) /\ ~(&1 - t pow 2 = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `b = smooth_step(&3 / &2 + &2 * t)` THEN
  UNDISCH_TAC `~(&1 - t = &0)` THEN UNDISCH_TAC `~(&1 - t pow 2 = &0)` THEN
  CONV_TAC REAL_FIELD);;

let SCH6_CAPQ_EQ = prove
 (`!t. --(&1 / &4) <= t /\ t < &1 ==> sch6_capq t = sch_capq (&0) t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sch_capq; REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_ADD_RID] THEN
  MP_TAC(SPEC `t:real` SCH6_CAPQ_PROFILE) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(&1 - t pow 2 = &0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let SCH6_CAPQ_EQ_BOT = prove
 (`!t. --(&1) < t /\ t <= &1 / &4 ==> sch6_capq t = sch_capq (&0) (--t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sch_capq; REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH `&1 - --t / &2 = &1 + t / &2`; REAL_RING `(--t) pow 2 = t pow 2`] THEN
  MP_TAC(SPEC `t:real` SCH6_CAPQ_PROFILE_BOT) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(&1 - t pow 2 = &0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The symmetric capsule.  sch6_gamma z = (a(z3) z', -1 + z3/2)              *)
(* with a = sqrt o sch6_capq is a global diffeomorphism; it maps the unit    *)
(* sphere onto the capsule whose top is sch_cap1 and whose bottom is the     *)
(* mirror image of sch_cap1 in the plane y3 = -1.                            *)
(* ------------------------------------------------------------------------- *)

let SCH6_SQRTQ_SMOOTH = prove
 (`!s (f:real^N->real).
        open s /\ smooth_map_on s (\x. lift(f x))
        ==> smooth_map_on s (\x. lift(sqrt(sch6_capq(f x))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(sch6_capq((f:real^N->real) x))`]
    SMOOTH_MAP_ON_LIFT_SQRT) THEN
  REWRITE_TAC[LIFT_DROP; SCH6_CAPQ_POS] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH6_REAL_COMPOSE THEN
  ASM_REWRITE_TAC[SCH6_CAPQ_SMOOTH]);;

let SCH6_SQRTQ_POS = prove
 (`!t. &0 < sqrt(sch6_capq t)`,
  GEN_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[SCH6_CAPQ_POS]);;

let sch6_gamma = new_definition
 `sch6_gamma (z:real^3) =
    vector[sqrt(sch6_capq(z$3)) * z$1; sqrt(sch6_capq(z$3)) * z$2;
           --(&1) + z$3 / &2]:real^3`;;

let sch6_gammai = new_definition
 `sch6_gammai (y:real^3) =
    vector[y$1 / sqrt(sch6_capq(&2 * (y$3 + &1)));
           y$2 / sqrt(sch6_capq(&2 * (y$3 + &1)));
           &2 * (y$3 + &1)]:real^3`;;

let SCH6_GAMMA_INVERSES = prove
 (`(!z. sch6_gammai(sch6_gamma z) = z) /\ (!y. sch6_gamma(sch6_gammai y) = y)`,
  CONJ_TAC THEN X_GEN_TAC `z:real^3` THEN
  REWRITE_TAC[sch6_gamma; sch6_gammai; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REWRITE_TAC[REAL_ARITH `&2 * ((--(&1) + t / &2) + &1) = t`;
              REAL_ARITH `--(&1) + (&2 * (t + &1)) / &2 = t`] THEN
  MP_TAC(MATCH_MP REAL_LT_IMP_NZ (SPEC `(z:real^3)$3` SCH6_SQRTQ_POS)) THEN
  MP_TAC(MATCH_MP REAL_LT_IMP_NZ (SPEC `&2 * ((z:real^3)$3 + &1)` SCH6_SQRTQ_POS)) THEN
  CONV_TAC REAL_FIELD);;

let SCH6_GAMMA_DIFFEO = prove
 (`diffeomorphism_on (:real^3) (:real^3) sch6_gamma sch6_gammai`,
  REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV; SCH6_GAMMA_INVERSES] THEN
  SUBGOAL_THEN `IMAGE sch6_gamma (:real^3) = (:real^3) /\
                IMAGE sch6_gammai (:real^3) = (:real^3)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN MESON_TAC[SCH6_GAMMA_INVERSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. smooth_map_on (:real^3) (\y:real^3. lift(y$k))` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. y`; `k:num`]
      SMOOTH_MAP_ON_LIFT_COMPONENT) THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b k. smooth_map_on (:real^3) (\y:real^3. lift(a + b * y$k))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\y:real^3. lift(sqrt(sch6_capq(y$3)))) /\
                smooth_map_on (:real^3)
                  (\y:real^3. lift(sqrt(sch6_capq(&2 * (y$3 + &1)))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SCH6_SQRTQ_SMOOTH THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `&2 * (t + &1) = &2 + &2 * t`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `sch6_gamma`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  MP_TAC(ISPECL [`(:real^3)`; `sch6_gammai`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_UNIV; DIMINDEX_3] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
  REWRITE_TAC[TAUT `(a \/ b \/ c ==> d) <=> (a ==> d) /\ (b ==> d) /\ (c ==> d)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[sch6_gamma; sch6_gammai; VECTOR_3] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(sqrt(sch6_capq(y$3)))`;
                   `\y:real^3. lift(y$1)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_UNIV];
    MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(sqrt(sch6_capq(y$3)))`;
                   `\y:real^3. lift(y$2)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ONCE_REWRITE_TAC[REAL_ARITH `--(&1) + t / &2 = --(&1) + inv(&2) * t`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(y$1)`;
                   `\y:real^3. lift(sqrt(sch6_capq(&2 * (y$3 + &1))))`]
      SMOOTH_MAP_ON_LIFT_DIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN REWRITE_TAC[SCH6_SQRTQ_POS];
    MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(y$2)`;
                   `\y:real^3. lift(sqrt(sch6_capq(&2 * (y$3 + &1))))`]
      SMOOTH_MAP_ON_LIFT_DIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN REWRITE_TAC[SCH6_SQRTQ_POS];
    ONCE_REWRITE_TAC[REAL_ARITH `&2 * (t + &1) = &2 + &2 * t`] THEN ASM_REWRITE_TAC[]]);;

let SCH6_GAMMA_HOMEO = prove
 (`homeomorphism ((:real^3),(:real^3)) (sch6_gamma,sch6_gammai)`,
  MP_TAC SCH6_GAMMA_DIFFEO THEN
  REWRITE_TAC[diffeomorphism_on; homeomorphism; IN_UNIV] THEN
  MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;

(* The capsule region is the image of the closed unit ball, and the capsule *)
(* bounds the ball chart sch6_gamma.                                         *)

let SCH6_GAMMA_INSIDE = prove
 (`IMAGE sch6_gamma (sphere(vec 0,&1)) UNION inside(IMAGE sch6_gamma (sphere(vec 0,&1))) =
   IMAGE sch6_gamma (cball(vec 0,&1))`,
  MP_TAC(ISPECL [`sch6_gamma`; `sch6_gammai`; `sphere(vec 0:real^3,&1)`]
    SCH_INSIDE_HOMEOMORPHISM) THEN
  REWRITE_TAC[SCH6_GAMMA_HOMEO; INSIDE_SPHERE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM IMAGE_UNION; GSYM BALL_UNION_SPHERE] THEN
  REWRITE_TAC[UNION_COMM]);;

let SCH6_GAMMA_BOUNDS = prove
 (`sch_bounds_ball (IMAGE sch6_gamma (sphere(vec 0,&1)))`,
  REWRITE_TAC[sch_bounds_ball; SCH6_GAMMA_INSIDE] THEN
  MAP_EVERY EXISTS_TAC [`sch6_gamma`; `sch6_gammai`] THEN REWRITE_TAC[sch_ball] THEN
  MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN REWRITE_TAC[SCH6_GAMMA_DIFFEO; OPEN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* The capsule collar sch6_capsule e0: the model cap collar on               *)
(* the cone sch_capcone, its mirror image in the plane y3 = -1 on the        *)
(* flipped cone (the two agree on the band |x3| < |x|/4).  On the unit       *)
(* sphere it is sch6_gamma.                                                  *)
(* ------------------------------------------------------------------------- *)

let sch6_mir = new_definition
 `sch6_mir (y:real^3) = vector[y$1; y$2; --(&2) - y$3]:real^3`;;

let sch6_capsule = new_definition
 `sch6_capsule (e0:real) (x:real^3) =
    if --(&1 / &4) * norm x < x$3 then sch_cap_collar e0 x
    else sch6_mir(sch_cap_collar e0 (sch_flip3 x))`;;

let SCH6_FLIP3_COMPONENTS = prove
 (`!x:real^3. (sch_flip3 x)$1 = x$1 /\ (sch_flip3 x)$2 = x$2 /\ (sch_flip3 x)$3 = --(x$3)`,
  REWRITE_TAC[sch_flip3; VECTOR_3]);;

let SCH6_MIR_COMPONENTS = prove
 (`!y:real^3. (sch6_mir y)$1 = y$1 /\ (sch6_mir y)$2 = y$2 /\ (sch6_mir y)$3 = --(&2) - y$3`,
  REWRITE_TAC[sch6_mir; VECTOR_3]);;

let SCH6_NORM_FLIP3 = prove
 (`!x:real^3. norm(sch_flip3 x) = norm x`,
  GEN_TAC THEN REWRITE_TAC[NORM_EQ; DOT_3; SCH6_FLIP3_COMPONENTS] THEN REAL_ARITH_TAC);;

let SCH6_MIR_INVOLUTION = prove
 (`!y:real^3. sch6_mir(sch6_mir y) = y`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; SCH6_MIR_COMPONENTS] THEN REAL_ARITH_TAC);;

(* On the band the cap collar and its mirror image agree. *)

let SCH6_CAPSULE_BAND = prove
 (`!e0 x:real^3. &0 < norm x /\ abs(x$3) < norm x / &4
       ==> sch_cap_collar e0 x = sch6_mir(sch_cap_collar e0 (sch_flip3 x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs((x:real^3)$3 / norm x) < &1 / &4` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sch_cap_collar; sch_capq; sch6_mir; SCH6_NORM_FLIP3; SCH6_FLIP3_COMPONENTS;
              CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  SUBGOAL_THEN `--((x:real^3)$3) / norm x = --(x$3 / norm x)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LNEG]; ALL_TAC] THEN
  ABBREV_TAC `c = (x:real^3)$3 / norm x` THEN
  ABBREV_TAC `e = e0 * (norm(x:real^3) - &1)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `smooth_step(&8 * c - &6) = &0 /\ smooth_step(&8 * --c - &6) = &0`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_RID] THEN
  SUBGOAL_THEN `sch_cap_profile(&1 - c / &2) = &1 /\ sch_cap_profile(&1 - --c / &2) = &1`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_RING `(--c) pow 2 = c pow 2`] THEN REAL_ARITH_TAC);;

let SCH6_CAPSULE_CONE = prove
 (`!e0 x. x IN sch_capcone ==> sch6_capsule e0 x = sch_cap_collar e0 x`,
  SIMP_TAC[sch_capcone; IN_ELIM_THM; sch6_capsule]);;

let SCH6_CAPSULE_FCONE = prove
 (`!e0 x:real^3. &0 < norm x /\ x$3 < norm x / &4
       ==> sch6_capsule e0 x = sch6_mir(sch_cap_collar e0 (sch_flip3 x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch6_capsule] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SCH6_CAPSULE_BAND THEN ASM_REAL_ARITH_TAC);;

(* On the unit sphere the capsule collar is sch6_gamma. *)

let SCH6_CAPSULE_SPHERE = prove
 (`!e0 x:real^3. norm x = &1 ==> sch6_capsule e0 x = sch6_gamma x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs((x:real^3)$3) <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((x:real^3)$3) = &1 ==> x$1 = &0 /\ x$2 = &0` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3)$3 * x$3 = &1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP
        (REAL_ARITH `abs a = &1 ==> a = &1 \/ a = -- &1`)) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `norm(x:real^3) = &1` THEN REWRITE_TAC[NORM_EQ_1; DOT_3] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `(x:real^3)$1` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `(x:real^3)$2` REAL_LE_SQUARE) THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3)$1 * x$1 = &0 /\ x$2 * x$2 = &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ENTIRE] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[sch6_capsule; sch6_gamma; ASSUME `norm(x:real^3) = &1`] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[sch_cap_collar; sch6_mir; SCH6_NORM_FLIP3; SCH6_FLIP3_COMPONENTS;
              ASSUME `norm(x:real^3) = &1`; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              REAL_SUB_REFL; REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID; REAL_DIV_1] THEN
  REWRITE_TAC[REAL_MUL_LID] THENL
   [ASM_CASES_TAC `(x:real^3)$3 = &1` THENL
     [SUBGOAL_THEN `(x:real^3)$1 = &0 /\ x$2 = &0` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `sch6_capq((x:real^3)$3) = sch_capq (&0) (x$3)` SUBST1_TAC THENL
     [MATCH_MP_TAC SCH6_CAPQ_EQ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_CASES_TAC `(x:real^3)$3 = -- &1` THENL
     [SUBGOAL_THEN `(x:real^3)$1 = &0 /\ x$2 = &0` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sch6_capq((x:real^3)$3) = sch_capq (&0) (--(x$3))` SUBST1_TAC THENL
     [MATCH_MP_TAC SCH6_CAPQ_EQ_BOT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The capsule collar is a collared sphere (sch_neck) whenever               *)
(* the model cap collar is a diffeomorphism on the cone sch_capcone.         *)
(* ------------------------------------------------------------------------- *)

let SCH6_FLIP3_LINEAR = prove
 (`linear sch_flip3`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; SCH6_FLIP3_COMPONENTS;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC);;

let SCH6_FLIP3_SMOOTH = prove
 (`!s. open s ==> smooth_map_on s sch_flip3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `\x:real^3. x`; `sch_flip3`] SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SCH6_FLIP3_LINEAR; o_DEF; ETA_AX]);;

let SCH6_MIR_ALT = prove
 (`sch6_mir = \y. sch_flip3 y + vector[&0; &0; --(&2)]`,
  REWRITE_TAC[FUN_EQ_THM; CART_EQ; DIMINDEX_3; FORALL_3; SCH6_MIR_COMPONENTS;
              SCH6_FLIP3_COMPONENTS; VECTOR_ADD_COMPONENT; VECTOR_3] THEN REAL_ARITH_TAC);;

let SCH6_MIR_SMOOTH = prove
 (`!s. open s ==> smooth_map_on s sch6_mir`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SCH6_MIR_ALT] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; ETA_AX; SCH6_FLIP3_SMOOTH]);;

let SCH6_MIR_CONTINUOUS = prove
 (`!x. sch6_mir continuous at x`,
  GEN_TAC THEN REWRITE_TAC[SCH6_MIR_ALT] THEN MATCH_MP_TAC CONTINUOUS_ADD THEN
  REWRITE_TAC[CONTINUOUS_CONST; ETA_AX] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[SCH6_FLIP3_LINEAR]);;

(* The cone, the flipped cone and the annulus. *)

let sch6_fcone = new_definition
 `sch6_fcone = {x:real^3 | &1 / &2 < norm x /\ norm x < &2 /\ x$3 < norm x / &4}`;;

let SCH6_FCONE_FLIP = prove
 (`!x:real^3. x IN sch6_fcone <=> sch_flip3 x IN sch_capcone`,
  REWRITE_TAC[sch6_fcone; sch_capcone; IN_ELIM_THM; SCH6_NORM_FLIP3;
              SCH6_FLIP3_COMPONENTS] THEN REAL_ARITH_TAC);;

let SCH6_ANNULUS_CONES = prove
 (`annulus (&1 / &2) (&2) = sch_capcone UNION sch6_fcone`,
  REWRITE_TAC[EXTENSION; IN_UNION; sch_capcone; sch6_fcone; IN_ELIM_THM; annulus] THEN
  REAL_ARITH_TAC);;

let SCH6_OPEN_HALF = prove
 (`!a b. open {x:real^3 | a * norm x < b * x$3}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:real^3 | a * norm x < b * x$3} =
                {x | lift(b * x$3 - a * norm x) IN {y:real^1 | y$1 > &0}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN GEN_TAC THEN
  REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_CMUL THENL
   [SIMP_TAC[CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_3; ARITH];
    REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_NORM]]);;

let SCH6_OPEN_ANNULUS_PART = prove
 (`!s:real^3->bool. open s ==> open {x | &1 / &2 < norm x /\ norm x < &2 /\ x IN s}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^3 | &1 / &2 < norm x /\ norm x < &2 /\ x IN s} =
                ((:real^3) DIFF cball(vec 0,&1 / &2)) INTER ball(vec 0,&2) INTER s`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_DIFF; IN_UNIV; IN_CBALL_0;
                IN_BALL_0; REAL_NOT_LE];
    ASM_SIMP_TAC[OPEN_INTER; OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL; OPEN_BALL]]);;

let SCH6_OPEN_CAPCONE = prove
 (`open sch_capcone`,
  MP_TAC(ISPEC `{x:real^3 | --(&1 / &4) * norm x < &1 * x$3}` SCH6_OPEN_ANNULUS_PART) THEN
  REWRITE_TAC[SCH6_OPEN_HALF; IN_ELIM_THM; REAL_MUL_LID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[sch_capcone; EXTENSION; IN_ELIM_THM]);;

let SCH6_OPEN_FCONE = prove
 (`open sch6_fcone`,
  MP_TAC(ISPEC `{x:real^3 | --(&1 / &4) * norm x < --(&1) * x$3}` SCH6_OPEN_ANNULUS_PART) THEN
  REWRITE_TAC[SCH6_OPEN_HALF; IN_ELIM_THM] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[sch6_fcone; EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* Heights: off the band, the cap collar stays above -29/32. *)

let SCH6_CAPCOLLAR_HEIGHT_TOP = prove
 (`!e0 x:real^3. &0 < e0 /\ e0 <= &1 / &16 /\ x IN sch_capcone /\ norm x / &4 <= x$3
                 ==> --(&29 / &32) <= (sch_cap_collar e0 x)$3`,
  REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[sch_cap_collar; VECTOR_3] THEN
  SUBGOAL_THEN `&1 / &4 <= (x:real^3)$3 / norm x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 / &2 < n ==> &0 < n`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&8 * ((x:real^3)$3 / norm x) - &6` SMOOTH_STEP_BOUNDS) THEN
  ABBREV_TAC `b = smooth_step(&8 * ((x:real^3)$3 / norm x) - &6)` THEN
  ABBREV_TAC `c = (x:real^3)$3 / norm x` THEN
  ABBREV_TAC `n = norm(x:real^3)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `--(&1 / &32) <= e0 * (n - &1) * b` MP_TAC THENL
   [ASM_CASES_TAC `&0 <= n - &1` THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --(&1 / &32) <= x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= e0 * (&1 - n) * b /\ e0 * (&1 - n) * b <= e0 * (&1 - n) * &1 /\
                    e0 * (&1 - n) <= (&1 / &16) * (&1 / &2)`
      MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_MUL_RID] THEN REAL_ARITH_TAC]];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The capsule collar is a collared sphere.  Inverse: h (the                 *)
(* inverse of the cap collar) at heights >= -1, its mirror image below;      *)
(* off the band the two halves are separated by height (>= -29/32 against    *)
(* <= -35/32), on the band the two formulas agree.                           *)
(* ------------------------------------------------------------------------- *)

let SCH6_CAPSULE_FCONE_IN = prove
 (`!e0 x. x IN sch6_fcone
          ==> sch6_capsule e0 x = sch6_mir(sch_cap_collar e0 (sch_flip3 x))`,
  REWRITE_TAC[sch6_fcone; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SCH6_CAPSULE_FCONE THEN ASM_REAL_ARITH_TAC);;

let SCH6_CAPSULE_LEFT_INV = prove
 (`!e0 h x:real^3.
        &0 < e0 /\ e0 <= &1 / &16 /\
        (!z. z IN sch_capcone ==> h(sch_cap_collar e0 z) = z) /\
        x IN annulus (&1 / &2) (&2)
        ==> (if --(&1) <= (sch6_capsule e0 x)$3 then h(sch6_capsule e0 x)
             else sch_flip3(h(sch6_mir(sch6_capsule e0 x)))) = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 < norm(x:real^3) /\ norm x < &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN sch_capcone` ASSUME_TAC THENL
     [REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `--(&1) <= (sch6_capsule e0 x)$3` THEN
      SUBGOAL_THEN `sch6_capsule e0 x = sch6_mir(sch_cap_collar e0 (sch_flip3 x))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SCH6_CAPSULE_FCONE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SCH6_MIR_COMPONENTS] THEN
      MP_TAC(SPECL [`e0:real`; `sch_flip3 x`] SCH6_CAPCOLLAR_HEIGHT_TOP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM SCH6_FCONE_FLIP; sch6_fcone; IN_ELIM_THM; SCH6_NORM_FLIP3;
                        SCH6_FLIP3_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ASM_SIMP_TAC[SCH6_CAPSULE_CONE]];
    SUBGOAL_THEN `(x:real^3) IN sch6_fcone` ASSUME_TAC THENL
     [REWRITE_TAC[sch6_fcone; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(--(&1) <= (sch6_capsule e0 x)$3)` THEN
      SUBGOAL_THEN `(x:real^3) IN sch_capcone` ASSUME_TAC THENL
       [REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SCH6_CAPSULE_CONE] THEN
      MP_TAC(SPECL [`e0:real`; `x:real^3`] SCH6_CAPCOLLAR_HEIGHT_TOP) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SCH6_CAPSULE_FCONE_IN; SCH6_MIR_INVOLUTION] THEN
    SUBGOAL_THEN `h(sch_cap_collar e0 (sch_flip3 x)) = sch_flip3 x` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[GSYM SCH6_FCONE_FLIP]; ALL_TAC] THEN
    REWRITE_TAC[SCH_FLIP3_INVOLUTION]]);;

let SCH6_CAPSULE_IMAGE = prove
 (`!e0. IMAGE (sch6_capsule e0) (annulus (&1 / &2) (&2)) =
        IMAGE (sch_cap_collar e0) sch_capcone UNION
        IMAGE sch6_mir (IMAGE (sch_cap_collar e0) sch_capcone)`,
  GEN_TAC THEN REWRITE_TAC[SCH6_ANNULUS_CONES; IMAGE_UNION] THEN BINOP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
                            ==> IMAGE f s = IMAGE g s`) THEN
    REWRITE_TAC[SCH6_CAPSULE_CONE];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `sch_cap_collar e0 (sch_flip3 x)` THEN
      ASM_SIMP_TAC[SCH6_CAPSULE_FCONE_IN] THEN EXISTS_TAC `sch_flip3 x` THEN
      ASM_REWRITE_TAC[GSYM SCH6_FCONE_FLIP];
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `sch_flip3 z` THEN
      ASM_REWRITE_TAC[SCH6_FCONE_FLIP; SCH_FLIP3_INVOLUTION] THEN
      SUBGOAL_THEN `sch_flip3 z IN sch6_fcone` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[SCH6_FCONE_FLIP; SCH_FLIP3_INVOLUTION]; ALL_TAC] THEN
      ASM_SIMP_TAC[SCH6_CAPSULE_FCONE_IN; SCH_FLIP3_INVOLUTION]]]);;

let SCH6_CAPSULE_SMOOTH = prove
 (`!e0. smooth_map_on sch_capcone (sch_cap_collar e0)
        ==> smooth_map_on (annulus (&1 / &2) (&2)) (sch6_capsule e0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[OPEN_ANNULUS; SCH6_ANNULUS_CONES; IN_UNION] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
   [EXISTS_TAC `sch_capcone` THEN ASM_REWRITE_TAC[SCH6_OPEN_CAPCONE] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `sch_cap_collar e0` THEN
    ASM_SIMP_TAC[SCH6_CAPSULE_CONE];
    EXISTS_TAC `sch6_fcone` THEN ASM_REWRITE_TAC[SCH6_OPEN_FCONE] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `sch6_mir o sch_cap_collar e0 o sch_flip3` THEN CONJ_TAC THENL
     [SIMP_TAC[o_THM; SCH6_CAPSULE_FCONE_IN];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
      SIMP_TAC[SCH6_OPEN_FCONE; OPEN_UNIV; SUBSET_UNIV; SCH6_MIR_SMOOTH] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `sch_capcone` THEN
      ASM_SIMP_TAC[SCH6_OPEN_FCONE; SCH6_OPEN_CAPCONE; SCH6_FLIP3_SMOOTH] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GSYM SCH6_FCONE_FLIP] THEN SIMP_TAC[]]]);;

(* The inverse on the two halves of the image. *)

let SCH6_CAPSULE_RIGHT1 = prove
 (`!e0 h y:real^3.
        &0 < e0 /\ e0 <= &1 / &16 /\
        (!z. z IN sch_capcone ==> h(sch_cap_collar e0 z) = z) /\
        y IN IMAGE (sch_cap_collar e0) sch_capcone
        ==> (if --(&1) <= y$3 then h y else sch_flip3(h(sch6_mir y))) = h y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "HL") (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "HL" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN sch_capcone`)]) THEN
  SUBGOAL_THEN `(x:real^3)$3 < norm x / &4` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(--(&1) <= (sch_cap_collar e0 x)$3)` THEN
    MP_TAC(SPECL [`e0:real`; `x:real^3`] SCH6_CAPCOLLAR_HEIGHT_TOP) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN sch_capcone` THEN
  REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e0:real`; `x:real^3`] SCH6_CAPSULE_BAND) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SCH6_MIR_INVOLUTION] THEN
  SUBGOAL_THEN `h(sch_cap_collar e0 (sch_flip3 x)) = sch_flip3 x` SUBST1_TAC THENL
   [USE_THEN "HL" MATCH_MP_TAC THEN
    REWRITE_TAC[sch_capcone; IN_ELIM_THM; SCH6_NORM_FLIP3; SCH6_FLIP3_COMPONENTS] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SCH_FLIP3_INVOLUTION]]);;

let SCH6_CAPSULE_RIGHT2 = prove
 (`!e0 h y:real^3.
        &0 < e0 /\ e0 <= &1 / &16 /\
        (!z. z IN sch_capcone ==> h(sch_cap_collar e0 z) = z) /\
        y IN IMAGE sch6_mir (IMAGE (sch_cap_collar e0) sch_capcone)
        ==> (if --(&1) <= y$3 then h y else sch_flip3(h(sch6_mir y))) =
            sch_flip3(h(sch6_mir y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "HL") (X_CHOOSE_THEN `w:real^3`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[SCH6_MIR_INVOLUTION] THEN
  USE_THEN "HL" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^3) IN sch_capcone`)]) THEN
  SUBGOAL_THEN `(z:real^3)$3 < norm z / &4` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `--(&1) <= (sch6_mir(sch_cap_collar e0 z))$3` THEN
    REWRITE_TAC[SCH6_MIR_COMPONENTS] THEN
    MP_TAC(SPECL [`e0:real`; `z:real^3`] SCH6_CAPCOLLAR_HEIGHT_TOP) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(z:real^3) IN sch_capcone` THEN
  REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e0:real`; `z:real^3`] SCH6_CAPSULE_BAND) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SCH6_MIR_INVOLUTION] THEN
  USE_THEN "HL" MATCH_MP_TAC THEN
  REWRITE_TAC[sch_capcone; IN_ELIM_THM; SCH6_NORM_FLIP3; SCH6_FLIP3_COMPONENTS] THEN
  ASM_REAL_ARITH_TAC);;

let SCH6_MIR_IMAGE_OPEN = prove
 (`!s:real^3->bool. open s ==> open(IMAGE sch6_mir s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE sch6_mir s = {y:real^3 | sch6_mir y IN s}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[SCH6_MIR_INVOLUTION];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[SCH6_MIR_CONTINUOUS]]);;

(* The capsule collar is a collared sphere. *)

let SCH6_CAPSULE_NECK = prove
 (`!e0 h. &0 < e0 /\ e0 <= &1 / &16 /\
          diffeomorphism_on sch_capcone (IMAGE (sch_cap_collar e0) sch_capcone)
                            (sch_cap_collar e0) h
          ==> sch_neck (sch6_capsule e0)
                (\y. if --(&1) <= y$3 then h y else sch_flip3(h(sch6_mir y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  SUBGOAL_THEN `!x:real^3. x IN annulus (&1 / &2) (&2)
                    ==> (if --(&1) <= (sch6_capsule e0 x)$3 then h(sch6_capsule e0 x)
                         else sch_flip3(h(sch6_mir(sch6_capsule e0 x)))) = x`
  (LABEL_TAC "LI") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH6_CAPSULE_LEFT_INV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sch_neck; diffeomorphism_on; OPEN_ANNULUS] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SCH6_CAPSULE_IMAGE] THEN MATCH_MP_TAC OPEN_UNION THEN
    ASM_SIMP_TAC[SCH6_MIR_IMAGE_OPEN];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC))) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `sch6_capsule e0 x` THEN ASM_SIMP_TAC[] THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[]];
    BETA_TAC THEN USE_THEN "LI" ACCEPT_TAC;
    REWRITE_TAC[FORALL_IN_IMAGE] THEN BETA_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SCH6_CAPSULE_SMOOTH THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SCH6_CAPSULE_IMAGE] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    CONJ_TAC THENL [MATCH_MP_TAC OPEN_UNION THEN ASM_SIMP_TAC[SCH6_MIR_IMAGE_OPEN]; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [EXISTS_TAC `IMAGE (sch_cap_collar e0) sch_capcone` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `h:real^3->real^3` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN BETA_TAC THEN
      MP_TAC(SPECL [`e0:real`; `h:real^3->real^3`; `w:real^3`] SCH6_CAPSULE_RIGHT1) THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `IMAGE sch6_mir (IMAGE (sch_cap_collar e0) sch_capcone)` THEN
      ASM_SIMP_TAC[SCH6_MIR_IMAGE_OPEN] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `sch_flip3 o h o sch6_mir` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
        CONV_TAC SYM_CONV THEN BETA_TAC THEN
        MP_TAC(SPECL [`e0:real`; `h:real^3->real^3`; `w:real^3`] SCH6_CAPSULE_RIGHT2) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
        ASM_SIMP_TAC[SCH6_MIR_IMAGE_OPEN; OPEN_UNIV; SUBSET_UNIV; SCH6_FLIP3_SMOOTH] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
        EXISTS_TAC `IMAGE (sch_cap_collar e0) sch_capcone` THEN
        ASM_SIMP_TAC[SCH6_MIR_IMAGE_OPEN; SCH6_MIR_SMOOTH] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; SCH6_MIR_INVOLUTION] THEN
        SIMP_TAC[FUN_IN_IMAGE]]]]);;

(* ------------------------------------------------------------------------- *)
(* A ball chart of the capsule that follows the capsule collar               *)
(* on annulus(3/4,2), from SCH_COLLAR3_STATEMENT.  The inverted alternative  *)
(* of sch_fills is excluded at the point (0,0,10/9).                        *)
(* ------------------------------------------------------------------------- *)

let SCH6_CAPSULE_SPHERE_IMAGE = prove
 (`!e0. IMAGE (sch6_capsule e0) (sphere(vec 0,&1)) = IMAGE sch6_gamma (sphere(vec 0,&1))`,
  GEN_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
                         ==> IMAGE f s = IMAGE g s`) THEN
  SIMP_TAC[IN_SPHERE_0; SCH6_CAPSULE_SPHERE]);;

let SCH6_NORM_E3 = prove
 (`!a. &0 <= a ==> norm(vector[&0; &0; a]:real^3) = a`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NORM_EQ_SQUARE; DOT_3; VECTOR_3] THEN
  REAL_ARITH_TAC);;

let SCH6_CAPCOLLAR_AXIS = prove
 (`!e0. sch_cap_collar e0 (vector[&0; &0; &9 / &10]) =
        vector[&0; &0; --(&1 / &2) - e0 / &10]`,
  GEN_TAC THEN
  REWRITE_TAC[sch_cap_collar; VECTOR_3] THEN
  SIMP_TAC[SCH6_NORM_E3; REAL_ARITH `&0 <= &9 / &10`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SMOOTH_STEP_1; REAL_LE_REFL] THEN
  SUBGOAL_THEN `smooth_step(&2) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_MUL_LZERO] THEN REAL_ARITH_TAC);;

let SCH6_CAPSULE_CHART = prove
 (`!e0 h. SCH_COLLAR3_STATEMENT /\ &0 < e0 /\ e0 <= &1 / &16 /\
          diffeomorphism_on sch_capcone (IMAGE (sch_cap_collar e0) sch_capcone)
                            (sch_cap_collar e0) h
          ==> ?c c'. sch_ball c c' /\
                     IMAGE c (cball(vec 0,&1)) = IMAGE sch6_gamma (cball(vec 0,&1)) /\
                     !x. x IN annulus (&3 / &4) (&2) ==> c x = sch6_capsule e0 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SCH_COLLAR3_STATEMENT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`sch6_capsule e0`;
    `\y:real^3. if --(&1) <= y$3 then h y else sch_flip3(h(sch6_mir y))`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SCH6_CAPSULE_SPHERE_IMAGE; SCH6_GAMMA_BOUNDS] THEN
    MATCH_MP_TAC SCH6_CAPSULE_NECK THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sch_fills; SCH6_CAPSULE_SPHERE_IMAGE; SCH6_GAMMA_INSIDE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->real^3` (X_CHOOSE_THEN `c':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:real^3->real^3`; `c':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `F` MP_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ABBREV_TAC `x0 = vector[&0; &0; &10 / &9]:real^3` THEN
  SUBGOAL_THEN `norm(x0:real^3) = &10 / &9` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN MATCH_MP_TAC SCH6_NORM_E3 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN annulus (&3 / &4) (&2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm(x0:real^3) pow 2) % x0 = vector[&0; &0; &9 / &10]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "x0" THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->real^3) x0 = vector[&0; &0; --(&1 / &2) - e0 / &10]` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x0:real^3) IN annulus (&3 / &4) (&2)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `vector[&0; &0; &9 / &10] IN sch_capcone` ASSUME_TAC THENL
     [REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN
      SIMP_TAC[SCH6_NORM_E3; REAL_ARITH `&0 <= &9 / &10`; VECTOR_3] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_SIMP_TAC[SCH6_CAPSULE_CONE; SCH6_CAPCOLLAR_AXIS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->real^3) x0 IN IMAGE sch6_gamma (cball(vec 0,&1))` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `vector[&0; &0; &1 - e0 / &5]:real^3` THEN CONJ_TAC THENL
     [REWRITE_TAC[sch6_gamma; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; REAL_MUL_RZERO] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[IN_CBALL_0] THEN
      MP_TAC(SPEC `&1 - e0 / &5` SCH6_NORM_E3) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (c:real^3->real^3) (cball(vec 0,&1)) = IMAGE sch6_gamma (cball(vec 0,&1))` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `sch_ball (c:real^3->real^3) c'` THEN REWRITE_TAC[sch_ball; diffeomorphism_on] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `x1:real^3 = x0` MP_TAC THENL
   [SUBGOAL_THEN `(c':real^3->real^3)(c x1) = x1 /\ c'(c x0) = x0` MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Conjugation of a compactly supported diffeomorphism by a                  *)
(* chart is a global diffeomorphism; the model cap collar is a              *)
(* diffeomorphism on the cone when the slab data give g1 = Theta o collar.   *)
(* ------------------------------------------------------------------------- *)

let SCH6_CONJ_SMOOTH = prove
 (`!(Xi:real^N->real^N) Xi' U D K.
        diffeomorphism_on U (IMAGE Xi U) Xi Xi' /\
        smooth_map_on U D /\ (!u. u IN U ==> D u IN U) /\
        compact K /\ K SUBSET U /\ (!x. x IN U /\ ~(x IN K) ==> D x = x)
        ==> smooth_map_on (:real^N) (\p. if p IN IMAGE Xi U then Xi(D(Xi' p)) else p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(IMAGE (Xi:real^N->real^N) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `p:real^N` THEN ASM_CASES_TAC `(p:real^N) IN IMAGE (Xi:real^N->real^N) U` THENL
   [EXISTS_TAC `IMAGE (Xi:real^N->real^N) U` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(Xi:real^N->real^N) o (D:real^N->real^N) o (Xi':real^N->real^N)` THEN
    CONJ_TAC THENL [SIMP_TAC[o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    EXISTS_TAC `(:real^N) DIFF IMAGE (Xi:real^N->real^N) K` THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\p:real^N. p` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_ID; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((Xi':real^N->real^N) q IN K) /\ Xi' q IN U` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

let SCH6_CONJ_DIFFEO = prove
 (`!(Xi:real^N->real^N) Xi' U D D' K.
        diffeomorphism_on U (IMAGE Xi U) Xi Xi' /\
        diffeomorphism_on U U D D' /\ compact K /\ K SUBSET U /\
        (!x. x IN U /\ ~(x IN K) ==> D x = x)
        ==> diffeomorphism_on (:real^N) (:real^N)
              (\p. if p IN IMAGE Xi U then Xi(D(Xi' p)) else p)
              (\p. if p IN IMAGE Xi U then Xi(D'(Xi' p)) else p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN U /\ ~(x IN K) ==> (D':real^N->real^N) x = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(!u:real^N. u IN U ==> D u IN U) /\ (!u:real^N. u IN U ==> D' u IN U) /\
                (!p:real^N. p IN IMAGE (Xi:real^N->real^N) U ==> (Xi':real^N->real^N) p IN U)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on U (IMAGE (Xi:real^N->real^N) U) Xi Xi'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:real^N. (if (if x IN IMAGE (Xi:real^N->real^N) U then Xi((D:real^N->real^N)((Xi':real^N->real^N) x)) else x) IN IMAGE Xi U
                 then Xi(D'(Xi'(if x IN IMAGE Xi U then Xi(D(Xi' x)) else x)))
                 else (if x IN IMAGE Xi U then Xi(D(Xi' x)) else x)) = x) /\
    (!x:real^N. (if (if x IN IMAGE Xi U then Xi(D'(Xi' x)) else x) IN IMAGE Xi U
                 then Xi(D(Xi'(if x IN IMAGE Xi U then Xi(D'(Xi' x)) else x)))
                 else (if x IN IMAGE Xi U then Xi(D'(Xi' x)) else x)) = x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN IMAGE (Xi:real^N->real^N) U` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC SCH6_CONJ_SMOOTH THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCH6_CONJ_SMOOTH THEN EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* A diffeomorphism transported along pointwise equal maps. *)

let SCH6_DIFFEO_EQ = prove
 (`!s t (f:real^N->real^N) g f' g'.
        diffeomorphism_on s t f g /\ (!x. x IN s ==> f x = f' x) /\
        (!y. y IN t ==> g y = g' y)
        ==> diffeomorphism_on s t f' g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE (f:real^N->real^N) s = t` THEN ASM SET_TAC[];
    UNDISCH_TAC `IMAGE (g:real^N->real^N) t = s` THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `f:real^N->real^N` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g:real^N->real^N` THEN ASM_SIMP_TAC[]]);;

(* The model cap collar is a diffeomorphism on the cone. *)

let SCH6_CAPCOLLAR_DIFFEO = prove
 (`!g1 g1' (Theta:real^3->real^3) Theta' N e0.
        sch_neck g1 g1' /\ open N /\ sch_slab_nbhd SUBSET N /\
        diffeomorphism_on N (IMAGE Theta N) Theta Theta' /\
        &0 < e0 /\ e0 <= &1 / &16 /\
        (!x. x IN sch_capcone ==> g1 x = Theta(sch_cap_collar e0 x))
        ==> diffeomorphism_on sch_capcone (IMAGE (sch_cap_collar e0) sch_capcone)
                              (sch_cap_collar e0) (\y. g1'(Theta y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch_capcone SUBSET annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; sch_capcone; annulus; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN sch_capcone ==> sch_cap_collar e0 x IN (N:real^3->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `sch_cap_collar e0 x IN sch_slab_nbhd` MP_TAC THENL
     [MP_TAC(SPECL [`e0:real`; `x:real^3`] SCH_CAP_COLLAR_LAYER) THEN ASM_SIMP_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN IMAGE (Theta:real^3->real^3) N ==> Theta(Theta' y) = y /\
                    Theta' y IN N` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta Theta'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN (N:real^3->bool) ==> (Theta':real^3->real^3)(Theta x) = x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta Theta'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on sch_capcone (IMAGE (g1:real^3->real^3) sch_capcone) g1 g1'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH2_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                          `IMAGE (g1:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
    ASM_REWRITE_TAC[SCH6_OPEN_CAPCONE; GSYM sch_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g1:real^3->real^3) sch_capcone SUBSET IMAGE (Theta:real^3->real^3) N`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (IMAGE (g1:real^3->real^3) sch_capcone)
                  (IMAGE (Theta':real^3->real^3) (IMAGE g1 sch_capcone)) Theta' Theta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH2_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (Theta:real^3->real^3) N`; `N:real^3->bool`] THEN
    ASM_SIMP_TAC[DIFFEOMORPHISM_ON_SYM] THEN
    UNDISCH_TAC `diffeomorphism_on sch_capcone (IMAGE (g1:real^3->real^3) sch_capcone) g1 g1'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Theta':real^3->real^3) (IMAGE g1 sch_capcone) =
                IMAGE (sch_cap_collar e0) sch_capcone` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SCH6_DIFFEO_EQ THEN
  MAP_EVERY EXISTS_TAC [`(Theta':real^3->real^3) o (g1:real^3->real^3)`;
                        `(g1':real^3->real^3) o (Theta:real^3->real^3)`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `IMAGE (g1:real^3->real^3) sch_capcone` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[o_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Flows of compactly supported vertical fields w(y) e3 on R^3:              *)
(* the time-one map is a diffeomorphism, the identity off the support, keeps *)
(* the horizontal coordinates, is a translation along vertical segments on   *)
(* which w is constant, and is increasing on every vertical line.            *)
(* ------------------------------------------------------------------------- *)

let sch6_vfield = new_definition
 `sch6_vfield (w:real^3->real) = \y:real^3. (w y % basis 3):real^3`;;

let sch6_vflow = new_definition
 `sch6_vflow (w:real^3->real) (t:real) = ode_vf_flow (sch6_vfield w) (:real^3) (lift t)`;;

let SCH6_VFIELD_SMOOTH = prove
 (`!w. smooth_map_on (:real^3) (\y. lift(w y)) ==> smooth_map_on (:real^3) (sch6_vfield w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch6_vfield] THEN
  MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(w y)`; `\y:real^3. basis 3:real^3`]
    SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LIFT_DROP]);;

let SCH6_VFLOW_BASIC = prove
 (`!w K. smooth_map_on (:real^3) (\y. lift(w y)) /\ compact K /\
         (!y. ~(y IN K) ==> w y = &0)
         ==> (!t. diffeomorphism_on (:real^3) (:real^3) (sch6_vflow w t)
                                    (sch6_vflow w (--t))) /\
             (!t y. ~(y IN K) ==> sch6_vflow w t y = y) /\
             (!t y. y IN K ==> sch6_vflow w t y IN K) /\
             (!y. ode_vf_maxint (sch6_vfield w) (:real^3) y = (:real^1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sch6_vfield w`; `(:real^3)`; `K:real^3->bool`] ODE_VF_COMPLETE) THEN
  ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SCH6_VFIELD_SMOOTH; IN_UNIV] THEN ANTS_TAC THENL
   [REWRITE_TAC[sch6_vfield] THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[sch6_vflow; LIFT_NEG]);;

(* A component with zero derivative is constant. *)

let SCH6_COMPONENT_CONST = prove
 (`!(u:real^1->real^3) (v:real^1->real^3) k.
        1 <= k /\ k <= 3 /\
        (!t. (u has_vector_derivative v t) (at t)) /\ (!t. (v t)$k = &0)
        ==> !t. (u t)$k = (u (vec 0))$k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. lift((u:real^1->real^3) s$k)`; `(:real^1)`]
    HAS_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV; WITHIN_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `s:real^1` THEN
    SUBGOAL_THEN `((\s. lift((u:real^1->real^3) s$k)) has_vector_derivative
                   lift((v:real^1->real^3) s$k)) (at s)` MP_TAC THENL
     [UNDISCH_TAC `!t. ((u:real^1->real^3) has_vector_derivative v t) (at t)` THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o
        GEN_REWRITE_RULE I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] o SPEC `s:real^1`) THEN
      REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[LIFT_NUM; has_vector_derivative; VECTOR_MUL_RZERO]];
    DISCH_THEN(X_CHOOSE_TAC `c:real^1`) THEN
    REWRITE_TAC[GSYM LIFT_EQ] THEN ASM_REWRITE_TAC[]]);;

let SCH6_VFLOW_HORIZ = prove
 (`!w K t y. smooth_map_on (:real^3) (\y. lift(w y)) /\ compact K /\
             (!y. ~(y IN K) ==> w y = &0)
             ==> (sch6_vflow w t y)$1 = y$1 /\ (sch6_vflow w t y)$2 = y$2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w:real^3->real`; `K:real^3->bool`] SCH6_VFLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^3) (sch6_vfield w)` ASSUME_TAC THENL
   [MP_TAC(SPEC `w:real^3->real` SCH6_VFIELD_SMOOTH) THEN ASM_SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sch6_vfield w`; `(:real^3)`; `y:real^3`] ODE_VF_MAXIMAL) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k s. 1 <= k /\ k <= 2
                      ==> (ode_vf_flow (sch6_vfield w) (:real^3) s y)$k = (y:real^3)$k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\s:real^1. ode_vf_flow (sch6_vfield w) (:real^3) s y`;
                   `\t:real^1. sch6_vfield w (ode_vf_flow (sch6_vfield w) (:real^3) t y)`;
                   `k:num`] SCH6_COMPONENT_CONST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[sch6_vfield; VECTOR_MUL_COMPONENT] THEN GEN_TAC THEN
      SUBGOAL_THEN `~(k = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH_RULE `k <= 2 ==> k <= 3`;
                   REAL_MUL_RZERO];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[sch6_vflow] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* Along a vertical segment on which w = c the flow is a translation. *)

let SCH6_VFLOW_TRANSLATE = prove
 (`!w K y c. smooth_map_on (:real^3) (\y. lift(w y)) /\ compact K /\
             (!y. ~(y IN K) ==> w y = &0) /\
             (!s. &0 <= s /\ s <= &1 ==> w(y + s % (c % basis 3)) = c)
             ==> sch6_vflow w (&1) y = y + c % basis 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^3) (sch6_vfield w)` ASSUME_TAC THENL
   [MP_TAC(SPEC `w:real^3->real` SCH6_VFIELD_SMOOTH) THEN ASM_SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sch6_vfield w`; `(:real^3)`; `interval[vec 0:real^1,vec 1]`;
                 `\t:real^1. y + drop t % (c % basis 3):real^3`; `vec 0:real^1`]
    ODE_VF_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; IS_INTERVAL_INTERVAL; ENDS_IN_UNIT_INTERVAL] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[sch6_vfield] THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`(\t:real^1. y):real^1->real^3`; `vec 0:real^3`;
                   `\t:real^1. drop t % (c % basis 3):real^3`; `c % basis 3:real^3`;
                   `at (t:real^1)`] HAS_VECTOR_DERIVATIVE_ADD) THEN
    REWRITE_TAC[VECTOR_ADD_LID; HAS_VECTOR_DERIVATIVE_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MP_TAC(ISPECL [`\x:real^1. x`; `c % basis 3:real^3`] LINEAR_VMUL_DROP) THEN
    REWRITE_TAC[LINEAR_ID];
    DISCH_THEN(MP_TAC o SPEC `vec 1:real^1`) THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; VECTOR_SUB_RZERO; DROP_VEC; VECTOR_MUL_LID;
                VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[sch6_vflow; LIFT_NUM] THEN MESON_TAC[]]);;

(* On each vertical line the time-one map is increasing in the height. *)

let SCH6_VFLOW_MONO = prove
 (`!w K a b s t. smooth_map_on (:real^3) (\y. lift(w y)) /\ compact K /\
                 (!y. ~(y IN K) ==> w y = &0) /\ s < t
                 ==> (sch6_vflow w (&1) (vector[a; b; s]))$3 <
                     (sch6_vflow w (&1) (vector[a; b; t]))$3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w:real^3->real`; `K:real^3->bool`] SCH6_VFLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. (sch6_vflow w (&1) y)$1 = (y:real^3)$1 /\
                    (sch6_vflow w (&1) y)$2 = y$2` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SCH6_VFLOW_HORIZ THEN
    EXISTS_TAC `K:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch6_vflow w (&1) continuous_on (:real^3) /\
                (!y. sch6_vflow w (--(&1)) (sch6_vflow w (&1) y) = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!t. diffeomorphism_on (:real^3) (:real^3) (sch6_vflow w t)
                                      (sch6_vflow w (--t))` THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN
    SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  ABBREV_TAC `f = \r:real^1. lift((sch6_vflow w (&1) (vector[a; b; drop r]:real^3))$3)` THEN
  SUBGOAL_THEN `(f:real^1->real^1) continuous_on (:real^1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^1->real^1) =
                  (\z:real^3. lift(z$3)) o sch6_vflow w (&1) o
                  (\r:real^1. vector[a; b; &0] + drop r % basis 3)` SUBST1_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r1 r2. (f:real^1->real^1) r1 = f r2 ==> r1 = r2` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r1:real^1`; `r2:real^1`] THEN EXPAND_TAC "f" THEN
    REWRITE_TAC[LIFT_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sch6_vflow w (&1) (vector[a; b; drop r1]:real^3) =
                  sch6_vflow w (&1) (vector[a; b; drop r2])` MP_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[VECTOR_3];
      DISCH_THEN(MP_TAC o AP_TERM `sch6_vflow w (--(&1))`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; GSYM DROP_EQ] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `(:real^1)`] CONTINUOUS_INJECTIVE_IFF_MONOTONIC) THEN
  ASM_REWRITE_TAC[IS_INTERVAL_UNIV; IN_UNIV] THEN
  MP_TAC(MATCH_MP COMPACT_IMP_BOUNDED (ASSUME `compact(K:real^3->bool)`)) THEN
  REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z. z < --B ==> (f:real^1->real^1) (lift z) = lift z` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[LIFT_DROP; LIFT_EQ] THEN
    SUBGOAL_THEN `~((vector[a; b; z]:real^3) IN K)` (fun th -> ASM_SIMP_TAC[th; VECTOR_3]) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vector[a; b; z]:real^3` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `norm:real^3->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_NOT_LE] THEN
    MP_TAC(ISPECL [`vector[a; b; z]:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_3] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(MP_TAC o SPECL [`lift s`; `lift t`]) THEN EXPAND_TAC "f" THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    DISCH_THEN(MP_TAC o SPECL [`lift(--B - &1)`; `lift(--B - &1 / &2)`]) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < B ==> --B - &1 < --B /\ --B - &1 / &2 < --B`;
                 LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The reflection sch_flip3 (y3 -> -y3) carries a slab                        *)
(* configuration to a slab configuration with the two surgered spheres       *)
(* exchanged (SCH6_SLAB_FLIP), collars to collars, model collars to model    *)
(* collars and balls to balls.  This symmetry handles the nested case.       *)
(* ------------------------------------------------------------------------- *)

let SCH6_FLIP3_DIFFEO = prove
 (`diffeomorphism_on (:real^3) (:real^3) sch_flip3 sch_flip3`,
  REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV; SCH_FLIP3_INVOLUTION] THEN
  SIMP_TAC[SCH6_FLIP3_SMOOTH; OPEN_UNIV] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN MESON_TAC[SCH_FLIP3_INVOLUTION]);;

let SCH6_IN_FLIP3 = prove
 (`!y:real^3 s. y IN IMAGE sch_flip3 s <=> sch_flip3 y IN s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[SCH_FLIP3_INVOLUTION]);;

let SCH6_FLIP3_INSIDE = prove
 (`!s:real^3->bool. inside(IMAGE sch_flip3 s) = IMAGE sch_flip3 (inside s) /\
                    outside(IMAGE sch_flip3 s) = IMAGE sch_flip3 (outside s)`,
  GEN_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC INSIDE_LINEAR_IMAGE; MATCH_MP_TAC OUTSIDE_LINEAR_IMAGE] THEN
  REWRITE_TAC[SCH6_FLIP3_LINEAR] THEN MESON_TAC[SCH_FLIP3_INVOLUTION]);;

let SCH6_FLIP3_OPEN = prove
 (`!s:real^3->bool. open s ==> open(IMAGE sch_flip3 s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE sch_flip3 s = {y:real^3 | sch_flip3 y IN s}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; SCH6_IN_FLIP3; IN_ELIM_THM];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; SCH6_FLIP3_LINEAR]]);;

let SCH6_FLIP3_MODEL_SETS = prove
 (`IMAGE sch_flip3 sch_lat = sch_lat /\ IMAGE sch_flip3 sch_cap1 = sch_cap2 /\
   IMAGE sch_flip3 sch_cap2 = sch_cap1 /\ IMAGE sch_flip3 sch_slab_nbhd = sch_slab_nbhd /\
   IMAGE sch_flip3 (sphere(vec 0,&1)) = sphere(vec 0,&1) /\
   IMAGE sch_flip3 (annulus (&1 / &2) (&2)) = annulus (&1 / &2) (&2)`,
  REWRITE_TAC[EXTENSION; SCH6_IN_FLIP3] THEN REPEAT CONJ_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[sch_lat; IN_ELIM_THM; SCH6_FLIP3_COMPONENTS] THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `sch_flip3 x` SCH_FLIP3_CAP) THEN REWRITE_TAC[SCH_FLIP3_INVOLUTION] THEN
    MESON_TAC[];
    REWRITE_TAC[SCH_FLIP3_CAP];
    REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM; SCH6_FLIP3_COMPONENTS] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_SPHERE_0; SCH6_NORM_FLIP3];
    REWRITE_TAC[annulus; IN_ELIM_THM; SCH6_NORM_FLIP3]]);;

let SCH6_IMAGE_FLIP3_CONJ = prove
 (`!(f:real^3->real^3) s.
        IMAGE (sch_flip3 o f o sch_flip3) s = IMAGE sch_flip3 (IMAGE f (IMAGE sch_flip3 s))`,
  REWRITE_TAC[IMAGE_o]);;

(* A slab configuration reflected. *)

let SCH6_SLAB_FLIP = prove
 (`!S S1 S2 (Theta:real^3->real^3).
        sch_slab_config S S1 S2 Theta
        ==> sch_slab_config (IMAGE sch_flip3 S) (IMAGE sch_flip3 S2) (IMAGE sch_flip3 S1)
                            (sch_flip3 o Theta o sch_flip3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_slab_config] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `Theta':real^3->real^3`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o
    check (fun th -> is_eq(concl th) && is_var(lhs(concl th))))) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE sch_flip3 N`; `sch_flip3 o Theta' o sch_flip3`;
                        `IMAGE sch_flip3 E2`; `IMAGE sch_flip3 E1`] THEN
  SUBGOAL_THEN `!y:real^3. y IN IMAGE sch_flip3 N <=> sch_flip3 y IN N` ASSUME_TAC THENL
   [REWRITE_TAC[SCH6_IN_FLIP3]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. (sch_flip3 y)$1 pow 2 + (sch_flip3 y)$2 pow 2 =
                           y$1 pow 2 + y$2 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[SCH6_FLIP3_COMPONENTS]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SCH6_FLIP3_OPEN];
    REWRITE_TAC[SUBSET; SCH6_IN_FLIP3] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `sch_slab_nbhd SUBSET N` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[GSYM SCH6_IN_FLIP3] THEN ASM_REWRITE_TAC[SCH6_FLIP3_MODEL_SETS];
    REWRITE_TAC[SCH6_IMAGE_FLIP3_CONJ] THEN
    SUBGOAL_THEN `IMAGE sch_flip3 (IMAGE sch_flip3 N) = N:real^3->bool` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; SCH6_IN_FLIP3; SCH_FLIP3_INVOLUTION]; ALL_TAC] THEN
    SUBGOAL_THEN `diffeomorphism_on (IMAGE sch_flip3 N) N sch_flip3 sch_flip3`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`sch_flip3`; `sch_flip3`; `IMAGE sch_flip3 N`]
        SCH_DIFFEO_RESTRICT_UNIV) THEN
      ASM_SIMP_TAC[SCH6_FLIP3_DIFFEO; SCH6_FLIP3_OPEN] THEN
      SUBGOAL_THEN `IMAGE sch_flip3 (IMAGE sch_flip3 N) = N:real^3->bool`
        (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[EXTENSION; SCH6_IN_FLIP3; SCH_FLIP3_INVOLUTION];
      ALL_TAC] THEN
    SUBGOAL_THEN `diffeomorphism_on (IMAGE (Theta:real^3->real^3) N)
                    (IMAGE sch_flip3 (IMAGE Theta N)) sch_flip3 sch_flip3` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN REWRITE_TAC[SCH6_FLIP3_DIFFEO] THEN
      UNDISCH_TAC `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta Theta'` THEN
      SIMP_TAC[diffeomorphism_on];
      ALL_TAC] THEN
    SUBGOAL_THEN `diffeomorphism_on (IMAGE sch_flip3 N) (IMAGE (Theta:real^3->real^3) N)
                    (Theta o sch_flip3) (sch_flip3 o Theta')` ASSUME_TAC THENL
     [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `N:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE sch_flip3 N`; `IMAGE (Theta:real^3->real^3) N`;
                   `IMAGE sch_flip3 (IMAGE (Theta:real^3->real^3) N)`;
                   `(Theta:real^3->real^3) o sch_flip3`; `sch_flip3 o (Theta':real^3->real^3)`;
                   `sch_flip3`; `sch_flip3`] DIFFEOMORPHISM_ON_COMPOSE) THEN
    ASM_REWRITE_TAC[o_ASSOC];
    X_GEN_TAC `y:real^3` THEN ASM_REWRITE_TAC[o_THM; SCH6_IN_FLIP3; SCH_FLIP3_INVOLUTION] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IMAGE_UNION; SCH6_IMAGE_FLIP3_CONJ; SCH6_FLIP3_MODEL_SETS; UNION_ACI];
    UNDISCH_TAC `DISJOINT (E1:real^3->bool) E2` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; SCH6_IN_FLIP3] THEN MESON_TAC[];
    X_GEN_TAC `y:real^3` THEN ASM_REWRITE_TAC[o_THM; SCH6_IN_FLIP3; SCH_FLIP3_INVOLUTION] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[SCH6_FLIP3_COMPONENTS] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IMAGE_UNION; SCH6_IMAGE_FLIP3_CONJ; SCH6_FLIP3_MODEL_SETS];
    REWRITE_TAC[IMAGE_UNION; SCH6_IMAGE_FLIP3_CONJ; SCH6_FLIP3_MODEL_SETS];
    REWRITE_TAC[SCH6_FLIP3_INSIDE] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    X_GEN_TAC `y:real^3` THEN ASM_REWRITE_TAC[o_THM; SCH6_IN_FLIP3; SCH_FLIP3_INVOLUTION] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[]]);;

(* Collared spheres, model collars and balls reflected. *)

let SCH6_NECK_FLIP = prove
 (`!g g':real^3->real^3.
        sch_neck g g'
        ==> sch_neck (sch_flip3 o g o sch_flip3) (sch_flip3 o g' o sch_flip3) /\
            IMAGE (sch_flip3 o g o sch_flip3) (sphere(vec 0,&1)) =
            IMAGE sch_flip3 (IMAGE g (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_neck] THEN DISCH_TAC THEN
  REWRITE_TAC[SCH6_IMAGE_FLIP3_CONJ; SCH6_FLIP3_MODEL_SETS] THEN
  SUBGOAL_THEN `diffeomorphism_on (annulus (&1 / &2) (&2)) (annulus (&1 / &2) (&2))
                  sch_flip3 sch_flip3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sch_flip3`; `sch_flip3`; `annulus (&1 / &2) (&2):real^3->bool`]
      SCH_DIFFEO_RESTRICT_UNIV) THEN
    REWRITE_TAC[SCH6_FLIP3_DIFFEO; OPEN_ANNULUS; SCH6_FLIP3_MODEL_SETS];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2)))
                  (IMAGE sch_flip3 (IMAGE g (annulus (&1 / &2) (&2)))) sch_flip3 sch_flip3`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN REWRITE_TAC[SCH6_FLIP3_DIFFEO] THEN
    UNDISCH_TAC `diffeomorphism_on (annulus (&1 / &2) (&2))
                   (IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))) g g'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (annulus (&1 / &2) (&2))
                  (IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2)))
                  (g o sch_flip3) (sch_flip3 o g')` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`annulus (&1 / &2) (&2):real^3->bool`;
                 `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                 `IMAGE sch_flip3 (IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2)))`;
                 `(g:real^3->real^3) o sch_flip3`; `sch_flip3 o (g':real^3->real^3)`;
                 `sch_flip3`; `sch_flip3`] DIFFEOMORPHISM_ON_COMPOSE) THEN
  ASM_REWRITE_TAC[o_ASSOC]);;

let SCH6_BOUNDS_BALL_FLIP = prove
 (`!s:real^3->bool. sch_bounds_ball s ==> sch_bounds_ball (IMAGE sch_flip3 s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH_BOUNDS_BALL_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`sch_flip3`; `sch_flip3`] THEN
  REWRITE_TAC[SCH6_FLIP3_DIFFEO; GSYM IMAGE_o] THEN
  ASM_REWRITE_TAC[o_DEF; SCH_FLIP3_INVOLUTION; IMAGE_ID]);;

let SCH6_COLLAR_FLIP = prove
 (`!g1 g2 (Theta:real^3->real^3) e0.
        (!x. x IN sch_capcone
             ==> g1 x = Theta(sch_cap_collar e0 x) /\
                 g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x)))
        ==> (!x. x IN sch_capcone
                 ==> (sch_flip3 o g2 o sch_flip3) x =
                     (sch_flip3 o Theta o sch_flip3) (sch_cap_collar e0 x) /\
                     (sch_flip3 o g1 o sch_flip3) (sch_flip3 x) =
                     (sch_flip3 o Theta o sch_flip3) (sch_flip3(sch_cap_collar e0 x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM; SCH_FLIP3_INVOLUTION] THEN ASM_SIMP_TAC[]);;

