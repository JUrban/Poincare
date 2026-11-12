(* ========================================================================= *)
(* Unit pc_sch_capcol: for the surgery step of the smooth Schoenflies        *)
(* induction, the model collars sch_cap_collar of the caps (pc_sch_slab) on  *)
(* the extended cone c = x3/|x| > -9/20: radial compression, smoothness, a   *)
(* left inverse on the unit sphere, the layer function, and the consequences *)
(* for Theta o collar for a diffeomorphism Theta (tangential immersion,      *)
(* transversality of the radial direction).  Also a small toolkit for the    *)
(* smoothness of real-valued expressions.                                    *)
(* ========================================================================= *)

needs "src/pc_sch_vflow.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Smoothness of real-valued expressions (lifted), as rules for              *)
(* MATCH_MP_TAC, and a tactic applying them.                                 *)
(* ------------------------------------------------------------------------- *)

let SCH5C_SR_CONST = prove
 (`!s (c:real). smooth_map_on s (\x:real^M. lift c)`,
  REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let SCH5C_SR_COMP = prove
 (`!s k. open s ==> smooth_map_on s (\x:real^M. lift(x$k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`; `k:num`] SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]);;

let SCH5C_SR_ADD = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x + g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`;
                 `\x:real^M. lift((g:real^M->real) x)`] SMOOTH_MAP_ON_LIFT_ADD) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH5C_SR_SUB = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x - g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`;
                 `\x:real^M. lift((g:real^M->real) x)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH5C_SR_MUL = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x * g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`;
                 `\x:real^M. lift((g:real^M->real) x)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH5C_SR_NEG = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x)) ==> smooth_map_on s (\x. lift(--(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`]
    SMOOTH_MAP_ON_LIFT_NEG) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH5C_SR_DIV = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x)) /\
     (!x. x IN s ==> ~(g x = &0))
     ==> smooth_map_on s (\x. lift(f x / g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`;
                 `\x:real^M. lift((g:real^M->real) x)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let SCH5C_SR_DIVC = prove
 (`!s (f:real^M->real) c.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ ~(c = &0)
     ==> smooth_map_on s (\x. lift(f x / c))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH5C_SR_DIV THEN
  ASM_REWRITE_TAC[SCH5C_SR_CONST]);;

let SCH5C_SR_INV = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x)) /\ (!x. x IN s ==> ~(f x = &0))
     ==> smooth_map_on s (\x. lift(inv(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let SCH5C_SR_SQRT = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x)) /\ (!x. x IN s ==> &0 < f x)
     ==> smooth_map_on s (\x. lift(sqrt(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`]
    SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let SCH5C_SR_POW = prove
 (`!s (f:real^M->real) n.
     open s /\ smooth_map_on s (\x. lift(f x)) ==> smooth_map_on s (\x. lift(f x pow n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`; `n:num`]
    SMOOTH_MAP_ON_LIFT_POW) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH5C_SR_NORM = prove
 (`!s. open s /\ (!x:real^M. x IN s ==> ~(x = vec 0))
       ==> smooth_map_on s (\x:real^M. lift(norm x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `{x:real^M | ~(x = vec 0)}` THEN
  REWRITE_TAC[SMOOTH_MAP_ON_LIFT_NORM_NONZERO] THEN ASM SET_TAC[]);;

let SCH5C_SR_PROFILE = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. lift(sch_cap_profile(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `(:real^1)`; `\x:real^M. lift((f:real^M->real) x)`;
                 `sch_cap_profile`] SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SCH_CAP_PROFILE_SMOOTH; LIFT_DROP]);;

let SCH5C_SR_SSTEP = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. lift(smooth_step(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`]
    SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH5C_SV3 = prove
 (`!s (a:real^M->real) b c.
     open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x)) /\
     smooth_map_on s (\x. lift(c x))
     ==> smooth_map_on s (\x. vector[a x; b x; c x]:real^3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. vector[(a:real^M->real) x; b x; c x]:real^3`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
  X_GEN_TAC `k:num` THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[VECTOR_3]);;

let SCH5C_SV2 = prove
 (`!s (a:real^M->real) b.
     open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x))
     ==> smooth_map_on s (\x. vector[a x; b x]:real^2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. vector[(a:real^M->real) x; b x]:real^2`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= k /\ k <= 2 <=> k = 1 \/ k = 2`] THEN
  X_GEN_TAC `k:num` THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_2]);;

(* Repeatedly decompose a goal smooth_map_on s (\x. lift(expr)) or a vector *)
(* of such; leaves open s and the side conditions of DIV, INV, SQRT, NORM.  *)

let SCH5C_SMOOTH_TAC : tactic =
  let rules = [SCH5C_SV3; SCH5C_SV2; SCH5C_SR_ADD; SCH5C_SR_SUB;
               SCH5C_SR_MUL; SCH5C_SR_NEG; SCH5C_SR_DIVC; SCH5C_SR_DIV; SCH5C_SR_INV;
               SCH5C_SR_SQRT;
               SCH5C_SR_POW; SCH5C_SR_PROFILE; SCH5C_SR_SSTEP; SCH5C_SR_COMP;
               SCH5C_SR_NORM] in
  let step = FIRST (MATCH_ACCEPT_TAC SCH5C_SR_CONST ::
                    map (fun th g -> MATCH_MP_TAC th g) rules) in
  let numeral = CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC in
  REPEAT((step THEN REPEAT CONJ_TAC) ORELSE (CHANGED_TAC BETA_TAC) ORELSE numeral);;

(* ------------------------------------------------------------------------- *)
(* The extended cone c = x3/|x| > -9/20 of the shell, radial                 *)
(* compression of the model collar, its horizontal radius (the layer         *)
(* identity), and its position in the slab of height 3/2.                    *)
(* ------------------------------------------------------------------------- *)

let sch5c_cone = new_definition
 `sch5c_cone = {x:real^3 | &1 / &2 < norm x /\ norm x < &2 /\ --(&9 / &20) * norm x < x$3}`;;

let SCH5C_CONE_FACTS = prove
 (`open sch5c_cone /\ sch_capcone SUBSET sch5c_cone /\
   (!x. x IN sch5c_cone ==> ~(x = vec 0) /\ &0 < norm x /\
                             --(&9 / &20) < x$3 / norm x /\ x$3 / norm x <= &1)`,
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `sch5c_cone =
      {x | x IN {x:real^3 | ~(x = vec 0)} /\
           (\x:real^3. vector[norm x; x$3 + &9 / &20 * norm x]:real^2) x IN
           {z:real^2 | &1 / &2 < z$1 /\ z$1 < &2 /\ &0 < z$2}}` SUBST1_TAC THENL
     [REWRITE_TAC[sch5c_cone; EXTENSION; IN_ELIM_THM; VECTOR_2] THEN
      X_GEN_TAC `x:real^3` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 / &2 < norm(vec 0:real^3)` THEN
          REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      SUBGOAL_THEN `open {x:real^3 | ~(x = vec 0)}` ASSUME_TAC THENL
       [REWRITE_TAC[SET_RULE `{x | ~(x = a)} = (:real^N) DIFF {a}`] THEN
        SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING];
        ALL_TAC] THEN
      SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[SET_RULE `{x | ~(x = a)} = (:real^N) DIFF {a}`] THEN
      SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING];
      SUBGOAL_THEN `{z:real^2 | &1 / &2 < z$1 /\ z$1 < &2 /\ &0 < z$2} =
                    {z | z$1 > &1 / &2} INTER {z | z$1 < &2} INTER {z | z$2 > &0}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT]];
    REWRITE_TAC[sch_capcone; sch5c_cone; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[sch5c_cone; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN ASM_REAL_ARITH_TAC]);;

let SCH5C_COLLAR_RADIAL = prove
 (`!e0 k x:real^3.
     ~(x = vec 0) /\ &0 < &1 + k * (norm x - &1)
     ==> sch_cap_collar e0 (sch5_radial k x) = sch_cap_collar (e0 * k) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(sch5_radial k (x:real^3)) = &1 + k * (norm x - &1)` ASSUME_TAC THENL
   [REWRITE_TAC[sch5_radial; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. (sch5_radial k (x:real^3))$i / (&1 + k * (norm x - &1)) = x$i / norm x`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[sch5_radial; VECTOR_MUL_COMPONENT] THEN
    UNDISCH_TAC `&0 < norm(x:real^3)` THEN
    UNDISCH_TAC `&0 < &1 + k * (norm(x:real^3) - &1)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch_cap_collar] THEN
  REWRITE_TAC[REAL_ARITH `(&1 + a) - &1 = a`; REAL_MUL_ASSOC]);;

(* Positivity of the numerator of sch_capq off the axis. *)

let SCH5C_CAPQ_NUM_POS = prove
 (`!e c. --(&1 / &32) < e /\ e < &1 / &16 /\ --(&9 / &20) < c /\ c < &1
         ==> &0 < sch_cap_profile(&1 - c / &2 - e * smooth_step(&8 * c - &6)) + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&8 * c - &6` SMOOTH_STEP_BOUNDS) THEN STRIP_TAC THEN
  ABBREV_TAC `s = smooth_step(&8 * c - &6)` THEN
  ABBREV_TAC `t = &1 - c / &2 - e * s` THEN
  ASM_CASES_TAC `&5 / &8 <= t` THENL
   [MP_TAC(SPEC `t:real` SCH_CAP_PROFILE_LB) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `t:real` SCH_CAP_PROFILE_TIP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "t" THEN
  ASM_CASES_TAC `&0 <= e` THENL
   [SUBGOAL_THEN `&0 <= e * (&1 - s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &4 < c` ASSUME_TAC THENL
   [SUBGOAL_THEN `e * s <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `e * s <= &0 <=> &0 <= --e * s`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~(&5 / &8 <= t)` THEN EXPAND_TAC "t" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&7 / &8 <= c` THENL
   [SUBGOAL_THEN `s = &1` SUBST1_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `e <= e * (&1 - s)` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `e <= e * (&1 - s) <=> &0 <= --e * s`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SCH5C_E_BOUNDS = prove
 (`!e0 x:real^3.
     &0 < e0 /\ e0 <= &1 / &16 /\ &1 / &2 < norm x /\ norm x < &2
     ==> --(&1 / &32) < e0 * (norm x - &1) /\ e0 * (norm x - &1) < &1 / &16`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `e0 * --(&1 / &2) < e0 * (norm(x:real^3) - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `e0 * (norm(x:real^3) - &1) < e0 * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* The horizontal radius of the collar, and the layer identity on the       *)
(* extended cone: y1^2 + y2^2 - profile(-y3) = e0 (|x| - 1).                *)

let SCH5C_COLLAR_RADIUS = prove
 (`!e0 x:real^3.
     &0 < e0 /\ e0 <= &1 / &16 /\ x IN sch5c_cone
     ==> (sch_cap_collar e0 x)$1 pow 2 + (sch_cap_collar e0 x)$2 pow 2 =
         sch_cap_profile(&1 - (x$3 / norm x) / &2 -
                         e0 * (norm x - &1) * smooth_step(&8 * (x$3 / norm x) - &6)) +
         e0 * (norm x - &1) /\
         (sch_cap_collar e0 x)$3 = -- &1 + (x$3 / norm x) / &2 +
                                   e0 * (norm x - &1) * smooth_step(&8 * (x$3 / norm x) - &6) /\
         (x$3 / norm x < &1 ==> &0 < (sch_cap_collar e0 x)$1 pow 2 + (sch_cap_collar e0 x)$2 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real^3` (CONJUNCT2(CONJUNCT2 SCH5C_CONE_FACTS))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 < norm(x:real^3) /\ norm x < &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN sch5c_cone` THEN REWRITE_TAC[sch5c_cone; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real`; `x:real^3`] SCH5C_E_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[sch_cap_collar; VECTOR_3; sch_capq] THEN
  ABBREV_TAC `n = norm(x:real^3)` THEN ABBREV_TAC `c = (x:real^3)$3 / n` THEN
  SUBGOAL_THEN `(x:real^3)$1 pow 2 + x$2 pow 2 = n pow 2 * (&1 - c pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `n pow 2 = (x:real^3)$1 pow 2 + x$2 pow 2 + x$3 pow 2` MP_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[NORM_POW_2; DOT_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "c" THEN
    SUBGOAL_THEN `&0 < n` MP_TAC THENL [EXPAND_TAC "n" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  ASM_CASES_TAC `c = &1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(x:real^3)$1 = &0 /\ x$2 = &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3)$1 pow 2 + x$2 pow 2 = n pow 2 * (&1 - &1 pow 2)` THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_SOS_EQ_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_step(&8 * &1 - &6) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `&1 - &1 / &2 - e0 * (n - &1) * &1` SCH_CAP_PROFILE_TIP) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_POW_ZERO; ARITH_EQ;
                    REAL_ADD_LID; REAL_LT_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e0 * (n - &1)`; `c:real`] SCH5C_CAPQ_NUM_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - c pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `P = sch_cap_profile(&1 - c / &2 - (e0 * (n - &1)) * smooth_step(&8 * c - &6)) +
                  e0 * (n - &1)` THEN
  SUBGOAL_THEN `&0 <= P / (&1 - c pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap_profile(&1 - c / &2 - e0 * (n - &1) * smooth_step(&8 * c - &6)) +
                e0 * (n - &1) = P` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
  SUBGOAL_THEN `P / (&1 - c pow 2) * (x:real^3)$1 pow 2 / n pow 2 +
                P / (&1 - c pow 2) * x$2 pow 2 / n pow 2 =
                P / (&1 - c pow 2) * (x$1 pow 2 + x$2 pow 2) / n pow 2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `P / (&1 - c pow 2) * (n pow 2 * (&1 - c pow 2)) / n pow 2 = P`
  SUBST1_TAC THENL
   [UNDISCH_TAC `~(n = &0)` THEN UNDISCH_TAC `&0 < &1 - c pow 2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  EXPAND_TAC "P" THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC]);;

let SCH5C_COLLAR_LAYER = prove
 (`!e0 x:real^3.
     &0 < e0 /\ e0 <= &1 / &16 /\ x IN sch5c_cone
     ==> ((sch_cap_collar e0 x)$1 pow 2 + (sch_cap_collar e0 x)$2 pow 2) -
         sch_cap_profile(--((sch_cap_collar e0 x)$3)) = e0 * (norm x - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e0:real`; `x:real^3`] SCH5C_COLLAR_RADIUS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
  REWRITE_TAC[REAL_ARITH `--(-- &1 + a + b) = &1 - a - b`] THEN REAL_ARITH_TAC);;

let SCH5C_COLLAR_IN_SLAB = prove
 (`!e0 x:real^3.
     &0 < e0 /\ e0 <= &1 / &16 /\ x IN sch5c_cone
     ==> sch_cap_collar e0 x IN sch5v_slab(&3 / &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e0:real`; `x:real^3`] SCH5C_COLLAR_RADIUS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(SPEC `x:real^3` (CONJUNCT2(CONJUNCT2 SCH5C_CONE_FACTS))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 < norm(x:real^3) /\ norm x < &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN sch5c_cone` THEN REWRITE_TAC[sch5c_cone; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real`; `x:real^3`] SCH5C_E_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `&8 * ((x:real^3)$3 / norm x) - &6` SMOOTH_STEP_BOUNDS) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_ASSOC]) THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  ABBREV_TAC `s = smooth_step(&8 * ((x:real^3)$3 / norm x) - &6)` THEN
  ABBREV_TAC `e = e0 * (norm(x:real^3) - &1)` THEN
  ABBREV_TAC `c = (x:real^3)$3 / norm x` THEN
  SUBGOAL_THEN `--(&1 / &32) <= e * s /\ e * s <= &1 / &16` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_CASES_TAC `&0 <= e` THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --(&1 / &32) <= x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e:real` THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ARITH `e <= e * s <=> &0 <= --e * (&1 - s)`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
      ASM_CASES_TAC `&0 <= e` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e:real` THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_ARITH `e * s <= e <=> &0 <= e * (&1 - s)`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> x <= &1 / &16`) THEN
        REWRITE_TAC[REAL_ARITH `e * s <= &0 <=> &0 <= --e * s`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap_profile(&1 - c / &2 - e * s) <= &1` ASSUME_TAC THENL
   [ASM_CASES_TAC `&1 / &2 <= &1 - c / &2 - e * s` THENL
     [MP_TAC(SPEC `&1 - c / &2 - e * s` SCH_CAP_PROFILE_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MP_TAC(SPEC `&1 - c / &2 - e * s` SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of the model collar on the extended cone (the                  *)
(* defining formula away from the axis, the tip formula near the axis).     *)
(* ------------------------------------------------------------------------- *)

let SCH5C_OPEN_POS = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x)) ==> open {x | x IN s /\ &0 < f x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x | x IN s /\ &0 < (f:real^M->real) x} =
                {x | x IN s /\ (\x. lift(f x)) x IN {z:real^1 | z$1 > &0}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP; real_gt];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_HALFSPACE_COMPONENT_GT]);;

let SCH5C_CONE_SMOOTH_PARTS = prove
 (`(!x. x IN sch5c_cone ==> ~(x = vec 0)) /\
   smooth_map_on sch5c_cone (\x:real^3. lift(norm x)) /\
   smooth_map_on sch5c_cone (\x:real^3. lift(x$3 / norm x))`,
  SUBGOAL_THEN `!x:real^3. x IN sch5c_cone ==> ~(x = vec 0)` ASSUME_TAC THENL
   [MESON_TAC[SCH5C_CONE_FACTS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(CONJUNCT1 SCH5C_CONE_FACTS) THEN DISCH_TAC THEN
  CONJ_TAC THEN SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[NORM_EQ_0]);;

(* The tip formula of the collar near the north axis. *)

let SCH5C_COLLAR_TIP = prove
 (`!e0 x:real^3.
     &0 < e0 /\ e0 <= &1 / &16 /\ x IN sch5c_cone /\ &7 / &8 < x$3 / norm x
     ==> sch_cap_collar e0 x =
         vector[x$1 / sqrt(&2 * norm x * (norm x + x$3));
                x$2 / sqrt(&2 * norm x * (norm x + x$3));
                -- &1 + (x$3 / norm x) / &2 + e0 * (norm x - &1)]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real^3` (CONJUNCT2(CONJUNCT2 SCH5C_CONE_FACTS))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 < norm(x:real^3) /\ norm x < &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN sch5c_cone` THEN REWRITE_TAC[sch5c_cone; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real`; `x:real^3`] SCH5C_E_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_step(&8 * ((x:real^3)$3 / norm x) - &6) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[sch_cap_collar; sch_capq] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  MP_TAC(SPEC `&1 - ((x:real^3)$3 / norm x) / &2 - e0 * (norm x - &1)` SCH_CAP_PROFILE_TIP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `n = norm(x:real^3)` THEN ABBREV_TAC `c = (x:real^3)$3 / n` THEN
  SUBGOAL_THEN `&0 < n` ASSUME_TAC THENL [EXPAND_TAC "n" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3)$3 = c * n` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * n * (n + (x:real^3)$3) = (n pow 2) * (&2 * (&1 + c))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * (&1 + c)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(n pow 2 * &2 * (&1 + c)) = n * sqrt(&2 * (&1 + c))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[SQRT_MUL; REAL_POW_LE; REAL_LT_IMP_LE; ASSUME `&0 < n`;
             REAL_ARITH `&0 < &2 * (&1 + c) ==> &0 <= &2 * (&1 + c)`;
             ASSUME `&0 < &2 * (&1 + c)`] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `c = &1` THENL
   [SUBGOAL_THEN `(x:real^3)$1 = &0 /\ x$2 = &0` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `n pow 2 = (x:real^3)$1 pow 2 + x$2 pow 2 + x$3 pow 2` MP_TAC THENL
       [EXPAND_TAC "n" THEN REWRITE_TAC[NORM_POW_2; DOT_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_ARITH `n = a + b + n <=> a + b = &0`; REAL_SOS_EQ_0];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((&1 - c / &2 - e0 * (n - &1)) - &1 / &2 + e0 * (n - &1)) / (&1 - c pow 2) =
                inv(&2 * (&1 + c))` SUBST1_TAC THENL
   [UNDISCH_TAC `c < &1` THEN UNDISCH_TAC `&0 < &2 * (&1 + c)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_INV] THEN
  SUBGOAL_THEN `&0 < sqrt(&2 * (&1 + c))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  UNDISCH_TAC `&0 < sqrt(&2 * (&1 + c))` THEN UNDISCH_TAC `&0 < n` THEN
  CONV_TAC REAL_FIELD);;

let SCH5C_COLLAR_SMOOTH = prove
 (`!e0. &0 < e0 /\ e0 <= &1 / &16 ==> smooth_map_on sch5c_cone (sch_cap_collar e0)`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC SCH5C_CONE_SMOOTH_PARTS THEN
  MP_TAC SCH5C_CONE_FACTS THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^3)$3 / norm x < &15 / &16` THENL
   [EXISTS_TAC `{y:real^3 | y IN sch5c_cone /\ &0 < &15 / &16 - y$3 / norm y}` THEN
    SUBGOAL_THEN `open {y:real^3 | y IN sch5c_cone /\ &0 < &15 / &16 - y$3 / norm y}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SCH5C_OPEN_POS THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SCH5C_SR_SUB THEN ASM_REWRITE_TAC[SCH5C_SR_CONST];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!y:real^3. y IN {y | y IN sch5c_cone /\ &0 < &15 / &16 - y$3 / norm y}
                 ==> ~(norm y = &0) /\ ~(&1 - (y$3 / norm y) pow 2 = &0) /\
                     &0 < (sch_cap_profile(&1 - (y$3 / norm y) / &2 -
                            e0 * (norm y - &1) * smooth_step(&8 * (y$3 / norm y) - &6)) +
                           e0 * (norm y - &1)) / (&1 - (y$3 / norm y) pow 2)`
    (LABEL_TAC "SIDE") THENL
     [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(MP (SPEC `y:real^3` (ASSUME `!x:real^3. x IN sch5c_cone ==> ~(x = vec 0) /\
           &0 < norm x /\ --(&9 / &20) < x$3 / norm x /\ x$3 / norm x <= &1`))
           (ASSUME `(y:real^3) IN sch5c_cone`)) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&1 / &2 < norm(y:real^3) /\ norm y < &2` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN sch5c_cone` THEN REWRITE_TAC[sch5c_cone; IN_ELIM_THM] THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`e0:real`; `y:real^3`] SCH5C_E_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`e0 * (norm(y:real^3) - &1)`; `(y:real^3)$3 / norm y`]
        SCH5C_CAPQ_NUM_POS) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `&0 < &1 - ((y:real^3)$3 / norm y) pow 2` ASSUME_TAC THENL
       [MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sch_cap_collar e0 =
      (\y:real^3. vector[sqrt((sch_cap_profile(&1 - (y$3 / norm y) / &2 -
                            e0 * (norm y - &1) * smooth_step(&8 * (y$3 / norm y) - &6)) +
                           e0 * (norm y - &1)) / (&1 - (y$3 / norm y) pow 2)) * y$1 / norm y;
                         sqrt((sch_cap_profile(&1 - (y$3 / norm y) / &2 -
                            e0 * (norm y - &1) * smooth_step(&8 * (y$3 / norm y) - &6)) +
                           e0 * (norm y - &1)) / (&1 - (y$3 / norm y) pow 2)) * y$2 / norm y;
                         -- &1 + (y$3 / norm y) / &2 +
                         e0 * (norm y - &1) * smooth_step(&8 * (y$3 / norm y) - &6)]:real^3)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; sch_cap_collar; sch_capq; REAL_MUL_ASSOC]; ALL_TAC] THEN
    SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "SIDE" (fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
    ASM_MESON_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `{y:real^3 | y IN sch5c_cone /\ &0 < y$3 / norm y - &7 / &8}` THEN
  SUBGOAL_THEN `open {y:real^3 | y IN sch5c_cone /\ &0 < y$3 / norm y - &7 / &8}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5C_OPEN_POS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCH5C_SR_SUB THEN ASM_REWRITE_TAC[SCH5C_SR_CONST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN {y | y IN sch5c_cone /\ &0 < y$3 / norm y - &7 / &8}
               ==> ~(norm y = &0) /\ &0 < &2 * norm y * (norm y + y$3) /\
                   ~(sqrt(&2 * norm y * (norm y + y$3)) = &0)`
  (LABEL_TAC "SIDE") THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(MP (SPEC `y:real^3` (ASSUME `!x:real^3. x IN sch5c_cone ==> ~(x = vec 0) /\
         &0 < norm x /\ --(&9 / &20) < x$3 / norm x /\ x$3 / norm x <= &1`))
         (ASSUME `(y:real^3) IN sch5c_cone`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (y:real^3)$3` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < (y:real^3)$3 / norm y - &7 / &8` THEN
      ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_RDIV_EQ] THEN
      MP_TAC(ISPEC `y:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * norm(y:real^3) * (norm y + y$3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{y:real^3 | y IN sch5c_cone /\ &0 < y$3 / norm y - &7 / &8}`;
                 `\y:real^3. vector[y$1 / sqrt(&2 * norm y * (norm y + y$3));
                                    y$2 / sqrt(&2 * norm y * (norm y + y$3));
                                    -- &1 + (y$3 / norm y) / &2 + e0 * (norm y - &1)]:real^3`;
                 `sch_cap_collar e0`] SMOOTH_MAP_ON_EQ_OPEN) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH5C_COLLAR_TIP THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "SIDE" (fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
    ASM_MESON_TAC[NORM_EQ_0]]);;

(* ------------------------------------------------------------------------- *)
(* A smooth left inverse of the collar on the unit sphere                    *)
(* (c = 2(y3 + 1) recovers t3, the horizontal part is rescaled).            *)
(* ------------------------------------------------------------------------- *)

let sch5c_sinv = new_definition
 `sch5c_sinv (y:real^3) =
    if &7 / &8 < &2 * (y$3 + &1)
    then vector[sqrt(&2 * (&1 + &2 * (y$3 + &1))) * y$1;
                sqrt(&2 * (&1 + &2 * (y$3 + &1))) * y$2; &2 * (y$3 + &1)]:real^3
    else vector[sqrt((&1 - (&2 * (y$3 + &1)) pow 2) / sch_cap_profile(--(y$3))) * y$1;
                sqrt((&1 - (&2 * (y$3 + &1)) pow 2) / sch_cap_profile(--(y$3))) * y$2;
                &2 * (y$3 + &1)]`;;

let SCH5C_SQRT_EQ_1 = prove
 (`!x. x = &1 ==> sqrt x = &1`,
  SIMP_TAC[SQRT_1]);;

let SCH5C_COLLAR_SPHERE_FORM = prove
 (`!e0 t:real^3.
     norm t = &1 /\ --(&9 / &20) < t$3
     ==> sch_cap_collar e0 t =
         vector[sqrt(sch_cap_profile(&1 - t$3 / &2) / (&1 - t$3 pow 2)) * t$1;
                sqrt(sch_cap_profile(&1 - t$3 / &2) / (&1 - t$3 pow 2)) * t$2;
                -- &1 + t$3 / &2]`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[sch_cap_collar; sch_capq; REAL_SUB_REFL; REAL_MUL_RZERO; REAL_MUL_LZERO;
                  REAL_SUB_RZERO; REAL_ADD_RID; REAL_DIV_1]);;

let SCH5C_LINV_COLLAR = prove
 (`!e0 t:real^3.
     t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3
     ==> sch5c_sinv(sch_cap_collar e0 t) = t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SCH5C_COLLAR_SPHERE_FORM] THEN
  SUBGOAL_THEN `abs((t:real^3)$3) <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^3`; `3`] COMPONENT_LE_NORM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3)$1 pow 2 + t$2 pow 2 = &1 - t$3 pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(t:real^3) = &1` THEN REWRITE_TAC[NORM_EQ_1; DOT_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sch5c_sinv; VECTOR_3] THEN
  REWRITE_TAC[REAL_ARITH `&2 * ((-- &1 + c / &2) + &1) = c`;
              REAL_ARITH `--(-- &1 + c / &2) = &1 - c / &2`] THEN
  ABBREV_TAC `c = (t:real^3)$3` THEN
  ASM_CASES_TAC `c = &1` THENL
   [SUBGOAL_THEN `(t:real^3)$1 = &0 /\ t$2 = &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^3)$1 pow 2 + t$2 pow 2 = &1 - c pow 2` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_SOS_EQ_0];
      ALL_TAC] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - c pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sch_cap_profile(&1 - c / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_CAP_PROFILE_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if &7 / &8 < c then sqrt(&2 * (&1 + c)) else
                 sqrt((&1 - c pow 2) / sch_cap_profile(&1 - c / &2))) *
                sqrt(sch_cap_profile(&1 - c / &2) / (&1 - c pow 2)) = &1` MP_TAC THENL
   [COND_CASES_TAC THENL
     [MP_TAC(SPEC `&1 - c / &2` SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SCH5C_SQRT_EQ_1 THEN
      UNDISCH_TAC `c < &1` THEN UNDISCH_TAC `~(c = &1)` THEN
      UNDISCH_TAC `&0 < &1 - c pow 2` THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SCH5C_SQRT_EQ_1 THEN
      UNDISCH_TAC `&0 < sch_cap_profile(&1 - c / &2)` THEN
      UNDISCH_TAC `&0 < &1 - c pow 2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of the collar at points of the unit sphere                 *)
(* in the extended cone is injective (tangential part: the left inverse;    *)
(* radial part: the layer function grows at rate e0).                        *)
(* ------------------------------------------------------------------------- *)

let SCH5C_SINV_SMOOTH = prove
 (`smooth_map_on {y:real^3 | --(&9 / &20) < &2 * (y$3 + &1) /\ &2 * (y$3 + &1) < &2}
                 sch5c_sinv`,
  ABBREV_TAC `V = {y:real^3 | --(&9 / &20) < &2 * (y$3 + &1) /\ &2 * (y$3 + &1) < &2}` THEN
  SUBGOAL_THEN `open(V:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    REWRITE_TAC[SET_RULE `{y:real^3 | P y /\ Q y} = {y | P y} INTER {y | Q y}`] THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^3 | --(&9 / &20) < &2 * (y$3 + &1)} = {y | y$3 > --(&49 / &40)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT]];
      SUBGOAL_THEN `{y:real^3 | &2 * (y$3 + &1) < &2} = {y | y$3 < &0}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT]]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `&2 * ((y:real^3)$3 + &1) < &15 / &16` THENL
   [EXISTS_TAC `{z:real^3 | z IN V /\ &0 < &15 / &16 - &2 * (z$3 + &1)}` THEN
    SUBGOAL_THEN `open {z:real^3 | z IN V /\ &0 < &15 / &16 - &2 * (z$3 + &1)}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SCH5C_OPEN_POS THEN ASM_REWRITE_TAC[] THEN SCH5C_SMOOTH_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!z:real^3. z IN {z | z IN V /\ &0 < &15 / &16 - &2 * (z$3 + &1)}
                 ==> &0 < sch_cap_profile(--(z$3)) /\
                     &0 < (&1 - (&2 * (z$3 + &1)) pow 2) / sch_cap_profile(--(z$3)) /\
                     ~(sch_cap_profile(--(z$3)) = &0)` (LABEL_TAC "SIDE") THENL
     [X_GEN_TAC `z:real^3` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&0 < sch_cap_profile(--((z:real^3)$3))` ASSUME_TAC THENL
       [MATCH_MP_TAC SCH_CAP_PROFILE_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{z:real^3 | z IN V /\ &0 < &15 / &16 - &2 * (z$3 + &1)}`;
      `\y:real^3. vector[sqrt((&1 - (&2 * (y$3 + &1)) pow 2) / sch_cap_profile(--(y$3))) * y$1;
                         sqrt((&1 - (&2 * (y$3 + &1)) pow 2) / sch_cap_profile(--(y$3))) * y$2;
                         &2 * (y$3 + &1)]:real^3`; `sch5c_sinv`] SMOOTH_MAP_ON_EQ_OPEN) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[sch5c_sinv] THEN
      ASM_CASES_TAC `&7 / &8 < &2 * ((z:real^3)$3 + &1)` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `--((z:real^3)$3)` SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `(&1 - (&2 * ((z:real^3)$3 + &1)) pow 2) / (--(z$3) - &1 / &2) =
                    &2 * (&1 + &2 * (z$3 + &1))` (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `~(--((z:real^3)$3) - &1 / &2 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "SIDE" (fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `{z:real^3 | z IN V /\ &0 < &2 * (z$3 + &1) - &7 / &8}` THEN
  SUBGOAL_THEN `open {z:real^3 | z IN V /\ &0 < &2 * (z$3 + &1) - &7 / &8}` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5C_OPEN_POS THEN ASM_REWRITE_TAC[] THEN SCH5C_SMOOTH_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`{z:real^3 | z IN V /\ &0 < &2 * (z$3 + &1) - &7 / &8}`;
    `\y:real^3. vector[sqrt(&2 * (&1 + &2 * (y$3 + &1))) * y$1;
                       sqrt(&2 * (&1 + &2 * (y$3 + &1))) * y$2; &2 * (y$3 + &1)]:real^3`;
    `sch5c_sinv`] SMOOTH_MAP_ON_EQ_OPEN) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[sch5c_sinv] THEN
    SUBGOAL_THEN `&7 / &8 < &2 * ((z:real^3)$3 + &1)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    SCH5C_SMOOTH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REAL_ARITH_TAC]);;

let SCH5C_SPHERE_IN_CONE = prove
 (`!t:real^3. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3
              ==> t IN sch5c_cone /\ norm t = &1 /\
                  (!x. x IN sphere(vec 0,&1) /\ dist(x,t) < t$3 + &9 / &20
                       ==> --(&9 / &20) < x$3)`,
  GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[sch5c_cone; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x - t:real^3`; `3`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; GSYM dist] THEN ASM_REAL_ARITH_TAC);;

let SCH5C_LAYER_FN_SMOOTH = prove
 (`smooth_map_on (:real^3)
     (\y:real^3. lift((y$1 pow 2 + y$2 pow 2) - sch_cap_profile(--(y$3))))`,
  SCH5C_SMOOTH_TAC THEN REWRITE_TAC[OPEN_UNIV]);;

let SCH5C_COLLAR_DERIV_INJ = prove
 (`!e0 t:real^3.
     &0 < e0 /\ e0 <= &1 / &16 /\ t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3
     ==> sch_cap_collar e0 differentiable (at t) /\
         !w. frechet_derivative (sch_cap_collar e0) (at t) w = vec 0 ==> w = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEAR"))) THEN
  SUBGOAL_THEN `sch_cap_collar e0 differentiable (at t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `sch5c_cone` THEN
    ASM_SIMP_TAC[SCH5C_COLLAR_SMOOTH; SCH5C_CONE_FACTS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = frechet_derivative (sch_cap_collar e0) (at t)` THEN
  SUBGOAL_THEN `linear(D:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sch_cap_collar e0 (t:real^3))$3 = -- &1 + t$3 / &2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH5C_COLLAR_SPHERE_FORM; VECTOR_3]; ALL_TAC] THEN
  SUBGOAL_THEN `sch5c_sinv differentiable (at (sch_cap_collar e0 t))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{y:real^3 | --(&9 / &20) < &2 * (y$3 + &1) /\ &2 * (y$3 + &1) < &2}` THEN
    REWRITE_TAC[SCH5C_SINV_SMOOTH; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `{y:real^3 | P y /\ Q y} = {y | P y} INTER {y | Q y}`] THEN
      MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
       [SUBGOAL_THEN `{y:real^3 | --(&9 / &20) < &2 * (y$3 + &1)} = {y | y$3 > --(&49 / &40)}`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
          REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT]];
        SUBGOAL_THEN `{y:real^3 | &2 * (y$3 + &1) < &2} = {y | y$3 < &0}` SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
          REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT]]];
      MP_TAC(ISPECL [`t:real^3`; `3`] COMPONENT_LE_NORM) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. orthogonal t v
                    ==> frechet_derivative sch5c_sinv (at (sch_cap_collar e0 t)) (D v) = v`
  (LABEL_TAC "TAN") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`sch5c_sinv o sch_cap_collar e0`; `\x:real^3. x`; `t:real^3`;
                   `(t:real^3)$3 + &9 / &20`] SCH5_SPHERE_TANGENT_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[DIFFERENTIABLE_ID] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
        MATCH_MP_TAC SCH5C_LINV_COLLAR THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "NEAR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `frechet_derivative (sch5c_sinv o sch_cap_collar e0) (at t) =
                  frechet_derivative sch5c_sinv (at (sch_cap_collar e0 t)) o D`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN EXPAND_TAC "D" THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative (\x:real^3. x) (at t) = (\h. h)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID];
      REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `Lf = \y:real^3. lift((y$1 pow 2 + y$2 pow 2) - sch_cap_profile(--(y$3)))` THEN
  SUBGOAL_THEN `(Lf:real^3->real^1) differentiable (at (sch_cap_collar e0 t))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^3)` THEN
    EXPAND_TAC "Lf" THEN REWRITE_TAC[SCH5C_LAYER_FN_SMOOTH; OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `DL = frechet_derivative (Lf:real^3->real^1) (at (sch_cap_collar e0 t))` THEN
  SUBGOAL_THEN `linear(DL:real^3->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "DL" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(((Lf:real^3->real^1) o sch_cap_collar e0) has_derivative ((DL:real^3->real^1) o (D:real^3->real^3))) (at t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN EXPAND_TAC "D" THEN EXPAND_TAC "DL" THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN sch5c_cone
                    ==> (Lf:real^3->real^1)(sch_cap_collar e0 x) = lift(e0 * (norm x - &1))`
  (LABEL_TAC "LAY") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Lf" THEN REWRITE_TAC[LIFT_EQ] THEN
    MATCH_MP_TAC SCH5C_COLLAR_LAYER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. orthogonal t v ==> (DL:real^3->real^1)((D:real^3->real^3) v) = vec 0`
  (LABEL_TAC "TZ") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(Lf:real^3->real^1) o sch_cap_collar e0`; `t:real^3`;
                   `(t:real^3)$3 + &9 / &20`; `vec 0:real^1`] SCH5_SPHERE_TANGENT_ZERO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
        X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(x:real^3) IN sch5c_cone /\ norm x = &1` STRIP_ASSUME_TAC THENL
         [MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> p /\ q`) THEN CONJ_TAC THENL
           [DISCH_TAC THEN MP_TAC(SPEC `x:real^3` SCH5C_SPHERE_IN_CONE) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[] THEN USE_THEN "NEAR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
              SIMP_TAC[]];
            UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0]];
          ALL_TAC] THEN
        REWRITE_TAC[o_THM] THEN
        USE_THEN "LAY" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN sch5c_cone`)]) THEN
        ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; LIFT_NUM]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(DL:real^3->real^1)((D:real^3->real^3) t) = lift e0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s:real^1. drop s % (t:real^3)`; `t:real^3`;
                   `(Lf:real^3->real^1) o sch_cap_collar e0`; `(DL:real^3->real^1) o (D:real^3->real^3)`;
                   `lift(&1)`] SCH5_CHAIN_VECTOR) THEN
    REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`((Lf:real^3->real^1) o sch_cap_collar e0) o (\s:real^1. drop s % (t:real^3))`;
                   `((DL:real^3->real^1) o (D:real^3->real^3)) t`;
                   `\s:real^1. e0 % (s - lift(&1))`; `lift(&1)`; `&1 / &2`]
      HAS_VECTOR_DERIVATIVE_TRANSFORM_AT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
      SUBGOAL_THEN `drop s % (t:real^3) IN sch5c_cone /\ norm(drop s % t) = drop s`
      STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
        SUBGOAL_THEN `abs(drop s) = drop s` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[sch5c_cone; IN_ELIM_THM; NORM_MUL; VECTOR_MUL_COMPONENT] THEN
        ASM_REWRITE_TAC[REAL_MUL_RID] THEN
        SUBGOAL_THEN `abs(drop s) = drop s` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `--(&9 / &20) * d < d * t3 <=> &0 < d * (t3 + &9 / &20)`] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[o_THM] THEN
      USE_THEN "LAY" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `drop s % (t:real^3) IN sch5c_cone`)]) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_SUB; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\s:real^1. e0 % (s - lift(&1))`; `lift(&1)`;
                   `((DL:real^3->real^1) o (D:real^3->real^3)) t`; `lift e0`]
      VECTOR_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `lift e0 = e0 % (vec 1 - vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_RZERO; GSYM LIFT_NUM; GSYM LIFT_CMUL; REAL_MUL_RID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID; HAS_VECTOR_DERIVATIVE_CONST];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  ABBREV_TAC `a = (t:real^3) dot w` THEN
  SUBGOAL_THEN `(t:real^3) dot t = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_EQ_1]; ALL_TAC] THEN
  SUBGOAL_THEN `orthogonal (t:real^3) (w - a % t)` ASSUME_TAC THENL
   [REWRITE_TAC[orthogonal; DOT_RSUB; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^3->real^3) w = a % D t + D(w - a % t)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL (ASSUME `linear(D:real^3->real^3)`));
                GSYM(MATCH_MP LINEAR_ADD (ASSUME `linear(D:real^3->real^3)`))] THEN
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(DL:real^3->real^1)((D:real^3->real^3) w) = vec 0` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear(DL:real^3->real^1)`)];
      ALL_TAC] THEN
    UNDISCH_TAC `(D:real^3->real^3) w = a % D t + D(w - a % t)` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear(DL:real^3->real^1)`);
                MATCH_MP LINEAR_CMUL (ASSUME `linear(DL:real^3->real^1)`)] THEN
    USE_THEN "TZ" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `orthogonal (t:real^3) (w - a % t)`)]) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_RID; GSYM LIFT_CMUL; GSYM LIFT_NUM; LIFT_EQ; REAL_ENTIRE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "TAN" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `orthogonal (t:real^3) (w - a % t)`))) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN `linear(frechet_derivative sch5c_sinv (at (sch_cap_collar e0 t)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME
    `linear(frechet_derivative sch5c_sinv (at (sch_cap_collar e0 t)))`)] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

(* ------------------------------------------------------------------------- *)
(* Theta o collar for a diffeomorphism Theta defined on the                  *)
(* slab of height 3/2: smooth on the extended cone, invertible derivative   *)
(* at points of the unit sphere there, injective on that part of the sphere.*)
(* ------------------------------------------------------------------------- *)

let SCH5C_THETA_COLLAR = prove
 (`!e0 (Theta:real^3->real^3) Theta' N.
     &0 < e0 /\ e0 <= &1 / &16 /\ diffeomorphism_on N (IMAGE Theta N) Theta Theta' /\
     sch5v_slab(&3 / &2) SUBSET N
     ==> smooth_map_on sch5c_cone (Theta o sch_cap_collar e0) /\
         (!t. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3
              ==> (Theta o sch_cap_collar e0) differentiable (at t) /\
                  (!w. frechet_derivative (Theta o sch_cap_collar e0) (at t) w = vec 0
                       ==> w = vec 0) /\
                  ~(det(matrix(frechet_derivative (Theta o sch_cap_collar e0) (at t))) = &0)) /\
         (!t t'. t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\
                 t' IN sphere(vec 0,&1) /\ --(&9 / &20) < t'$3 /\
                 Theta(sch_cap_collar e0 t) = Theta(sch_cap_collar e0 t')
                 ==> t = t')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `!x. x IN sch5c_cone ==> sch_cap_collar e0 x IN N` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
      check (fun th -> concl th = `sch5v_slab(&3 / &2) SUBSET N`)) THEN
    MATCH_MP_TAC SCH5C_COLLAR_IN_SLAB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `N:real^3->bool` THEN
    ASM_SIMP_TAC[SCH5C_COLLAR_SMOOTH; SCH5C_CONE_FACTS] THEN ASM SET_TAC[];
    X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`e0:real`; `t:real^3`] SCH5C_COLLAR_DERIV_INJ) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Theta:real^3->real^3) differentiable (at (sch_cap_collar e0 t))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `N:real^3->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `((Theta:real^3->real^3) o sch_cap_collar e0) differentiable (at t)` ASSUME_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative ((Theta:real^3->real^3) o sch_cap_collar e0) (at t) =
                  frechet_derivative Theta (at (sch_cap_collar e0 t)) o
                  frechet_derivative (sch_cap_collar e0) (at t)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    SUBGOAL_THEN `!w. frechet_derivative ((Theta:real^3->real^3) o sch_cap_collar e0) (at t) w
                      = vec 0 ==> w = vec 0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      MATCH_MP_TAC SCH2_DIFFEO_DERIV_INJ THEN
      MAP_EVERY EXISTS_TAC [`Theta:real^3->real^3`; `Theta':real^3->real^3`;
                            `N:real^3->bool`; `IMAGE (Theta:real^3->real^3) N`;
                            `sch_cap_collar e0 t`] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SCH5_INJ_DET THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    MAP_EVERY X_GEN_TAC [`t:real^3`; `t':real^3`] THEN STRIP_TAC THEN
    MP_TAC(SPEC `t:real^3` SCH5C_SPHERE_IN_CONE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `t':real^3` SCH5C_SPHERE_IN_CONE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sch_cap_collar e0 t = sch_cap_collar e0 t'` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `Theta':real^3->real^3` o
        check (fun th -> concl th = `(Theta:real^3->real^3)(sch_cap_collar e0 t) =
                                     Theta(sch_cap_collar e0 t')`)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `sch5c_sinv`) THEN ASM_SIMP_TAC[SCH5C_LINV_COLLAR]]);;

(* ------------------------------------------------------------------------- *)
(* The collar on the unit sphere: the cylinder part (r = 1,                  *)
(* height -1 + t3/2 for t3 <= 1/4) and the inverse on the surface of        *)
(* revolution r^2 = profile(-y3) (which contains sch_cap1).                 *)
(* ------------------------------------------------------------------------- *)

let SCH5C_COLLAR_CYL = prove
 (`!e0 t:real^3.
     t IN sphere(vec 0,&1) /\ --(&9 / &20) < t$3 /\ t$3 <= &1 / &4
     ==> sch_cap_collar e0 t =
         vector[t$1 / sqrt(&1 - t$3 pow 2); t$2 / sqrt(&1 - t$3 pow 2); -- &1 + t$3 / &2]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SCH5C_COLLAR_SPHERE_FORM] THEN
  MP_TAC(SPEC `&1 - (t:real^3)$3 / &2` SCH_CAP_PROFILE_TOP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - (t:real^3)$3 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; SQRT_INV] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC);;

let SCH5C_COLLAR_SINV = prove
 (`!e0 y:real^3.
     --(&9 / &20) < &2 * (y$3 + &1) /\ &2 * (y$3 + &1) <= &1 /\
     y$1 pow 2 + y$2 pow 2 = sch_cap_profile(--(y$3))
     ==> sch5c_sinv y IN sphere(vec 0,&1) /\ (sch5c_sinv y)$3 = &2 * (y$3 + &1) /\
         sch_cap_collar e0 (sch5c_sinv y) = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = &2 * ((y:real^3)$3 + &1)` THEN
  SUBGOAL_THEN `(y:real^3)$3 = -- &1 + c / &2` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--((y:real^3)$3) = &1 - c / &2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?k. &0 <= k /\ sch5c_sinv y = vector[k * (y:real^3)$1; k * y$2; c] /\
                    k pow 2 * sch_cap_profile(&1 - c / &2) = &1 - c pow 2 /\
                    (c < &1 ==> k * sqrt(sch_cap_profile(&1 - c / &2) / (&1 - c pow 2)) = &1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch5c_sinv] THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [EXISTS_TAC `sqrt(&2 * (&1 + c))` THEN
      SUBGOAL_THEN `&0 < &2 * (&1 + c)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `&1 - c / &2` SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE; SQRT_POW_2] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SCH5C_SQRT_EQ_1 THEN
      SUBGOAL_THEN `&0 < &1 - c pow 2` MP_TAC THENL
       [MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD;
      EXISTS_TAC `sqrt((&1 - c pow 2) / sch_cap_profile(&1 - c / &2))` THEN
      SUBGOAL_THEN `&0 < sch_cap_profile(&1 - c / &2)` ASSUME_TAC THENL
       [MATCH_MP_TAC SCH_CAP_PROFILE_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &1 - c pow 2` ASSUME_TAC THENL
       [MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (&1 - c pow 2) / sch_cap_profile(&1 - c / &2)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < sch_cap_profile(&1 - c / &2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      DISCH_TAC THEN REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SCH5C_SQRT_EQ_1 THEN
      UNDISCH_TAC `&0 < sch_cap_profile(&1 - c / &2)` THEN
      UNDISCH_TAC `&0 < &1 - c pow 2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(&1 - c / &2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(--(y$3))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5c_sinv y IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_3; VECTOR_3] THEN
    UNDISCH_TAC `k pow 2 * sch_cap_profile(&1 - c / &2) = &1 - c pow 2` THEN
    UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(&1 - c / &2)` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_3] THEN
  SUBGOAL_THEN `norm(vector[k * (y:real^3)$1; k * y$2; c]:real^3) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `sch5c_sinv y IN sphere(vec 0,&1)` THEN ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real`; `vector[k * (y:real^3)$1; k * y$2; c]:real^3`]
    SCH5C_COLLAR_SPHERE_FORM) THEN
  ASM_REWRITE_TAC[VECTOR_3] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `c = &1` THENL
   [SUBGOAL_THEN `(y:real^3)$1 = &0 /\ y$2 = &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(&1 - c / &2)` THEN
      REWRITE_TAC[ASSUME `c = &1`] THEN
      MP_TAC(SPEC `&1 - &1 / &2` SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_SOS_EQ_0];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; REAL_MUL_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c < &1` (fun th -> FIRST_X_ASSUM(MP_TAC o C MP th)) THENL
   [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `sqrt(sch_cap_profile(&1 - c / &2) / (&1 - c pow 2)) * k = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID] THEN REAL_ARITH_TAC);;

