(* ========================================================================= *)
(* pc_sch_slab: the statements that connect the surgery construction         *)
(* (pc_sch_surg) and the gluing (pc_sch_glue). In model coordinates y        *)
(* (Theta^-1 near the disc of the surgery) the sphere S is the lateral       *)
(* cylinder y1^2 + y2^2 = 1; the two surgered spheres replace the lateral    *)
(* annulus |y3| <= 1 by two model caps (surfaces of revolution with exact    *)
(* paraboloid tips at heights -1/2 and 1/2). Contents: the model sets,       *)
(* sch_slab_config, a fixed neighbourhood sch_slab_nbhd of the model         *)
(* cylinder inside the chart domain, the model collars sch_cap_collar of the *)
(* caps (which the surgered collars g1, g2 follow near the caps), the        *)
(* statement constants SCH_SURG_CONSTRUCT_STATEMENT (the surgery             *)
(* construction) and SCH_SLAB_GLUE_STATEMENT (the gluing), the glue          *)
(* SCH_SURGERY_FROM_SLAB, the statement constants SCH_LEVEL_NECK_STATEMENT   *)
(* and SCH_LEVEL_INNERMOST_STATEMENT about regular levels (proved in         *)
(* pc_sch_level2), profile facts, a model sanity theorem (the sphere of      *)
(* radius 2 is in slab configuration), round-sphere instances of the two     *)
(* level statements, and the facts on the model collars.                     *)
(* ========================================================================= *)

needs "src/pc_sch_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Model sets, the slab configuration, statement constants and               *)
(* the glue.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Radius profile of the caps: = t - 1/2 near the tip (t <= 5/8), = 1 near   *)
(* the cylinder (t >= 7/8).                                                  *)

let sch_cap_profile = new_definition
 `sch_cap_profile (t:real) =
    (&1 - smooth_step(&4 * t - &5 / &2)) * (t - &1 / &2) + smooth_step(&4 * t - &5 / &2)`;;

let sch_cyl = new_definition
 `sch_cyl = {y:real^3 | y$1 pow 2 + y$2 pow 2 <= &1 /\ abs(y$3) <= &1}`;;

let sch_lat = new_definition
 `sch_lat = {y:real^3 | y$1 pow 2 + y$2 pow 2 = &1 /\ abs(y$3) <= &1}`;;

let sch_cap1 = new_definition
 `sch_cap1 = {y:real^3 | -- &1 <= y$3 /\ y$3 <= --(&1 / &2) /\
                         y$1 pow 2 + y$2 pow 2 = sch_cap_profile(--(y$3))}`;;

let sch_cap2 = new_definition
 `sch_cap2 = {y:real^3 | &1 / &2 <= y$3 /\ y$3 <= &1 /\
                         y$1 pow 2 + y$2 pow 2 = sch_cap_profile(y$3)}`;;

(* A fixed open neighbourhood of the closed model cylinder on which the      *)
(* chart Theta is required to be defined (room for the model collars).       *)

let sch_slab_nbhd = new_definition
 `sch_slab_nbhd = {y:real^3 | y$1 pow 2 + y$2 pow 2 < &4 /\ abs(y$3) < &5 / &4}`;;

(* S is a tube in the chart Theta; S1 (S2) is the part of S below (above)    *)
(* the slab, closed by the lower (upper) model cap.  The inside of S is the  *)
(* solid tube (disjoint case) or its complement (nested case).              *)

let sch_slab_config = new_definition
 `sch_slab_config (S:real^3->bool) S1 S2 (Theta:real^3->real^3) <=>
    ?N Theta' E1 E2.
       open N /\ sch_slab_nbhd SUBSET N /\
       diffeomorphism_on N (IMAGE Theta N) Theta Theta' /\
       (!y. y IN N ==> (Theta y IN S <=> y$1 pow 2 + y$2 pow 2 = &1)) /\
       S = E1 UNION IMAGE Theta sch_lat UNION E2 /\ DISJOINT E1 E2 /\
       (!y. y IN N
            ==> (Theta y IN E1 <=> y$1 pow 2 + y$2 pow 2 = &1 /\ y$3 < -- &1) /\
                (Theta y IN E2 <=> y$1 pow 2 + y$2 pow 2 = &1 /\ &1 < y$3)) /\
       S1 = E1 UNION IMAGE Theta sch_cap1 /\
       S2 = E2 UNION IMAGE Theta sch_cap2 /\
       ((!y. y IN N ==> (Theta y IN inside S <=> y$1 pow 2 + y$2 pow 2 < &1)) \/
        (!y. y IN N ==> (Theta y IN outside S <=> y$1 pow 2 + y$2 pow 2 < &1)))`;;

(* The model collars of the caps.  On the cone                              *)
(* sch_capcone of the shell (directions with x3 > -|x|/4) the surgered      *)
(* collar g1 is Theta o sch_cap_collar e0 for some small e0, and g2 is the  *)
(* mirror image (sch_flip3 on both sides).  With c = x3/|x| and             *)
(* e = e0 (|x| - 1): the height is y3 = -1 + c/2 + e smooth_step(8c - 6),  *)
(* the horizontal radius squared is sch_cap_profile(-y3) + e, so the layers *)
(* |x| = const are the level sets of y1^2 + y2^2 - sch_cap_profile(-y3);    *)
(* the unit sphere goes to sch_cap1 for x3 >= 0 (north pole to the apex     *)
(* (0,0,-1/2), height linear in x3) and to the cylinder just below the slab *)
(* for -1/4 < x3 < 0; near the pole the layers are vertical translates of   *)
(* the exact paraboloid, near the cylinder they are coaxial cylinders.      *)

let sch_flip3 = new_definition
 `sch_flip3 (x:real^3) = vector[x$1; x$2; --(x$3)]:real^3`;;

let sch_capcone = new_definition
 `sch_capcone = {x:real^3 | &1 / &2 < norm x /\ norm x < &2 /\ --(&1 / &4) * norm x < x$3}`;;

let sch_capq = new_definition
 `sch_capq (e:real) (c:real) =
    (sch_cap_profile(&1 - c / &2 - e * smooth_step(&8 * c - &6)) + e) / (&1 - c pow 2)`;;

let sch_cap_collar = new_definition
 `sch_cap_collar (e0:real) (x:real^3) =
    vector[sqrt(sch_capq (e0 * (norm x - &1)) (x$3 / norm x)) * x$1 / norm x;
           sqrt(sch_capq (e0 * (norm x - &1)) (x$3 / norm x)) * x$2 / norm x;
           -- &1 + (x$3 / norm x) / &2 +
           e0 * (norm x - &1) * smooth_step(&8 * (x$3 / norm x) - &6)]:real^3`;;

(* The surgery construction: surgery along an innermost circle of a regular  *)
(* level between two saddles produces two collared Morse spheres in slab     *)
(* configuration, whose collars are the model collars near the caps.         *)

let SCH_SURG_CONSTRUCT_STATEMENT = new_definition
 `SCH_SURG_CONSTRUCT_STATEMENT <=>
    !g g':real^3->real^3 t1 t2 a.
        sch_neck g g' /\ sch_morse g /\
        t1 IN sch_saddles g /\ t2 IN sch_saddles g /\
        (g t1)$3 < a /\ a < (g t2)$3 /\ (!t. sch_crit g t ==> ~((g t)$3 = a))
        ==> ?g1 g1' g2 g2' Theta.
              sch_neck g1 g1' /\ sch_morse g1 /\
              sch_neck g2 g2' /\ sch_morse g2 /\
              (!t. sch_crit g1 t ==> ~((g1 t)$3 = a)) /\
              (!t. sch_crit g2 t ==> ~((g2 t)$3 = a)) /\
              CARD(sch_saddles g1) <= CARD(sch_saddles g) /\
              CARD(sch_saddles g2) <= CARD(sch_saddles g) /\
              (CARD(sch_saddles g1) = CARD(sch_saddles g)
               ==> (?s1 s2. s1 IN sch_saddles g1 /\ s2 IN sch_saddles g1 /\
                            (g1 s1)$3 < a /\ a < (g1 s2)$3) /\
                   CARD(components(sch_level g1 a)) <
                   CARD(components(sch_level g a))) /\
              (CARD(sch_saddles g2) = CARD(sch_saddles g)
               ==> (?s1 s2. s1 IN sch_saddles g2 /\ s2 IN sch_saddles g2 /\
                            (g2 s1)$3 < a /\ a < (g2 s2)$3) /\
                   CARD(components(sch_level g2 a)) <
                   CARD(components(sch_level g a))) /\
              sch_slab_config (IMAGE g (sphere(vec 0,&1))) (IMAGE g1 (sphere(vec 0,&1)))
                              (IMAGE g2 (sphere(vec 0,&1))) Theta /\
              (?e0. &0 < e0 /\ e0 <= &1 / &16 /\
                    !x. x IN sch_capcone
                        ==> g1 x = Theta(sch_cap_collar e0 x) /\
                            g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x)))`;;

(* The gluing: balls for the two surgered spheres give a ball for S (the     *)
(* necks of the surgered spheres are the model collars near the caps).       *)

let SCH_SLAB_GLUE_STATEMENT = new_definition
 `SCH_SLAB_GLUE_STATEMENT <=>
    !g g' g1 g1' g2 g2' (Theta:real^3->real^3).
        sch_neck g g' /\ sch_neck g1 g1' /\ sch_neck g2 g2' /\
        sch_slab_config (IMAGE g (sphere(vec 0,&1))) (IMAGE g1 (sphere(vec 0,&1)))
                        (IMAGE g2 (sphere(vec 0,&1))) Theta /\
        (?e0. &0 < e0 /\ e0 <= &1 / &16 /\
              !x. x IN sch_capcone
                  ==> g1 x = Theta(sch_cap_collar e0 x) /\
                      g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
        sch_bounds_ball (IMAGE g1 (sphere(vec 0,&1))) /\
        sch_bounds_ball (IMAGE g2 (sphere(vec 0,&1)))
        ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`;;

let SCH_SURGERY_FROM_SLAB = prove
 (`SCH_SURG_CONSTRUCT_STATEMENT /\ SCH_SLAB_GLUE_STATEMENT ==> SCH_SURGERY_STATEMENT`,
  REWRITE_TAC[SCH_SURG_CONSTRUCT_STATEMENT; SCH_SLAB_GLUE_STATEMENT; SCH_SURGERY_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CON") (LABEL_TAC "GLU")) THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `t1:real^3`; `t2:real^3`;
                       `a:real`] THEN
  DISCH_TAC THEN
  USE_THEN "CON" (MP_TAC o SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t1:real^3`;
                                 `t2:real^3`; `a:real`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
      (X_CHOOSE_THEN `Theta:real^3->real^3` (LABEL_TAC "C")))))) THEN
  MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `g1':real^3->real^3`;
                        `g2:real^3->real^3`; `g2':real^3->real^3`] THEN
  REMOVE_THEN "C" MP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "GLU" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `g1:real^3->real^3`; `g1':real^3->real^3`;
                        `g2:real^3->real^3`; `g2':real^3->real^3`; `Theta:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[]);;

(* The two statements about regular levels used by the surgery construction: *)
(* each component of a regular level is the central circle of a planar neck  *)
(* at that height, and some component is innermost (its planar inside misses *)
(* the sphere).                                                              *)

let SCH_LEVEL_NECK_STATEMENT = new_definition
 `SCH_LEVEL_NECK_STATEMENT <=>
    !g g':real^3->real^3 a C.
        sch_neck g g' /\ sch_morse g /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
        C IN components(sch_level g a)
        ==> ?F F':real^2->real^2.
              sch_neck F F' /\
              C = IMAGE (\x. vector[(F x)$1; (F x)$2; a]:real^3) (sphere(vec 0,&1))`;;

let SCH_LEVEL_INNERMOST_STATEMENT = new_definition
 `SCH_LEVEL_INNERMOST_STATEMENT <=>
    !g g':real^3->real^3 a.
        sch_neck g g' /\ sch_morse g /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
        ~(sch_level g a = {})
        ==> ?C. C IN components(sch_level g a) /\
                !x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                           ==> ~((vector[x$1; x$2; a]:real^3) IN IMAGE g (sphere(vec 0,&1)))`;;

(* ------------------------------------------------------------------------- *)
(* Profile facts and sanity theorems (the round sphere of                    *)
(* radius 2 is in slab configuration; the round unit sphere satisfies the    *)
(* conclusions of the two level statements).                                 *)
(* ------------------------------------------------------------------------- *)

let SCH_CAP_PROFILE_TIP = prove
 (`!t. t <= &5 / &8 ==> sch_cap_profile t = t - &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch_cap_profile] THEN
  SUBGOAL_THEN `smooth_step(&4 * t - &5 / &2) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let SCH_CAP_PROFILE_TOP = prove
 (`!t. &7 / &8 <= t ==> sch_cap_profile t = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch_cap_profile] THEN
  SUBGOAL_THEN `smooth_step(&4 * t - &5 / &2) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let SCH_CAP_PROFILE_POS = prove
 (`!t. &1 / &2 < t ==> &0 < sch_cap_profile t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&7 / &8 <= t` THENL
   [ASM_SIMP_TAC[SCH_CAP_PROFILE_TOP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[sch_cap_profile] THEN
  MP_TAC(SPEC `&4 * t - &5 / &2` SMOOTH_STEP_BOUNDS) THEN
  ABBREV_TAC `b = smooth_step(&4 * t - &5 / &2)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= b * (&3 / &2 - t)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let SCH_CAP_PROFILE_SMOOTH = prove
 (`smooth_map_on (:real^1) (lift o sch_cap_profile o drop)`,
  REWRITE_TAC[o_DEF; sch_cap_profile] THEN
  MP_TAC(ISPECL [`&4`; `&5 / &2`] SMOOTH_STEP_AFFINE_SMOOTH) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!c. smooth_map_on (:real^1) (\x:real^1. lift(drop x - c))` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(&1 - smooth_step(&4 * drop x - &5 / &2))`;
                 `\x:real^1. lift(drop x - &1 / &2)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST]);;

(* The model chart of the sphere of radius 2 near its equator. *)

let SCH_SLAB_THETA0 = prove
 (`diffeomorphism_on {y:real^3 | abs(y$3) < &3 / &2} {y:real^3 | abs(y$3) < &3 / &2}
     (\y. vector[sqrt(&4 - y$3 pow 2) * y$1; sqrt(&4 - y$3 pow 2) * y$2; y$3]:real^3)
     (\x. vector[x$1 / sqrt(&4 - x$3 pow 2); x$2 / sqrt(&4 - x$3 pow 2); x$3]:real^3)`,
  ABBREV_TAC `N0 = {y:real^3 | abs(y$3) < &3 / &2}` THEN
  ABBREV_TAC `f = \y:real^3. vector[sqrt(&4 - y$3 pow 2) * y$1; sqrt(&4 - y$3 pow 2) * y$2;
                                    y$3]:real^3` THEN
  ABBREV_TAC `g = \x:real^3. vector[x$1 / sqrt(&4 - x$3 pow 2); x$2 / sqrt(&4 - x$3 pow 2);
                                    x$3]:real^3` THEN
  SUBGOAL_THEN `open(N0:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN
    SUBGOAL_THEN `{y:real^3 | abs(y$3) < &3 / &2} =
                  {y | y$3 > --(&3 / &2)} INTER {y | y$3 < &3 / &2}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN N0 ==> &0 < &4 - y$3 pow 2 /\ &0 < sqrt(&4 - y$3 pow 2) /\
                                      sqrt(&4 - y$3 pow 2) pow 2 = &4 - y$3 pow 2`
  (LABEL_TAC "Q") THENL
   [EXPAND_TAC "N0" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &4 - (y:real^3)$3 pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SUB_LT] THEN
      SUBGOAL_THEN `(y:real^3)$3 pow 2 = abs(y$3) pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `(&3 / &2) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y:real^3. y IN N0 ==> (g:real^3->real^3) (f y) = y) /\
                (!x:real^3. x IN N0 ==> (f:real^3->real^3) (g x) = x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "Q" (MP_TAC o C MP (ASSUME `(y:real^3) IN N0`) o SPEC `y:real^3`) THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y:real^3. y IN N0 ==> (f:real^3->real^3) y IN N0) /\
                (!x:real^3. x IN N0 ==> (g:real^3->real^3) x IN N0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N0"; "f"; "g"] THEN REWRITE_TAC[IN_ELIM_THM; VECTOR_3]; ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) N0 = N0 /\ IMAGE (g:real^3->real^3) N0 = N0`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. smooth_map_on N0 (\y:real^3. lift(y$k))` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`N0:real^3->bool`; `\y:real^3. y`; `k:num`]
      SMOOTH_MAP_ON_LIFT_COMPONENT) THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on N0 (\y:real^3. lift(sqrt(&4 - y$3 pow 2)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`N0:real^3->bool`; `\y:real^3. lift(&4 - y$3 pow 2)`]
      SMOOTH_MAP_ON_LIFT_SQRT) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MP_TAC(ISPECL [`N0:real^3->bool`; `\y:real^3. lift(y$3)`; `2`] SMOOTH_MAP_ON_LIFT_POW) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N0:real^3->bool`; `f:real^3->real^3`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  MP_TAC(ISPECL [`N0:real^3->bool`; `g:real^3->real^3`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[ASSUME `open(N0:real^3->bool)`; DIMINDEX_3] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
  REWRITE_TAC[TAUT `(a \/ b \/ c ==> d) <=> (a ==> d) /\ (b ==> d) /\ (c ==> d)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  MAP_EVERY EXPAND_TAC ["f"; "g"] THEN REWRITE_TAC[VECTOR_3] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`N0:real^3->bool`; `\y:real^3. lift(sqrt(&4 - y$3 pow 2))`;
                   `\y:real^3. lift(y$1)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`N0:real^3->bool`; `\y:real^3. lift(sqrt(&4 - y$3 pow 2))`;
                   `\y:real^3. lift(y$2)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`N0:real^3->bool`; `\y:real^3. lift(y$1)`;
                   `\y:real^3. lift(sqrt(&4 - y$3 pow 2))`] SMOOTH_MAP_ON_LIFT_DIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    USE_THEN "Q" (fun th -> REWRITE_TAC[MP (SPEC `x:real^3` th) (ASSUME `(x:real^3) IN N0`)]);
    MP_TAC(ISPECL [`N0:real^3->bool`; `\y:real^3. lift(y$2)`;
                   `\y:real^3. lift(sqrt(&4 - y$3 pow 2))`] SMOOTH_MAP_ON_LIFT_DIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    USE_THEN "Q" (fun th -> REWRITE_TAC[MP (SPEC `x:real^3` th) (ASSUME `(x:real^3) IN N0`)]);
    ASM_REWRITE_TAC[]]);;

let SCH_SLAB_N0_POS = prove
 (`!y:real^3. abs(y$3) < &3 / &2 ==> &0 < &4 - y$3 pow 2`,
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LT] THEN
  SUBGOAL_THEN `(y:real^3)$3 pow 2 = abs(y$3) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `(&3 / &2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SCH_SLAB_THETA0_NORM = prove
 (`!y:real^3. abs(y$3) < &3 / &2
     ==> (norm(vector[sqrt(&4 - y$3 pow 2) * y$1; sqrt(&4 - y$3 pow 2) * y$2;
                      y$3]:real^3) = &2
          <=> y$1 pow 2 + y$2 pow 2 = &1) /\
         (norm(vector[sqrt(&4 - y$3 pow 2) * y$1; sqrt(&4 - y$3 pow 2) * y$2;
                      y$3]:real^3) < &2
          <=> y$1 pow 2 + y$2 pow 2 < &1)`,
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH_SLAB_N0_POS) THEN
  SUBGOAL_THEN `sqrt(&4 - (y:real^3)$3 pow 2) pow 2 = &4 - y$3 pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&4 - (y:real^3)$3 pow 2 = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  REWRITE_TAC[NORM_EQ_SQUARE; NORM_LT_SQUARE; DOT_3; VECTOR_3] THEN
  SUBGOAL_THEN `(sqrt(&4 - (y:real^3)$3 pow 2) * y$1) * (sqrt(&4 - y$3 pow 2) * y$1) +
                (sqrt(&4 - y$3 pow 2) * y$2) * (sqrt(&4 - y$3 pow 2) * y$2) + y$3 * y$3 =
                (&4 - y$3 pow 2) * (y$1 pow 2 + y$2 pow 2) + y$3 pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `sqrt(&4 - (y:real^3)$3 pow 2) pow 2 = &4 - y$3 pow 2` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`(y:real^3)$1 pow 2 + y$2 pow 2`; `&1`; `&4 - (y:real^3)$3 pow 2`]
    REAL_LT_LMUL_EQ) THEN
  MP_TAC(SPECL [`&4 - (y:real^3)$3 pow 2`; `(y:real^3)$1 pow 2 + y$2 pow 2`; `&1`]
    REAL_EQ_MUL_LCANCEL) THEN
  REWRITE_TAC[ASSUME `~(&4 - (y:real^3)$3 pow 2 = &0)`;
              ASSUME `&0 < &4 - (y:real^3)$3 pow 2`; REAL_MUL_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* Model sanity: the round sphere of radius 2 with the chart above. *)

let SCH_SLAB_MODEL = prove
 (`sch_slab_config (sphere(vec 0:real^3,&2))
     ({x:real^3 | x IN sphere(vec 0,&2) /\ x$3 < -- &1} UNION
      IMAGE (\y:real^3. vector[sqrt(&4 - y$3 pow 2) * y$1; sqrt(&4 - y$3 pow 2) * y$2;
                               y$3]:real^3) sch_cap1)
     ({x:real^3 | x IN sphere(vec 0,&2) /\ &1 < x$3} UNION
      IMAGE (\y:real^3. vector[sqrt(&4 - y$3 pow 2) * y$1; sqrt(&4 - y$3 pow 2) * y$2;
                               y$3]:real^3) sch_cap2)
     (\y:real^3. vector[sqrt(&4 - y$3 pow 2) * y$1; sqrt(&4 - y$3 pow 2) * y$2;
                        y$3]:real^3)`,
  ASSUME_TAC SCH_SLAB_THETA0 THEN
  REWRITE_TAC[sch_slab_config] THEN
  MAP_EVERY EXISTS_TAC
   [`{y:real^3 | abs(y$3) < &3 / &2}`;
    `\x:real^3. vector[x$1 / sqrt(&4 - x$3 pow 2); x$2 / sqrt(&4 - x$3 pow 2);
                       x$3]:real^3`;
    `{x:real^3 | x IN sphere(vec 0,&2) /\ x$3 < -- &1}`;
    `{x:real^3 | x IN sphere(vec 0,&2) /\ &1 < x$3}`] THEN
  ABBREV_TAC `N0 = {y:real^3 | abs(y$3) < &3 / &2}` THEN
  ABBREV_TAC `Th = \y:real^3. vector[sqrt(&4 - y$3 pow 2) * y$1; sqrt(&4 - y$3 pow 2) * y$2;
                                     y$3]:real^3` THEN
  ABBREV_TAC `g = \x:real^3. vector[x$1 / sqrt(&4 - x$3 pow 2); x$2 / sqrt(&4 - x$3 pow 2);
                                    x$3]:real^3` THEN
  SUBGOAL_THEN `!y:real^3. y IN N0
                  ==> ((Th:real^3->real^3) y IN sphere(vec 0,&2) <=>
                       y$1 pow 2 + y$2 pow 2 = &1) /\
                      (Th y IN ball(vec 0,&2) <=> y$1 pow 2 + y$2 pow 2 < &1)`
  (LABEL_TAC "B") THENL
   [EXPAND_TAC "N0" THEN EXPAND_TAC "Th" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SPHERE_0; IN_BALL_0] THEN SIMP_TAC[SCH_SLAB_THETA0_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. abs(y$3) <= &1 ==> y IN N0` (LABEL_TAC "N1") THENL
   [EXPAND_TAC "N0" THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ((Th:real^3->real^3) y)$3 = y$3` (LABEL_TAC "C") THENL
   [EXPAND_TAC "Th" THEN REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
  SUBGOAL_THEN `open(N0:real^3->bool) /\ IMAGE (Th:real^3->real^3) N0 = N0 /\
                (!x. x IN N0 ==> (g:real^3->real^3) x IN N0) /\
                (!x. x IN N0 ==> (Th:real^3->real^3) (g x) = x)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on N0 N0 (Th:real^3->real^3) g` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) N0 = N0` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y:real^3. vector[sqrt(&4 - y$3 pow 2) * y$1; sqrt(&4 - y$3 pow 2) * y$2;
                                  y$3]:real^3 = Th y` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Th" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the fixed neighbourhood of the model cylinder lies in N0 *)
    REWRITE_TAC[sch_slab_nbhd; SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN UNDISCH_TAC `{y:real^3 | abs(y$3) < &3 / &2} = N0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `abs((y:real^3)$3) < &5 / &4` THEN REAL_ARITH_TAC;
    (* preimage of the sphere *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "B" (fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN N0`)]);
    (* the decomposition of the sphere *)
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_IMAGE; sch_lat] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(x:real^3)$3 < -- &1` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `&1 < (x:real^3)$3` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^3) IN N0` ASSUME_TAC THENL
       [USE_THEN "N1" MATCH_MP_TAC THEN UNDISCH_TAC `~((x:real^3)$3 < -- &1)` THEN
        UNDISCH_TAC `~(&1 < (x:real^3)$3)` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXISTS_TAC `(g:real^3->real^3) x` THEN
      SUBGOAL_THEN `(Th:real^3->real^3) (g x) = x /\ (g:real^3->real^3) x IN N0`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `((g:real^3->real^3) x)$3 = x$3` SUBST1_TAC THENL
       [USE_THEN "C" (MP_TAC o SPEC `(g:real^3->real^3) x`) THEN
        REWRITE_TAC[ASSUME `(Th:real^3->real^3) (g x) = x`] THEN
        DISCH_THEN(ACCEPT_TAC o SYM);
        ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "B" (MP_TAC o CONJUNCT1 o C MP (ASSUME `(g:real^3->real^3) x IN N0`) o
                      SPEC `(g:real^3->real^3) x`) THEN
        REWRITE_TAC[ASSUME `(Th:real^3->real^3) (g x) = x`;
                    ASSUME `(x:real^3) IN sphere(vec 0,&2)`];
        UNDISCH_TAC `~((x:real^3)$3 < -- &1)` THEN
        UNDISCH_TAC `~(&1 < (x:real^3)$3)` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x':real^3) IN N0` ASSUME_TAC THENL
     [USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "B" (fun th -> REWRITE_TAC[MP (SPEC `x':real^3` th) (ASSUME `(x':real^3) IN N0`)]) THEN
    ASM_REWRITE_TAC[];
    (* the two ends are disjoint *)
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC;
    (* preimages of the two ends *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    USE_THEN "B" (fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN N0`)]) THEN
    ASM_REWRITE_TAC[];
    (* the inside of the sphere is the inside of the cylinder *)
    DISJ1_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[INSIDE_SPHERE] THEN
    USE_THEN "B" (fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN N0`)])]);;

(* ------------------------------------------------------------------------- *)
(* Sanity checks of the two level statements on the round sphere: between    *)
(* the poles each level is one circle, and its planar neck is a scaling.     *)
(* ------------------------------------------------------------------------- *)

let SCH_SLAB_ROUND_POS = prove
 (`!a. abs a < &1
       ==> &0 < &1 - a pow 2 /\ &0 < sqrt(&1 - a pow 2) /\
           sqrt(&1 - a pow 2) pow 2 = &1 - a pow 2`,
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 - a pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs a pow 2 < &1 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN ARITH_TAC;
      REWRITE_TAC[REAL_POW2_ABS] THEN REAL_ARITH_TAC];
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]]);;

let SCH_SLAB_ROUND_LEVEL = prove
 (`!a. abs a < &1
       ==> sch_level (\x:real^3. x) a =
           IMAGE (\u:real^2. vector[sqrt(&1 - a pow 2) * u$1; sqrt(&1 - a pow 2) * u$2;
                                    a]:real^3)
                 (sphere(vec 0,&1))`,
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH_SLAB_ROUND_POS) THEN
  ABBREV_TAC `r = sqrt(&1 - a pow 2)` THEN
  SUBGOAL_THEN `~(r = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  REWRITE_TAC[sch_level; IMAGE_ID] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_SPHERE_0] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `vector[(x:real^3)$1 / r; x$2 / r]:real^2` THEN
    REWRITE_TAC[VECTOR_2; NORM_EQ_1; DOT_2] THEN CONJ_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL];
      UNDISCH_TAC `norm(x:real^3) = &1` THEN REWRITE_TAC[NORM_EQ_1; DOT_3] THEN
      UNDISCH_TAC `(x:real^3)$3 = a` THEN UNDISCH_TAC `r pow 2 = &1 - a pow 2` THEN
      UNDISCH_TAC `~(r = &0)` THEN CONV_TAC REAL_FIELD];
    DISCH_THEN(X_CHOOSE_THEN `u:real^2` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    REWRITE_TAC[VECTOR_3; NORM_EQ_1; DOT_2; DOT_3] THEN
    UNDISCH_TAC `r pow 2 = &1 - a pow 2` THEN CONV_TAC REAL_RING]);;

let SCH_SLAB_ROUND_COMPONENTS = prove
 (`!a. abs a < &1
       ==> components(sch_level (\x:real^3. x) a) = {sch_level (\x:real^3. x) a}`,
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN REWRITE_TAC[COMPONENTS_EQ_SING] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SCH_SLAB_ROUND_LEVEL) THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3; LIFT_CMUL; CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC);;

let SCH_SLAB_ROUND_PROJ = prove
 (`!a. abs a < &1
       ==> IMAGE (\y:real^3. vector[y$1; y$2]:real^2) (sch_level (\x:real^3. x) a) =
           sphere(vec 0,sqrt(&1 - a pow 2))`,
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SCH_SLAB_ROUND_LEVEL) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP SCH_SLAB_ROUND_POS) THEN
  SPEC_TAC(`sqrt(&1 - a pow 2)`,`r:real`) THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_3] THEN
  SUBGOAL_THEN `!u:real^2. (vector[r * u$1; r * u$2]:real^2) = r % u`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_MUL_COMPONENT]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `inv r % (y:real^2)` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; NORM_MUL] THEN
    REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_LINV; REAL_LT_IMP_NZ]]);;

let SCH_SLAB_SCALE_NECK = prove
 (`!r. &0 < r ==> sch_neck (\x:real^2. r % x) (\x. inv r % x)`,
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r = &0)` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  REWRITE_TAC[sch_neck; diffeomorphism_on] THEN
  ABBREV_TAC `A = annulus (&1 / &2) (&2):real^2->bool` THEN
  SUBGOAL_THEN `open(A:real^2->bool) /\ open(IMAGE (\x:real^2. r % x) A)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN ASM_SIMP_TAC[OPEN_ANNULUS; OPEN_SCALING]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID; IMAGE_ID];
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LINV; REAL_MUL_RID; REAL_MUL_LID;
                 VECTOR_MUL_LID];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]]);;

let SCH_LEVEL_NECK_ROUND = prove
 (`!a. abs a < &1
       ==> (!t. sch_crit (\x:real^3. x) t ==> ~(t$3 = a)) /\
           !C. C IN components(sch_level (\x:real^3. x) a)
               ==> ?F F':real^2->real^2.
                     sch_neck F F' /\
                     C = IMAGE (\x. vector[(F x)$1; (F x)$2; a]:real^3)
                               (sphere(vec 0,&1))`,
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[SCH_ROUND_CRIT] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_NEG_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `abs a < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCH_SLAB_ROUND_COMPONENTS th; IN_SING]) THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCH_SLAB_ROUND_LEVEL th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH_SLAB_ROUND_POS) THEN
  MAP_EVERY EXISTS_TAC [`\x:real^2. sqrt(&1 - a pow 2) % x`;
                        `\x:real^2. inv(sqrt(&1 - a pow 2)) % x`] THEN
  ASM_SIMP_TAC[SCH_SLAB_SCALE_NECK] THEN REWRITE_TAC[VECTOR_MUL_COMPONENT]);;

let SCH_LEVEL_INNERMOST_ROUND = prove
 (`!a. abs a < &1
       ==> ~(sch_level (\x:real^3. x) a = {}) /\
           ?C. C IN components(sch_level (\x:real^3. x) a) /\
               !x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                          ==> ~((vector[x$1; x$2; a]:real^3) IN
                                IMAGE (\x:real^3. x) (sphere(vec 0,&1)))`,
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH_SLAB_ROUND_POS) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCH_SLAB_ROUND_COMPONENTS th; IN_SING]) THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCH_SLAB_ROUND_PROJ th]) THEN
  REWRITE_TAC[INSIDE_SPHERE; IN_BALL_0; IMAGE_ID; IN_SPHERE_0] THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCH_SLAB_ROUND_LEVEL th]) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(x:real^2) pow 2 < sqrt(&1 - a pow 2) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_POW_2; DOT_2; NORM_EQ_1; DOT_3; VECTOR_3] THEN REAL_ARITH_TAC);;

(* The two level statements hold for the round sphere (instances g = id).   *)

let SCH_SLAB_ROUND_LEVEL_CASES = prove
 (`!a. (!t. sch_crit (\x:real^3. x) t ==> ~(t$3 = a))
       ==> abs a < &1 \/ sch_level (\x:real^3. x) a = {}`,
  GEN_TAC THEN REWRITE_TAC[SCH_ROUND_CRIT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `abs a < &1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(a = &1) /\ ~(a = -- &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `basis 3:real^3`);
      FIRST_X_ASSUM(MP_TAC o SPEC `--basis 3:real^3`)] THEN
    ASM_SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[sch_level; IMAGE_ID] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_SPHERE_0] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(abs a < &1)` THEN UNDISCH_TAC `~(a = &1)` THEN
  UNDISCH_TAC `~(a = -- &1)` THEN REAL_ARITH_TAC);;

let SCH_LEVEL_NECK_ROUND_INSTANCE = prove
 (`!a C. sch_neck (\x:real^3. x) (\x. x) /\ sch_morse (\x:real^3. x) /\
         (!t. sch_crit (\x:real^3. x) t ==> ~(t$3 = a)) /\
         C IN components(sch_level (\x:real^3. x) a)
         ==> ?F F':real^2->real^2.
               sch_neck F F' /\
               C = IMAGE (\x. vector[(F x)$1; (F x)$2; a]:real^3) (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP SCH_SLAB_ROUND_LEVEL_CASES) THENL
   [MP_TAC(SPEC `a:real` SCH_LEVEL_NECK_ROUND) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `C:real^3->bool` o CONJUNCT2) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    UNDISCH_TAC `(C:real^3->bool) IN components(sch_level (\x:real^3. x) a)` THEN
    ASM_REWRITE_TAC[COMPONENTS_EMPTY; NOT_IN_EMPTY]]);;

let SCH_LEVEL_INNERMOST_ROUND_INSTANCE = prove
 (`!a. sch_neck (\x:real^3. x) (\x. x) /\ sch_morse (\x:real^3. x) /\
       (!t. sch_crit (\x:real^3. x) t ==> ~(t$3 = a)) /\
       ~(sch_level (\x:real^3. x) a = {})
       ==> ?C. C IN components(sch_level (\x:real^3. x) a) /\
               !x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                          ==> ~((vector[x$1; x$2; a]:real^3) IN
                                IMAGE (\x:real^3. x) (sphere(vec 0,&1)))`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP SCH_SLAB_ROUND_LEVEL_CASES) THENL
   [MP_TAC(SPEC `a:real` SCH_LEVEL_INNERMOST_ROUND) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2);
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Facts on the model collars of the caps.                                  *)
(* ------------------------------------------------------------------------- *)

let SCH_CAP_PROFILE_BOUNDS = prove
 (`!t. &1 / &2 <= t /\ t <= &3 / &2
       ==> &0 <= sch_cap_profile t /\ sch_cap_profile t <= &1`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[sch_cap_profile] THEN
  MP_TAC(SPEC `&4 * t - &5 / &2` SMOOTH_STEP_BOUNDS) THEN
  ABBREV_TAC `b = smooth_step(&4 * t - &5 / &2)` THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(&1 - b) * (t - &1 / &2) <= (&1 - b) * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let SCH_CAP_PROFILE_LB = prove
 (`!t. &5 / &8 <= t ==> &1 / &8 <= sch_cap_profile t`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[sch_cap_profile] THEN
  MP_TAC(SPEC `&4 * t - &5 / &2` SMOOTH_STEP_BOUNDS) THEN
  ABBREV_TAC `b = smooth_step(&4 * t - &5 / &2)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&1 - b) * (&1 / &8) <= (&1 - b) * (t - &1 / &2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The two caps are mirror images. *)

let SCH_FLIP3_CAP = prove
 (`!y:real^3. sch_flip3 y IN sch_cap2 <=> y IN sch_cap1`,
  GEN_TAC THEN REWRITE_TAC[sch_flip3; sch_cap1; sch_cap2; IN_ELIM_THM; VECTOR_3] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN REAL_ARITH_TAC);;

let SCH_FLIP3_INVOLUTION = prove
 (`!x:real^3. sch_flip3(sch_flip3 x) = x`,
  REWRITE_TAC[sch_flip3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; REAL_NEG_NEG]);;

let SCH_SLAB_SQ_LT1 = prove
 (`!c. abs c < &1 ==> &0 < &1 - c pow 2`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_1_LT THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN ARITH_TAC);;

(* On the unit sphere the collar parametrizes the cap (x3 >= 0) and the     *)
(* cylinder just below the slab (-1/4 < x3 < 0).                            *)

let SCH_CAP_COLLAR_SPHERE = prove
 (`!e0 x:real^3.
     norm x = &1 /\ --(&1 / &4) < x$3
     ==> (&0 <= x$3 ==> sch_cap_collar e0 x IN sch_cap1) /\
         (x$3 < &0
          ==> (sch_cap_collar e0 x)$1 pow 2 + (sch_cap_collar e0 x)$2 pow 2 = &1 /\
              --(&9 / &8) < (sch_cap_collar e0 x)$3 /\ (sch_cap_collar e0 x)$3 < -- &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3)$1 pow 2 + x$2 pow 2 = &1 - x$3 pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(x:real^3) = &1` THEN REWRITE_TAC[NORM_EQ_1; DOT_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((x:real^3)$3) <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `c = (x:real^3)$3` THEN
  ASM_REWRITE_TAC[sch_cap_collar; sch_capq; sch_cap1; IN_ELIM_THM; VECTOR_3] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_SUB_RZERO;
              REAL_ADD_RID; REAL_DIV_1] THEN
  SUBGOAL_THEN `&0 <= sch_cap_profile(&1 - c / &2)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&1 - c / &2` SCH_CAP_PROFILE_BOUNDS) THEN
    ANTS_TAC THENL [UNDISCH_TAC `abs(c:real) <= &1` THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sch_cap_profile(&1 - c / &2) / (&1 - c pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `--(--(&1) + c / &2) = &1 - c / &2`] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `sch_cap_profile(&1 - c / &2) / (&1 - c pow 2) * (&1 - c pow 2) =
                  sch_cap_profile(&1 - c / &2)` SUBST1_TAC THENL
     [ASM_CASES_TAC `c = &1` THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[REAL_MUL_RZERO] THEN
        MP_TAC(SPEC `&1 / &2` SCH_CAP_PROFILE_TIP) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_DIV_RMUL THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN UNDISCH_TAC `~(c = &1)` THEN
        UNDISCH_TAC `abs(c:real) <= &1` THEN UNDISCH_TAC `&0 <= c` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `abs(c:real) <= &1` THEN UNDISCH_TAC `&0 <= c` THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `sch_cap_profile(&1 - c / &2) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN UNDISCH_TAC `c < &0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / (&1 - c pow 2) * (&1 - c pow 2) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN
      UNDISCH_TAC `--(&1 / &4) < c` THEN UNDISCH_TAC `c < &0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `--(&1 / &4) < c` THEN UNDISCH_TAC `c < &0` THEN REAL_ARITH_TAC]);;

(* The layers |x| = const of the collar are level sets of                   *)
(* y1^2 + y2^2 - sch_cap_profile(-y3), and the collar stays in the fixed    *)
(* neighbourhood of the model cylinder.                                      *)

let SCH_CAP_COLLAR_LAYER = prove
 (`!e0 x:real^3.
     &0 < e0 /\ e0 <= &1 / &16 /\ x IN sch_capcone
     ==> (sch_cap_collar e0 x)$1 pow 2 + (sch_cap_collar e0 x)$2 pow 2 =
         sch_cap_profile(--((sch_cap_collar e0 x)$3)) + e0 * (norm x - &1) /\
         sch_cap_collar e0 x IN sch_slab_nbhd`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3)$1 pow 2 + x$2 pow 2 = norm x pow 2 - x$3 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((x:real^3)$3) <= norm x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `n = norm(x:real^3)` THEN
  SUBGOAL_THEN `&0 < n` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 / &2 < n` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = (x:real^3)$3 / n` THEN
  SUBGOAL_THEN `(x:real^3)$3 = c * n` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `--(&1 / &4) < c /\ c <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `--(&1 / &4) * n < (x:real^3)$3` THEN
    UNDISCH_TAC `abs((x:real^3)$3) <= n` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `n:real` THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `n:real` THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3)$1 pow 2 + x$2 pow 2 = n pow 2 * (&1 - c pow 2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ABBREV_TAC `e = e0 * (n - &1)` THEN
  SUBGOAL_THEN `--(&1 / &32) < e /\ e < &1 / &16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN CONJ_TAC THENL
     [SUBGOAL_THEN `e0 * --(&1 / &2) < e0 * (n - &1)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `e0 * (n - &1) < e0 * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `b = smooth_step(&8 * c - &6)` THEN
  SUBGOAL_THEN `&0 <= b /\ b <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[SMOOTH_STEP_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `--(&1 / &32) <= e * b /\ e * b <= &1 / &16 /\
                --(&1 / &32) <= e * (&1 - b)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= e` THENL
     [SUBGOAL_THEN `&0 <= e * b /\ e * b <= e * &1 /\ &0 <= e * (&1 - b)` MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LE_MUL] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 <= --e * b /\ --e * b <= --e * &1 /\ &0 <= --e * (&1 - b) /\
                    --e * (&1 - b) <= --e * &1` MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL;
          MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_LNEG] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `s = &1 - c / &2 - e * b` THEN
  SUBGOAL_THEN `&0 <= sch_cap_profile s + e` ASSUME_TAC THENL
   [ASM_CASES_TAC `s <= &5 / &8` THENL
     [ASM_SIMP_TAC[SCH_CAP_PROFILE_TIP] THEN EXPAND_TAC "s" THEN
      ASM_CASES_TAC `&7 / &8 <= c` THENL
       [SUBGOAL_THEN `b = &1` SUBST1_TAC THENL
         [EXPAND_TAC "b" THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_ARITH `&1 - c / &2 - e * b - &1 / &2 + e =
                                (&1 - c) / &2 + e * (&1 - b)`] THEN
        ASM_REAL_ARITH_TAC];
      MP_TAC(SPEC `s:real` SCH_CAP_PROFILE_LB) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - c pow 2` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN REWRITE_TAC[REAL_SUB_LE] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sch_capq e c` ASSUME_TAC THENL
   [REWRITE_TAC[sch_capq] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(sqrt(sch_capq e c) * (x:real^3)$1 / n) pow 2 + (sqrt(sch_capq e c) * x$2 / n) pow 2 =
    sch_cap_profile s + e`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
    REWRITE_TAC[REAL_FIELD `q * a / m + q * b / m = q * (a + b) / m`] THEN
    REWRITE_TAC[ASSUME `(x:real^3)$1 pow 2 + x$2 pow 2 = n pow 2 * (&1 - c pow 2)`] THEN
    SUBGOAL_THEN `~(n pow 2 = &0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(m = &0) ==> q * (m * d) / m = q * d`] THEN
    REWRITE_TAC[sch_capq] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `c = &1` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_RZERO] THEN
      SUBGOAL_THEN `b = &1` ASSUME_TAC THENL
       [EXPAND_TAC "b" THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `s = &1 / &2 - e` SUBST1_TAC THENL
       [EXPAND_TAC "s" THEN REWRITE_TAC[ASSUME `c = &1`; ASSUME `b = &1`] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `&1 / &2 - e` SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(&1 - c pow 2 = &0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SCH_SLAB_SQ_LT1 THEN
      UNDISCH_TAC `~(c = &1)` THEN UNDISCH_TAC `--(&1 / &4) < c` THEN
      UNDISCH_TAC `c <= &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) + c / &2 + e * b = --s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap_profile s <= &1` ASSUME_TAC THENL
   [ASM_CASES_TAC `&1 / &2 <= s` THENL
     [MP_TAC(SPEC `s:real` SCH_CAP_PROFILE_BOUNDS) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN EXPAND_TAC "s" THEN
        UNDISCH_TAC `--(&1 / &4) < c` THEN UNDISCH_TAC `--(&1 / &32) <= e * b` THEN
        REAL_ARITH_TAC;
        SIMP_TAC[]];
      MP_TAC(SPEC `s:real` SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [UNDISCH_TAC `~(&1 / &2 <= s)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `~(&1 / &2 <= s)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs s < &5 / &4` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    UNDISCH_TAC `--(&1 / &4) < c` THEN UNDISCH_TAC `c <= &1` THEN
    UNDISCH_TAC `--(&1 / &32) <= e * b` THEN UNDISCH_TAC `e * b <= &1 / &16` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sch_cap_collar; sch_slab_nbhd; IN_ELIM_THM; VECTOR_3] THEN
  REWRITE_TAC[ASSUME `norm(x:real^3) = n`] THEN
  REWRITE_TAC[ASSUME `(x:real^3)$3 / n = c`] THEN
  REWRITE_TAC[REAL_ARITH `e0 * (n - &1) * b' = (e0 * (n - &1)) * b'`] THEN
  REWRITE_TAC[ASSUME `e0 * (n - &1) = e`; ASSUME `smooth_step(&8 * c - &6) = b`] THEN
  REWRITE_TAC[ASSUME `(sqrt(sch_capq e c) * (x:real^3)$1 / n) pow 2 +
                      (sqrt(sch_capq e c) * x$2 / n) pow 2 = sch_cap_profile s + e`;
              ASSUME `--(&1) + c / &2 + e * b = --s`; REAL_NEG_NEG; REAL_ABS_NEG] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `sch_cap_profile s <= &1` THEN UNDISCH_TAC `e < &1 / &16` THEN
  REAL_ARITH_TAC);;

