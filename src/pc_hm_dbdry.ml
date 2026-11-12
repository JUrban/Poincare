(* ========================================================================= *)
(* Unit pc_hm_dbdry: part 2 of the chain unit for                            *)
(* CM_CHAIN_HM_DIRICHLET_STATEMENT.  Continuity up to the boundary of        *)
(* small-energy harmonic maps with C^0 /\ W^{1,2} boundary values (in place  *)
(* of Qing 1993): the Courant-Lebesgue lemma at a boundary point with the    *)
(* radius outside a given null set, zero traces of continuous W_0 maps on    *)
(* almost every arc, eps-regularity on balls touching the normal segment,    *)
(* and the resulting quantitative boundary estimate HMD_QBE.                 *)
(* ========================================================================= *)

needs "src/pc_hm_dexist.ml";;
needs "src/pc_wan_sob2c.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The Courant-Lebesgue lemma at a boundary point of a disc, with the        *)
(* radius chosen outside a given null set of radii.  The proof is that of    *)
(* WAN_COURANT_LEBESGUE_BDRY (pc_wan_sob2c) with the null set N' added to    *)
(* the excluded radii.                                                       *)
(* ------------------------------------------------------------------------- *)

let HMD_CL_AVOID = prove
 (`!(a:real^2) R x0 R0 d E (u:real^2->real^K) N'.
     &0 < R /\ x0 IN sphere(a,R) /\ &0 < R0 /\ &0 < d /\ d < &1 /\
     u continuous_on (ball(a,R) INTER ball(x0,R0)) /\
     wan_w12 (ball(a,R) INTER ball(x0,R0)) u /\
     wan_dir (ball(a,R) INTER ball(x0,R0)) u <= &2 * E /\ negligible N'
     ==> ?r. d * R0 < r /\ r < sqrt d * R0 /\ ~(lift r IN N') /\
             !y z. y IN ball(a,R) INTER sphere(x0,r) /\ z IN ball(a,R) INTER sphere(x0,r)
                   ==> norm(u y - u z) <= sqrt(&4 * pi * E / log(inv d))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `th0:real` o MATCH_MP WAN_SPHERE_ANGLE) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && fst(dest_var(lhs(concl th))) = "a")) THEN
  ABBREV_TAC `D = ball(wan_circ x0 R th0,R) INTER ball(x0:real^2,R0)` THEN
  SUBGOAL_THEN `open(D:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN SIMP_TAC[OPEN_INTER; OPEN_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `u:real^2->real^K`; `x0:real^2`; `th0 - pi`] WAN_ARC_ACL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WAN_SQRT_FACTS o CONJ (ASSUME `&0 < d`)) THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`D:real^2->bool`; `u:real^2->real^K`] WAN_DIR_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d * R0 /\ d * R0 < sqrt d * R0 /\ sqrt d * R0 < R0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_RMUL_EQ] THEN
    GEN_REWRITE_TAC (RAND_CONV) [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = \x. lift(norm(wan_wd D 1 (u:real^2->real^K) x) pow 2 + norm(wan_wd D 2 u x) pow 2)` THEN
  ABBREV_TAC `G' = \x. if x IN D then (G:real^2->real^1) x else vec 0` THEN
  SUBGOAL_THEN `(G:real^2->real^1) absolutely_integrable_on D` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC WAN_DIR_DENSITY_ABS_INT THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G':real^2->real^1) absolutely_integrable_on (:real^2) /\
                integral (:real^2) G' = integral (D:real^2->bool) (G:real^2->real^1) /\
                (!x. &0 <= drop(G' x))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G'" THEN
    ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; REAL_LE_REFL] THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[LIFT_DROP] THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G':real^2->real^1) absolutely_integrable_on
    {x | d * R0 < norm(x - x0) /\ norm(x - x0) < sqrt d * R0}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV; WAN_ANNULUS_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G':real^2->real^1`; `x0:real^2`; `th0 - pi`; `d * R0`; `sqrt d * R0`]
                WAN_POLAR_ANNULUS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `N:real^1->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N"))) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `drop(integral (interval[lift(d * R0),lift(sqrt d * R0)])
           (\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                           (\t. (G':real^2->real^1)
                                  (wan_circ x0 (drop r) ((th0 - pi) + drop t))))) <= &2 * E`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (:real^2) (G':real^2->real^1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; SUBSET_UNIV];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN ASM_SIMP_TAC[GSYM WAN_DIR_2D_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ABBREV_TAC `c = &4 * E / log(inv d)` THEN
  MP_TAC(ISPECL [`c:real`; `d * R0`; `sqrt d * R0`] WAN_INTEGRAL_INV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; WAN_LOG_SQRT_RATIO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                    (\t. (G':real^2->real^1)(wan_circ x0 (drop r) ((th0 - pi) + drop t)))`;
    `\r:real^1. lift(c * inv(drop r))`; `lift(d * R0)`; `lift(sqrt d * R0)`;
    `lift(d * R0) INSERT lift(sqrt d * R0) INSERT ((S:real^1->bool) UNION N UNION N')`]
   WAN_INTEGRAL_STRICT_AE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP; NEGLIGIBLE_INSERT; NEGLIGIBLE_UNION_EQ] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      ASM_MESON_TAC[integrable_on];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; IN_UNION; IN_INTERVAL_1; LIFT_DROP; DE_MORGAN_THM;
                GSYM DROP_EQ] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `d * R0 < drop x /\ drop x < sqrt d * R0 /\ &0 < drop x`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "neg" (MP_TAC o SPEC `drop x`) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE; LIFT_DROP] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`x0:real^2`; `R:real`; `R0:real`; `th0:real`; `drop x`;
                   `y:real^2`; `z:real^2`] WAN_BDRY_ARC_PARAM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
    SUBGOAL_THEN
     `norm((u:real^2->real^K) y - u z) =
      norm(u(wan_circ x0 (drop x) ((th0 - pi) + t2)) - u(wan_circ x0 (drop x) ((th0 - pi) + t1)))`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    USE_THEN "S" (MP_TAC o SPECL [`drop x`; `t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN STRIP_TAC THEN
    USE_THEN "N" (MP_TAC o SPEC `drop x`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LIFT_DROP]; DISCH_TAC] THEN
    ABBREV_TAC
     `J = drop(integral (interval[vec 0,lift(&2 * pi)])
                (\t. (G':real^2->real^1)(wan_circ x0 (drop x) ((th0 - pi) + drop t))))` THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`\s. drop x % (--(sin((th0 - pi) + drop s)) %
                     wan_wd D 1 (u:real^2->real^K) (wan_circ x0 (drop x) ((th0 - pi) + drop s)) +
                     cos((th0 - pi) + drop s) %
                     wan_wd D 2 u (wan_circ x0 (drop x) ((th0 - pi) + drop s)))`;
      `(u:real^2->real^K)(wan_circ x0 (drop x) ((th0 - pi) + t2)) -
       u(wan_circ x0 (drop x) ((th0 - pi) + t1))`;
      `\s. drop x pow 2 *
           (norm(wan_wd D 1 (u:real^2->real^K) (wan_circ x0 (drop x) ((th0 - pi) + drop s))) pow 2 +
            norm(wan_wd D 2 u (wan_circ x0 (drop x) ((th0 - pi) + drop s))) pow 2)`;
      `t1:real`; `t2:real`] WAN_ARC_OSC_BOUND) THEN
    SUBGOAL_THEN `!y. lift(drop x pow 2 * y) = drop x pow 2 % lift y` ASSUME_TAC THENL
     [REWRITE_TAC[LIFT_CMUL]; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2; WAN_TRIG_COMB_SQ]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
    ABBREV_TAC
     `I12 = drop(integral (interval[lift t1,lift t2])
                 (\s. lift(norm(wan_wd D 1 (u:real^2->real^K)
                                  (wan_circ x0 (drop x) ((th0 - pi) + drop s))) pow 2 +
                           norm(wan_wd D 2 u (wan_circ x0 (drop x) ((th0 - pi) + drop s))) pow 2)))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= I12 /\ I12 <= J` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "I12" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
        SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
        ALL_TAC] THEN
      EXPAND_TAC "I12" THEN EXPAND_TAC "J" THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `drop(integral (interval[lift t1,lift t2])
                    (\t. (G':real^2->real^1)(wan_circ x0 (drop x) ((th0 - pi) + drop t))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
        X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
        EXPAND_TAC "G'" THEN
        SUBGOAL_THEN `wan_circ x0 (drop x) ((th0 - pi) + drop s) IN (D:real^2->bool)`
        (fun th -> REWRITE_TAC[th]) THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          EXPAND_TAC "G" THEN REWRITE_TAC[]];
        MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
          EXISTS_TAC `interval[vec 0:real^1,lift(&2 * pi)]` THEN
          ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
          REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * pi * E / log(inv d) = pi * c` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [EXPAND_TAC "c" THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= pi * c` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MP_TAC PI_POS THEN REAL_ARITH_TAC;
        EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `pi * c < (t2 - t1) * drop x pow 2 * J` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `norm((u:real^2->real^K) y - u z) pow 2` THEN CONJ_TAC THENL
       [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP SQRT_POW_2 th)]) THEN
        MATCH_MP_TAC REAL_POW_LT2 THEN ASM_SIMP_TAC[SQRT_POS_LE; ARITH];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(t2 - t1) * drop x pow 2 * I12` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < drop x pow 2 * J` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(t2 - t1) * drop x pow 2 * J <= &0` MP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `c < drop x pow 2 * J` MP_TAC THENL
     [SUBGOAL_THEN `pi * c < pi * (drop x pow 2 * J)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(t2 - t1) * drop x pow 2 * J` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[REAL_LT_LMUL_EQ; PI_POS]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `(drop x * J) * drop x = drop x pow 2 * J` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (interval[lift(d * R0),lift(sqrt d * R0)]) (\r:real^1. lift(c * inv(drop r))) =
    lift(c * log(inv d) / &2)`
  SUBST1_TAC THENL [MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `c * log(inv d) / &2 = &2 * E` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < log(inv d)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Arcs of circles around a boundary point.  With a = wan_circ x0 R th0      *)
(* (so x0 is on sphere(a,R)), the point wan_circ x0 r ((th0 - pi) + t) lies *)
(* in ball(a,R) iff cos t < -(r / 2R) (WAN_CIRC_BDRY_BALL), in cball(a,R)   *)
(* iff cos t <= -(r / 2R); for 0 < r < 2R the arc is the angle interval      *)
(* (T1,T2) with cos T1 = cos T2 = -(r / 2R).  An abstract sup bound for     *)
(* maps of an interval with small oscillation and small square integral.   *)
(* ------------------------------------------------------------------------- *)

let HMD_ARC_DIST2 = prove
 (`!(x0:real^2) R r th0 t.
     norm(wan_circ x0 R th0 - wan_circ x0 r ((th0 - pi) + t)) pow 2 =
     R pow 2 + r pow 2 + &2 * R * r * cos t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wan_circ; VECTOR_ARITH `(x + a) - (x + b):real^N = a - b`] THEN
  REWRITE_TAC[NORM_POW_2; DOT_2; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REWRITE_TAC[REAL_ARITH `(th0 - pi) + t = (th0 + t) - pi`; COS_SUB; SIN_SUB; COS_PI;
              SIN_PI; COS_ADD; SIN_ADD] THEN
  MP_TAC(SPEC `th0:real` SIN_CIRCLE) THEN MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

let HMD_ARC_CBALL = prove
 (`!(x0:real^2) R r th0 t.
     &0 < r /\ &0 < R /\ cos t <= --(r / (&2 * R))
     ==> wan_circ x0 r ((th0 - pi) + t) IN cball(wan_circ x0 R th0,R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_EQ; HMD_ARC_DIST2] THEN
  SUBGOAL_THEN `(&2 * R * r) * cos t <= (&2 * R * r) * --(r / (&2 * R))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * R * r) * --(r / (&2 * R)) = --(r pow 2)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]);;

let HMD_ARC_END_NOT_BALL = prove
 (`!(x0:real^2) R r th0 t.
     &0 < r /\ &0 < R /\ cos t = --(r / (&2 * R))
     ==> ~(wan_circ x0 r ((th0 - pi) + t) IN ball(wan_circ x0 R th0,R))`,
  SIMP_TAC[WAN_CIRC_BDRY_BALL; REAL_LT_REFL]);;

let HMD_ARC_ANGLES = prove
 (`!k. &0 < k /\ k < &1
       ==> ?T1 T2. &0 < T1 /\ T1 < T2 /\ T2 < &2 * pi /\
                   cos T1 = --k /\ cos T2 = --k /\
                   (!t. T1 < t /\ t < T2 ==> cos t < --k) /\
                   (!t. T1 <= t /\ t <= T2 ==> cos t <= --k) /\
                   (!t. &0 <= t /\ t <= &2 * pi /\ cos t < --k ==> T1 < t /\ t < T2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:real` ACS_BOUNDS_LT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `cos(acs k) = k` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_ACS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `al = acs k` THEN
  SUBGOAL_THEN `cos(pi - al) = --k /\ cos(pi + al) = --k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COS_SUB; COS_PI; SIN_PI; REAL_ARITH `pi + al = al + pi`; COS_PERIODIC_PI] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. pi - al < t /\ t < pi + al ==> cos t < --k` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t <= pi` THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `cos(pi - al) = --k`)) THEN
      MATCH_MP_TAC COS_MONO_LT THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `cos t = cos(&2 * pi - t)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&2 * pi - t = --t + &2 * pi`; COS_PERIODIC; COS_NEG];
        ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `cos(pi - al) = --k`)) THEN
      MATCH_MP_TAC COS_MONO_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`pi - al`; `pi + al`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t = pi - al` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    ASM_CASES_TAC `t = pi + al` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) /\ (~q ==> F) ==> p /\ q`) THEN
  CONJ_TAC THEN DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THENL
   [SUBGOAL_THEN `cos(pi - al) <= cos t` MP_TAC THENL
     [MATCH_MP_TAC COS_MONO_LE THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `cos(pi - al) <= cos(&2 * pi - t)` MP_TAC THENL
     [MATCH_MP_TAC COS_MONO_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&2 * pi - t = --t + &2 * pi`; COS_PERIODIC; COS_NEG] THEN
    ASM_REAL_ARITH_TAC]);;

(* A map of an open interval whose oscillation is at most sqrt A and whose   *)
(* square is dominated by an integrable H with integral at most B' is       *)
(* bounded by sqrt(B' / (T2 - T1)) + sqrt A: some point has H below the     *)
(* mean (WAN_INTEGRAL_STRICT_AE), and the oscillation does the rest.         *)

let HMD_SUP_FROM_OSC = prove
 (`!(ff:real->real^K) (H:real->real) T1 T2 A B'.
     T1 < T2 /\ &0 <= A /\
     (!t t'. T1 < t /\ t <= t' /\ t' < T2 ==> norm(ff t' - ff t) pow 2 <= A) /\
     (!s. T1 < s /\ s < T2 ==> norm(ff s) pow 2 <= H s) /\
     (\s. lift(H(drop s))) integrable_on interval[lift T1,lift T2] /\
     drop(integral (interval[lift T1,lift T2]) (\s. lift(H(drop s)))) <= B'
     ==> !t. T1 < t /\ t < T2
             ==> norm(ff t) <= sqrt(B' / (T2 - T1)) + sqrt A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < T2 - T1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?s0. T1 < s0 /\ s0 < T2 /\ H s0 <= B' / (T2 - T1)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LE]) THEN
    MP_TAC(ISPECL [`\s:real^1. lift((H:real->real)(drop s))`;
                   `\s:real^1. lift(B' / (T2 - T1))`; `lift T1`; `lift T2`;
                   `{lift T1, lift T2}`] WAN_INTEGRAL_STRICT_AE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LIFT_DROP; INTEGRABLE_CONST; NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY] THEN
      X_GEN_TAC `x:real^1` THEN
      REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; IN_INSERT; NOT_IN_EMPTY; LIFT_DROP;
                  GSYM DROP_EQ; DE_MORGAN_THM] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `drop x`) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[INTEGRAL_CONST; DROP_CMUL; LIFT_DROP] THEN
    ASM_SIMP_TAC[CONTENT_1; LIFT_DROP; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `(T2 - T1) * B' / (T2 - T1) = B'` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < T2 - T1` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((ff:real->real^K) s0) <= sqrt(B' / (T2 - T1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(H:real->real) s0` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm((ff:real->real^K) t - ff s0) <= sqrt A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_CASES_TAC `s0 <= t` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `norm((ff:real->real^K) t - ff s0) <= sqrt A` THEN
  UNDISCH_TAC `norm((ff:real->real^K) s0) <= sqrt(B' / (T2 - T1))` THEN
  CONV_TAC NORM_ARITH);;

(* ------------------------------------------------------------------------- *)
(* Zero traces on almost every arc.  A continuous map f in W_0 of a          *)
(* disc is the limit of test maps phi_k with |f - phi_k|_{W^{1,2}}^2 <= 2^-k;*)
(* by WAN_ARC_NULL_SEQ and WAN_ARC_ACL, on almost every arc around a        *)
(* boundary point the maps f - phi_k tend to 0 uniformly, and phi_k vanishes *)
(* near the ends of the arc, so f takes arbitrarily small values on the arc. *)
(* ------------------------------------------------------------------------- *)

let HMD_W120_FAST_APPROX = prove
 (`!(s:real^N->bool) (f:real^N->real^K).
     open s /\ wan_w120 s f
     ==> ?phi. (!k. wan_vtest s (phi k)) /\
               (!k. lnorm s (&2) (\x. f x - phi k x) pow 2 +
                    wan_dir s (\x. f x - phi k x) <= inv(&2) pow k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_w120] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g:num->real^N->real^K` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[AND_FORALL_THM; GSYM SKOLEM_THM] THEN X_GEN_TAC `k:num` THEN
  SUBGOAL_THEN `&0 < inv(&2) pow k / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_POW_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2) pow k / &2` o
    GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY] o
    check (fun th -> can (find_term ((=) `wan_dir:(real^N->bool)->(real^N->real^K)->real`))
                         (concl th))) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  SUBGOAL_THEN `&0 < sqrt(inv(&2) pow k / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sqrt(inv(&2) pow k / &2)` o
    GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  EXISTS_TAC `(g:num->real^N->real^K) (N1 + N2)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wan_w12 s (\x. (g:num->real^N->real^K) (N1 + N2) x - f x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_SIMP_TAC[WAN_VTEST_W12; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `lnorm s (&2) (\x. (f:real^N->real^K) x - (g:num->real^N->real^K) (N1 + N2) x) =
                lnorm s (&2) (\x. g (N1 + N2) x - f x)` SUBST1_TAC THENL
   [SUBGOAL_THEN `(\x. (f:real^N->real^K) x - (g:num->real^N->real^K) (N1 + N2) x) =
                  (\x. --(g (N1 + N2) x - f x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; REWRITE_TAC[LNORM_NEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir s (\x. (f:real^N->real^K) x - (g:num->real^N->real^K) (N1 + N2) x) =
                wan_dir s (\x. g (N1 + N2) x - f x)` SUBST1_TAC THENL
   [MATCH_MP_TAC HMC_DIR_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lnorm s (&2) (\x. (g:num->real^N->real^K) (N1 + N2) x - f x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  REMOVE_THEN "N1" (MP_TAC o SPEC `N1 + N2:num`) THEN
  REMOVE_THEN "N2" (MP_TAC o SPEC `N1 + N2:num`) THEN
  REWRITE_TAC[LE_ADD; ARITH_RULE `(N2:num) <= N1 + N2`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a < c / &2 /\ b < c / &2 ==> a + b <= c`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `sqrt(inv(&2) pow k / &2) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    MATCH_MP_TAC(REAL_ARITH `abs x < c ==> x < c`) THEN ASM_REWRITE_TAC[]]);;

(* Points of the arc away from any compact subset of the disc.               *)

let HMD_ARC_ESCAPES = prove
 (`!(a:real^2) R x0 r K.
     &0 < R /\ x0 IN sphere(a,R) /\ &0 < r /\ r < &2 * R /\
     compact K /\ K SUBSET ball(a,R)
     ==> ?y. y IN ball(a,R) INTER sphere(x0,r) /\ ~(y IN K)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `th0:real` o MATCH_MP WAN_SPHERE_ANGLE) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && fst(dest_var(lhs(concl th))) = "a")) THEN
  MP_TAC(SPEC `r / (&2 * R)` HMD_ARC_ANGLES) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < R ==> &0 < &2 * R`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real` (X_CHOOSE_THEN `T2:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(wan_circ x0 r ((th0 - pi) + T1) IN K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x0:real^2`; `R:real`; `r:real`; `th0:real`; `T1:real`]
      HMD_ARC_END_NOT_BALL) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open((:real^2) DIFF K)` MP_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `wan_circ x0 r ((th0 - pi) + T1)`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `ep:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`x0:real^2`; `r:real`; `th0 - pi`] WAN_CIRC_CONT) THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `lift T1`) THEN REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `ep:real`) THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t = T1 + min dl (T2 - T1) / &2` THEN
  SUBGOAL_THEN `T1 < t /\ t < T2 /\ abs(t - T1) < dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `wan_circ x0 r ((th0 - pi) + t)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[WAN_CIRC_BDRY_BALL];
      REWRITE_TAC[IN_SPHERE; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      REWRITE_TAC[WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `lift t`) THEN
    REWRITE_TAC[DIST_LIFT; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "SUBSET" (concl th) &&
      can (find_term ((=) `ep:real`)) (concl th))) THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `wan_circ x0 r ((th0 - pi) + t)`) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The arc estimates.  HMD_ARC_H_FACTS: the W^{1,2} density                  *)
(* |g|^2 + |d_1 g|^2 + |d_2 g|^2, extended by 0 off the disc, has integral  *)
(* lnorm^2 + dir.  HMD_ARC_OSC_K: on a sub-arc where g is absolutely        *)
(* continuous the squared increment is at most 2 pi r^2 times the arc       *)
(* integral of the gradient density.                                         *)
(* ------------------------------------------------------------------------- *)

let HMD_ARC_H_FACTS = prove
 (`!(B:real^2->bool) (C:real^2->bool) (g:real^2->real^K).
     open B /\ B SUBSET C /\ wan_w12 B g
     ==> (\x. lift(if x IN B then norm(g x) pow 2 + norm(wan_wd B 1 g x) pow 2 +
                                  norm(wan_wd B 2 g x) pow 2 else &0)) integrable_on C /\
         drop(integral C (\x. lift(if x IN B
                                   then norm(g x) pow 2 + norm(wan_wd B 1 g x) pow 2 +
                                        norm(wan_wd B 2 g x) pow 2 else &0))) =
         lnorm B (&2) g pow 2 + wan_dir B g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(norm((g:real^2->real^K) x) pow 2)) integrable_on B /\
    (\x. lift(norm(wan_wd B 1 (g:real^2->real^K) x) pow 2)) integrable_on B /\
    (\x. lift(norm(wan_wd B 2 (g:real^2->real^K) x) pow 2)) integrable_on B`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    ASM_SIMP_TAC[WAN_W12_IMP_LSPACE; WAN_WD_WORKS; DIMINDEX_2; ARITH; ETA_AX];
    ALL_TAC] THEN
  ABBREV_TAC
   `F0 = \x. lift(norm((g:real^2->real^K) x) pow 2) +
             lift(norm(wan_wd B 1 g x) pow 2) + lift(norm(wan_wd B 2 g x) pow 2)` THEN
  SUBGOAL_THEN `(F0:real^2->real^1) integrable_on B` ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN REPEAT(MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN B
        ==> lift(if x IN B then norm((g:real^2->real^K) x) pow 2 +
                                norm(wan_wd B 1 g x) pow 2 + norm(wan_wd B 2 g x) pow 2
                 else &0) = (F0:real^2->real^1) x`
  ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN SIMP_TAC[LIFT_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(if x IN B then norm((g:real^2->real^K) x) pow 2 +
                             norm(wan_wd B 1 g x) pow 2 + norm(wan_wd B 2 g x) pow 2
              else &0)) integrable_on B`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_EQ THEN EXISTS_TAC `F0:real^2->real^1` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ON_SUPERSET THEN EXISTS_TAC `B:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral C (\x. lift(if x IN B then norm((g:real^2->real^K) x) pow 2 +
                                       norm(wan_wd B 1 g x) pow 2 +
                                       norm(wan_wd B 2 g x) pow 2 else &0)) =
    integral B (F0:real^2->real^1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `integral B (\x. lift(if x IN B then norm((g:real^2->real^K) x) pow 2 +
                                         norm(wan_wd B 1 g x) pow 2 +
                                         norm(wan_wd B 2 g x) pow 2 else &0))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC HMC_INTEGRAL_SUPPORT_SUBSET THEN
      EXISTS_TAC `B:real^2->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL; IN_DIFF] THEN
      SIMP_TAC[LIFT_NUM];
      MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "F0" THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_ADD; DROP_ADD] THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ; WAN_W12_IMP_LSPACE] THEN
  REWRITE_TAC[wan_dir; DIMINDEX_2; SUM_2] THEN REAL_ARITH_TAC);;

let HMD_ARC_OSC_K = prove
 (`!(B:real^2->bool) (g:real^2->real^K) x0 al r t t' J.
     &0 < r /\ &0 <= t /\ t <= t' /\ t' <= &2 * pi /\
     ((\s. r % (--(sin(al + drop s)) % wan_wd B 1 g (wan_circ x0 r (al + drop s)) +
                cos(al + drop s) % wan_wd B 2 g (wan_circ x0 r (al + drop s))))
      has_integral (g(wan_circ x0 r (al + t')) - g(wan_circ x0 r (al + t))))
     (interval[lift t,lift t']) /\
     (\s. lift(norm(wan_wd B 1 g (wan_circ x0 r (al + drop s))) pow 2 +
               norm(wan_wd B 2 g (wan_circ x0 r (al + drop s))) pow 2))
     integrable_on interval[lift t,lift t'] /\
     drop(integral (interval[lift t,lift t'])
            (\s. lift(norm(wan_wd B 1 g (wan_circ x0 r (al + drop s))) pow 2 +
                      norm(wan_wd B 2 g (wan_circ x0 r (al + drop s))) pow 2))) <= J
     ==> norm(g(wan_circ x0 r (al + t')) - g(wan_circ x0 r (al + t))) pow 2
         <= &2 * pi * r pow 2 * J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `I0 = drop(integral (interval[lift t,lift t'])
               (\s. lift(norm(wan_wd B 1 (g:real^2->real^K)
                                (wan_circ x0 r (al + drop s))) pow 2 +
                         norm(wan_wd B 2 g (wan_circ x0 r (al + drop s))) pow 2)))` THEN
  SUBGOAL_THEN `&0 <= I0` ASSUME_TAC THENL
   [EXPAND_TAC "I0" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. r % (--(sin(al + drop s)) % wan_wd B 1 (g:real^2->real^K)
                                        (wan_circ x0 r (al + drop s)) +
              cos(al + drop s) % wan_wd B 2 g (wan_circ x0 r (al + drop s)))`;
    `(g:real^2->real^K)(wan_circ x0 r (al + t')) - g(wan_circ x0 r (al + t))`;
    `\s. r pow 2 *
         (norm(wan_wd B 1 (g:real^2->real^K) (wan_circ x0 r (al + drop s))) pow 2 +
          norm(wan_wd B 2 g (wan_circ x0 r (al + drop s))) pow 2)`;
    `t:real`; `t':real`] WAN_ARC_OSC_BOUND) THEN
  SUBGOAL_THEN `!y. lift(r pow 2 * y) = r pow 2 % lift y` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2; WAN_TRIG_COMB_SQ]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * pi) * r pow 2 * I0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_POS; PI_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Good radii and the zero-trace lemma.  HMD_ARC_GOOD_RADII: for maps        *)
(* g_k with |g_k|_{W^{1,2}}^2 <= 2^-k, on almost every arc around a boundary *)
(* point some g_k is uniformly small.  HMD_ARC_TRACE: a continuous W_0 map  *)
(* takes arbitrarily small values on almost every such arc.                  *)
(* ------------------------------------------------------------------------- *)

let HMD_ARC_GOOD_RADII = prove
 (`!(a:real^2) R x0 (g:num->real^2->real^K).
     &0 < R /\ x0 IN sphere(a,R) /\
     (!k. g k continuous_on ball(a,R) /\ wan_w12 (ball(a,R)) (g k) /\
          lnorm (ball(a,R)) (&2) (g k) pow 2 + wan_dir (ball(a,R)) (g k) <= inv(&2) pow k)
     ==> ?N. negligible N /\
             !r. &0 < r /\ r < &2 * R /\ ~(lift r IN N)
                 ==> !e. &0 < e
                         ==> ?k. !y. y IN ball(a,R) INTER sphere(x0,r) ==> norm(g k y) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `th0:real` o MATCH_MP WAN_SPHERE_ANGLE) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && fst(dest_var(lhs(concl th))) = "a")) THEN
  ABBREV_TAC `BB = ball(wan_circ x0 R th0,R)` THEN
  ABBREV_TAC
   `h = \k x. if x IN BB
              then norm((g:num->real^2->real^K) k x) pow 2 +
                   norm(wan_wd BB 1 (g k) x) pow 2 + norm(wan_wd BB 2 (g k) x) pow 2
              else &0` THEN
  SUBGOAL_THEN
   `(!k x. &0 <= (h:num->real^2->real) k x) /\
    (!k. (\x. lift(h k x)) integrable_on cball(wan_circ x0 R th0,R)) /\
    (!k. drop(integral (cball(wan_circ x0 R th0,R)) (\x. lift(h k x))) <= inv(&2) pow k)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
      X_GEN_TAC `k:num` THEN
      MP_TAC(ISPECL [`BB:real^2->bool`; `cball(wan_circ x0 R th0,R)`;
                     `(g:num->real^2->real^K) k`] HMD_ARC_H_FACTS) THEN
      EXPAND_TAC "BB" THEN ASM_SIMP_TAC[OPEN_BALL; BALL_SUBSET_CBALL];
      X_GEN_TAC `k:num` THEN
      MP_TAC(ISPECL [`BB:real^2->bool`; `cball(wan_circ x0 R th0,R)`;
                     `(g:num->real^2->real^K) k`] HMD_ARC_H_FACTS) THEN
      EXPAND_TAC "BB" THEN ASM_SIMP_TAC[OPEN_BALL; BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->real^2->real`; `cball(wan_circ x0 R th0,R)`; `x0:real^2`;
                 `th0 - pi`] WAN_ARC_NULL_SEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E1:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E1"))) THEN
  SUBGOAL_THEN
   `?SS:num->real^1->bool.
      !k. negligible (SS k) /\
          !r t1 t2.
            &0 < r /\ ~(lift r IN SS k) /\ &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi /\
            (!t. t1 <= t /\ t <= t2 ==> wan_circ x0 r ((th0 - pi) + t) IN BB)
            ==> ((\s. r % (--(sin((th0 - pi) + drop s)) %
                           wan_wd BB 1 ((g:num->real^2->real^K) k)
                                  (wan_circ x0 r ((th0 - pi) + drop s)) +
                           cos((th0 - pi) + drop s) %
                           wan_wd BB 2 (g k) (wan_circ x0 r ((th0 - pi) + drop s))))
                 has_integral (g k (wan_circ x0 r ((th0 - pi) + t2)) -
                               g k (wan_circ x0 r ((th0 - pi) + t1))))
                (interval[lift t1,lift t2]) /\
                (\s. lift(norm(wan_wd BB 1 (g k) (wan_circ x0 r ((th0 - pi) + drop s))) pow 2 +
                          norm(wan_wd BB 2 (g k) (wan_circ x0 r ((th0 - pi) + drop s))) pow 2))
                integrable_on interval[lift t1,lift t2]`
  (X_CHOOSE_THEN `SS:num->real^1->bool` (LABEL_TAC "SS")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC WAN_ARC_ACL THEN EXPAND_TAC "BB" THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  EXISTS_TAC `E1 UNION UNIONS {(SS:num->real^1->bool) k | k IN (:num)}` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(lift r IN E1) /\ !k. ~(lift r IN (SS:num->real^1->bool) k)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(lift r IN E1 UNION UNIONS {(SS:num->real^1->bool) k | k IN (:num)})` THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `r / (&2 * R)` HMD_ARC_ANGLES) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < R ==> &0 < &2 * R`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real` (X_CHOOSE_THEN `T2:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!t. T1 < t /\ t < T2 ==> wan_circ x0 r ((th0 - pi) + t) IN BB`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "BB" THEN ASM_SIMP_TAC[WAN_CIRC_BDRY_BALL];
    ALL_TAC] THEN
  USE_THEN "E1" (MP_TAC o SPECL [`r:real`; `T1:real`; `T2:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC HMD_ARC_CBALL THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ABBREV_TAC
   `J = \k. drop(integral (interval[lift T1,lift T2])
                   (\s. lift((h:num->real^2->real) k
                               (wan_circ x0 r ((th0 - pi) + drop s)))))` THEN
  SUBGOAL_THEN
   `(\k. drop(integral (interval[lift T1,lift T2])
                (\s. lift((h:num->real^2->real) k
                            (wan_circ x0 r ((th0 - pi) + drop s)))))) = J`
  SUBST1_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!k. &0 <= (J:num->real) k` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "J" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k t. T1 < t /\ t < T2
          ==> norm((g:num->real^2->real^K) k (wan_circ x0 r ((th0 - pi) + t)))
              <= sqrt(J k / (T2 - T1)) + sqrt(&2 * pi * r pow 2 * J k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL [`\t. (g:num->real^2->real^K) k (wan_circ x0 r ((th0 - pi) + t))`;
                   `\t. (h:num->real^2->real) k (wan_circ x0 r ((th0 - pi) + t))`;
                   `T1:real`; `T2:real`; `&2 * pi * r pow 2 * (J:num->real) k`;
                   `(J:num->real) k`] HMD_SUP_FROM_OSC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PI_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MAP_EVERY X_GEN_TAC [`t:real`; `t':real`] THEN STRIP_TAC THEN
      USE_THEN "SS" (MP_TAC o SPECL [`k:num`] ) THEN
      DISCH_THEN(MP_TAC o SPECL [`r:real`; `t:real`; `t':real`] o CONJUNCT2) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      STRIP_TAC THEN MATCH_MP_TAC HMD_ARC_OSC_K THEN EXISTS_TAC `BB:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `drop(integral (interval[lift t,lift t'])
                    (\s. lift((h:num->real^2->real) k
                                (wan_circ x0 r ((th0 - pi) + drop s)))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
          EXISTS_TAC `interval[lift T1,lift T2]` THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
          X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
          SUBGOAL_THEN `wan_circ x0 r ((th0 - pi) + drop s) IN BB` ASSUME_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          EXPAND_TAC "h" THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b + c <= a + b + c`) THEN
          REWRITE_TAC[REAL_LE_POW_2]];
        EXPAND_TAC "J" THEN REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
        ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
          EXISTS_TAC `interval[lift T1,lift T2]` THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `wan_circ x0 r ((th0 - pi) + s) IN BB` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "h" THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ &0 <= c ==> a <= a + b + c`) THEN
      REWRITE_TAC[REAL_LE_POW_2];
      ASM_REWRITE_TAC[];
      EXPAND_TAC "J" THEN REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < T2 - T1 /\ &0 < &2 * pi * r pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[PI_POS; REAL_POW_LT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min ((e / &2) pow 2 * (T2 - T1))
                                   ((e / &2) pow 2 / (&2 * pi * r pow 2))` o
    GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY] o
    check (fun th -> can (find_term ((=) `J:num->real`)) (concl th) &&
                     can (find_term ((=) `sequentially`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (MP_TAC o SPEC `k:num`)) THEN
  REWRITE_TAC[LE_REFL; REAL_SUB_RZERO; REAL_LT_MIN] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN STRIP_TAC THEN
  EXISTS_TAC `k:num` THEN X_GEN_TAC `y:real^2` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_SPHERE_CIRC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` ASSUME_TAC) THEN
  MP_TAC(SPECL [`x0:real^2`; `r:real`; `th0 - pi`; `t0:real`] WAN_CIRC_OFFSET_REP) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `y = wan_circ x0 r ((th0 - pi) + s)` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cos s < --(r / (&2 * R))` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_circ x0 r ((th0 - pi) + s) IN BB` THEN EXPAND_TAC "BB" THEN
    ASM_SIMP_TAC[WAN_CIRC_BDRY_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `T1 < s /\ s < T2` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sqrt((J:num->real) k / (T2 - T1)) + sqrt(&2 * pi * r pow 2 * J k)` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a < e / &2 /\ b < e / &2 ==> a + b < e`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
  (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
    ONCE_REWRITE_TAC[REAL_ARITH `&2 * pi * r pow 2 * j = (&2 * pi * r pow 2) * j`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]]);;

let HMD_ARC_TRACE = prove
 (`!(a:real^2) R x0 (f:real^2->real^K).
     &0 < R /\ x0 IN sphere(a,R) /\ f continuous_on ball(a,R) /\ wan_w120 (ball(a,R)) f
     ==> ?N. negligible N /\
             !r. &0 < r /\ r < &2 * R /\ ~(lift r IN N)
                 ==> !e. &0 < e
                         ==> ?y. y IN ball(a,R) INTER sphere(x0,r) /\ norm(f y) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(a:real^2,R)`; `f:real^2->real^K`] HMD_W120_FAST_APPROX) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wan_w12 (ball(a,R)) (f:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w120]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `R:real`; `x0:real^2`;
                 `\k x. (f:real^2->real^K) x - (phi:num->real^2->real^K) k x`] HMD_ARC_GOOD_RADII) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[ETA_AX] THEN X_GEN_TAC `k:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
      ASM_MESON_TAC[wan_vtest];
      MATCH_MP_TAC WAN_W12_SUB THEN ASM_SIMP_TAC[WAN_VTEST_W12; OPEN_BALL; ETA_AX]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:real^1->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term ((=) `wan_vtest:(real^2->bool)->(real^2->real^K)->bool`)) (concl th))) THEN
  REWRITE_TAC[wan_vtest] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^2->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`a:real^2`; `R:real`; `x0:real^2`; `r:real`; `K:real^2->bool`]
                HMD_ARC_ESCAPES) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^2` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(phi:num->real^2->real^K) k y = vec 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
    can (find_term ((=) `e:real`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Interior tools for the boundary estimate: eps-regularity at the           *)
(* centre of a ball inside the domain (HMC_GRAD_BOUND on the small ball,     *)
(* local energy), the mean value theorem along a segment from bounds on the *)
(* two partial derivatives, and the normal segment at a boundary point.      *)
(* hmd_epsreg S G e0 C is CM_EPS_REG's conclusion for one target.            *)
(* ------------------------------------------------------------------------- *)

let hmd_epsreg = new_definition
 `hmd_epsreg (S:real^K->bool) (G:real^K->real^K^K) e0 (C:num->real) <=>
    &0 < e0 /\ (!k. &0 < C k) /\
    !(a:real^2) r (u:real^2->real^K) l x.
       &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
       wan_gdir (ball(a,r)) G u <= e0 /\
       ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
       ==> r pow (LENGTH l) * norm(iterated_partial l u x)
           <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)`;;

let HMD_EPSREG_FROM = prove
 (`!S (G:real^K->real^K^K) d.
     CM_EPS_REG_STATEMENT (:K) /\ cm_target S G d ==> ?e0 C. hmd_epsreg S G e0 C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CM_EPS_REG_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[hmd_epsreg]);;

let HMD_EPSREG_MONO = prove
 (`!S (G:real^K->real^K^K) e0 C e1.
     hmd_epsreg S G e0 C /\ &0 < e1 /\ e1 <= e0 ==> hmd_epsreg S G e1 C`,
  REWRITE_TAC[hmd_epsreg] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The gradient at the centre of a ball inside the domain is controlled by   *)
(* the energy of any open set between the ball and the domain.               *)

let HMD_GRAD_AT_CENTER = prove
 (`!S (G:real^K->real^K^K) d e0 C (B:real^2->bool) D (w:real^2->real^K) z s i.
     cm_target S G d /\ hmd_epsreg S G e0 C /\ open B /\ open D /\ D SUBSET B /\
     cm_harmonic S G B w /\ wan_w12 B w /\ wan_gdir B G w <= e0 /\
     &0 < s /\ ball(z,s) SUBSET D /\ 1 <= i /\ i <= 2
     ==> s * norm(partial_derivative i w z) <= C 1 * sqrt(wan_gdir D G w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `smooth_map_on B (w:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_harmonic]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(z:real^2,s) SUBSET B` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir D G (w:real^2->real^K) <= wan_gdir B G w` ASSUME_TAC THENL
   [MATCH_MP_TAC HMC_GDIR_MONO THEN EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on D (w:real^2->real^K) /\ wan_w12 D w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `B:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `B:real^2->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(z,s)) G (w:real^2->real^K) <= wan_gdir D G w` ASSUME_TAC THENL
   [MATCH_MP_TAC HMC_GDIR_MONO THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [hmd_epsreg]) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`; `C:num->real`;
                 `Lam:real`; `z:real^2`; `s:real`; `w:real^2->real^K`] HMC_GRAD_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN EXISTS_TAC `B:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `B:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:real^2`; `i:num`]) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; VECTOR_SUB_REFL; NORM_0; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]);;

(* Differentiability of smooth maps on open sets; the derivative through the *)
(* two partials; the mean value theorem along a segment.                     *)

let HMD_SMOOTH_HAS_DERIVATIVE = prove
 (`!(U:real^M->bool) (w:real^M->real^N) z.
     open U /\ smooth_map_on U w /\ z IN U
     ==> (w has_derivative frechet_derivative w (at z)) (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC 0` o GEN_REWRITE_RULE I [smooth_map_on]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON) THEN
  REWRITE_TAC[differentiable_on] THEN DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_WITHIN_OPEN]);;

let HMD_FRECHET_2 = prove
 (`!(w:real^2->real^N) z v.
     w differentiable (at z)
     ==> frechet_derivative w (at z) v =
         v$1 % partial_derivative 1 w z + v$2 % partial_derivative 2 w z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; partial_derivative] THEN
  REWRITE_TAC[DIMINDEX_2; VSUM_2]);;

let HMD_SEGMENT_MVT = prove
 (`!(U:real^2->bool) (w:real^2->real^K) x y L.
     open U /\ smooth_map_on U w /\ segment[x,y] SUBSET U /\
     (!z i. z IN segment[x,y] /\ 1 <= i /\ i <= 2 ==> norm(partial_derivative i w z) <= L)
     ==> norm(w x - w y) <= &2 * L * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`w:real^2->real^K`; `\z. frechet_derivative (w:real^2->real^K) (at z)`;
                 `segment[x:real^2,y]`; `&2 * L`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
   [SUBGOAL_THEN
     `!z. z IN segment[x:real^2,y]
          ==> ((w:real^2->real^K) has_derivative frechet_derivative w (at z)) (at z)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMD_SMOOTH_HAS_DERIVATIVE THEN
      EXISTS_TAC `U:real^2->bool` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THENL
     [ASM_SIMP_TAC[HAS_DERIVATIVE_AT_WITHIN]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2->real^K) differentiable (at z)` ASSUME_TAC THENL
     [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    ASM_SIMP_TAC[ONORM_LE_EQ] THEN X_GEN_TAC `v:real^2` THEN
    ASM_SIMP_TAC[HMD_FRECHET_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((v:real^2)$1) * L + abs(v$2) * L` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(a:real^K) <= x /\ norm(b:real^K) <= y ==> norm(a + b) <= x + y`) THEN
      REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(partial_derivative 1 (w:real^2->real^K) z)` THEN
      REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((v:real^2)$1) <= norm v /\ abs(v$2) <= norm v` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[COMPONENT_LE_NORM]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((v:real^2)$1) * L <= norm v * L /\ abs(v$2) * L <= norm v * L`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]]);;

(* The inner normal segment at a boundary point.                            *)

let HMD_NORMAL_POINT = prove
 (`!(a:real^2) r x1 s.
     &0 < r /\ x1 IN sphere(a,r) /\ &0 <= s /\ s <= r
     ==> norm((x1 + (s / r) % (a - x1)) - x1) = s /\
         norm((x1 + (s / r) % (a - x1)) - a) = r - s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE; dist] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(x1 - a:real^2) = r` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s / r /\ s / r <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `(x1 + c % (a - x1)) - x1:real^2 = c % (a - x1)`;
              VECTOR_ARITH `(x1 + c % (a - x1)) - a:real^2 = (&1 - c) % (x1 - a)`] THEN
  ASM_REWRITE_TAC[NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`;
               REAL_ARITH `x <= &1 ==> abs(&1 - x) = &1 - x`] THEN
  UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The quantitative boundary estimate.  For a harmonic map w of small        *)
(* energy on ball(a,r) with the boundary values of a C^0 /\ W^{1,2} map u    *)
(* (W_0 sense), at the point at distance t < r/2 from the boundary point x1 *)
(* on the inner normal:                                                      *)
(*   |w(x) - u(x1)| <= CQ sqrt(E_G(w; ball(a,r) /\ ball(x1,2t))) + eta,      *)
(* where eta bounds the oscillation of u on cball(a,r) /\ cball(x1,t).       *)
(* Courant-Lebesgue (outside the bad radii of the trace lemma) gives an arc  *)
(* at radius rho in (t/2,t) with small oscillation of w and a point where    *)
(* w - u is small; eps-regularity on the normal segment joins it to x.      *)
(* ------------------------------------------------------------------------- *)

let HMD_SEGMENT_NORMAL = prove
 (`!(a:real^2) r x1 t rho z.
     &0 < r /\ x1 IN sphere(a,r) /\ &0 <= rho /\ rho <= t /\ t <= r /\
     z IN segment[x1 + (t / r) % (a - x1),x1 + (rho / r) % (a - x1)]
     ==> ?s. rho <= s /\ s <= t /\ z = x1 + (s / r) % (a - x1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  EXISTS_TAC `(&1 - u) * t + u * rho` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - u) * (t - rho) ==> rho <= (&1 - u) * t + u * rho`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= u * (t - rho) ==> (&1 - u) * t + u * rho <= t`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % (x1 + a % v) + u % (x1 + b % v):real^2 = x1 + ((&1 - u) * a + u * b) % v`] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD]);;

let HMD_DIV_BOUND1 = prove
 (`!p s t m. &0 < t /\ t <= &2 * s /\ &0 <= p /\ s * p <= m ==> p <= &2 * m / t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * m / t = (&2 * m) / t` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p * &2 * s` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);;

let HMD_DIV_BOUND2 = prove
 (`!m t rho. &0 <= m /\ &0 < t /\ t <= &2 * rho
             ==> &2 * (&2 * m / t) * (t - rho) <= &2 * m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * (&2 * m / t) * (t - rho) = (&2 * m) * ((&2 * (t - rho)) / t)`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let HMD_QBE_SEGMENT = prove
 (`!S (G:real^K->real^K^K) d e0 C (a:real^2) r (w:real^2->real^K) x1 t rho.
     cm_target S G d /\ hmd_epsreg S G e0 C /\ &0 < r /\
     cm_harmonic S G (ball(a,r)) w /\ wan_w12 (ball(a,r)) w /\
     wan_gdir (ball(a,r)) G w <= e0 /\
     x1 IN sphere(a,r) /\ &0 < t /\ &2 * t < r /\ t / &2 < rho /\ rho < t
     ==> norm(w(x1 + (t / r) % (a - x1)) - w(x1 + (rho / r) % (a - x1)))
         <= &2 * C 1 * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `&0 < (C:num->real) 1` ASSUME_TAC THENL
   [ASM_MESON_TAC[hmd_epsreg]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(a,r)) (w:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_harmonic]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open(ball(a:real^2,r) INTER ball(x1,&2 * t)) /\
    ball(a:real^2,r) INTER ball(x1,&2 * t) SUBSET ball(a,r)`
  STRIP_ASSUME_TAC THENL [SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G (w:real^2->real^K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMC_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `m = C 1 * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G
                                 (w:real^2->real^K))` THEN
  SUBGOAL_THEN `&0 <= m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `x1:real^2`; `t:real`] HMD_NORMAL_POINT) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `x1:real^2`; `rho:real`] HMD_NORMAL_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `x1 + (t / r) % (a - x1) IN ball(a:real^2,r) /\
                x1 + (rho / r) % (a - x1) IN ball(a:real^2,r)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (&2 * m / t) *
              norm((x1 + (t / r) % (a - x1)) - (x1 + (rho / r) % (a - x1:real^2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HMD_SEGMENT_MVT THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_BALL]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`z:real^2`; `i:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^2`; `r:real`; `x1:real^2`; `t:real`; `rho:real`; `z:real^2`]
                  HMD_SEGMENT_NORMAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`a:real^2`; `r:real`; `x1:real^2`; `s:real`] HMD_NORMAL_POINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC HMD_DIV_BOUND1 THEN EXISTS_TAC `s:real` THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN EXPAND_TAC "m" THEN
    MATCH_MP_TAC HMD_GRAD_AT_CENTER THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `e0:real`; `ball(a:real^2,r)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; dist] THEN
    X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `norm((x1 + (s / r) % (a - x1)) - x1:real^2) = s` THEN
    UNDISCH_TAC `norm((x1 + (s / r) % (a - x1)) - a:real^2) = r - s` THEN
    UNDISCH_TAC `norm((x1 + (s / r) % (a - x1)) - q:real^2) < s` THEN
    UNDISCH_TAC `s <= t` THEN
    SPEC_TAC(`x1 + (s / r) % (a - x1:real^2)`,`zz:real^2`) THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((x1 + (t / r) % (a - x1)) - (x1 + (rho / r) % (a - x1:real^2))) =
                t - rho` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `(x1 + a % v) - (x1 + b % v):real^2 = (a - b) % v`] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `norm(a - x1:real^2) = r` SUBST1_TAC THENL
     [UNDISCH_TAC `(x1:real^2) IN sphere(a,r)` THEN REWRITE_TAC[IN_SPHERE; dist] THEN
      MESON_TAC[NORM_SUB];
      ALL_TAC] THEN
    SUBGOAL_THEN `t / r - rho / r = (t - rho) / r` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < r ==> abs r = r`;
                 REAL_ARITH `rho < t ==> abs(t - rho) = t - rho`] THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC HMD_DIV_BOUND2 THEN ASM_REAL_ARITH_TAC);;

let HMD_QBE = prove
 (`!S (G:real^K->real^K^K) d e0 C.
     cm_target S G d /\ hmd_epsreg S G e0 C
     ==> ?CQ. &0 < CQ /\
          !(a:real^2) r (u:real^2->real^K) w x1 t eta.
            &0 < r /\ cm_cmap S (ball(a,r)) u /\ cm_harmonic S G (ball(a,r)) w /\
            wan_w12 (ball(a,r)) w /\ wan_gdir (ball(a,r)) G w <= e0 /\
            wan_w120 (ball(a,r)) (\x. w x - u x) /\
            x1 IN sphere(a,r) /\ &0 < t /\ &2 * t < r /\
            (!p. p IN cball(a,r) /\ norm(p - x1) <= t ==> norm(u p - u x1) <= eta)
            ==> norm(w(x1 + (t / r) % (a - x1)) - u x1)
                <= CQ * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G w) + eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [hmd_epsreg]) THEN
  SUBGOAL_THEN `&0 < log(&4)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `CL = sqrt(&2 * pi / (lam * log(&4)))` THEN
  SUBGOAL_THEN `&0 <= CL` ASSUME_TAC THENL
   [EXPAND_TAC "CL" THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    CONJ_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `&2 * C 1 + CL` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `C:num->real`)) (concl th) &&
      not(can (find_term ((=) `iterated_partial:(num)list->(real^2->real^K)->real^2->real^K`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real^K`; `w:real^2->real^K`;
                       `x1:real^2`; `t:real`; `eta:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `D = ball(a:real^2,r) INTER ball(x1,&2 * t)` THEN
  ABBREV_TAC `EG = wan_gdir D G (w:real^2->real^K)` THEN
  SUBGOAL_THEN `open(D:real^2->bool) /\ D SUBSET ball(a,r)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(a,r)) (w:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_harmonic]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2->real^K) continuous_on ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 D (w:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `G:real^K->real^K^K`; `w:real^2->real^K`;
                 `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  (* the trace lemma for w - u *)
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `x1:real^2`; `\x. (w:real^2->real^K) x - u x`]
                HMD_ARC_TRACE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `closure(ball(a:real^2,r))` THEN
    REWRITE_TAC[CLOSURE_SUBSET] THEN ASM_MESON_TAC[cm_cmap];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `NT:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NT"))) THEN
  (* Courant-Lebesgue at x1 *)
  SUBGOAL_THEN `(w:real^2->real^K) continuous_on D` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir D (w:real^2->real^K) <= &2 * EG / (&2 * lam)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * EG / (&2 * lam) = EG / lam` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC `lam * wan_dir D (w:real^2->real^K) <= EG` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * t /\ &0 < inv(&4) /\ inv(&4) < &1` STRIP_ASSUME_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `x1:real^2`; `&2 * t`; `inv(&4)`;
                 `EG / (&2 * lam)`; `w:real^2->real^K`; `NT:real^1->bool`] HMD_CL_AVOID) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(inv(&4)) = inv(&2)` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t / &2 < rho /\ rho < t` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&4 * pi * (EG / (&2 * lam)) / log(&4)) = CL * sqrt EG` ASSUME_TAC THENL
   [EXPAND_TAC "CL" THEN REWRITE_TAC[GSYM SQRT_MUL] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `&0 < log(&4)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* the two normal points *)
  ABBREV_TAC `x = x1 + (t / r) % (a - x1:real^2)` THEN
  ABBREV_TAC `y = x1 + (rho / r) % (a - x1:real^2)` THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `x1:real^2`; `t:real`] HMD_NORMAL_POINT) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `x1:real^2`; `rho:real`] HMD_NORMAL_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN ball(a,r) /\ (y:real^2) IN ball(a,r) INTER sphere(x1,rho)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_BALL; IN_SPHERE; dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* eps-regularity along the normal segment *)
  SUBGOAL_THEN `norm((w:real^2->real^K) x - w y) <= &2 * C 1 * sqrt EG` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"; "EG"; "D"] THEN MATCH_MP_TAC HMD_QBE_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `e0:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* conclusion by an epsilon argument *)
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `dd = norm((w:real^2->real^K) x - (u:real^2->real^K) x1) - ((&2 * C 1 + CL) * sqrt EG + eta)` THEN
  SUBGOAL_THEN `&0 < dd` ASSUME_TAC THENL [EXPAND_TAC "dd" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "NT" (MP_TAC o SPEC `rho:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `norm((w:real^2->real^K) y - w y') <= CL * sqrt EG` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> is_eq(concl th) && lhs(concl th) =
        `sqrt(&4 * pi * (EG / (&2 * lam)) / log(&4))`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((u:real^2->real^K) y' - u x1) <= eta` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(y':real^2) IN ball(a,r) INTER sphere(x1,rho)` THEN
    REWRITE_TAC[IN_INTER; IN_SPHERE] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `norm(y' - x1:real^2) = rho` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[dist; NORM_SUB]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((w:real^2->real^K) x - (u:real^2->real^K) x1) <=
    norm(w x - w y) + norm(w y - w y') + norm(w y' - u y') + norm(u y' - u x1)`
  MP_TAC THENL [CONV_TAC NORM_ARITH; ALL_TAC] THEN
  UNDISCH_TAC `norm((w:real^2->real^K) x - w y) <= &2 * C 1 * sqrt EG` THEN
  UNDISCH_TAC `norm((w:real^2->real^K) y - w y') <= CL * sqrt EG` THEN
  UNDISCH_TAC `norm((w:real^2->real^K) y' - u y') < dd` THEN
  UNDISCH_TAC `norm((u:real^2->real^K) y' - u x1) <= eta` THEN
  UNDISCH_TAC `norm((w:real^2->real^K) x - (u:real^2->real^K) x1) -
               ((&2 * C 1 + CL) * sqrt EG + eta) = dd` THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Continuity up to the boundary.  HMD_ENERGY_UNIF_SMALL: the energy of      *)
(* a smooth W^{1,2} map on the parts of the domain inside small balls is     *)
(* uniformly small (absolute continuity of the integral).  HMD_NORMAL_REP:   *)
(* every point of the disc other than the centre lies on the inner normal of *)
(* its nearest boundary point.  HMD_BDRY_CONT: a harmonic map of small      *)
(* energy with the boundary values of u in the W_0 sense, extended by u on  *)
(* the circle, is continuous on the closed disc.                             *)
(* ------------------------------------------------------------------------- *)

let HMD_MEASURE_BALL_TRANSLATE = prove
 (`!t:real^N c:real^N s. measure(ball(t,s)) = measure(ball(c,s))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `ball(t:real^N,s) = IMAGE (\x. (t - c) + x) (ball(c,s))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM BALL_TRANSLATION; VECTOR_ARITH `(t - c) + c:real^N = t`];
    REWRITE_TAC[MEASURE_TRANSLATION]]);;

let HMD_SMALL_BALLS = prove
 (`!dd. &0 < dd ==> ?rho. &0 < rho /\ !x0:real^2 rho'. &0 < rho' /\ rho' <= rho
                                                        ==> measure(ball(x0,rho')) < dd`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m1 = measure(ball(vec 0:real^2,&1))` THEN
  SUBGOAL_THEN `&0 < m1` ASSUME_TAC THENL
   [EXPAND_TAC "m1" THEN REWRITE_TAC[MEASURE_BALL_POS] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (&1) (dd / (&2 * m1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `measure(ball(x0:real^2,rho')) = measure(ball(vec 0:real^2,rho'))`
  SUBST1_TAC THENL [MATCH_ACCEPT_TAC HMD_MEASURE_BALL_TRANSLATE; ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `rho':real`; `&1`] MEASURE_BALL_SCALING) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_RID; DIMINDEX_2] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `min:real->real->real`))
                                              (concl th))) THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `rho' * m1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dd / (&2 * m1) * m1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    SUBGOAL_THEN `dd / (&2 * m1) * m1 = dd / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < m1` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]]);;

let HMD_ENERGY_UNIF_SMALL = prove
 (`!S (G:real^K->real^K^K) d (B:real^2->bool) (w:real^2->real^K) eps.
     cm_target S G d /\ open B /\ smooth_map_on B w /\ wan_w12 B w /\ &0 < eps
     ==> ?rho. &0 < rho /\
               !x0 rho'. &0 < rho' /\ rho' <= rho
                         ==> wan_gdir (B INTER ball(x0,rho')) G w < eps`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  ABBREV_TAC
   `q = \i x. partial_derivative i (w:real^2->real^K) x dot
              ((G:real^K->real^K^K)(w x) ** partial_derivative i w x)` THEN
  SUBGOAL_THEN `!i x. &0 <= (q:num->real^2->real) i x` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * norm(partial_derivative i (w:real^2->real^K) x) pow 2` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 B (w:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. open t /\ t SUBSET B
        ==> wan_gdir t G (w:real^2->real^K) =
            drop(integral t (\x. lift((q:num->real^2->real) 1 x))) +
            drop(integral t (\x. lift(q 2 x)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:real^2->bool`; `G:real^K->real^K^K`; `w:real^2->real^K`]
                  HMC_GDIR_CLASSICAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
        EXISTS_TAC `B:real^2->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `B:real^2->bool` THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIMINDEX_2; SUM_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift((q:num->real^2->real) i x)) absolutely_integrable_on B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    REWRITE_TAC[DIMINDEX_1] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^2`; `j:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `j = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM drop; LIFT_DROP] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
    EXISTS_TAC `\x. lift(wan_wd B i (w:real^2->real^K) x dot
                         ((G:real^K->real^K^K)(w x) ** wan_wd B i w x))` THEN
    EXISTS_TAC `{x | x IN B /\ ~(wan_wd B i (w:real^2->real^K) x = partial_derivative i w x)}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HMC_WD_CLASSICAL THEN ASM_REWRITE_TAC[DIMINDEX_2];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN EXPAND_TAC "q" THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC HMD_GDIR_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[DIMINDEX_2] THEN REPEAT GEN_TAC THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPECL [`z:real^K`; `xi:real^K`] o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `lam:real`)) (concl th))) THEN
      SUBGOAL_THEN `&0 <= lam * norm(xi:real^K) pow 2` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((q:num->real^2->real) 1 x)`; `B:real^2->bool`; `eps / &2`]
                ABSOLUTELY_CONTINUOUS_INTEGRAL) THEN
  MP_TAC(ISPECL [`\x. lift((q:num->real^2->real) 2 x)`; `B:real^2->bool`; `eps / &2`]
                ABSOLUTELY_CONTINUOUS_INTEGRAL) THEN
  ASM_SIMP_TAC[ARITH; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `min d1 d2` HMD_SMALL_BALLS) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x0:real^2`; `rho':real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x0:real^2`; `rho':real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `measurable(B INTER ball(x0:real^2,rho')) /\
                measure(B INTER ball(x0:real^2,rho')) <= measure(ball(x0,rho'))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_OPEN THEN
      ASM_SIMP_TAC[BOUNDED_INTER; BOUNDED_BALL; OPEN_INTER; OPEN_BALL];
      DISCH_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[MEASURABLE_BALL; INTER_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_gdir (B INTER ball(x0:real^2,rho')) G (w:real^2->real^K) =
    drop(integral (B INTER ball(x0,rho')) (\x. lift((q:num->real^2->real) 1 x))) +
    drop(integral (B INTER ball(x0,rho')) (\x. lift(q 2 x)))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `B INTER ball(x0:real^2,rho')` o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `d1:real`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `B INTER ball(x0:real^2,rho')` o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `d2:real`)) (concl th))) THEN
  REWRITE_TAC[INTER_SUBSET] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `eps / &2`)) (concl th) &&
                                                  not(is_forall(concl th))))) THEN
  REWRITE_TAC[NORM_1] THEN REAL_ARITH_TAC);;

let HMD_NORMAL_REP = prove
 (`!(a:real^2) r x.
     &0 < r /\ x IN ball(a,r) /\ ~(x = a)
     ==> (a + (r / norm(x - a)) % (x - a)) IN sphere(a,r) /\
         x = (a + (r / norm(x - a)) % (x - a)) +
             ((r - norm(x - a)) / r) % (a - (a + (r / norm(x - a)) % (x - a)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL; IN_SPHERE; dist] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x - a:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `a - (a + c % v):real^2 = --(c % v)`; NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < r ==> abs r = r`; REAL_ABS_NORM] THEN
    UNDISCH_TAC `&0 < norm(x - a:real^2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a + c % v) + e % (a - (a + c % v)):real^2 = a + (c - e * c) % v`] THEN
  SUBGOAL_THEN `r / norm(x - a:real^2) - (r - norm(x - a)) / r * r / norm(x - a) = &1`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(x - a:real^2)` THEN UNDISCH_TAC `&0 < r` THEN
    CONV_TAC REAL_FIELD;
    VECTOR_ARITH_TAC]);;

let HMD_BDRY_CONT = prove
 (`!S (G:real^K->real^K^K) d e0 C (a:real^2) r (u:real^2->real^K) w.
     cm_target S G d /\ hmd_epsreg S G e0 C /\
     &0 < r /\ cm_cmap S (ball(a,r)) u /\ cm_harmonic S G (ball(a,r)) w /\
     wan_w12 (ball(a,r)) w /\ wan_gdir (ball(a,r)) G w <= e0 /\
     wan_w120 (ball(a,r)) (\x. w x - u x) /\ (!x. x IN sphere(a,r) ==> w x = u x)
     ==> w continuous_on cball(a,r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`;
                 `C:num->real`] HMD_QBE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CQ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QBE"))) THEN
  SUBGOAL_THEN `smooth_map_on (ball(a,r)) (w:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_harmonic]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2->real^K) continuous_on ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2->real^K) continuous_on cball(a,r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_cmap; CLOSURE_BALL]; ALL_TAC] THEN
  REWRITE_TAC[continuous_on] THEN X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x0:real^2) IN ball(a,r)` THENL
   [UNDISCH_TAC `(w:real^2->real^K) continuous_on ball(a,r)` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `x0:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d0 (r - dist(a:real^2,x0))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x0:real^2) IN ball(a,r)` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x':real^2` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[IN_BALL] THEN
    UNDISCH_TAC `dist(x':real^2,x0) < min d0 (r - dist(a,x0))` THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^2) IN sphere(a,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^2) IN cball(a,r)` THEN UNDISCH_TAC `~((x0:real^2) IN ball(a,r))` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `cball(a:real^2,r)`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `du:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `ball(a:real^2,r)`;
                 `w:real^2->real^K`; `(e / (&4 * CQ)) pow 2`] HMD_ENERGY_UNIF_SMALL) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (du / &2) (min (rho0 / &4) (r / &4))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x':real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^2->real^K) x0 = u x0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(x':real^2) IN sphere(a,r)` THENL
   [SUBGOAL_THEN `(w:real^2->real^K) x' = u x'` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `e / &4` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x':real^2) IN ball(a,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x':real^2) IN cball(a,r)` THEN UNDISCH_TAC `~((x':real^2) IN sphere(a,r))` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = r - norm(x' - a:real^2)` THEN
  SUBGOAL_THEN `&0 < t /\ t <= dist(x',x0:real^2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    UNDISCH_TAC `(x':real^2) IN ball(a,r)` THEN UNDISCH_TAC `(x0:real^2) IN sphere(a,r)` THEN
    REWRITE_TAC[IN_BALL; IN_SPHERE] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x':real^2 = a)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_SUB_REFL; NORM_0; REAL_SUB_RZERO; REAL_LT_MIN]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `x':real^2`] HMD_NORMAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `x1 = a + (r / norm(x' - a)) % (x' - a:real^2)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `norm(x' - x1:real^2) = t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^2`; `r:real`; `x1:real^2`; `t:real`] HMD_NORMAL_POINT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [EXPAND_TAC "t" THEN SIMP_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `x':real^2`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t < du / &2 /\ t < rho0 / &4 /\ t < r / &4 /\
                dist(x',x0:real^2) < du / &2 /\ dist(x',x0:real^2) < rho0 / &4`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dist(x':real^2,x0) < min (du / &2) (min (rho0 / &4) (r / &4))` THEN
    UNDISCH_TAC `t <= dist(x':real^2,x0)` THEN REWRITE_TAC[REAL_LT_MIN] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "QBE" (MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real^K`;
                                  `w:real^2->real^K`; `x1:real^2`; `t:real`; `e / &4`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:real^2` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ONCE_REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x1:real^2) IN sphere(a,r)` THEN
      REWRITE_TAC[IN_SPHERE; IN_CBALL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `x':real^2`)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G (w:real^2->real^K)
                < (e / (&4 * CQ)) pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `CQ * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G (w:real^2->real^K))
                < e / &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G (w:real^2->real^K))
                  < e / (&4 * CQ)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < CQ ==> &0 < &4 * CQ`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((u:real^2->real^K) x1,u x0) < e / &4` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(x0:real^2) IN sphere(a,r)` THEN
      REWRITE_TAC[IN_SPHERE; IN_CBALL] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(x1:real^2) IN sphere(a,r)` THEN
      REWRITE_TAC[IN_SPHERE; IN_CBALL] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `norm(x' - x1:real^2) = t` THEN
      UNDISCH_TAC `dist(x':real^2,x0) < du / &2` THEN
      UNDISCH_TAC `t < du / &2` THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  UNDISCH_TAC `dist((u:real^2->real^K) x1,u x0) < e / &4` THEN
  UNDISCH_TAC `CQ * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G (w:real^2->real^K))
               < e / &4` THEN
  UNDISCH_TAC `norm((w:real^2->real^K) x' - u x1) <=
               CQ * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G w) + e / &4` THEN
  SPEC_TAC(`CQ * sqrt(wan_gdir (ball(a,r) INTER ball(x1,&2 * t)) G (w:real^2->real^K))`,
           `qq:real`) THEN
  REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH);;

