(* ========================================================================= *)
(* Unit pc_p3_s13met (Part 3 proofs; MT Ch 13): the surgery                 *)
(* metric of MT p. 332 on the region {s1 > -1/dl} of the standard initial   *)
(* manifold (s1 = A0 + 4 - d),                                               *)
(*   gS = h^2 phi(s1) [alpha(s1) h^-2 nc^* gN + (1 - alpha(s1)) eta g0],    *)
(* eta = 1 - dl: a smooth Riemannian metric equal to nc^* gN                *)
(* on s1 < 0.  The neck coordinates nc are a diffeomorphism onto annuli.    *)
(* ========================================================================= *)

needs "src/pc_p3_s13fun.ml";;
needs "src/pc_p3_s13rot.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The neck coordinates nc(x) = exp(s1(x)/sqrt 2) x/|x| (with                *)
(* s1 = A0 + 4 - d) and their inverse ncinv(y) = rinv(A0 + 4 - sqrt 2 log|y|) *)
(* y/|y|: a diffeomorphism from {a < s1 < b} onto the annulus                *)
(* exp(a/sqrt 2) < |y| < exp(b/sqrt 2) for b <= A0 + 4.                      *)
(* ========================================================================= *)

let p3s_ncinv = new_definition
 `p3s_ncinv (g0:real^3->real^3^3) (A0:real) (y:real^3) =
    (p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm y)) * inv(norm y)) % y`;;

let P3S_SQRT2_POS = prove
 (`&0 < sqrt(&2)`,
  MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC);;

let P3S_DIST_0 = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> p3_std_dist g0 (vec 0) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `vec 0:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[NORM_0; P3S_RHO_0]);;

let P3S_DIST_POS = prove
 (`!g0 A0 (x:real^3). p3_std_initial g0 A0 /\ ~(x = vec 0) ==> &0 < p3_std_dist g0 x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC P3S_RHO_POS THEN
  EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[NORM_POS_LT]);;

let P3S_NC_NORM = prove
 (`!g0 A0 (x:real^3). ~(x = vec 0)
                      ==> norm(p3_std_nc g0 A0 x) =
                          exp((A0 + &4 - p3_std_dist g0 x) / sqrt(&2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_std_nc; NORM_MUL; REAL_ABS_EXP] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

let P3S_NC_NCINV = prove
 (`!g0 A0 (x:real^3). p3_std_initial g0 A0 /\ ~(x = vec 0)
                      ==> p3s_ncinv g0 A0 (p3_std_nc g0 A0 x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_ncinv] THEN
  ASM_SIMP_TAC[P3S_NC_NORM; LOG_EXP] THEN
  SUBGOAL_THEN `A0 + &4 - sqrt(&2) * (A0 + &4 - p3_std_dist g0 x) / sqrt(&2) =
                p3_std_dist g0 (x:real^3)` SUBST1_TAC THENL
   [MP_TAC P3S_SQRT2_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_RINV_UNIQUE) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p3_std_nc; VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ABBREV_TAC `ee = exp((A0 + &4 - p3_std_dist g0 (x:real^3)) / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < ee` ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < ee` THEN CONV_TAC REAL_FIELD);;

let P3S_NCINV_FACTS = prove
 (`!g0 A0 (y:real^3).
     p3_std_initial g0 A0 /\ ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4
     ==> ~(p3s_ncinv g0 A0 y = vec 0) /\
         norm(p3s_ncinv g0 A0 y) = p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm y)) /\
         p3_std_dist g0 (p3s_ncinv g0 A0 y) = A0 + &4 - sqrt(&2) * log(norm y) /\
         p3_std_nc g0 A0 (p3s_ncinv g0 A0 y) = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = A0 + &4 - sqrt(&2) * log(norm(y:real^3))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = p3s_rad_rinv g0 c` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(p3s_ncinv g0 A0 (y:real^3)) = r` ASSUME_TAC THENL
   [REWRITE_TAC[p3s_ncinv] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p3s_ncinv g0 A0 (y:real^3) = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `norm(p3s_ncinv g0 A0 (y:real^3)) = r` THEN
    ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 (p3s_ncinv g0 A0 (y:real^3)) = c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_ncinv g0 A0 (y:real^3)`]
           P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exp((A0 + &4 - c) / sqrt(&2)) = norm(y:real^3)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(A0 + &4 - c) / sqrt(&2) = log(norm(y:real^3))` SUBST1_TAC THENL
     [UNDISCH_TAC `A0 + &4 - sqrt(&2) * log(norm(y:real^3)) = c` THEN
      MP_TAC P3S_SQRT2_POS THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[EXP_LOG]];
    ALL_TAC] THEN
  REWRITE_TAC[p3_std_nc] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p3s_ncinv] THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < norm(y:real^3)` THEN
  CONV_TAC REAL_FIELD);;

let P3S_LIFT_NORM_SMOOTH = prove
 (`smooth_map_on ((:real^3) DELETE vec 0) (\x:real^3. lift(norm x))`,
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\x:real^3. x`] SMOOTH_MAP_ON_LIFT_NORM) THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_ID; IN_DELETE; IN_UNIV]);;

let P3S_LIFT_LOGNORM_SMOOTH = prove
 (`smooth_map_on ((:real^3) DELETE vec 0) (\x:real^3. lift(log(norm x)))`,
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\x:real^3. lift(norm x)`]
         SMOOTH_MAP_ON_LIFT_LOG) THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; P3S_LIFT_NORM_SMOOTH; IN_DELETE; IN_UNIV; LIFT_DROP] THEN
  REWRITE_TAC[NORM_POS_LT]);;

let P3S_NC_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on ((:real^3) DELETE vec 0) (p3_std_nc g0 A0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p3_std_nc g0 A0 =
    (\x:real^3. drop((\x. lift(exp(drop((\x. inv(sqrt(&2)) %
                                            (lift(A0 + &4) - lift(p3_std_dist g0 x))) x))))
                     x) %
                (drop((\x. lift(inv(drop((\x. lift(norm x)) x)))) x) % x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p3_std_nc; LIFT_DROP; DROP_CMUL; DROP_SUB] THEN
    GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN REWRITE_TAC[P3S_OPEN_PUNCT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_EXP THEN REWRITE_TAC[P3S_OPEN_PUNCT] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[P3S_OPEN_PUNCT] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_CONST] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP P3S_ROT_DIST_SMOOTH th)]);
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_ID] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_INV THEN
    REWRITE_TAC[P3S_OPEN_PUNCT; P3S_LIFT_NORM_SMOOTH; IN_DELETE; IN_UNIV; LIFT_DROP] THEN
    REWRITE_TAC[NORM_EQ_0]]);;

let P3S_NCINV_DOM_OPEN = prove
 (`!A0. open {y:real^3 | ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4}`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\y:real^3. lift(sqrt(&2) * log(norm y))`; `(:real^3) DELETE vec 0`;
                 `{z:real^1 | drop z < A0 + &4}`] CONTINUOUS_OPEN_PREIMAGE) THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; P2C_OPEN_DROP_LT; IN_DELETE; IN_UNIV; IN_ELIM_THM;
              LIFT_DROP] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    REWRITE_TAC[P3S_OPEN_PUNCT; P3S_LIFT_LOGNORM_SMOOTH];
    REWRITE_TAC[]]);;

let P3S_NCINV_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on {y:real^3 | ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4}
                             (p3s_ncinv g0 A0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `W = {y:real^3 | ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4}` THEN
  SUBGOAL_THEN `open(W:real^3->bool) /\ W SUBSET (:real^3) DELETE vec 0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[P3S_NCINV_DOM_OPEN] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p3s_ncinv g0 A0 =
    (\y:real^3. drop((\y. lift(p3s_rad_rinv g0
                     (drop((\y. lift(A0 + &4) - sqrt(&2) % lift(log(norm y))) y)))) y) %
                (drop((\y. lift(inv(drop((\x. lift(norm x)) y)))) y) % y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p3s_ncinv; LIFT_DROP; DROP_CMUL; DROP_SUB; VECTOR_MUL_ASSOC] THEN
    GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`W:real^3->bool`; `{s:real^1 | &0 < drop s}`;
                   `\y:real^3. lift(A0 + &4) - sqrt(&2) % lift(log(norm y))`;
                   `p3s_rad_rinv g0`] SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
    ASM_REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM; DROP_SUB; DROP_CMUL; LIFT_DROP] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        ASM_REWRITE_TAC[P3S_LIFT_LOGNORM_SMOOTH];
        MATCH_MP_TAC P3S_RINV_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[DROP_SUB; DROP_CMUL; LIFT_DROP]];
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_INV THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[P3S_LIFT_NORM_SMOOTH];
      EXPAND_TAC "W" THEN SIMP_TAC[IN_ELIM_THM; NORM_EQ_0]]]);;

let P3S_NC_DIFFEO = prove
 (`!g0 A0 a b.
     p3_std_initial g0 A0 /\ a < b /\ b <= A0 + &4
     ==> diffeomorphism_on
           {x:real^3 | a < A0 + &4 - p3_std_dist g0 x /\ A0 + &4 - p3_std_dist g0 x < b}
           {y:real^3 | exp(a / sqrt(&2)) < norm y /\ norm y < exp(b / sqrt(&2))}
           (p3_std_nc g0 A0) (p3s_ncinv g0 A0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `V = {x:real^3 | a < A0 + &4 - p3_std_dist g0 x /\
                              A0 + &4 - p3_std_dist g0 x < b}` THEN
  ABBREV_TAC `W = {y:real^3 | exp(a / sqrt(&2)) < norm y /\ norm y < exp(b / sqrt(&2))}` THEN
  MP_TAC P3S_SQRT2_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN V ==> ~(x = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3S_DIST_0 th]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN W ==> ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4 /\
                         a < sqrt(&2) * log(norm y) /\ sqrt(&2) * log(norm y) < b`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [MP_TAC(SPEC `a / sqrt(&2)` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `a / sqrt(&2) < log(norm(y:real^3)) /\ log(norm y) < b / sqrt(&2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[EXP_LOG];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN
    SUBGOAL_THEN `a < sqrt(&2) * log(norm(y:real^3)) /\ sqrt(&2) * log(norm y) < b`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `a / sqrt(&2) < log(norm(y:real^3))` THEN
      UNDISCH_TAC `log(norm(y:real^3)) < b / sqrt(&2)` THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN V ==> p3_std_nc g0 A0 x IN W` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN V` THEN MAP_EVERY EXPAND_TAC ["V"; "W"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[P3S_NC_NORM; REAL_EXP_MONO_LT; REAL_LT_DIV2_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN W ==> p3s_ncinv g0 A0 y IN V /\ p3_std_nc g0 A0 (p3s_ncinv g0 A0 y) = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      can (term_match [] `!y:real^3. y IN W ==> ~(y = vec 0) /\ P y`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_NCINV_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN V ==> p3s_ncinv g0 A0 (p3_std_nc g0 A0 x) = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_NC_NCINV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `V = {x:real^3 | x IN (:real^3) DELETE vec 0 /\
                      lift(A0 + &4 - p3_std_dist g0 x) IN {z:real^1 | a < drop z /\ drop z < b}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; IN_UNIV; LIFT_DROP] THEN
      X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
       [DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:real^3) IN V` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM];
        EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[P3S_OPEN_PUNCT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      REWRITE_TAC[REAL_ARITH `a + b - c = (a + b) - c:real`; LIFT_SUB] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_CONST] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP P3S_ROT_DIST_SMOOTH th)]);
      REWRITE_TAC[SET_RULE `{z:real^1 | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
      MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_OPEN_DROP_LT]];
    SUBGOAL_THEN
     `W = {y:real^3 | y IN (:real^3) /\
                      lift(norm y) IN {z:real^1 | exp(a / sqrt(&2)) < drop z /\
                                                  drop z < exp(b / sqrt(&2))}}`
    SUBST1_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV; LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[OPEN_UNIV] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
      REWRITE_TAC[SET_RULE `{z:real^1 | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
      MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_OPEN_DROP_LT]];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `p3s_ncinv g0 A0 (y:real^3)` THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `p3_std_nc g0 A0 (x:real^3)` THEN ASM_SIMP_TAC[]];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[P3S_NC_SMOOTH] THEN REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{y:real^3 | ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4}` THEN
    ASM_SIMP_TAC[P3S_NCINV_SMOOTH] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* The surgery metric gS and its basic identities.                          *)
(* ========================================================================= *)

let p3s_gs = new_definition
 `p3s_gs (g0:real^3->real^3^3) (A0:real) (c:real) (q:real) (r0:real) (dl:real)
         (h:real) (gN:real^3->real^3^3) (x:real^3) =
    (h pow 2 * p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 x)) %%
    ((if A0 + &4 - p3_std_dist g0 x < &3
      then p3s_alpha (A0 + &4 - p3_std_dist g0 x) %%
           (inv(h pow 2) %% mpullback (p3_std_nc g0 A0) gN x)
      else mat 0) +
     ((&1 - p3s_alpha (A0 + &4 - p3_std_dist g0 x)) * (&1 - dl)) %% g0 x)`;;

let P3S_GS_NEAR = prove
 (`!g0 A0 c q r0 dl h gN (x:real^3).
     &0 < h /\ A0 + &4 - p3_std_dist g0 x < &3
     ==> p3s_gs g0 A0 c q r0 dl h gN x =
         (p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 x) *
          p3s_alpha (A0 + &4 - p3_std_dist g0 x)) %%
         mpullback (p3_std_nc g0 A0) gN x +
         (h pow 2 * p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 x) *
          (&1 - p3s_alpha (A0 + &4 - p3_std_dist g0 x)) * (&1 - dl)) %% g0 x`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[p3s_gs] THEN
  REWRITE_TAC[MATRIX_CMUL_ADD_LDISTRIB; MATRIX_CMUL_ASSOC] THEN
  SUBGOAL_THEN `~(h pow 2 = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ]; ALL_TAC] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(h pow 2 = &0)` THEN CONV_TAC REAL_FIELD);;

let P3S_GS_FAR = prove
 (`!g0 A0 c q r0 dl h gN (x:real^3).
     &2 <= A0 + &4 - p3_std_dist g0 x
     ==> p3s_gs g0 A0 c q r0 dl h gN x =
         (h pow 2 * p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 x) * (&1 - dl)) %% g0 x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_gs] THEN
  MP_TAC P3S_ALPHA THEN DISCH_THEN(MP_TAC o SPEC `A0 + &4 - p3_std_dist g0 (x:real^3)` o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_CMUL_LZERO; COND_ID; MATRIX_ADD_LID; MATRIX_CMUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let P3S_GS_NECK = prove
 (`!g0 A0 c q r0 dl h gN (x:real^3).
     &0 < h /\ &0 < q /\ &0 < r0 /\ r0 <= A0 + &4 /\ A0 + &4 - p3_std_dist g0 x < &0
     ==> p3s_gs g0 A0 c q r0 dl h gN x = mpullback (p3_std_nc g0 A0) gN x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `q:real`; `r0:real`;
                `dl:real`; `h:real`; `gN:real^3->real^3^3`; `x:real^3`] P3S_GS_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`;
                `A0 + &4 - p3_std_dist g0 (x:real^3)`] P3S_PHI_LOW) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0 + &4 - p3_std_dist g0 (x:real^3)`] P3S_F_ZERO) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC P3S_ALPHA THEN DISCH_THEN(MP_TAC o SPEC `A0 + &4 - p3_std_dist g0 (x:real^3)` o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID; REAL_SUB_REFL;
              REAL_MUL_LZERO; MATRIX_CMUL_LZERO; MATRIX_ADD_RID; MATRIX_CMUL_LID]);;

(* ========================================================================= *)
(* gS is a metric field on {s1 > -1/dl}.                                    *)
(* ========================================================================= *)

let P3S_S1_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on ((:real^3) DELETE vec 0)
                             (\x. lift(A0 + &4 - p3_std_dist g0 x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `a + b - c = (a + b) - c:real`; LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_CONST] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP P3S_ROT_DIST_SMOOTH th)]));;

let P3S_S1_COMP_SMOOTH = prove
 (`!g0 A0 (p:real->real) s.
     p3_std_initial g0 A0 /\ open s /\ s SUBSET (:real^3) DELETE vec 0 /\
     smooth_map_on (:real^1) (lift o p o drop)
     ==> smooth_map_on s (\x. lift(p(A0 + &4 - p3_std_dist g0 x)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `(:real^1)`;
                 `\x:real^3. lift(A0 + &4 - p3_std_dist g0 x)`; `p:real->real`]
                SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  ASM_SIMP_TAC[P3S_OPEN_PUNCT; OPEN_UNIV; IN_UNIV; P3S_S1_SMOOTH; LIFT_DROP]);;

let P3S_METRIC_FIELD_COMB = prove
 (`!U (G1:real^N->real^N^N) G2 p q.
     metric_field U G1 /\ metric_field U G2 /\
     smooth_map_on U (\z. lift(p z)) /\ smooth_map_on U (\z. lift(q z)) /\
     (!z. z IN U ==> &0 <= p z /\ &0 <= q z /\ &0 < p z + q z)
     ==> metric_field U (\z. p z %% G1 z + q z %% G2 z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z. p z %% (G1:real^N->real^N^N) z + q z %% G2 z) =
      (\z. drop((\z. lift(p z)) z) % (vectorize o G1) z +
           drop((\z. lift(q z)) z) % (vectorize o G2) z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_ADD; VECTORIZE_CMUL; LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`)) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                    MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RMUL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN
    ASM_CASES_TAC `p(y:real^N) = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]]);;

let P3S_METRIC_FIELD_FMUL = prove
 (`!U (G:real^N->real^N^N) p.
     metric_field U G /\ smooth_map_on U (\z. lift(p z)) /\
     (!z. z IN U ==> &0 < p z)
     ==> metric_field U (\z. p z %% G z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_METRIC_FIELD_EQ THEN
  EXISTS_TAC `\z. (\z:real^N. &0) z %% (G:real^N->real^N^N) z + p z %% G z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3S_METRIC_FIELD_COMB THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; REAL_ADD_LID];
    REWRITE_TAC[MATRIX_CMUL_LZERO; MATRIX_ADD_LID]]);;

let P3S_GS_COEFS = prove
 (`!c q A0 r0 dl h s.
     &0 <= c /\ &0 < q /\ &0 < r0 /\ &0 < dl /\ dl < &1 /\ &0 < h
     ==> &0 <= p3s_phi c q A0 r0 s * p3s_alpha s /\
         &0 <= h pow 2 * p3s_phi c q A0 r0 s * (&1 - p3s_alpha s) * (&1 - dl) /\
         &0 < p3s_phi c q A0 r0 s * p3s_alpha s +
              h pow 2 * p3s_phi c q A0 r0 s * (&1 - p3s_alpha s) * (&1 - dl) /\
         &0 < h pow 2 * p3s_phi c q A0 r0 s * (&1 - dl)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `s:real`] P3S_PHI_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < p3s_phi c q A0 r0 s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `exp(--(&2 * p3s_f c q (A0 + &4)))` THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  MP_TAC P3S_ALPHA THEN DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
     `p3s_phi c q A0 r0 s * p3s_alpha s +
      h pow 2 * p3s_phi c q A0 r0 s * (&1 - p3s_alpha s) * (&1 - dl) =
      p3s_phi c q A0 r0 s *
      (p3s_alpha s * &1 + (&1 - p3s_alpha s) * (h pow 2 * (&1 - dl)))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `min (&1) (h pow 2 * (&1 - dl))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P3S_CONVEX_GE THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3S_TIP_BALL = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> &0 < p3s_rad_rinv g0 r /\
                 !x:real^3. x IN ball(vec 0,p3s_rad_rinv g0 r) ==> p3_std_dist g0 x < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`;
                `p3s_rad_rinv g0 r`] P3S_RHO_LT_EQ) THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]);;

let P3S_GS_FIELD = prove
 (`!g0 A0 c q r0 dl h gN.
     p3_std_initial g0 A0 /\ &0 <= c /\ &0 < q /\ &0 < r0 /\ r0 <= &1 /\
     &0 < dl /\ dl < &1 / &4 /\ &0 < h /\
     metric_field (rfs_neck_dom dl) gN
     ==> metric_field {z:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 z}
                      (p3s_gs g0 A0 c q r0 dl h gN)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  MP_TAC P3S_SQRT2_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `&4 < inv dl` ASSUME_TAC THENL
   [MP_TAC(SPECL [`dl:real`; `&1 / &4`] REAL_LT_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0 / &2`] P3S_TIP_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `rb = p3s_rad_rinv g0 (r0 / &2)` THEN
  (* the three pieces *)
  ABBREV_TAC `PA = {x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x /\
                               A0 + &4 - p3_std_dist g0 x < &3}` THEN
  ABBREV_TAC `PB = {x:real^3 | x IN (:real^3) DELETE vec 0 /\
                               lift(A0 + &4 - p3_std_dist g0 x) IN {w:real^1 | &2 < drop w}}` THEN
  SUBGOAL_THEN `open(PB:real^3->bool) /\ PB SUBSET (:real^3) DELETE vec 0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "PB" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[P3S_OPEN_PUNCT; P2C_OPEN_DROP_GT; SMOOTH_MAP_ON_CONTINUOUS_ON;
                   P3S_S1_SMOOTH];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `--(inv dl)`; `&3`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `open(PA:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `PA SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "PA" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3S_DIST_0 th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field
      {y:real^3 | exp(--(inv dl) / sqrt(&2)) < norm y /\ norm y < exp(&3 / sqrt(&2))} gN`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    REWRITE_TAC[rfs_neck_dom; annulus; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH `a < b ==> c = a ==> c < b`)) THEN
      AP_TERM_TAC THEN UNDISCH_TAC `&0 < dl` THEN MP_TAC P3S_SQRT2_POS THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(&3 / sqrt(&2))` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      SUBGOAL_THEN `inv(sqrt(&2) * dl) = inv dl / sqrt(&2)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < dl` THEN MP_TAC P3S_SQRT2_POS THEN CONV_TAC REAL_FIELD;
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field PA (mpullback (p3_std_nc g0 A0) gN)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`{y:real^3 | exp(--(inv dl) / sqrt(&2)) < norm y /\ norm y < exp(&3 / sqrt(&2))}`;
      `p3s_ncinv g0 A0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{z:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 z} =
      {z | z IN (:real^3) DELETE vec 0 /\
           lift(A0 + &4 - p3_std_dist g0 z) IN {w:real^1 | --(inv dl) < drop w}} UNION
      ball(vec 0,rb)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_DELETE; IN_UNIV; LIFT_DROP] THEN
      X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `x:real^3 = vec 0` THENL
       [ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3S_DIST_0 th]) THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
          can (term_match [] `!x:real^3. x IN ball(vec 0,r) ==> P x`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_UNION THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[P3S_OPEN_PUNCT; P2C_OPEN_DROP_GT; SMOOTH_MAP_ON_CONTINUOUS_ON;
                 P3S_S1_SMOOTH];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `A0 + &4 - p3_std_dist g0 (y:real^3) < &3` THENL
   [EXISTS_TAC `PA:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "PA" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RFB_METRIC_FIELD_EQ THEN
    EXISTS_TAC
     `\x:real^3. (p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 x) *
                  p3s_alpha (A0 + &4 - p3_std_dist g0 x)) %%
                 mpullback (p3_std_nc g0 A0) gN x +
                 (h pow 2 * p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 x) *
                  (&1 - p3s_alpha (A0 + &4 - p3_std_dist g0 x)) * (&1 - dl)) %% g0 x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3S_METRIC_FIELD_COMB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
                      ASM_REWRITE_TAC[SUBSET_UNIV]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                       `\s. p3s_phi c q A0 r0 s * p3s_alpha s`; `PA:real^3->bool`]
                      P3S_S1_COMP_SMOOTH) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV; ETA_AX; P3S_ALPHA] THEN
        MATCH_MP_TAC P3S_PHI_SMOOTH THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                       `\s. h pow 2 * p3s_phi c q A0 r0 s * (&1 - p3s_alpha s) * (&1 - dl)`;
                       `PA:real^3->bool`] P3S_S1_COMP_SMOOTH) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST] THEN
        MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
         [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P3S_PHI_SMOOTH THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST] THEN
          MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX] THEN
          REWRITE_TAC[P3S_ALPHA]];
        X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `dl:real`; `h:real`;
                      `A0 + &4 - p3_std_dist g0 (z:real^3)`] P3S_GS_COEFS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      X_GEN_TAC `x:real^3` THEN EXPAND_TAC "PA" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN MATCH_MP_TAC P3S_GS_NEAR THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `y:real^3 = vec 0` THENL
   [EXISTS_TAC `ball(vec 0:real^3,rb)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MATCH_MP_TAC RFB_METRIC_FIELD_EQ THEN
    EXISTS_TAC `\x:real^3. (h pow 2 * exp(--(&2 * p3s_f c q (A0 + &4))) * (&1 - dl)) %%
                           (g0:real^3->real^3^3) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[OPEN_BALL; SUBSET_UNIV];
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `A0 + &4 - r0 / &2 <= A0 + &4 - p3_std_dist g0 (x:real^3)`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
          can (term_match [] `!x:real^3. x IN ball(vec 0,r) ==> P x`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `q:real`; `r0:real`;
                    `dl:real`; `h:real`; `gN:real^3->real^3^3`; `x:real^3`] P3S_GS_FAR) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`;
                    `A0 + &4 - p3_std_dist g0 (x:real^3)`] P3S_PHI_HIGH) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    EXISTS_TAC `PB:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "PB" THEN REWRITE_TAC[IN_ELIM_THM; IN_DELETE; IN_UNIV; LIFT_DROP] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC RFB_METRIC_FIELD_EQ THEN
    EXISTS_TAC `\x:real^3. (h pow 2 * p3s_phi c q A0 r0 (A0 + &4 - p3_std_dist g0 x) *
                            (&1 - dl)) %% (g0:real^3->real^3^3) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                       `\s. h pow 2 * p3s_phi c q A0 r0 s * (&1 - dl)`;
                       `PB:real^3->bool`] P3S_S1_COMP_SMOOTH) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST] THEN
        MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST] THEN
        REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P3S_PHI_SMOOTH THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `dl:real`; `h:real`;
                      `A0 + &4 - p3_std_dist g0 (z:real^3)`] P3S_GS_COEFS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      X_GEN_TAC `x:real^3` THEN EXPAND_TAC "PB" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DELETE; IN_UNIV; LIFT_DROP] THEN STRIP_TAC THEN
      MATCH_MP_TAC P3S_GS_FAR THEN ASM_REAL_ARITH_TAC]]);;


(* ========================================================================= *)
(* Open-set atlases: a Riemannian metric on open_set_atlas U                 *)
(* is a metric field on U and conversely; gS is a Riemannian metric on       *)
(* open_set_atlas {s1 > -1/dl}.                                             *)
(* ========================================================================= *)

let P3S_OPEN_RIEM_FIELD = prove
 (`!U (g:real^N->real^N^N).
     open U /\ riemannian_metric (open_set_atlas U) g ==> metric_field U g`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U:real^N->bool,(\x:real^N. x))` o
                REWRITE_RULE[riemannian_metric]) THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND; IMAGE_ID] THEN
  DISCH_TAC THEN MATCH_MP_TAC RFB_METRIC_FIELD_EQ THEN
  EXISTS_TAC `metric_local (open_set_atlas U) (U:real^N->bool,(\x:real^N. x)) g` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN ASM_REWRITE_TAC[]);;

let P3S_OPEN_S1 = prove
 (`!g0 A0 a. p3_std_initial g0 A0 /\ a < A0 + &4
             ==> open {z:real^3 | a < A0 + &4 - p3_std_dist g0 z}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &4 - a`] P3S_TIP_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `{z:real^3 | a < A0 + &4 - p3_std_dist g0 z} =
    {z | z IN (:real^3) DELETE vec 0 /\
         lift(A0 + &4 - p3_std_dist g0 z) IN {w:real^1 | a < drop w}} UNION
    ball(vec 0,p3s_rad_rinv g0 (A0 + &4 - a))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_DELETE; IN_UNIV; LIFT_DROP] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `x:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3S_DIST_0 th]) THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
        can (term_match [] `!x:real^3. x IN ball(vec 0,r) ==> P x`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_UNION THEN REWRITE_TAC[OPEN_BALL] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  ASM_SIMP_TAC[P3S_OPEN_PUNCT; P2C_OPEN_DROP_GT; SMOOTH_MAP_ON_CONTINUOUS_ON;
               P3S_S1_SMOOTH]);;

let P3S_GS_RIEMANNIAN = prove
 (`!g0 A0 c q r0 dl h gN.
     p3_std_initial g0 A0 /\ &0 <= c /\ &0 < q /\ &0 < r0 /\ r0 <= &1 /\
     &0 < dl /\ dl < &1 / &4 /\ &0 < h /\
     riemannian_metric (open_set_atlas (rfs_neck_dom dl)) gN
     ==> riemannian_metric
           (open_set_atlas {z:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
           (p3s_gs g0 A0 c q r0 dl h gN)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 < a ==> --x < a + &4`) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ];
    MATCH_MP_TAC P3S_GS_FIELD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[rfs_neck_dom; annulus] THEN
    SUBGOAL_THEN
     `!r1 r2. {x:real^3 | r1 < norm x /\ norm x < r2} =
              {x | x IN (:real^3) /\ lift(norm x) IN {w:real^1 | r1 < drop w /\ drop w < r2}}`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    REWRITE_TAC[OPEN_UNIV; REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM] THEN
    REWRITE_TAC[SET_RULE `{z:real^1 | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
    MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_OPEN_DROP_LT]]);;

