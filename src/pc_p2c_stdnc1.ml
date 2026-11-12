(* ========================================================================= *)
(* Unit pc_p2c_stdnc1 (Part 2C): the time-0 geometry of a standard initial   *)
(* metric g0 needed for the noncollapsing of partial standard flows          *)
(* (P2C_STD_NONCOLL_STATEMENT, pc_p2c_stdncs): good charts stnc_psi of       *)
(* uniformly bounded distortion (the identity on the core d0 <= A0 + 2, the  *)
(* inverse neck coordinates on the cylindrical end, where g0 = nc^* cyl(0) = *)
(* |nc q|^2 (2 / |y|^2) I in the chart), the g0-balls they contain, and the  *)
(* g0-volumes of their images (MFD_AREA_FORMULA).                            *)
(* ========================================================================= *)

needs "src/pc_p2c_stdncs.ml";;
needs "src/pc_p3_s13met.ml";;
needs "src/pc_grg_area.ml";;
needs "src/pc_grg_dist2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Uniform bounds of g0 on the Euclidean balls cball(0,R), from              *)
(* the rotational form (P3S_ROT_FORM, P3S_ROT_TIP) and the continuity and   *)
(* positivity of the radial and tangential coefficients (P3S_ROT_AB).       *)
(* ------------------------------------------------------------------------- *)

let STNC_RAD_COEF_BOUNDS = prove
 (`!g0 A0 R. p3_std_initial g0 A0
     ==> ?lam Lam. &0 < lam /\ lam <= Lam /\
           !r. &0 <= r /\ r <= R
               ==> lam <= p3s_rad_a g0 r /\ p3s_rad_a g0 r <= Lam /\
                   lam <= p3s_rad_b g0 r /\ p3s_rad_b g0 r <= Lam`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  ASM_CASES_TAC `&0 <= R` THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`&1`; `&1`] THEN REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `p3s_rad_a g0 real_continuous_on real_interval[&0,R] /\
                p3s_rad_b g0 real_continuous_on real_interval[&0,R]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_compact(real_interval[&0,R]) /\ ~(real_interval[&0,R] = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p3s_rad_a g0`; `real_interval[&0,R]`] REAL_CONTINUOUS_ATTAINS_INF) THEN
  MP_TAC(ISPECL [`p3s_rad_a g0`; `real_interval[&0,R]`] REAL_CONTINUOUS_ATTAINS_SUP) THEN
  MP_TAC(ISPECL [`p3s_rad_b g0`; `real_interval[&0,R]`] REAL_CONTINUOUS_ATTAINS_INF) THEN
  MP_TAC(ISPECL [`p3s_rad_b g0`; `real_interval[&0,R]`] REAL_CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b1"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b2"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a3"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `r4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a4"))) THEN
  MAP_EVERY EXISTS_TAC [`min (p3s_rad_a g0 r4) (p3s_rad_b g0 r2)`;
                        `max (p3s_rad_a g0 r3) (p3s_rad_b g0 r1)`] THEN
  SUBGOAL_THEN `&0 < p3s_rad_a g0 r4 /\ &0 < p3s_rad_b g0 r2` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p3s_rad_a g0 r4 <= p3s_rad_a g0 r3` ASSUME_TAC THENL
   [USE_THEN "a4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `r IN real_interval[&0,R]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `p3s_rad_a g0 r <= p3s_rad_a g0 r3 /\ p3s_rad_a g0 r4 <= p3s_rad_a g0 r /\
                p3s_rad_b g0 r <= p3s_rad_b g0 r1 /\ p3s_rad_b g0 r2 <= p3s_rad_b g0 r`
  MP_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC]);;

let STNC_CORE_QF = prove
 (`!g0 A0 R. p3_std_initial g0 A0
     ==> ?lam Lam. &0 < lam /\ lam <= Lam /\
           !x v. norm x <= R
                 ==> lam * (v dot v) <= v dot (g0 x ** v) /\
                     v dot (g0 x ** v) <= Lam * (v dot v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `R:real` o MATCH_MP STNC_RAD_COEF_BOUNDS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `lam:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Lam:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ab"))) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= v dot (v:real^3)` ASSUME_TAC THENL [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `v:real^3`; `v:real^3`] P3S_ROT_TIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "ab" (MP_TAC o SPEC `&0`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[NORM_0; REAL_LE_REFL]; STRIP_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `v:real^3`] P3S_ROT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `w = (v dot (x:real^3)) pow 2 / norm x pow 2` THEN
  SUBGOAL_THEN `&0 <= w /\ w <= v dot (v:real^3)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    SUBGOAL_THEN `&0 < norm(x:real^3) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL; GSYM REAL_LE_SQUARE_ABS] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM; NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  USE_THEN "ab" (MP_TAC o SPEC `norm(x:real^3)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LE]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= v dot (v:real^3) - w` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `lam * w <= p3s_rad_a g0 (norm(x:real^3)) * w /\
    p3s_rad_a g0 (norm x) * w <= Lam * w /\
    lam * (v dot v - w) <= p3s_rad_b g0 (norm x) * (v dot (v:real^3) - w) /\
    p3s_rad_b g0 (norm x) * (v dot v - w) <= Lam * (v dot v - w)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The good charts stnc_psi g0 A0 q (a translation on the core              *)
(* d0(q) <= A0 + 2, ncinv o (y -> nc q + |nc q| y) on the end), the facts  *)
(* on the end chart, and D nc (ncinv y) o D ncinv (y) = id.                  *)
(* ------------------------------------------------------------------------- *)

let stnc_psi = new_definition
 `stnc_psi (g0:real^3->real^3^3) (A0:real) (q:real^3) =
    if p3_std_dist g0 q <= A0 + &2 then (\z:real^3. q + z)
    else (\z. p3s_ncinv g0 A0 (p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z))`;;

let STNC_LOG32_BOUND = prove
 (`sqrt(&2) * log(&3 / &2) < &1`,
  SUBGOAL_THEN `log(&3 / &2) <= &1 / &2 /\ sqrt(&2) < &3 / &2 /\ &0 <= log(&3 / &2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `&1 / &2` LOG_LE) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
      MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC LOG_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&3 / &2) * (&1 / &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let STNC_END_FACTS = prove
 (`!g0 A0 (q:real^3) z.
     p3_std_initial g0 A0 /\ A0 + &2 < p3_std_dist g0 q /\ z IN ball(vec 0,&1 / &2)
     ==> ~(q = vec 0) /\ &0 < norm(p3_std_nc g0 A0 q) /\
         norm(p3_std_nc g0 A0 q) < exp(sqrt(&2)) /\
         norm(p3_std_nc g0 A0 q) / &2 <
         norm(p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z) /\
         norm(p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z) <
         &3 / &2 * norm(p3_std_nc g0 A0 q) /\
         ~(p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z = vec 0) /\
         sqrt(&2) * log(norm(p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z)) < &3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) pow 2 = &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`] P3S_NC_NORM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = norm(p3_std_nc g0 A0 (q:real^3))` THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN `&0 < c /\ c < exp(sqrt(&2)) /\
                  sqrt(&2) * log c = A0 + &4 - p3_std_dist g0 (q:real^3)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[th; REAL_EXP_POS_LT; REAL_EXP_MONO_LT; LOG_EXP] THEN
      SUBGOAL_THEN `sqrt(&2) * sqrt(&2) = &2` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM REAL_POW_2]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD];
      ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm(c % (z:real^3)) < c / &2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    UNDISCH_TAC `(z:real^3) IN ball(vec 0,&1 / &2)` THEN
    REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `c * x < c * (&1 / &2) ==> c * x < c / &2`) THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c / &2 < norm(p3_std_nc g0 A0 q + c % (z:real^3)) /\
    norm(p3_std_nc g0 A0 q + c % z) < &3 / &2 * c`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `norm(c % (z:real^3)) < c / &2` THEN
    UNDISCH_TAC `norm(p3_std_nc g0 A0 (q:real^3)) = c` THEN
    SPEC_TAC(`c % (z:real^3)`,`w:real^3`) THEN
    SPEC_TAC(`p3_std_nc g0 A0 (q:real^3)`,`n:real^3`) THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `c / &2 < norm(p3_std_nc g0 A0 q + c % (z:real^3))` THEN
    ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `y = p3_std_nc g0 A0 q + c % (z:real^3)` THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(norm(y:real^3)) < log(&3 / &2) + log c` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LOG_MUL; REAL_ARITH `&0 < &3 / &2`] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC STNC_LOG32_BOUND THEN
  SUBGOAL_THEN `sqrt(&2) * log(norm(y:real^3)) < sqrt(&2) * (log(&3 / &2) + log c)`
  MP_TAC THENL [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC);;

let STNC_NC_NCINV_DERIV = prove
 (`!g0 A0 (y:real^3) v.
     p3_std_initial g0 A0 /\ ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4
     ==> frechet_derivative (p3_std_nc g0 A0) (at (p3s_ncinv g0 A0 y))
           (frechet_derivative (p3s_ncinv g0 A0) (at y) v) = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D = {y:real^3 | ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4}` THEN
  SUBGOAL_THEN `open(D:real^3->bool) /\ (y:real^3) IN D` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[P3S_NCINV_DOM_OPEN; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN D ==> p3_std_nc g0 A0 (p3s_ncinv g0 A0 w) = w /\
                                      ~(p3s_ncinv g0 A0 w = vec 0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `w:real^3`] P3S_NCINV_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p3s_ncinv g0 A0) differentiable (at (y:real^3)) /\
                (p3_std_nc g0 A0) differentiable (at (p3s_ncinv g0 A0 y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN
      MATCH_MP_TAC P3S_NCINV_SMOOTH THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC P3S_NC_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (p3_std_nc g0 A0) (at (p3s_ncinv g0 A0 y)) o
    frechet_derivative (p3s_ncinv g0 A0) (at (y:real^3)) = (\h. h)`
  (fun th -> MP_TAC(AP_THM th `v:real^3`) THEN REWRITE_TAC[o_THM]) THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `p3_std_nc g0 A0 o p3s_ncinv g0 A0` THEN EXISTS_TAC `y:real^3` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\w:real^3. w`; `D:real^3->bool`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN ASM_SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The good charts are smooth on ball(0,1/2), centred at q,                  *)
(* injective, with open images of the balls ball(0,r), r <= 1/2, and their  *)
(* Frechet derivatives.                                                      *)
(* ------------------------------------------------------------------------- *)

let STNC_PSI_CORE = prove
 (`!g0 A0 (q:real^3). p3_std_dist g0 q <= A0 + &2 ==> stnc_psi g0 A0 q = (\z. q + z)`,
  SIMP_TAC[stnc_psi]);;

let STNC_PSI_END = prove
 (`!g0 A0 (q:real^3).
     A0 + &2 < p3_std_dist g0 q
     ==> stnc_psi g0 A0 q =
         (\z. p3s_ncinv g0 A0 (p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stnc_psi; GSYM REAL_NOT_LT] THEN ASM_REWRITE_TAC[]);;

let STNC_NCINV_DOM = prove
 (`!g0 A0 (q:real^3) z.
     p3_std_initial g0 A0 /\ A0 + &2 < p3_std_dist g0 q /\ z IN ball(vec 0,&1 / &2)
     ==> (p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z) IN
         {y:real^3 | ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`] STNC_END_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < A0` MP_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let STNC_PSI_0 = prove
 (`!g0 A0 (q:real^3). p3_std_initial g0 A0 ==> stnc_psi g0 A0 q (vec 0) = q`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p3_std_dist g0 (q:real^3) <= A0 + &2` THENL
   [ASM_SIMP_TAC[STNC_PSI_CORE; VECTOR_ADD_RID]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  ASM_SIMP_TAC[STNC_PSI_END; VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  MATCH_MP_TAC P3S_NC_NCINV THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `vec 0:real^3`]
                STNC_END_FACTS) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]);;

let STNC_PSI_SMOOTH = prove
 (`!g0 A0 (q:real^3). p3_std_initial g0 A0
     ==> smooth_map_on (ball(vec 0,&1 / &2)) (stnc_psi g0 A0 q)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p3_std_dist g0 (q:real^3) <= A0 + &2` THENL
   [ASM_SIMP_TAC[STNC_PSI_CORE] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN ASM_SIMP_TAC[STNC_PSI_END] THEN
  SUBGOAL_THEN
   `(\z. p3s_ncinv g0 A0 (p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z)) =
    p3s_ncinv g0 A0 o (\z:real^3. p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{y:real^3 | ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4}` THEN
  REWRITE_TAC[OPEN_BALL; P3S_NCINV_DOM_OPEN] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC STNC_NCINV_DOM THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC P3S_NCINV_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let STNC_PSI_INJ = prove
 (`!g0 A0 (q:real^3) z z'.
     p3_std_initial g0 A0 /\ z IN ball(vec 0,&1 / &2) /\ z' IN ball(vec 0,&1 / &2) /\
     stnc_psi g0 A0 q z = stnc_psi g0 A0 q z'
     ==> z = z'`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p3_std_dist g0 (q:real^3) <= A0 + &2` THENL
   [ASM_SIMP_TAC[STNC_PSI_CORE; VECTOR_ARITH `(a:real^3) + x = a + y <=> x = y`]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN ASM_SIMP_TAC[STNC_PSI_END] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`] STNC_NCINV_DOM) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z':real^3`] STNC_NCINV_DOM) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`] STNC_END_FACTS) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = norm(p3_std_nc g0 A0 (q:real^3))` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3_std_nc g0 A0 q + c % (z:real^3)`]
                P3S_NCINV_FACTS) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3_std_nc g0 A0 q + c % (z':real^3)`]
                P3S_NCINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3_std_nc g0 A0 q + c % (z:real^3) = p3_std_nc g0 A0 q + c % z'` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `(a:real^3) + x = a + y <=> x = y`; VECTOR_MUL_LCANCEL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

let STNC_PSI_OPEN = prove
 (`!g0 A0 (q:real^3) r.
     p3_std_initial g0 A0 /\ &0 < r /\ r <= &1 / &2
     ==> open(IMAGE (stnc_psi g0 A0 q) (ball(vec 0,r)))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p3_std_dist g0 (q:real^3) <= A0 + &2` THENL
   [ASM_SIMP_TAC[STNC_PSI_CORE] THEN MATCH_MP_TAC OPEN_TRANSLATION THEN
    REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN ASM_SIMP_TAC[STNC_PSI_END] THEN
  ABBREV_TAC `c = norm(p3_std_nc g0 A0 (q:real^3))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `vec 0:real^3`]
                  STNC_END_FACTS) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\z. p3s_ncinv g0 A0 (p3_std_nc g0 A0 q + c % z)) (ball(vec 0:real^3,r)) =
    {x | x IN (:real^3) DELETE vec 0 /\ p3_std_nc g0 A0 x IN ball(p3_std_nc g0 A0 q,c * r)}`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    SIMP_TAC[OPEN_BALL; OPEN_DELETE; OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC P3S_NC_SMOOTH THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_DELETE; IN_UNIV; IN_BALL; IN_BALL_0] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(z:real^3) IN ball(vec 0,&1 / &2)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`]
                  STNC_NCINV_DOM) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3_std_nc g0 A0 q + c % (z:real^3)`]
                  P3S_NCINV_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^3,a + b) = norm b`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_LMUL_EQ];
    STRIP_TAC THEN
    EXISTS_TAC `inv c % (p3_std_nc g0 A0 x - p3_std_nc g0 A0 (q:real^3))` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 VECTOR_ARITH `a + (b - a):real^3 = b`; P3S_NC_NCINV] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    UNDISCH_TAC `dist(p3_std_nc g0 A0 q,p3_std_nc g0 A0 (x:real^3)) < c * r` THEN
    REWRITE_TAC[dist] THEN MESON_TAC[NORM_SUB]]);;

let STNC_PSI_DERIV_CORE = prove
 (`!g0 A0 (q:real^3) z.
     p3_std_dist g0 q <= A0 + &2
     ==> frechet_derivative (stnc_psi g0 A0 q) (at z) = (\h. h)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[STNC_PSI_CORE] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  SUBGOAL_THEN `(\h:real^3. h) = (\h. vec 0 + h)` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID]);;

let STNC_PSI_DERIV_END = prove
 (`!g0 A0 (q:real^3) z.
     p3_std_initial g0 A0 /\ A0 + &2 < p3_std_dist g0 q /\ z IN ball(vec 0,&1 / &2)
     ==> frechet_derivative (stnc_psi g0 A0 q) (at z) =
         (\h. frechet_derivative (p3s_ncinv g0 A0)
                (at (p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z))
                (norm(p3_std_nc g0 A0 q) % h))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[STNC_PSI_END] THEN
  ABBREV_TAC `c = norm(p3_std_nc g0 A0 (q:real^3))` THEN
  ABBREV_TAC `y = p3_std_nc g0 A0 q + c % (z:real^3)` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`] STNC_NCINV_DOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p3s_ncinv g0 A0) differentiable (at (y:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{y:real^3 | ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4}` THEN
    ASM_REWRITE_TAC[P3S_NCINV_DOM_OPEN] THEN MATCH_MP_TAC P3S_NCINV_SMOOTH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  SUBGOAL_THEN
   `(\z. p3s_ncinv g0 A0 (p3_std_nc g0 A0 q + c % z)) =
    p3s_ncinv g0 A0 o (\z:real^3. p3_std_nc g0 A0 q + c % z) /\
    (\h. frechet_derivative (p3s_ncinv g0 A0) (at y) (c % h)) =
    frechet_derivative (p3s_ncinv g0 A0) (at y) o (\h:real^3. c % h)`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\h:real^3. c % h) = (\h. vec 0 + c % h)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;


(* ------------------------------------------------------------------------- *)
(* The distortion bounds of the good charts, uniform in q:                  *)
(* lam |v|^2 <= (Dpsi v) . g0(psi z) (Dpsi v) <= Lam |v|^2 on ball(0,1/2).  *)
(* On the end the form is 2 c^2 |v|^2 / |y|^2 with c/2 < |y| < 3c/2.        *)
(* ------------------------------------------------------------------------- *)

let STNC_CYL0_FORM = prove
 (`!(y:real^3) w. w dot (cylinder_flow (&0) y ** w) = &2 * (w dot w) / norm y pow 2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cylinder_flow; REAL_SUB_RZERO; real_div; REAL_MUL_LZERO] THEN
  REWRITE_TAC[MATRIX_CMUL_LZERO; MATRIX_ADD_RID; MATRIX_CMUL_LID] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN REAL_ARITH_TAC);;

let STNC_END_QF_EQ = prove
 (`!g0 A0 (q:real^3) z v.
     p3_std_initial g0 A0 /\ A0 + &2 < p3_std_dist g0 q /\ z IN ball(vec 0,&1 / &2)
     ==> (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
         (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) =
         &2 * norm(p3_std_nc g0 A0 q) pow 2 * (v dot v) /
         norm(p3_std_nc g0 A0 q + norm(p3_std_nc g0 A0 q) % z) pow 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[STNC_PSI_DERIV_END] THEN
  ASM_SIMP_TAC[STNC_PSI_END] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`] STNC_NCINV_DOM) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`] STNC_END_FACTS) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = norm(p3_std_nc g0 A0 (q:real^3))` THEN
  ABBREV_TAC `y = p3_std_nc g0 A0 q + c % (z:real^3)` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_NCINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = p3s_ncinv g0 A0 (y:real^3)` THEN
  SUBGOAL_THEN `(g0:real^3->real^3^3) x =
                mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)) x` SUBST1_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w = frechet_derivative (p3s_ncinv g0 A0) (at (y:real^3)) (c % v)` THEN
  SUBGOAL_THEN `(p3_std_nc g0 A0) differentiable (at (x:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN
    MATCH_MP_TAC P3S_NC_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix(frechet_derivative (p3_std_nc g0 A0) (at (x:real^3))) ** w = c % v`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `linear(frechet_derivative (p3_std_nc g0 A0) (at (x:real^3)))`
      (fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["w"; "x"] THEN MATCH_MP_TAC STNC_NC_NCINV_DERIV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[STNC_CYL0_FORM] THEN REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let STNC_END_QF = prove
 (`!g0 A0 (q:real^3) z v.
     p3_std_initial g0 A0 /\ A0 + &2 < p3_std_dist g0 q /\ z IN ball(vec 0,&1 / &2)
     ==> &8 / &9 * (v dot v) <=
         (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
         (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) /\
         (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
         (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) <=
         &8 * (v dot v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`; `v:real^3`]
                STNC_END_QF_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STNC_END_FACTS) THEN
  ABBREV_TAC `c = norm(p3_std_nc g0 A0 (q:real^3))` THEN
  ABBREV_TAC `ny = norm(p3_std_nc g0 A0 q + c % (z:real^3))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= v dot (v:real^3)` ASSUME_TAC THENL [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ny` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c pow 2 < &4 * ny pow 2 /\ &4 * ny pow 2 < &9 * c pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `c pow 2 < (&2 * ny) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      SUBGOAL_THEN `(&2 * ny) pow 2 < (&3 * c) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ny pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * c pow 2 * (v dot v) / ny pow 2 =
                ((&2 * c pow 2) / ny pow 2) * (v dot (v:real^3))`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&8 / &9 <= (&2 * c pow 2) / ny pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * c pow 2) / ny pow 2 <= &8` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The core charts (translations, on cball(0, rinv(A0+2) + 1))              *)
(* and the distortion bounds of all good charts, uniform in q.              *)
(* ------------------------------------------------------------------------- *)

let STNC_CORE_RADIUS = prove
 (`!g0 A0 (q:real^3).
     p3_std_initial g0 A0 /\ p3_std_dist g0 q <= A0 + &2
     ==> norm q <= p3s_rad_rinv g0 (A0 + &2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &2`] P3S_RINV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 (A0 + &2)`;
                 `norm(q:real^3)`] P3S_RHO_STRICT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let STNC_QF_WEAKEN = prove
 (`!l L m M a f.
     &0 <= a /\ m <= l /\ L <= M /\ l * a <= f /\ f <= L * a
     ==> m * a <= f /\ f <= M * a`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `l * a` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * a` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

let STNC_CORE_QF_PSI = prove
 (`!g0 A0. p3_std_initial g0 A0
     ==> ?lam Lam. &0 < lam /\ lam <= Lam /\
           !(q:real^3) z v.
              p3_std_dist g0 q <= A0 + &2 /\ z IN ball(vec 0,&1 / &2)
              ==> lam * (v dot v) <=
                  (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
                  (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) /\
                  (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
                  (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v)
                  <= Lam * (v dot v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 (A0 + &2) + &1`]
                STNC_CORE_QF) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `lam:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Lam:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qf"))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`q:real^3`; `z:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[STNC_PSI_DERIV_CORE; STNC_PSI_CORE] THEN
  USE_THEN "qf" MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`] STNC_CORE_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^3) IN ball(vec 0,&1 / &2)` THEN
  REWRITE_TAC[IN_BALL_0] THEN
  SPEC_TAC(`p3s_rad_rinv g0 (A0 + &2)`,`R0:real`) THEN NORM_ARITH_TAC);;

let STNC_PSI_QF = prove
 (`!g0 A0. p3_std_initial g0 A0
     ==> ?lam Lam. &0 < lam /\ lam <= Lam /\
           !(q:real^3) z v.
              z IN ball(vec 0,&1 / &2)
              ==> lam * (v dot v) <=
                  (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
                  (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) /\
                  (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
                  (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v)
                  <= Lam * (v dot v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `l1:real` (X_CHOOSE_THEN `L1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "core")))) o
    MATCH_MP STNC_CORE_QF_PSI) THEN
  MAP_EVERY EXISTS_TAC [`min l1 (&8 / &9)`; `max L1 (&8)`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:real^3`; `z:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= v dot (v:real^3)` ASSUME_TAC THENL [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  ASM_CASES_TAC `p3_std_dist g0 (q:real^3) <= A0 + &2` THENL
   [USE_THEN "core" (MP_TAC o SPECL [`q:real^3`; `z:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN MATCH_MP_TAC STNC_QF_WEAKEN THEN
    MAP_EVERY EXISTS_TAC [`l1:real`; `L1:real`] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`; `v:real^3`]
                  STNC_END_QF) THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN STRIP_TAC THEN MATCH_MP_TAC STNC_QF_WEAKEN THEN
    MAP_EVERY EXISTS_TAC [`&8 / &9`; `&8`] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Chart images of small balls lie in g0-balls.  The curve                  *)
(* t -> psi(t z) on [0,1] is C^1 (GRGD_C1_CURVE_PUSH of the segment), its   *)
(* velocity is Dpsi(t z) z, so its g0-length is at most sqrt(Lam) |z|.      *)
(* ------------------------------------------------------------------------- *)

let STNC_SEG_IN_BALL = prove
 (`!(z:real^3) t r. z IN ball(vec 0,r) /\ t IN real_interval[&0,&1] ==> t % z IN ball(vec 0,r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL_0; NORM_MUL; IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(z:real^3)` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC);;

let STNC_PSI_SEG_VD = prove
 (`!g0 A0 (q:real^3) z t.
     p3_std_initial g0 A0 /\ z IN ball(vec 0,&1 / &2) /\ t IN real_interval[&0,&1]
     ==> vector_derivative (\r. stnc_psi g0 A0 q (drop r % z))
           (at (lift t) within interval[lift(&0),lift(&1)]) =
         frechet_derivative (stnc_psi g0 A0 q) (at (t % z)) z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  SUBGOAL_THEN `(t % z:real^3) IN ball(vec 0,&1 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC STNC_SEG_IN_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(stnc_psi g0 A0 (q:real^3)) differentiable (at (t % z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN
    ASM_SIMP_TAC[OPEN_BALL; STNC_PSI_SMOOTH];
    ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN
   `(\r. stnc_psi g0 A0 q (drop r % z)) = stnc_psi g0 A0 q o (\r:real^1. drop r % (z:real^3)) /\
    (\h:real^1. drop h % frechet_derivative (stnc_psi g0 A0 q) (at (t % z)) z) =
    frechet_derivative (stnc_psi g0 A0 (q:real^3)) (at (t % z)) o (\h. drop h % z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_CMUL THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    REWRITE_TAC[VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC];
    ASM_REWRITE_TAC[LIFT_DROP; GSYM FRECHET_DERIVATIVE_WORKS]]);;

let STNC_PSI_SEG_C1 = prove
 (`!g0 A0 (q:real^3) z.
     p3_std_initial g0 A0 /\ z IN ball(vec 0,&1 / &2)
     ==> mfd_c1_curve (euclidean,open_set_atlas (:real^3))
           (\t. stnc_psi g0 A0 q (t % z)) (&0) (&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. stnc_psi g0 A0 (q:real^3) (t % z)) = stnc_psi g0 A0 q o (\t. t % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] GRGD_C1_CURVE_PUSH) THEN
  MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                        `ball(vec 0:real^3,&1 / &2)`] THEN
  REWRITE_TAC[P2C_EUCLID_FACTS; P2C_SEGMENT_C1; REAL_LT_01; GSYM OPEN_IN; OPEN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[STNC_PSI_SMOOTH];
    REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS; IN_INTER; IN_UNIV] THEN
    REWRITE_TAC[SET_RULE `{x:real^3 | x IN s} = s`] THEN ASM_SIMP_TAC[STNC_PSI_SMOOTH];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC STNC_SEG_IN_BALL THEN ASM_REWRITE_TAC[]]);;

let STNC_PSI_BALL = prove
 (`!g0 A0 lam Lam (q:real^3) rho.
     p3_std_initial g0 A0 /\ &0 < lam /\ lam <= Lam /\
     (!(q:real^3) z v.
        z IN ball(vec 0,&1 / &2)
        ==> lam * (v dot v) <=
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) /\
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v)
            <= Lam * (v dot v)) /\
     &0 < rho /\ rho <= sqrt Lam / &2
     ==> IMAGE (stnc_psi g0 A0 q) (ball(vec 0,rho / sqrt Lam)) SUBSET
         mfd_ball (euclidean,open_set_atlas (:real^3)) g0 q rho`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "qf") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `&0 < Lam /\ &0 < sqrt Lam` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; mfd_ball; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN ball(vec 0,&1 / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `rho / sqrt Lam` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`]
                STNC_PSI_SEG_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_C1_CURVE_JOINABLE) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  ASM_SIMP_TAC[STNC_PSI_0] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `\t. stnc_psi g0 A0 (q:real^3) (t % z)`;
                 `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS; VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  ASM_SIMP_TAC[STNC_PSI_0] THEN
  MATCH_MP_TAC(REAL_ARITH `y < r ==> x <= y ==> x < r`) THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`; `\t. stnc_psi g0 A0 (q:real^3) (t % z)`;
                 `&0`; `&1`] MFD_LENGTH_OPEN_SET_ATLAS) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,&1]) (\t. sqrt Lam * norm(z:real^3))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `g0:real^3->real^3^3`; `\t. stnc_psi g0 A0 (q:real^3) (t % z)`;
                     `&0`; `&1`] MFD_SPEED_CONTINUOUS) THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
      EXISTS_TAC `mfd_speed (open_set_atlas (:real^3)) g0
                    (\t. stnc_psi g0 A0 (q:real^3) (t % z)) (&0) (&1)` THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`;
                     `\t. stnc_psi g0 A0 (q:real^3) (t % z)`; `&0`; `&1`; `t:real`]
                    GRGD_OPEN_SET_SPEED) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`; `z:real^3`; `t:real`]
                  STNC_PSI_SEG_VD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(t % z:real^3) IN ball(vec 0,&1 / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC STNC_SEG_IN_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "qf" (MP_TAC o SPECL [`q:real^3`; `t % z:real^3`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `sqrt Lam * norm(z:real^3) = sqrt(Lam * (z dot z))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; DOT_POS_LE; vector_norm]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS; REAL_SUB_RZERO; REAL_MUL_RID] THEN
    UNDISCH_TAC `norm(z:real^3) < rho / sqrt Lam` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* g0-volumes of chart images, by the area formula.  The                    *)
(* density |det Dpsi| sqrt(det g0(psi)) = sqrt(det(Dpsi^T g0 Dpsi)) lies in  *)
(* [lam^(3/2), Lam^(3/2)] (GRGA_SQRT_DET_QF_LE); psi is injective, so the   *)
(* volume of IMAGE psi (ball(0,r)) is the integral, at least                 *)
(* lam^(3/2) (4/3) pi r^3.                                                   *)
(* ------------------------------------------------------------------------- *)

let STNC_DET_DENSITY = prove
 (`!(M:real^3^3) (G:real^3^3).
     &0 <= det G ==> abs(det M) * sqrt(det G) = sqrt(det(transp M ** G ** M))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DET_MUL; DET_TRANSP] THEN
  SUBGOAL_THEN `det(M:real^3^3) * det(G:real^3^3) * det M = det M pow 2 * det G`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT_ABS]);;

let STNC_PULLBACK_QF = prove
 (`!(f:real^3->real^3) (G:real^3^3) v.
     linear f ==> v dot ((transp(matrix f) ** G ** matrix f) ** v) = (f v) dot (G ** f v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let STNC_SQRT_DET_BOUNDS = prove
 (`!(P:real^3^3) lam Lam.
     symmetric_matrix P /\ &0 < lam /\
     (!v. lam * (v dot v) <= v dot (P ** v) /\ v dot (P ** v) <= Lam * (v dot v))
     ==> lam * sqrt lam <= sqrt(det P) /\ sqrt(det P) <= Lam * sqrt Lam`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "qf"))) THEN
  SUBGOAL_THEN `&0 <= Lam` ASSUME_TAC THENL
   [USE_THEN "qf" (MP_TAC o SPEC `basis 1:real^3`) THEN
    SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `positive_semidefinite(P:real^3^3) /\ positive_semidefinite(mat 1:real^3^3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[positive_semidefinite; symmetric_matrix; TRANSP_MAT; MATRIX_VECTOR_MUL_LID;
                DOT_POS_LE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[symmetric_matrix]) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^3` THEN USE_THEN "qf" (MP_TAC o SPEC `v:real^3`) THEN
    MP_TAC(ISPEC `v:real^3` DOT_POS_LE) THEN
    SUBGOAL_THEN `&0 <= lam * (v dot (v:real^3))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; DOT_POS_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt lam /\ sqrt lam pow 2 = lam /\ sqrt Lam pow 2 = Lam`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`mat 1:real^3^3`; `P:real^3^3`; `inv lam`] GRGA_SQRT_DET_QF_LE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; MATRIX_VECTOR_MUL_LID] THEN
      X_GEN_TAC `w:real^3` THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      USE_THEN "qf" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[DET_I; SQRT_1; DIMINDEX_3; SQRT_INV; REAL_POW_INV] THEN
    ABBREV_TAC `d = sqrt(det(P:real^3^3))` THEN
    ABBREV_TAC `s = sqrt lam` THEN
    SUBGOAL_THEN `lam * s = s pow 3` SUBST1_TAC THENL
     [UNDISCH_TAC `s pow 2 = lam` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `s3 * &1 <= s3 * (inv s3 * d) /\ s3 * (inv s3 * d) = d
                             ==> s3 <= d`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      UNDISCH_TAC `&0 < s pow 3` THEN CONV_TAC REAL_FIELD];
    MP_TAC(ISPECL [`P:real^3^3`; `mat 1:real^3^3`; `Lam:real`] GRGA_SQRT_DET_QF_LE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN GEN_TAC THEN
      USE_THEN "qf" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[DET_I; SQRT_1; DIMINDEX_3; REAL_MUL_RID] THEN
    SUBGOAL_THEN `sqrt Lam pow 3 = Lam * sqrt Lam` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `sqrt Lam pow 2 = Lam` THEN DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN REAL_ARITH_TAC]);;

let STNC_PSI_DENSITY_BOUNDS = prove
 (`!g0 A0 lam Lam (q:real^3) Z.
     p3_std_initial g0 A0 /\ &0 < lam /\ lam <= Lam /\
     (!(q:real^3) z v.
        z IN ball(vec 0,&1 / &2)
        ==> lam * (v dot v) <=
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) /\
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v)
            <= Lam * (v dot v)) /\
     Z IN ball(vec 0,&1 / &2)
     ==> lam * sqrt lam <=
         abs(det(matrix(frechet_derivative (stnc_psi g0 A0 q) (at Z)))) *
         sqrt(det(g0(stnc_psi g0 A0 q Z))) /\
         abs(det(matrix(frechet_derivative (stnc_psi g0 A0 q) (at Z)))) *
         sqrt(det(g0(stnc_psi g0 A0 q Z))) <= Lam * sqrt Lam`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "qf") ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `transp((g0:real^3->real^3^3) (stnc_psi g0 A0 q Z)) = g0 (stnc_psi g0 A0 q Z) /\
    positive_definite(g0 (stnc_psi g0 A0 (q:real^3) Z))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_STD_METRIC_FIELD) THEN
    ASM_REWRITE_TAC[metric_field; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `stnc_psi g0 A0 (q:real^3) Z` o CONJUNCT2 o CONJUNCT2) THEN
    SIMP_TAC[positive_definite; symmetric_matrix];
    ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative (stnc_psi g0 A0 (q:real^3)) (at Z)` THEN
  ABBREV_TAC `G = (g0:real^3->real^3^3) (stnc_psi g0 A0 q Z)` THEN
  SUBGOAL_THEN `linear(D:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN
    ASM_SIMP_TAC[OPEN_BALL; STNC_PSI_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= det(G:real^3^3)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DET_POSITIVE_DEFINITE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[STNC_DET_DENSITY] THEN MATCH_MP_TAC STNC_SQRT_DET_BOUNDS THEN
  ASM_REWRITE_TAC[symmetric_matrix; MATRIX_TRANSP_MUL; TRANSP_TRANSP; GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[STNC_PULLBACK_QF] THEN GEN_TAC THEN
  USE_THEN "qf" (MP_TAC o SPECL [`q:real^3`; `Z:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

let STNC_PSI_DENSITY_CONT = prove
 (`!g0 A0 (q:real^3).
     p3_std_initial g0 A0
     ==> (\Z. lift(abs(det(matrix(frechet_derivative (stnc_psi g0 A0 q) (at Z)))) *
                   sqrt(det(g0(stnc_psi g0 A0 q Z)))))
         continuous_on ball(vec 0,&1 / &2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_3] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_SIMP_TAC[OPEN_BALL; STNC_PSI_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\Z. lift(sqrt(det((g0:real^3->real^3^3) (stnc_psi g0 A0 q Z))))) =
    (lift o sqrt o drop) o (\Z. lift(det(g0(stnc_psi g0 A0 (q:real^3) Z))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_LIFT_SQRT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\Z. lift((g0:real^3->real^3^3) (stnc_psi g0 A0 q Z)$i$j)) =
    (\x. lift(g0 x$i$j)) o stnc_psi g0 A0 (q:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[STNC_PSI_SMOOTH]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_STD_METRIC_FIELD) THEN
  ASM_REWRITE_TAC[metric_field] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[GSYM CONTINUOUS_ON_VECTORIZE_COMPONENTWISE; o_DEF] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`] o
    GEN_REWRITE_RULE I [CONTINUOUS_ON_VECTORIZE_COMPONENTWISE]) THEN
  ASM_REWRITE_TAC[DIMINDEX_3]);;


(* ------------------------------------------------------------------------- *)
(* The volume of IMAGE psi (ball(0,r)) is at least                          *)
(* lam^(3/2) (4/3) pi r^3 (MFD_AREA_FORMULA, equality by injectivity), and *)
(* small g0-balls: vol_g0 B_g0(x,rho) >= c0 rho^3 for rho <= rho0 (N0).     *)
(* ------------------------------------------------------------------------- *)

let STNC_PSI_VOLUME = prove
 (`!g0 A0 lam Lam (q:real^3) r.
     p3_std_initial g0 A0 /\ &0 < lam /\ lam <= Lam /\
     (!(q:real^3) z v.
        z IN ball(vec 0,&1 / &2)
        ==> lam * (v dot v) <=
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v) /\
            (frechet_derivative (stnc_psi g0 A0 q) (at z) v) dot
            (g0 (stnc_psi g0 A0 q z) ** frechet_derivative (stnc_psi g0 A0 q) (at z) v)
            <= Lam * (v dot v)) /\
     &0 < r /\ r <= &1 / &2
     ==> ?v. mfd_has_volume (euclidean,open_set_atlas (:real^3)) g0
               (IMAGE (stnc_psi g0 A0 q) (ball(vec 0,r))) v /\
             lam * sqrt lam * (&4 / &3 * pi * r pow 3) <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "qf") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,r) SUBSET ball(vec 0,&1 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `h = \Z. lift(abs(det(matrix(frechet_derivative (stnc_psi g0 A0 (q:real^3))
                                                              (at Z)))) *
                          sqrt(det((g0:real^3->real^3^3)(stnc_psi g0 A0 q Z))))` THEN
  SUBGOAL_THEN
   `!Z. Z IN ball(vec 0:real^3,&1 / &2)
        ==> lam * sqrt lam <= drop((h:real^3->real^1) Z) /\ drop(h Z) <= Lam * sqrt Lam`
  ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC STNC_PSI_DENSITY_BOUNDS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam * sqrt lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^1) integrable_on ball(vec 0,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\Z:real^3. lift(Lam * sqrt Lam)` THEN
    REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL; LIFT_DROP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "h" THEN MATCH_MP_TAC STNC_PSI_DENSITY_CONT THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(Z:real^3) IN ball(vec 0,&1 / &2)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `h:real^3->real^1`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `norm((h:real^3->real^1) Z) = abs(drop(h Z))` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `stnc_psi g0 A0 (q:real^3)`;
                 `\Z:real^3. frechet_derivative (stnc_psi g0 A0 (q:real^3)) (at Z)`;
                 `ball(vec 0:real^3,r)`] MFD_AREA_FORMULA) THEN
  SIMP_TAC[GRGD_OPEN_SET_CHART_AT; IN_UNIV] THEN REWRITE_TAC[P2C_EUCLID_FACTS] THEN
  REWRITE_TAC[mfd_density] THEN
  SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; OPEN_UNIV; IN_UNIV] THEN
  ASM_REWRITE_TAC[ETA_AX; LEBESGUE_MEASURABLE_BALL; SUBSET_UNIV] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[STNC_PSI_SMOOTH];
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MP_TAC(ISPECL [`ball(vec 0:real^3,&1 / &2)`; `stnc_psi g0 A0 (q:real^3)`]
                    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[OPEN_BALL; STNC_PSI_SMOOTH] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    MP_TAC))) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC STNC_PSI_INJ THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `v:real`)) THEN
  SUBGOAL_THEN `lam * sqrt lam * (&4 / &3 * pi * r pow 3) =
                drop(integral (ball(vec 0:real^3,r)) (\Z. lift(lam * sqrt lam)))`
  SUBST1_TAC THENL
   [SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
    ASM_SIMP_TAC[VOLUME_BALL; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\Z. lift(abs(det(matrix(frechet_derivative (stnc_psi g0 A0 (q:real^3)) (at Z)))) *
              sqrt(det((g0:real^3->real^3^3)(stnc_psi g0 A0 q Z))))) = h`
  SUBST1_TAC THENL [EXPAND_TAC "h" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL; LIFT_DROP] THEN
  X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Z:real^3) IN ball(vec 0,&1 / &2)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `h:real^3->real^1`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let STNC_G0_SMALL_BALLS = prove
 (`!g0 A0. p3_std_initial g0 A0
     ==> ?rho0 c0. &0 < rho0 /\ &0 < c0 /\
           !(x:real^3) rho.
              &0 < rho /\ rho <= rho0
              ==> ?v. mfd_has_volume (euclidean,open_set_atlas (:real^3)) g0
                        (mfd_ball (euclidean,open_set_atlas (:real^3)) g0 x rho) v /\
                      c0 * rho pow 3 <= v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qf")))) o
    MATCH_MP STNC_PSI_QF) THEN
  SUBGOAL_THEN `&0 < Lam /\ &0 < sqrt Lam /\ &0 < sqrt lam` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`sqrt Lam / &2`; `(lam * sqrt lam * (&4 / &3 * pi)) / (Lam * sqrt Lam)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &2`];
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LT_MUL]] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `rho:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho / sqrt Lam /\ rho / sqrt Lam <= &1 / &2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `lam:real`; `Lam:real`; `x:real^3`;
                 `rho / sqrt Lam`] STNC_PSI_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `lam:real`; `Lam:real`; `x:real^3`;
                 `rho:real`] STNC_PSI_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3) /\
                mfd_complete (euclidean,open_set_atlas (:real^3)) g0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `x:real^3`; `rho:real`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN STRIP_TAC THEN
  EXISTS_TAC `mfd_volume (euclidean,open_set_atlas (:real^3)) g0
                (mfd_ball (euclidean,open_set_atlas (:real^3)) g0 x rho)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`;
                 `IMAGE (stnc_psi g0 A0 (x:real^3)) (ball(vec 0,rho / sqrt Lam))`;
                 `mfd_ball (euclidean,open_set_atlas (:real^3)) g0 x rho`;
                 `mfd_volume (euclidean,open_set_atlas (:real^3)) g0
                    (mfd_ball (euclidean,open_set_atlas (:real^3)) g0 x rho)`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN ANTS_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_IMP_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `\x:real^3. &1`; `v0:real`] THEN
    ASM_REWRITE_TAC[GSYM mfd_has_volume; P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_volume (euclidean,open_set_atlas (:real^3)) g0
                  (IMAGE (stnc_psi g0 A0 (x:real^3)) (ball(vec 0,rho / sqrt Lam))) = v0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                          `g0:real^3->real^3^3`;
                          `IMAGE (stnc_psi g0 A0 (x:real^3)) (ball(vec 0,rho / sqrt Lam))`]
                         MFD_HAS_VOLUME_UNIQUE) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v0:real` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lam * sqrt lam * (&4 / &3 * pi * (rho / sqrt Lam) pow 3)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `sqrt Lam pow 2 = Lam` MP_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < sqrt Lam` THEN CONV_TAC REAL_FIELD);;


