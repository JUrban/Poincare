(* ========================================================================= *)
(* Unit pc_p3_s13pinch (Part 3 proofs; MT Ch 13, Prop 13.14 with            *)
(* Cor 13.6 and Cor 13.12): the surgery metric gS is pinched toward        *)
(* positive curvature at time t wherever gN is.  Below s1 = 1 the blend is   *)
(* h^-2 gN itself, gS = nc^*(h^2 e^{-2 cfr(s)} h^-2 gN), and the conformal   *)
(* change satisfies K^ >= min(0, K) on every plane and R^ >= R > 0 (from    *)
(* P3S_NECK_KHAT, P3S_NECK_RHAT; for s <= 0 the factor is 1); the pinching  *)
(* function x (log x + log(1 + t) - 3) then transfers (MT's two cases).     *)
(* Where s1 >= 1 the curvature is positive (pc_p3_s13neck, pc_p3_s13cap),    *)
(* hence pinched.  Headline P3S_PINCH_CLAUSE.                                *)
(*                                                                           *)
(* Contents: the comparison in the neck coordinates; sec_min bounds, the     *)
(* transfer below s1 = 1, the clause.                                        *)
(* ========================================================================= *)

needs "src/pc_p3_s13neck.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Comparison of curvatures on the neck below s = 1 (MT Cor                *)
(* 13.6, 13.12): for e^{-2F} Hn with F = cfr (= f > 0 for s > 0, = 0 for    *)
(* s <= 0), every sectional curvature K^ >= min(0, K) and R^ >= R > 0,     *)
(* when Hn is C^2-close to cyl0; arithmetic for the pinching function.     *)
(* ------------------------------------------------------------------------- *)

let P3S_CONT_ZERO_LEFT = prove
 (`!g. g real_continuous (atreal (&0)) /\ (!t. t < &0 ==> g t = &0) ==> g(&0) = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `g(&0) = &0` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `g real_continuous (atreal (&0))` THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `abs(g(&0))`) THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `--(d / &2)`))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--(d / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_CFR_NEG = prove
 (`!c q A0 r0 s. &0 <= c /\ &0 < q /\ &0 < r0 /\ &0 < A0 /\ r0 <= &1 /\ s <= &0
     ==> p3s_cfr c q A0 r0 s = &0 /\
         real_derivative (p3s_cfr c q A0 r0) s = &0 /\
         real_derivative (real_derivative (p3s_cfr c q A0 r0)) s = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t <= &0 ==> p3s_cfr c q A0 r0 t = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cfr] THEN
    MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `t:real`] P3S_PHI_LOW) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPECL [`c:real`; `q:real`; `t:real`] P3S_F_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; LOG_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`] P3S_CFR_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t < &0 ==> real_derivative (p3s_cfr c q A0 r0) t = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\u:real. &0`; `--t`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t < &0 ==> real_derivative (real_derivative (p3s_cfr c q A0 r0)) t = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\u:real. &0`; `--t`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `s < &0` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^1)`; `real_derivative (p3s_cfr c q A0 r0)`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `real_derivative (real_derivative (p3s_cfr c q A0 r0))`]
         P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC P3S_CONT_ZERO_LEFT THEN ASM_SIMP_TAC[ETA_AX] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THENL
   [EXISTS_TAC `real_derivative (real_derivative (p3s_cfr c q A0 r0)) (&0)`;
    EXISTS_TAC `real_derivative (real_derivative (real_derivative (p3s_cfr c q A0 r0))) (&0)`] THEN
  ASM_REWRITE_TAC[]);;

let P3S_EXP_POW_LOWER = prove
 (`!x n. &0 <= x /\ 1 <= n ==> (x / &n) pow n <= exp x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp x = exp(x / &n) pow n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < &n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x / &n` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

let P3S_XEXP_BOUNDS = prove
 (`!q s. &0 < q /\ &0 < s
     ==> (q / s pow 2) * exp(--(q / s)) <= &4 / q /\
         (q pow 2 / s pow 4) * exp(--(q / s)) <= &256 / q pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x = q / s` THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `q / s pow 2 = x pow 2 / q /\ q pow 2 / s pow 4 = x pow 4 / q pow 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "x" THEN
    UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `2`] P3S_EXP_POW_LOWER) THEN
  MP_TAC(SPECL [`x:real`; `4`] P3S_EXP_POW_LOWER) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < exp x /\ exp x * exp(--x) = &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_NEG_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `x pow 2 / q * exp(--x) = (x pow 2 * exp(--x)) / q` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    SUBGOAL_THEN `x pow 2 * exp(--x) = (&4 * (x / &2) pow 2) * exp(--x)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4 * exp x) * exp(--x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `x pow 4 / q pow 2 * exp(--x) = (x pow 4 * exp(--x)) / q pow 2`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    SUBGOAL_THEN `x pow 4 * exp(--x) = (&256 * (x / &4) pow 4) * exp(--x)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&256 * exp x) * exp(--x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

let P3S_F_BOUNDS01 = prove
 (`!c q s. &0 <= c /\ &8 <= q /\ &0 < s /\ s <= &1
     ==> &0 <= p3s_f c q s /\ p3s_f c q s <= c /\
         &0 <= (q / s pow 2) * p3s_f c q s /\
         &0 <= (q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s /\
         (q / s pow 2) * p3s_f c q s <=
         (&2 / q) * ((q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s) /\
         ((q / s pow 2) * p3s_f c q s) pow 2 <=
         &2 * c * ((q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s) /\
         (q / s pow 2) * p3s_f c q s <= &4 * c / q /\
         (q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s <= &256 * c / q pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p3s_f c q s /\ p3s_f c q s <= c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P3S_F_NONNEG; P3S_F_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `s:real`] P3S_F_D2_LOWER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`q:real`; `s:real`] P3S_XEXP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `f = p3s_f c q s` THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ &0 < s pow 3 /\ &0 < s pow 4 /\ s pow 4 <= s pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN
    SUBGOAL_THEN `s pow 4 = s pow 2 * s pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q pow 2 / (&2 * s pow 4) * f` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q / s pow 2 * f` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 / q) * (q pow 2 / (&2 * s pow 4) * f)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(&2 / q) * (q pow 2 / (&2 * s pow 4) * f) = (q / s pow 4) * f`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&0 < s pow 4` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * c * (q pow 2 / (&2 * s pow 4) * f)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(q / s pow 2 * f) pow 2 = (q pow 2 / s pow 4 * f) * f /\
                    &2 * c * (q pow 2 / (&2 * s pow 4) * f) = (q pow 2 / s pow 4 * f) * c`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [UNDISCH_TAC `&0 < s pow 4` THEN UNDISCH_TAC `&0 < s pow 2` THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `f = c * exp(--(q / s))` SUBST1_TAC THENL
     [EXPAND_TAC "f" THEN MATCH_MP_TAC P3S_F_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * (&4 / q)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `q / s pow 2 * c * exp(--(q / s)) = c * (q / s pow 2 * exp(--(q / s)))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(q pow 2 / s pow 4) * f` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a - b <= a`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `f = c * exp(--(q / s))` SUBST1_TAC THENL
     [EXPAND_TAC "f" THEN MATCH_MP_TAC P3S_F_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * (&256 / q pow 2)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `q pow 2 / s pow 4 * c * exp(--(q / s)) =
                    c * (q pow 2 / s pow 4 * exp(--(q / s)))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]]);;

let P3S_PINCH_SEC_ARITH = prove
 (`!Kh K Kc D sg Dl e Fe.
     abs(K - (&1 - sg) / &2) <= Kc * D /\ &0 <= sg /\ sg <= &1 /\
     K + Dl <= e * Kh /\ &0 < e /\ &1 - &2 * Fe <= e /\ &0 <= Fe /\
     (&1 / &2 <= sg ==> &2 * Fe * (Kc * D) <= Dl /\ &0 <= Dl) /\
     (sg < &1 / &2 ==> &0 < &1 / &4 - Kc * D + Dl)
     ==> min (&0) K <= Kh`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "HI") (LABEL_TAC "LO"))))))))) THEN
  SUBGOAL_THEN `&0 <= K + Dl ==> &0 <= Kh` (LABEL_TAC "POS") THENL
   [DISCH_TAC THEN ASM_CASES_TAC `&0 <= Kh` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e * Kh < &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`; GSYM REAL_MUL_RNEG] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_min] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `&0 <= K + Dl` (fun th -> USE_THEN "POS" (ACCEPT_TAC o C MP th)) THEN
    ASM_CASES_TAC `sg < &1 / &2` THENL
     [REMOVE_THEN "LO" (MP_TAC o C MP (ASSUME `sg < &1 / &2`)) THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&1 / &2 <= sg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "HI" (MP_TAC o C MP (ASSUME `&1 / &2 <= sg`)) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= K + Dl` THENL
   [USE_THEN "POS" (MP_TAC o C MP (ASSUME `&0 <= K + Dl`)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `sg < &1 / &2` THENL
   [REMOVE_THEN "LO" (MP_TAC o C MP (ASSUME `sg < &1 / &2`)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= sg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "HI" (MP_TAC o C MP (ASSUME `&1 / &2 <= sg`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `--K <= Kc * D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - e) * --K <= (&2 * Fe) * --K /\
                (&2 * Fe) * --K <= (&2 * Fe) * (Kc * D)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `e * K <= e * Kh` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

let P3S_PINCH_SCAL_ARITH = prove
 (`!R Rh Dr e. R + Dr <= e * Rh /\ &0 < e /\ e <= &1 /\ &0 <= R /\ &0 <= Dr ==> R <= Rh`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - e) * R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e * R <= e * Rh` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

let P3S_PINCH_FN_ARITH = prove
 (`!R Rh s sh t.
     R <= Rh /\ (sh < &0 ==> s <= sh) /\ &0 < R /\ &0 <= t /\
     -- &6 / (&4 * t + &1) <= R /\
     (&0 < --s ==> &2 * --s * (log(--s) + log(&1 + t) - &3) <= R)
     ==> -- &6 / (&4 * t + &1) <= Rh /\
         (&0 < --sh ==> &2 * --sh * (log(--sh) + log(&1 + t) - &3) <= Rh)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s <= sh /\ &0 < --s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `s <= sh` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `log(--sh) + log(&1 + t) - &3 <= &0` THENL
   [SUBGOAL_THEN `&2 * --sh * (log(--sh) + log(&1 + t) - &3) <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a * b * c <= &0 <=> &0 <= a * b * --c`] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(--sh) <= log(--s)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * --s * (log(--s) + log(&1 + t) - &3)` THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `R:real` THEN ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * --s * (log(--sh) + log(&1 + t) - &3)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC]);;

let P3S_CFR_EQ_F = prove
 (`!c q A0 r0 t. &0 < r0 /\ t <= A0 + &4 - r0 ==> p3s_cfr c q A0 r0 t = p3s_f c q t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cfr] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `t:real`] P3S_PHI_LOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LOG_EXP] THEN REAL_ARITH_TAC);;

let P3S_PINCH_Y_CORE = prove
 (`?Kc Pc. &0 <= Kc /\ &0 <= Pc /\
     !q c D A0 r0 U (Hn:real^3->real^3^3) y.
       &8 <= q /\ &0 <= c /\ c <= &1 / &32 /\ &0 <= D /\ D <= &1 / &212 /\
       Kc * D <= &4 /\ Pc * D < &1 /\ Kc * D + c pow 2 + &40 * D * c < &1 / &4 /\
       &0 < A0 /\ &0 < r0 /\ r0 <= &1 /\
       open U /\ U SUBSET (:real^3) DELETE vec 0 /\ metric_field U Hn /\ y IN U /\
       lck_dist2 2 (cylinder_flow (&0)) Hn y <= D pow 2 /\ p3s_sy y < &1
       ==> &0 < lscalar Hn y /\
           lscalar Hn y <=
           lscalar (\z. exp(--(&2 * p3s_cfr c q A0 r0 (p3s_sy z))) %% Hn z) y /\
           (!u v. ~collinear {vec 0,u,v}
                  ==> min (&0) (lsectional Hn y u v) <=
                      lsectional (\z. exp(--(&2 * p3s_cfr c q A0 r0 (p3s_sy z))) %% Hn z)
                                 y u v)`,
  X_CHOOSE_THEN `Kc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KH")) P3S_NECK_KHAT THEN
  X_CHOOSE_THEN `Pc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RH")) P3S_NECK_RHAT THEN
  MAP_EVERY EXISTS_TAC [`Kc:real`; `Pc:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q /\ D <= &1 / &10` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s0 = p3s_sy (y:real^3)` THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`] P3S_CFR_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^1) (lift o p3s_cfr c q A0 r0 o drop)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_CFR_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!Fr2. Fr2 = real_derivative (real_derivative (p3s_cfr c q A0 r0)) s0 ==>
                (real_derivative (p3s_cfr c q A0 r0) has_real_derivative Fr2)
                (atreal (p3s_sy y))` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s0 <= &0` THENL
   [MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `s0:real`] P3S_CFR_NEG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(real_derivative (p3s_cfr c q A0 r0) has_real_derivative &0)
                  (atreal (p3s_sy y))` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "RH" (MP_TAC o SPECL [`U:real^3->bool`; `Hn:real^3->real^3^3`;
      `p3s_cfr c q A0 r0`; `real_derivative (p3s_cfr c q A0 r0)`; `&0`; `y:real^3`;
      `D:real`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID; REAL_ABS_0;
                REAL_POW_ZERO; ARITH; REAL_ADD_RID; REAL_SUB_RZERO] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`Pc:real`; `D:real`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      REMOVE_THEN "KH" (MP_TAC o SPECL [`U:real^3->bool`; `Hn:real^3->real^3^3`;
        `p3s_cfr c q A0 r0`; `real_derivative (p3s_cfr c q A0 r0)`; `&0`; `y:real^3`;
        `u:real^3`; `v:real^3`; `D:real`]) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID;
                  REAL_ABS_0; REAL_POW_ZERO; ARITH; REAL_ADD_RID; REAL_SUB_RZERO] THEN
      STRIP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `s0:real`] P3S_CFR_LOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `A0:real`; `r0:real`; `s0:real`] P3S_CFR_EQ_F) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `s0:real`] P3S_F_BOUNDS01) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `s0:real`] P3S_F_D2_LOWER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `s0 pow 4 <= &1 /\ &0 < s0 pow 4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_1_LE; MATCH_MP_TAC REAL_POW_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `f = p3s_f c q s0` THEN
  ABBREV_TAC `F1 = (q / s0 pow 2) * f` THEN
  ABBREV_TAC `F2 = (q pow 2 / s0 pow 4 - &2 * q / s0 pow 3) * f` THEN
  SUBGOAL_THEN `q pow 2 / &2 * f <= F2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q pow 2 / (&2 * s0 pow 4) * f` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&32 * f <= q pow 2 / &2 * f` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`2`; `&8`; `q:real`] REAL_POW_LE2) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `F1 <= F2 / &4 /\ F1 pow 2 <= F2 / &16 /\ F1 <= c / &2 /\ F2 <= &4 * c`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&64 <= q pow 2` ASSUME_TAC THENL
     [MP_TAC(SPECL [`2`; `&8`; `q:real`] REAL_POW_LE2) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 / q) * F2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &4) * F2` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
                      ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * c * F2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &16) * F2` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * c / q` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `c * inv q <= c * inv(&8)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&256 * c / q pow 2` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `c * inv(q pow 2) <= c * inv(&64)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(--(&2 * f)) /\ exp(--(&2 * f)) <= &1 /\
                &1 - &2 * f <= exp(--(&2 * f))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `--(&2 * f)` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `F2:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `D * F1 <= D * (F2 / &4) /\ D * F1 pow 2 <= D * (F2 / &16) /\
                D * F2 <= F2 / &212 /\ D * F1 <= D * (c / &2) /\ D * F2 <= D * (&4 * c) /\
                F1 pow 2 <= (c / &2) pow 2 /\ &0 <= D * c /\ D * (c * c) <= D * c /\
                &0 <= F1 pow 2 * D` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `D * F2 <= (&1 / &212) * F2 ==> D * F2 <= F2 / &212`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  REMOVE_THEN "RH" (MP_TAC o SPECL [`U:real^3->bool`; `Hn:real^3->real^3^3`;
    `p3s_cfr c q A0 r0`; `real_derivative (p3s_cfr c q A0 r0)`; `F2:real`; `y:real^3`;
    `D:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= Pc * D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P3S_PINCH_SCAL_ARITH THEN
    MAP_EVERY EXISTS_TAC [`&3 * F2 - &28 * D * F1 - &3 * F1 pow 2`; `exp(--(&2 * f))`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= Pc * D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  REMOVE_THEN "KH" (MP_TAC o SPECL [`U:real^3->bool`; `Hn:real^3->real^3^3`;
    `p3s_cfr c q A0 r0`; `real_derivative (p3s_cfr c q A0 r0)`; `F2:real`; `y:real^3`;
    `u:real^3`; `v:real^3`; `D:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P3S_PINCH_SEC_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`Kc:real`; `D:real`; `sg:real`;
    `F2 * sg - F1 pow 2 * (&1 - sg) - D * (&6 * F1 + &7 * F2 + &9 * F1 pow 2)`;
    `exp(--(&2 * f))`; `f:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= F1 pow 2 * sg /\ &0 <= F2 * sg` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `F2 / &2 <= F2 * sg /\ f * (Kc * D) <= f * &4` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= F2 * (sg - &1 / &2) ==> F2 / &2 <= F2 * sg`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `c:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Lower and upper bounds for mfd_sec_min, the uniform lower               *)
(* bound of the neck sectional curvature, the transfer of pinching through  *)
(* nc below s1 = 1, and the pinching clause of Thm 13.2.                    *)
(* ------------------------------------------------------------------------- *)

let P3S_SECMIN_GE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x c.
     2 <= dimindex(:N) /\
     (!u v. ~collinear {vec 0,u,v} ==> c <= mfd_sectional atlas g x u v)
     ==> c <= mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sec_min] THEN
  MATCH_MP_TAC REAL_LE_INF THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`mfd_sectional (atlas:((A->bool)#(A->real^N))->bool) g x (basis 1) (basis 2)`;
    `basis 1:real^N`; `basis 2:real^N`] THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
    MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
    X_GEN_TAC `k:real` THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. v$2`) THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= 2 /\ 2 <= dimindex(:N) /\ 1 <= dimindex(:N)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC]);;

let P3S_SECMIN_LE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x b u v.
     (!u v. ~collinear {vec 0,u,v} ==> b <= mfd_sectional atlas g x u v) /\
     ~collinear {vec 0,u,v}
     ==> mfd_sec_min atlas g x <= mfd_sectional atlas g x u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sec_min] THEN
  MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC [`b:real`;
    `mfd_sectional (atlas:((A->bool)#(A->real^N))->bool) g x u v`] THEN
  REWRITE_TAC[REAL_LE_REFL; FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN
  ASM_REWRITE_TAC[]);;

let P3S_HN_SECT_LOWER = prove
 (`?Kc. &0 <= Kc /\
        !U (Hn:real^3->real^3^3) y D u v.
          open U /\ U SUBSET (:real^3) DELETE vec 0 /\ metric_field U Hn /\ y IN U /\
          &0 <= D /\ D <= &1 / &10 /\ lck_dist2 2 (cylinder_flow (&0)) Hn y <= D pow 2 /\
          ~collinear {vec 0,u,v}
          ==> --(Kc * D) <= lsectional Hn y u v`,
  X_CHOOSE_THEN `Kc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KH")) P3S_NECK_KHAT THEN
  EXISTS_TAC `Kc:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "KH" (MP_TAC o SPECL [`U:real^3->bool`; `Hn:real^3->real^3^3`;
    `\t:real. &0`; `\t:real. &0`; `&0`; `y:real^3`; `u:real^3`; `v:real^3`; `D:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    SUBGOAL_THEN `(lift o (\t:real. &0) o drop) = (\x:real^1. lift(&0))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` STRIP_ASSUME_TAC) THEN ASM_REAL_ARITH_TAC);;

let P3S_ANN_GEN = prove
 (`!a b y:real^3. exp(a / sqrt(&2)) < norm y /\ norm y < exp(b / sqrt(&2))
                  ==> ~(y = vec 0) /\ a < p3s_sy y /\ p3s_sy y < b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN
    MP_TAC(SPEC `a / sqrt(&2)` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[P3S_SY_EQ] THEN
  MP_TAC P3S_SQRT2_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `a / sqrt(&2) < log(norm(y:real^3)) /\ log(norm y) < b / sqrt(&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(&2) * (a / sqrt(&2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(&2) * (b / sqrt(&2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD]]);;

let P3S_MIN_DIV = prove
 (`!A B k. &0 < k /\ min (&0) A <= B ==> min (&0) (A / k) <= B / k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_min] THEN
  ASM_CASES_TAC `&0 <= A` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `&0 <= A / k` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `~(&0 <= A / k)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ]]);;

let P3S_MIN_LE_IMP = prove
 (`!s sh. min (&0) s <= sh ==> sh < &0 ==> s <= sh`,
  REWRITE_TAC[real_min] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

let P3S_PINCH_NECK = prove
 (`!g0 A0 q C0. p3_std_initial g0 A0 /\ &8 <= q /\ &0 < C0
     ==> ?dm. &0 < dm /\ dm <= &1 / &4 /\
          !r0 dl h gN t (x:real^3).
            &0 < r0 /\ r0 <= &1 /\ &0 < dl /\ dl <= dm /\ &0 < h /\ &0 <= t /\
            riemannian_metric (open_set_atlas (rfs_neck_dom dl)) gN /\
            rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                         (\y. inv(h pow 2) %% gN y) /\
            (!y. y IN rfs_neck_dom dl
                 ==> rfs_pinched_at (open_set_atlas (rfs_neck_dom dl)) gN t y) /\
            --(inv dl) < A0 + &4 - p3_std_dist g0 x /\ A0 + &4 - p3_std_dist g0 x < &1
            ==> rfs_pinched_at
                  (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                  (p3s_gs g0 A0 (C0 * dl) q r0 dl h gN) t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `Pc:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CORE")))) P3S_PINCH_Y_CORE THEN
  X_CHOOSE_THEN `Kl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOW")) P3S_HN_SECT_LOWER THEN
  ABBREV_TAC `M = C0 + Kc + Pc + C0 pow 2 + &40 * C0 + &1` THEN
  SUBGOAL_THEN `&1 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MP_TAC(SPEC `C0:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &212) (inv(&32 * M))` THEN
  REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_MIN] THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r0:real`; `dl:real`; `h:real`; `gN:real^3->real^3^3`; `t:real`;
                       `x:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&32 * M * dl <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC P3S_LE_INV_MUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `M * dl = C0 * dl + Kc * dl + Pc * dl + C0 pow 2 * dl + &40 * C0 * dl + dl`
  ASSUME_TAC THENL [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C0 * dl /\ &0 <= Kc * dl /\ &0 <= Pc * dl /\ &0 <= C0 pow 2 * dl /\
                &0 <= C0 * dl * dl /\ C0 * dl * dl <= C0 * dl /\
                C0 pow 2 * dl * dl <= C0 pow 2 * dl` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `dl * dl <= dl` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= C0 pow 2 /\ &0 <= dl * dl` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2; REAL_LE_SQUARE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv dl /\ &4 <= inv dl` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &4)` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 z} /\
                x IN {z:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 z}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC P3S_OPEN_S1 THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `--(inv dl)`; `&1`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `W = {x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x /\
                              A0 + &4 - p3_std_dist g0 x < &1}` THEN
  ABBREV_TAC `Ann = {y:real^3 | exp(--(inv dl) / sqrt(&2)) < norm y /\
                                norm y < exp(&1 / sqrt(&2))}` THEN
  SUBGOAL_THEN `open(W:real^3->bool) /\ open(Ann:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN Ann ==> ~(y = vec 0) /\ --(inv dl) < p3s_sy y /\ p3s_sy y < &1`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ann" THEN REWRITE_TAC[IN_ELIM_THM; P3S_ANN_GEN]; ALL_TAC] THEN
  SUBGOAL_THEN `Ann SUBSET (:real^3) DELETE vec 0 /\ Ann SUBSET rfs_neck_dom dl`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[P3S_NECK_DOM_S; GSYM P3S_SY_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom dl) (gN:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN ASM_REWRITE_TAC[P3S_NECK_DOM_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ &0 < inv(h pow 2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom dl) (\y:real^3. inv(h pow 2) %% gN y)` ASSUME_TAC
  THENL [MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX];
         ALL_TAC] THEN
  SUBGOAL_THEN `metric_field Ann (\y:real^3. inv(h pow 2) %% gN y)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C0 * dl` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Gc = \y:real^3. exp(--(&2 * p3s_cfr (C0 * dl) q A0 r0 (p3s_sy y))) %%
                              (inv(h pow 2) %% (gN:real^3->real^3^3) y)` THEN
  SUBGOAL_THEN `metric_field Ann (Gc:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Gc" THEN
    MATCH_MP_TAC(REWRITE_RULE[] (ISPECL [`Ann:real^3->bool`;
      `\y:real^3. inv(h pow 2) %% (gN:real^3->real^3^3) y`;
      `\y:real^3. p3s_cfr (C0 * dl) q A0 r0 (p3s_sy y)`] P3S_CONF_FIELD)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_COMPOSE_1D THEN EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P3S_SY_SMOOTH_ON; P3S_CFR_SMOOTH] THEN
    MATCH_MP_TAC P3S_CFR_SMOOTH THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field Ann (\y:real^3. h pow 2 %% (Gc:real^3->real^3^3) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN W
       ==> p3s_gs g0 A0 (C0 * dl) q r0 dl h gN z =
           mpullback (p3_std_nc g0 A0) (\y. h pow 2 %% (Gc:real^3->real^3^3) y) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `C0 * dl`; `q:real`; `r0:real`;
                  `dl:real`; `h:real`; `gN:real^3->real^3^3`; `z:real^3`] P3S_GS_PULLBACK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[mpullback] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "Gc" THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3S_SY_NC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC P3S_ALPHA THEN DISCH_THEN(MP_TAC o SPEC `A0 + &4 - p3_std_dist g0 z` o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; MATRIX_CMUL_LZERO; MATRIX_CMUL_LID; MATRIX_ADD_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Ann:real^3->bool`; `W:real^3->bool`; `p3_std_nc g0 A0`;
                 `p3s_ncinv g0 A0`; `x:real^3`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `y0 = p3_std_nc g0 A0 (x:real^3)` THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p3s_sy y0 = A0 + &4 - p3_std_dist g0 (x:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`]
      P3S_SY_NC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 2 (cylinder_flow (&0)) (\y:real^3. inv(h pow 2) %% gN y) y0
                <= dl pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl) o
      REWRITE_RULE[rfs_close_on] o check (can (find_term (fun t -> try fst(dest_const t) =
        "rfs_close_on" with Failure _ -> false)) o concl)) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
                  (\y:real^3. inv(h pow 2) %% gN y) y0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom dl` THEN
      ASM_SIMP_TAC[P3S_NECK_CYL_FIELD] THEN MATCH_MP_TAC APX_KREG_TWO THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REMOVE_THEN "CORE" (MP_TAC o BETA_RULE o SPECL [`q:real`; `C0 * dl`; `dl:real`; `A0:real`;
    `r0:real`; `Ann:real^3->bool`; `\y:real^3. inv(h pow 2) %% (gN:real^3->real^3^3) y`;
    `y0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ABBREV_TAC `Hn = \y:real^3. inv(h pow 2) %% (gN:real^3->real^3^3) y` THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v}
                      ==> --(Kl * dl) <= lsectional (Hn:real^3->real^3^3) y0 u v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "LOW" (MP_TAC o SPECL [`Ann:real^3->bool`;
      `Hn:real^3->real^3^3`; `y0:real^3`; `dl:real`; `u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  (* gN quantities at y0 *)
  SUBGOAL_THEN
   `mfd_scalar (open_set_atlas (rfs_neck_dom dl)) gN y0 = lscalar Hn y0 / h pow 2 /\
    (!u v. mfd_sectional (open_set_atlas (rfs_neck_dom dl)) gN y0 u v =
           lsectional Hn y0 u v / h pow 2)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(gN:real^3->real^3^3) = \z. h pow 2 %% Hn z` SUBST1_TAC THENL
     [EXPAND_TAC "Hn" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR; P3S_OPEN_MFD_SECTIONAL; P3S_NECK_DOM_OPEN] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_SCALE THEN EXISTS_TAC `Ann:real^3->bool` THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN MATCH_MP_TAC APX_LSECTIONAL_SCALE THEN
      EXISTS_TAC `Ann:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
       (p3s_gs g0 A0 (C0 * dl) q r0 dl h gN) x = lscalar Gc y0 / h pow 2 /\
    (!u v. mfd_sectional (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
              (p3s_gs g0 A0 (C0 * dl) q r0 dl h gN) x u v =
           lsectional Gc y0 (frechet_derivative (p3_std_nc g0 A0) (at x) u)
                            (frechet_derivative (p3_std_nc g0 A0) (at x) v) / h pow 2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR; P3S_OPEN_MFD_SECTIONAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `lscalar (mpullback (p3_std_nc g0 A0)
                    (\y. h pow 2 %% (Gc:real^3->real^3^3) y)) x` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `W:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`Ann:real^3->bool`; `W:real^3->bool`; `p3_std_nc g0 A0`;
        `p3s_ncinv g0 A0`; `\y. h pow 2 %% (Gc:real^3->real^3^3) y`; `x:real^3`]
        LSCALAR_PULLBACK) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC LSCALAR_SCALE THEN EXISTS_TAC `Ann:real^3->bool` THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `lsectional (mpullback (p3_std_nc g0 A0)
                    (\y. h pow 2 %% (Gc:real^3->real^3^3) y)) x u v` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `W:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`Ann:real^3->bool`; `W:real^3->bool`; `p3_std_nc g0 A0`;
        `p3s_ncinv g0 A0`; `\y. h pow 2 %% (Gc:real^3->real^3^3) y`; `x:real^3`;
        `u:real^3`; `v:real^3`] MFDR_LSECTIONAL_PULLBACK) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC APX_LSECTIONAL_SCALE THEN EXISTS_TAC `Ann:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v}
                      ==> --(Kl * dl) / h pow 2 <=
                          mfd_sectional (open_set_atlas (rfs_neck_dom dl)) gN y0 u v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `min (&0) (mfd_sec_min (open_set_atlas (rfs_neck_dom dl)) gN y0) <=
    mfd_sec_min (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                (p3s_gs g0 A0 (C0 * dl) q r0 dl h gN) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_SECMIN_GE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `u' = frechet_derivative (p3_std_nc g0 A0) (at x) (u:real^3)` THEN
    ABBREV_TAC `v' = frechet_derivative (p3_std_nc g0 A0) (at x) (v:real^3)` THEN
    SUBGOAL_THEN `~collinear {vec 0,u':real^3,v'}` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["u'"; "v'"] THEN MATCH_MP_TAC P3S_DIFFEO_NONCOLL THEN
      MAP_EVERY EXISTS_TAC [`Ann:real^3->bool`; `W:real^3->bool`; `p3s_ncinv g0 A0`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `min (&0) (lsectional (Hn:real^3->real^3^3) y0 u' v' / h pow 2)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`open_set_atlas (rfs_neck_dom dl)`; `gN:real^3->real^3^3`; `y0:real^3`;
                     `--(Kl * dl) / h pow 2`; `u':real^3`; `v':real^3`] P3S_SECMIN_LE) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P3S_MIN_DIV THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_MIN_LE_IMP) THEN
  REWRITE_TAC[rfs_pinched_at] THEN MATCH_MP_TAC P3S_PINCH_FN_ARITH THEN
  MAP_EVERY EXISTS_TAC [`mfd_scalar (open_set_atlas (rfs_neck_dom dl)) gN y0`;
                        `mfd_sec_min (open_set_atlas (rfs_neck_dom dl)) gN y0`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y0:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_pinched_at"
                             with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[rfs_pinched_at] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ASM_SIMP_TAC[REAL_LT_DIV]]);;

let P3S_PINCHED_OF_POS = prove
 (`!U (G:real^3->real^3^3) t x.
     open U /\ metric_field U G /\ x IN U /\ &0 <= t /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < mfd_sectional (open_set_atlas U) G x u v)
     ==> rfs_pinched_at (open_set_atlas U) G t x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pinched_at] THEN
  SUBGOAL_THEN `&0 < mfd_scalar (open_set_atlas U) (G:real^3->real^3^3) x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR] THEN MATCH_MP_TAC P2B_LSCALAR_POS_SECT THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `x:real^3`; `u:real^3`;
                   `v:real^3`] P3S_OPEN_MFD_SECTIONAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_sec_min (open_set_atlas U) (G:real^3->real^3^3) x` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_SECMIN_GE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_ARITH `--x <= &0 <=> &0 <= x`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_PINCH_CLAUSE = prove
 (`!g0 A0 q C0. p3_std_initial g0 A0 /\ &8 <= q /\ &0 < C0
     ==> ?dm. &0 < dm /\ dm <= &1 / &8 /\
          !r0 dl h gN t.
            &0 < r0 /\ r0 <= &1 /\ &0 < dl /\ dl <= dm /\ &0 < h /\ &0 <= t /\
            riemannian_metric (open_set_atlas (rfs_neck_dom dl)) gN /\
            rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                         (\y. inv(h pow 2) %% gN y) /\
            (!y. y IN rfs_neck_dom dl
                 ==> rfs_pinched_at (open_set_atlas (rfs_neck_dom dl)) gN t y) /\
            (!x u v. &1 <= A0 + &4 - p3_std_dist g0 x /\ ~collinear {vec 0,u,v}
                     ==> &0 < mfd_sectional
                                (open_set_atlas
                                   {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                                (p3s_gs g0 A0 (C0 * dl) q r0 dl h gN) x u v)
            ==> !x. --(inv dl) < A0 + &4 - p3_std_dist g0 x
                    ==> rfs_pinched_at
                          (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                          (p3s_gs g0 A0 (C0 * dl) q r0 dl h gN) t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real`; `C0:real`] P3S_PINCH_NECK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dm:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PN")))) THEN
  EXISTS_TAC `min dm (&1 / &8)` THEN
  REWRITE_TAC[REAL_LT_MIN; REAL_LE_MIN; REAL_MIN_LE] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `A0 + &4 - p3_std_dist g0 (x:real^3) < &1` THENL
   [REMOVE_THEN "PN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P3S_PINCHED_OF_POS THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv dl` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ]; FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P3S_GS_FIELD THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN ASM_REWRITE_TAC[P3S_NECK_DOM_OPEN]];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

