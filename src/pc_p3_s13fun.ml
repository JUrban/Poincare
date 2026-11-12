(* ========================================================================= *)
(* Unit pc_p3_s13fun (Part 3 proofs; MT Ch 13): the one-variable            *)
(* profile functions of the surgery on a delta-neck.  The conformal         *)
(* exponent f(s) = C0 delta exp(-q/s) (p3s_f, with c = C0 delta), the bump  *)
(* functions alpha and beta and the conformal factor phi of MT p. 332, and  *)
(* the profile lambda of the smooth radial collapse map (lambda(s) = L - s  *)
(* for s <= 2, lambda = 0 near L, |lambda'| <= 1 + 4 e).                    *)
(* ========================================================================= *)

needs "src/pc_p2c_stdinit.ml";;
needs "src/ns_smooth_elem.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The conformal exponent of MT Ch 13, f(s) = c exp(-q/s) for              *)
(* s > 0 and 0 for s <= 0 (c = C0 delta), as c * cutoff_flat(s / q):        *)
(* smoothness, sign, monotonicity, and the first two derivatives            *)
(* f' = (q / s^2) f and f'' = (q^2 / s^4 - 2 q / s^3) f for s > 0.           *)
(* ------------------------------------------------------------------------- *)

let p3s_f = new_definition
 `p3s_f (c:real) (q:real) (s:real) = c * cutoff_flat(s / q)`;;

let P3S_S1_COMPOSE = prove
 (`!s t (f:real->real) g.
     open s /\ open t /\ smooth_map_on s (lift o g o drop) /\
     smooth_map_on t (lift o f o drop) /\ (!x. x IN s ==> lift(g(drop x)) IN t)
     ==> smooth_map_on s (lift o (\u. f(g u)) o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(lift o (\u. (f:real->real)(g u)) o drop) =
                (lift o f o drop) o (lift o g o drop)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `t:real^1->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM]);;

let P3S_F_SMOOTH = prove
 (`!c q. ~(q = &0) ==> smooth_map_on (:real^1) (lift o p3s_f c q o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_f c q = (\s. c * cutoff_flat((\u. inv q * u + &0) s))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p3s_f; real_div] THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ADD_RID] THEN REPEAT GEN_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_CMUL THEN REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC P3S_S1_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; P2C_S1_AFFINE; CUTOFF_FLAT_SMOOTH]);;

let P3S_F_ZERO = prove
 (`!c q s. &0 < q /\ s <= &0 ==> p3s_f c q s = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_f; REAL_ENTIRE] THEN DISJ2_TAC THEN
  MATCH_MP_TAC CUTOFF_FLAT_ZERO THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]);;

let P3S_F_POS = prove
 (`!c q s. &0 < q /\ &0 < s ==> p3s_f c q s = c * exp(--(q / s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_f; cutoff_flat] THEN
  SUBGOAL_THEN `~(s / q <= &0)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_NOT_LE] THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_INV_DIV]);;

let P3S_F_NONNEG = prove
 (`!c q s. &0 <= c ==> &0 <= p3s_f c q s`,
  SIMP_TAC[p3s_f; REAL_LE_MUL; CUTOFF_FLAT_POS_LE]);;

let P3S_F_LE = prove
 (`!c q s. &0 <= c /\ &0 < q ==> p3s_f c q s <= c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_f] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[cutoff_flat] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_POS] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_NEG_LE0] THEN
  MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC);;

let P3S_F_MONO = prove
 (`!c q s t. &0 <= c /\ &0 < q /\ s <= t ==> p3s_f c q s <= p3s_f c q t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_f] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CUTOFF_FLAT_MONO THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ]);;

let P3S_F_DERIV = prove
 (`!c q s. &0 < q /\ &0 < s
           ==> (p3s_f c q has_real_derivative (q / s pow 2) * p3s_f c q s) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\u. c * exp(--(q / u))` THEN EXISTS_TAC `s:real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P3S_F_POS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(u - s) < s` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[P3S_F_POS] THEN
  REAL_DIFF_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The second derivative of the conformal exponent and the                  *)
(* inequality q^2 / s^4 - 2 q / s^3 >= q^2 / (2 s^4) for 4 s <= q (MT       *)
(* (13.2)); the bump functions alpha (1 on s <= 1, 0 on s >= 2) and beta    *)
(* (1 on s <= A0 + 4 - r0, 0 on s >= A0 + 4 - r0 / 2) of MT p. 332 built    *)
(* from smooth_step, and the conformal factor                               *)
(*   phi(s) = beta(s) exp(-2 f(s)) + (1 - beta(s)) exp(-2 f(A0 + 4))         *)
(* of the surgery metric (MT's [beta e^-2f + (1 - beta) e^-2f(A'')] on       *)
(* [A',A''], and e^-2f below A').                                           *)
(* ------------------------------------------------------------------------- *)

let P3S_F_DERIV2 = prove
 (`!c q s. &0 < q /\ &0 < s
           ==> ((\u. (q / u pow 2) * p3s_f c q u) has_real_derivative
                ((q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `q:real`; `s:real`] P3S_F_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\u. q / u pow 2) has_real_derivative --(&2 * q / s pow 3)) (atreal s)`
  ASSUME_TAC THENL
   [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ] THEN
    UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(MATCH_MP HAS_REAL_DERIVATIVE_MUL_ATREAL
    (CONJ (ASSUME `((\u. q / u pow 2) has_real_derivative --(&2 * q / s pow 3)) (atreal s)`)
          (ASSUME `(p3s_f c q has_real_derivative q / s pow 2 * p3s_f c q s) (atreal s)`)))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

let P3S_F_D2_LOWER = prove
 (`!c q s. &0 <= c /\ &0 < q /\ &0 < s /\ &4 * s <= q
           ==> q pow 2 / (&2 * s pow 4) * p3s_f c q s <=
               (q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[P3S_F_NONNEG] THEN
  SUBGOAL_THEN `&0 < s pow 4 /\ &0 < s pow 3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `s pow 4 = s * s pow 3` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < s /\ &0 < t
                           ==> q pow 2 / (&2 * (s * t)) = (q / s) * (q / (&2 * t)) /\
                               q pow 2 / (s * t) - &2 * q / t =
                               (q / s - &2) * (q / t)`] THEN
  SUBGOAL_THEN `&4 <= q / s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q / s pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `q / (&2 * s pow 3) = (q / s pow 3) / &2` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b / &2 = (a / &2) * b`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_REAL_ARITH_TAC);;

let p3s_alpha = new_definition
 `p3s_alpha (s:real) = smooth_step(&2 - s)`;;

let p3s_beta = new_definition
 `p3s_beta (A0:real) (r0:real) (s:real) =
    smooth_step((A0 + &4 - r0 / &2 - s) / (r0 / &2))`;;

let p3s_phi = new_definition
 `p3s_phi (c:real) (q:real) (A0:real) (r0:real) (s:real) =
    p3s_beta A0 r0 s * exp(--(&2 * p3s_f c q s)) +
    (&1 - p3s_beta A0 r0 s) * exp(--(&2 * p3s_f c q (A0 + &4)))`;;

let P3S_ALPHA = prove
 (`smooth_map_on (:real^1) (lift o p3s_alpha o drop) /\
   (!s. &0 <= p3s_alpha s /\ p3s_alpha s <= &1) /\
   (!s. s <= &1 ==> p3s_alpha s = &1) /\
   (!s. &2 <= s ==> p3s_alpha s = &0)`,
  REWRITE_TAC[p3s_alpha; SMOOTH_STEP_BOUNDS] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(lift o p3s_alpha o drop) =
                  (lift o (\s. smooth_step((\u. --(&1) * u + &2) s)) o drop)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[p3s_alpha] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P2C_S1_SMOOTH_STEP THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_AFFINE]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC]);;

let P3S_BETA = prove
 (`!A0 r0. &0 < r0
           ==> smooth_map_on (:real^1) (lift o p3s_beta A0 r0 o drop) /\
               (!s. &0 <= p3s_beta A0 r0 s /\ p3s_beta A0 r0 s <= &1) /\
               (!s. s <= A0 + &4 - r0 ==> p3s_beta A0 r0 s = &1) /\
               (!s. A0 + &4 - r0 / &2 <= s ==> p3s_beta A0 r0 s = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < r0 / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3s_beta; SMOOTH_STEP_BOUNDS] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(lift o p3s_beta A0 r0 o drop) =
      (lift o (\s. smooth_step((\u. --(inv(r0 / &2)) * u +
                                    (A0 + &4 - r0 / &2) / (r0 / &2)) s)) o drop)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[p3s_beta] THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC P2C_S1_SMOOTH_STEP THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_AFFINE]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Properties of the conformal factor phi.  Smooth; equal to               *)
(* exp(-2 f) up to A0 + 4 - r0 and to the constant exp(-2 f(A0 + 4)) from  *)
(* A0 + 4 - r0 / 2 on; exp(-2 f(A0 + 4)) <= phi <= 1; and phi(s) <=         *)
(* exp(-2 f(s0)) for s >= s0 >= 0 when s0 <= A0 + 4 (the slack used by the  *)
(* collapse map).                                                           *)
(* ------------------------------------------------------------------------- *)

let P3S_PHI_SMOOTH = prove
 (`!c q A0 r0. &0 < q /\ &0 < r0
               ==> smooth_map_on (:real^1) (lift o p3s_phi c q A0 r0 o drop)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `p3s_phi c q A0 r0 =
                (\s. p3s_beta A0 r0 s * exp(--(&2 * p3s_f c q s)) +
                     (&1 - p3s_beta A0 r0 s) * exp(--(&2 * p3s_f c q (A0 + &4))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_phi]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_ADD THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THEN
  MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\s. p3s_beta A0 r0 s) = p3s_beta A0 r0` (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC P2C_S1_EXP THEN REWRITE_TAC[OPEN_UNIV] THEN
    SUBGOAL_THEN `(\s. --(&2 * p3s_f c q s)) = (\s. --(&2) * p3s_f c q s)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2C_S1_CMUL THEN REWRITE_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC P3S_F_SMOOTH THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[P2C_S1_CONST]]);;

let P3S_PHI_LOW = prove
 (`!c q A0 r0 s. &0 < r0 /\ s <= A0 + &4 - r0
                 ==> p3s_phi c q A0 r0 s = exp(--(&2 * p3s_f c q s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[p3s_phi] THEN REAL_ARITH_TAC);;

let P3S_PHI_HIGH = prove
 (`!c q A0 r0 s. &0 < r0 /\ A0 + &4 - r0 / &2 <= s
                 ==> p3s_phi c q A0 r0 s = exp(--(&2 * p3s_f c q (A0 + &4)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[p3s_phi] THEN REAL_ARITH_TAC);;

let P3S_CONVEX_LE = prove
 (`!b x y m. &0 <= b /\ b <= &1 /\ x <= m /\ y <= m ==> b * x + (&1 - b) * y <= m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `x:real`; `m:real`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`&1 - b`; `y:real`; `m:real`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_SUB_LE] THEN REAL_ARITH_TAC);;

let P3S_CONVEX_GE = prove
 (`!b x y m. &0 <= b /\ b <= &1 /\ m <= x /\ m <= y ==> m <= b * x + (&1 - b) * y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `m:real`; `x:real`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`&1 - b`; `m:real`; `y:real`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_SUB_LE] THEN REAL_ARITH_TAC);;

let P3S_PHI_BOUNDS = prove
 (`!c q A0 r0 s. &0 <= c /\ &0 < q /\ &0 < r0
                 ==> exp(--(&2 * p3s_f c q (A0 + &4))) <= p3s_phi c q A0 r0 s /\
                     p3s_phi c q A0 r0 s <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  ABBREV_TAC `bb = p3s_beta A0 r0 s` THEN
  SUBGOAL_THEN `&0 <= bb /\ bb <= &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[p3s_phi] THEN
  SUBGOAL_THEN
   `exp(--(&2 * p3s_f c q s)) <= &1 /\ exp(--(&2 * p3s_f c q (A0 + &4))) <= &1 /\
    &0 < exp(--(&2 * p3s_f c q (A0 + &4)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --(&2 * x) <= &0`) THEN
    ASM_SIMP_TAC[P3S_F_NONNEG];
    ALL_TAC] THEN
  ASM_CASES_TAC `A0 + &4 - r0 / &2 <= s` THENL
   [SUBGOAL_THEN `bb = &0` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_SUB_RZERO; REAL_MUL_LID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(&2 * p3s_f c q (A0 + &4))) <= exp(--(&2 * p3s_f c q s))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> --(&2 * y) <= --(&2 * x)`) THEN
    MATCH_MP_TAC P3S_F_MONO THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3S_CONVEX_GE THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    MATCH_MP_TAC P3S_CONVEX_LE THEN ASM_REWRITE_TAC[]]);;

let P3S_PHI_SLACK = prove
 (`!c q A0 r0 s0 s. &0 <= c /\ &0 < q /\ &0 < r0 /\ s0 <= A0 + &4 /\ s0 <= s
                    ==> p3s_phi c q A0 r0 s <= exp(--(&2 * p3s_f c q s0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A0:real`; `r0:real`] P3S_BETA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  ABBREV_TAC `bb = p3s_beta A0 r0 s` THEN
  SUBGOAL_THEN `&0 <= bb /\ bb <= &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[p3s_phi] THEN
  SUBGOAL_THEN
   `exp(--(&2 * p3s_f c q s)) <= exp(--(&2 * p3s_f c q s0)) /\
    exp(--(&2 * p3s_f c q (A0 + &4))) <= exp(--(&2 * p3s_f c q s0))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> --(&2 * y) <= --(&2 * x)`) THEN
    MATCH_MP_TAC P3S_F_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P3S_CONVEX_LE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The profile of the smooth collapse map (MT's collapse map has a kink).   *)
(* lambda(s) = integral over [s,L] of a density rho with rho = 1 on s <= 2, *)
(* rho = 0 on s >= L - e and 0 <= rho <= 1 + k, k <= 4 e; the factor k is  *)
(* chosen so that the integral over [2,L] is L - 2.  Hence lambda(s) =      *)
(* L - s for s <= 2, lambda = 0 for s >= L - e, lambda' = -rho, smooth.     *)
(* ------------------------------------------------------------------------- *)

let p3s_lam_h = new_definition
 `p3s_lam_h (L:real) (e:real) (u:real) = smooth_step((u - (L - &2 * e)) / e)`;;

let p3s_lam_b = new_definition
 `p3s_lam_b (u:real) = smooth_step(u - &2)`;;

let p3s_lam_k = new_definition
 `p3s_lam_k (L:real) (e:real) =
    ((L - &2) - real_integral (real_interval[&2,L]) (\u. &1 - p3s_lam_h L e u)) /
    real_integral (real_interval[&2,L]) (\u. p3s_lam_b u * (&1 - p3s_lam_h L e u))`;;

let p3s_lam_rho = new_definition
 `p3s_lam_rho (L:real) (e:real) (u:real) =
    (&1 + p3s_lam_k L e * p3s_lam_b u) * (&1 - p3s_lam_h L e u)`;;

let p3s_lam = new_definition
 `p3s_lam (L:real) (e:real) (s:real) =
    real_integral (real_interval[s,L]) (p3s_lam_rho L e)`;;

let P3S_LAM_H = prove
 (`!L e. &0 < e
         ==> smooth_map_on (:real^1) (lift o p3s_lam_h L e o drop) /\
             (!u. &0 <= p3s_lam_h L e u /\ p3s_lam_h L e u <= &1) /\
             (!u. u <= L - &2 * e ==> p3s_lam_h L e u = &0) /\
             (!u. L - e <= u ==> p3s_lam_h L e u = &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[p3s_lam_h; SMOOTH_STEP_BOUNDS] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(lift o p3s_lam_h L e o drop) =
                  (lift o (\u. smooth_step((\v. inv e * v + --((L - &2 * e) / e)) u)) o drop)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; p3s_lam_h] THEN GEN_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P2C_S1_SMOOTH_STEP THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_AFFINE]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let P3S_LAM_B = prove
 (`smooth_map_on (:real^1) (lift o p3s_lam_b o drop) /\
   (!u. &0 <= p3s_lam_b u /\ p3s_lam_b u <= &1) /\
   (!u. u <= &2 ==> p3s_lam_b u = &0) /\
   (!u. &3 <= u ==> p3s_lam_b u = &1)`,
  REWRITE_TAC[p3s_lam_b; SMOOTH_STEP_BOUNDS] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(lift o p3s_lam_b o drop) =
                  (lift o (\u. smooth_step((\v. &1 * v + --(&2)) u)) o drop)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; p3s_lam_b] THEN GEN_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P2C_S1_SMOOTH_STEP THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_AFFINE]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC]);;

let P3S_LAM_RHO = prove
 (`!L e. &4 <= L /\ &0 < e /\ e <= &1 / &4
         ==> smooth_map_on (:real^1) (lift o p3s_lam_rho L e o drop) /\
             &0 <= p3s_lam_k L e /\ p3s_lam_k L e <= &4 * e /\
             (!u. &0 <= p3s_lam_rho L e u /\ p3s_lam_rho L e u <= &1 + p3s_lam_k L e) /\
             (!u. u <= &2 ==> p3s_lam_rho L e u = &1) /\
             (!u. L - e <= u ==> p3s_lam_rho L e u = &0) /\
             real_integral (real_interval[&2,L]) (p3s_lam_rho L e) = L - &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:real`; `e:real`] P3S_LAM_H) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "HS") (CONJUNCTS_THEN2 (LABEL_TAC "HB")
    (CONJUNCTS_THEN2 (LABEL_TAC "H0") (LABEL_TAC "H1")))) THEN
  STRIP_ASSUME_TAC P3S_LAM_B THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^1) (lift o (\u. &1 - p3s_lam_h L e u) o drop) /\
    smooth_map_on (:real^1) (lift o (\u. p3s_lam_b u * (&1 - p3s_lam_h L e u)) o drop)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV; ETA_AX] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `I1 = real_integral (real_interval[&2,L]) (\u. &1 - p3s_lam_h L e u)` THEN
  ABBREV_TAC `I2 = real_integral (real_interval[&2,L])
                     (\u. p3s_lam_b u * (&1 - p3s_lam_h L e u))` THEN
  SUBGOAL_THEN
   `!a b. (\u. &1 - p3s_lam_h L e u) real_integrable_on real_interval[a,b] /\
          (\u. p3s_lam_b u * (&1 - p3s_lam_h L e u)) real_integrable_on real_interval[a,b]`
  (LABEL_TAC "INT") THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC P2C_S1_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `L - &2 * e - &2 <= I1 /\ I1 <= L - &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "I1" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\u. &1 - p3s_lam_h L e u`; `&2`; `L:real`; `L - &2 * e`]
                    REAL_INTEGRAL_COMBINE) THEN
      USE_THEN "INT" (fun th -> REWRITE_TAC[th]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC(REAL_ARITH `a = c /\ &0 <= b ==> c <= a + b`) THEN CONJ_TAC THENL
       [TRANS_TAC EQ_TRANS `real_integral (real_interval[&2,L - &2 * e]) (\u. &1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
          REPEAT STRIP_TAC THEN USE_THEN "H0" (fun th -> ASM_SIMP_TAC[th]) THEN
          REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH
            `&4 <= L /\ e <= &1 / &4 ==> &2 <= L - &2 * e`] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_INTEGRAL_POS THEN USE_THEN "INT" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        USE_THEN "HB" (MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC];
      TRANS_TAC REAL_LE_TRANS `real_integral (real_interval[&2,L]) (\u. &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_LE THEN USE_THEN "INT" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[REAL_INTEGRABLE_CONST; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        USE_THEN "HB" (MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `&4 <= L ==> &2 <= L`] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `L - &2 * e - &3 <= I2` ASSUME_TAC THENL
   [EXPAND_TAC "I2" THEN
    MP_TAC(ISPECL [`\u. p3s_lam_b u * (&1 - p3s_lam_h L e u)`; `&2`; `L:real`; `&3`]
                  REAL_INTEGRAL_COMBINE) THEN
    USE_THEN "INT" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`\u. p3s_lam_b u * (&1 - p3s_lam_h L e u)`; `&3`; `L:real`;
                   `L - &2 * e`] REAL_INTEGRAL_COMBINE) THEN
    USE_THEN "INT" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     `!a b. &0 <= real_integral (real_interval[a,b])
                    (\u. p3s_lam_b u * (&1 - p3s_lam_h L e u))`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
      USE_THEN "INT" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "HB" (MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `real_integral (real_interval[&3,L - &2 * e])
        (\u. p3s_lam_b u * (&1 - p3s_lam_h L e u)) = L - &2 * e - &3`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS `real_integral (real_interval[&3,L - &2 * e]) (\u. &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
        USE_THEN "H0" (fun th -> ASM_SIMP_TAC[th]) THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH
          `&4 <= L /\ e <= &1 / &4 ==> &3 <= L - &2 * e`] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= c ==> b <= a + (b + c)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= I2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p3s_lam_k L e = (L - &2 - I1) / I2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p3s_lam_k]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p3s_lam_k L e /\ p3s_lam_k L e <= &4 * e` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < I2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * e <= (&4 * e) * I2` ASSUME_TAC THENL
     [MP_TAC(SPECL [`&4 * e`; `&1 / &2`; `I2:real`] REAL_LE_LMUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `p3s_lam_rho L e =
                  (\u. &1 * (&1 - p3s_lam_h L e u) +
                       p3s_lam_k L e * (p3s_lam_b u * (&1 - p3s_lam_h L e u)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; p3s_lam_rho] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2C_S1_ADD THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2C_S1_CMUL THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `u:real` THEN REWRITE_TAC[p3s_lam_rho] THEN
    USE_THEN "HB" (MP_TAC o SPEC `u:real`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `u:real` o
      check (fun th -> can (term_match [] `!u. &0 <= p3s_lam_b u /\ p3s_lam_b u <= &1`)
                           (concl th))) THEN
    STRIP_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `p3s_lam_k L e * p3s_lam_b u <= p3s_lam_k L e /\
                  &0 <= p3s_lam_k L e * p3s_lam_b u` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `(&1 + p3s_lam_k L e * p3s_lam_b u) * &1` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN REWRITE_TAC[p3s_lam_rho] THEN
    SUBGOAL_THEN `p3s_lam_b u = &0 /\ p3s_lam_h L e u = &0` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN USE_THEN "H0" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN REWRITE_TAC[p3s_lam_rho] THEN
    USE_THEN "H1" (fun th -> ASM_SIMP_TAC[th]) THEN REAL_ARITH_TAC;
    TRANS_TAC EQ_TRANS
     `real_integral (real_interval[&2,L])
        (\u. (&1 - p3s_lam_h L e u) +
             p3s_lam_k L e * (p3s_lam_b u * (&1 - p3s_lam_h L e u)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[p3s_lam_rho] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\u. &1 - p3s_lam_h L e u`;
                   `\u. p3s_lam_k L e * (p3s_lam_b u * (&1 - p3s_lam_h L e u))`;
                   `real_interval[&2,L]`] REAL_INTEGRAL_ADD) THEN
    ANTS_TAC THENL
     [USE_THEN "INT" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN USE_THEN "INT" (fun th -> REWRITE_TAC[th]);
      BETA_TAC THEN DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`\u. p3s_lam_b u * (&1 - p3s_lam_h L e u)`; `p3s_lam_k L e`;
                   `real_interval[&2,L]`] REAL_INTEGRAL_LMUL) THEN
    USE_THEN "INT" (fun th -> REWRITE_TAC[th]) THEN BETA_TAC THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(I2 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD]);;

let P3S_LAM_INTEGRABLE = prove
 (`!L e a b. &4 <= L /\ &0 < e /\ e <= &1 / &4
             ==> p3s_lam_rho L e real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC P2C_S1_CONTINUOUS THEN
  MP_TAC(SPECL [`L:real`; `e:real`] P3S_LAM_RHO) THEN ASM_SIMP_TAC[]);;

let P3S_LAM_SPLIT = prove
 (`!L e a s. &4 <= L /\ &0 < e /\ e <= &1 / &4 /\ a <= s
             ==> p3s_lam L e s =
                 real_integral (real_interval[a,L]) (p3s_lam_rho L e) -
                 real_integral (real_interval[a,s]) (p3s_lam_rho L e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_lam] THEN
  MP_TAC(SPECL [`L:real`; `e:real`] P3S_LAM_RHO) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `s <= L` THENL
   [MP_TAC(ISPECL [`p3s_lam_rho L e`; `a:real`; `L:real`; `s:real`]
                  REAL_INTEGRAL_COMBINE) THEN
    ASM_SIMP_TAC[P3S_LAM_INTEGRABLE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[s,L]) (p3s_lam_rho L e) = &0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_NULL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `a <= L` THENL
   [ALL_TAC;
    SUBGOAL_THEN `real_integral (real_interval[a,L]) (p3s_lam_rho L e) = &0 /\
                  real_integral (real_interval[a,s]) (p3s_lam_rho L e) = &0`
      (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_NULL THEN ASM_REAL_ARITH_TAC;
      TRANS_TAC EQ_TRANS `real_integral (real_interval[a,s]) (\u. &0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_INTEGRAL_0]]]] THEN
  MP_TAC(ISPECL [`p3s_lam_rho L e`; `a:real`; `s:real`; `L:real`]
                REAL_INTEGRAL_COMBINE) THEN
  ASM_SIMP_TAC[P3S_LAM_INTEGRABLE] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN `real_integral (real_interval[L,s]) (p3s_lam_rho L e) = &0`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `real_integral (real_interval[L,s]) (\u. &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INTEGRAL_0]];
    REAL_ARITH_TAC]);;

let P3S_LAM_DERIV = prove
 (`!L e s. &4 <= L /\ &0 < e /\ e <= &1 / &4
           ==> (p3s_lam L e has_real_derivative --(p3s_lam_rho L e s)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\t. real_integral (real_interval[s - &1,L]) (p3s_lam_rho L e) -
                  real_integral (real_interval[s - &1,t]) (p3s_lam_rho L e)` THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P3S_LAM_SPLIT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `--x = &0 - x`] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC P2C_INTEGRAL_DERIV_AT THEN REWRITE_TAC[REAL_ARITH `s - &1 < s`] THEN
  MATCH_MP_TAC P2C_S1_CONTINUOUS THEN
  MP_TAC(SPECL [`L:real`; `e:real`] P3S_LAM_RHO) THEN ASM_SIMP_TAC[]);;

let P3S_LAM = prove
 (`!L e. &4 <= L /\ &0 < e /\ e <= &1 / &4
         ==> smooth_map_on (:real^1) (lift o p3s_lam L e o drop) /\
             (!s. s <= &2 ==> p3s_lam L e s = L - s) /\
             (!s. L - e <= s ==> p3s_lam L e s = &0) /\
             (!s. &0 <= p3s_lam L e s) /\
             (!s t. s <= t ==> p3s_lam L e t <= p3s_lam L e s) /\
             (!s. &0 <= s ==> p3s_lam L e s <= L) /\
             (!s. (p3s_lam L e has_real_derivative --(p3s_lam_rho L e s)) (atreal s)) /\
             (!s. &0 <= p3s_lam_rho L e s /\ p3s_lam_rho L e s <= &1 + &4 * e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:real`; `e:real`] P3S_LAM_RHO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RS") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "RB")
    (CONJUNCTS_THEN2 (LABEL_TAC "R1") (CONJUNCTS_THEN2 (LABEL_TAC "R0")
     (LABEL_TAC "RI"))))))) THEN
  SUBGOAL_THEN `!s. (p3s_lam L e has_real_derivative --(p3s_lam_rho L e s)) (atreal s)`
  (LABEL_TAC "D") THENL
   [GEN_TAC THEN MATCH_MP_TAC P3S_LAM_DERIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s t. s <= t
                      ==> p3s_lam L e s =
                          real_integral (real_interval[s,t]) (p3s_lam_rho L e) +
                          p3s_lam L e t`
  (LABEL_TAC "ADD") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`L:real`; `e:real`; `s:real`; `t:real`] P3S_LAM_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p3s_lam] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. &0 <= real_integral (real_interval[s,t]) (p3s_lam_rho L e)`
  (LABEL_TAC "POS") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
    ASM_SIMP_TAC[P3S_LAM_INTEGRABLE] THEN USE_THEN "RB" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. L - e <= s ==> p3s_lam L e s = &0` (LABEL_TAC "Z") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_lam] THEN
    ASM_CASES_TAC `L <= s` THENL
     [MATCH_MP_TAC REAL_INTEGRAL_NULL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `real_integral (real_interval[s,L]) (\u. &0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN USE_THEN "R0" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INTEGRAL_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= &2 ==> p3s_lam L e s = L - s` (LABEL_TAC "LIN") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "ADD" (SUBST1_TAC o C MP (ASSUME `s <= &2`) o SPECL [`s:real`; `&2`]) THEN
    SUBGOAL_THEN `p3s_lam L e (&2) = L - &2` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[p3s_lam]; ALL_TAC] THEN
    SUBGOAL_THEN `real_integral (real_interval[s,&2]) (p3s_lam_rho L e) = &2 - s`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS `real_integral (real_interval[s,&2]) (\u. &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THEN USE_THEN "R1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= p3s_lam L e s` (LABEL_TAC "NN") THENL
   [GEN_TAC THEN ASM_CASES_TAC `L - e <= s` THENL
     [USE_THEN "Z" (fun th -> ASM_SIMP_TAC[th; REAL_LE_REFL]); ALL_TAC] THEN
    USE_THEN "ADD" (MP_TAC o SPECL [`s:real`; `L - e`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "Z" (fun th -> SIMP_TAC[th; REAL_LE_REFL; REAL_ADD_RID]) THEN
    USE_THEN "POS" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. s <= t ==> p3s_lam L e t <= p3s_lam L e s` (LABEL_TAC "MONO") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "ADD" (SUBST1_TAC o C MP (ASSUME `s <= t`) o SPECL [`s:real`; `t:real`]) THEN
    USE_THEN "POS" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_REAL_DERIVATIVE_1D THEN
    EXISTS_TAC `\s. --(p3s_lam_rho L e s)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [USE_THEN "D" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    SUBGOAL_THEN `(\s. --(p3s_lam_rho L e s)) = (\s. --(&1) * p3s_lam_rho L e s)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2C_S1_CMUL THEN REWRITE_TAC[OPEN_UNIV; ETA_AX] THEN
    USE_THEN "RS" (fun th -> REWRITE_TAC[th]);
    USE_THEN "LIN" (fun th -> REWRITE_TAC[th]);
    USE_THEN "Z" (fun th -> REWRITE_TAC[th]);
    USE_THEN "NN" (fun th -> REWRITE_TAC[th]);
    USE_THEN "MONO" (fun th -> REWRITE_TAC[th]);
    REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `p3s_lam L e (&0)` THEN CONJ_TAC THENL
     [USE_THEN "MONO" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "LIN" (fun th -> SIMP_TAC[th; REAL_POS]) THEN REAL_ARITH_TAC];
    USE_THEN "D" (fun th -> REWRITE_TAC[th]);
    GEN_TAC THEN USE_THEN "RB" (MP_TAC o SPEC `s:real`) THEN ASM_REAL_ARITH_TAC]);;

