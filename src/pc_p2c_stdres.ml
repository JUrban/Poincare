(* ========================================================================= *)
(* Unit pc_p2c_stdres (Part 2C; MT Ch 12, the standard solution):            *)
(* restarts of the maximal standard flow and sec >= 0 on [0,Tm).  An        *)
(* SO(3)-invariant complete metric h with sec >= 0 is modified far out:      *)
(* the warping function keeps its value and its derivative is cut off       *)
(* (F_M' = F' chi), so the curvature stays >= 0 and bounded, and beyond the *)
(* cut the metric is a product, then (after a change of the radial          *)
(* coefficient, which leaves the curvature alone) a constant multiple of    *)
(* the standard initial metric g0.  The double of g0 then carries the       *)
(* modified metric; the compact doubles flow (PDE_CURVATURE_TIME), keep     *)
(* sec >= 0 (SEC_PRESERVED) and converge to a flow from h (Prop 5.14);      *)
(* glued to the maximal flow and identified with it by uniqueness, this     *)
(* gives sec >= 0 of the maximal flow, step by step.                        *)
(* ========================================================================= *)

needs "src/pc_p2c_stdsym.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The radial functions of the modification.  For h with                    *)
(* stds_rgood h (SO(3)-invariant, complete, sec >= 0) and r1 > 0, with      *)
(* a, b the coefficients of h, rho its radial distance, F = r sqrt(b) and   *)
(* step = smooth_step:                                                       *)
(*   chi = 1 - step(rho - rho(r1)): 1 up to r1, 0 once rho >= rho(r1) + 1;   *)
(*   w = F' (1 - chi), F_M = F - (integral of w from 0), so F_M' = F' chi;   *)
(*   psi = step(rho - rho(r1) - 2); c_M = F_M(far)^2 / 2;                    *)
(*   A_M = (1 - psi) a + psi c_M a0 (a0 the radial coefficient of g0);       *)
(*   B_M = (F_M / r)^2.                                                      *)
(* ------------------------------------------------------------------------- *)

let stds_rgood = new_definition
 `stds_rgood (h:real^3->real^3^3) <=>
    stds_rotm h /\ mfd_complete (euclidean,open_set_atlas (:real^3)) h /\
    (!x u v. ~collinear {vec 0,u,v}
             ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) h x u v)`;;

let stds_mchi = new_definition
 `stds_mchi (h:real^3->real^3^3) (r1:real) (r:real) =
    &1 - smooth_step(p3s_rad_rho h r - p3s_rad_rho h r1)`;;

let stds_mFh = new_definition
 `stds_mFh (h:real^3->real^3^3) (r:real) = r * sqrt(p3s_rad_b h r)`;;

let stds_mw = new_definition
 `stds_mw (h:real^3->real^3^3) (r1:real) (u:real) =
    real_derivative (stds_mFh h) u * (&1 - stds_mchi h r1 u)`;;

let stds_mF = new_definition
 `stds_mF (h:real^3->real^3^3) (r1:real) (r:real) =
    stds_mFh h r - real_integral (real_interval[&0,r]) (stds_mw h r1)`;;

let stds_mre = new_definition
 `stds_mre (h:real^3->real^3^3) (r1:real) =
    @r. &0 <= r /\ p3s_rad_rho h r1 + &1 <= p3s_rad_rho h r`;;

let stds_mc = new_definition
 `stds_mc (h:real^3->real^3^3) (r1:real) = stds_mF h r1 (stds_mre h r1) pow 2 / &2`;;

let stds_mpsi = new_definition
 `stds_mpsi (h:real^3->real^3^3) (r1:real) (r:real) =
    smooth_step(p3s_rad_rho h r - p3s_rad_rho h r1 - &2)`;;

let stds_mA = new_definition
 `stds_mA (h:real^3->real^3^3) (g0:real^3->real^3^3) (r1:real) (r:real) =
    (&1 - stds_mpsi h r1 r) * p3s_rad_a h r +
    stds_mpsi h r1 r * stds_mc h r1 * p3s_rad_a g0 r`;;

let stds_mB = new_definition
 `stds_mB (h:real^3->real^3^3) (r1:real) (r:real) = (stds_mF h r1 r / r) pow 2`;;

(* The radial distance below 0 and its monotonicity.                         *)

let STDS_RHO_NONPOS = prove
 (`!h r. r <= &0 ==> p3s_rad_rho h r = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r = &0` THEN ASM_REWRITE_TAC[P3S_RHO_0] THEN
  REWRITE_TAC[p3s_rad_rho] THEN
  SUBGOAL_THEN `real_interval[&0,r] = {}` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_INTEGRAL_EMPTY]]);;

let STDS_RHO_MONO = prove
 (`!h r s. stds_rotm h /\ r <= s ==> p3s_rad_rho h r <= p3s_rad_rho h s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r <= &0` THENL
   [ASM_SIMP_TAC[STDS_RHO_NONPOS] THEN ASM_CASES_TAC `s <= &0` THENL
     [ASM_SIMP_TAC[STDS_RHO_NONPOS; REAL_LE_REFL];
      MATCH_MP_TAC STDS_RT_RHO_POS_LE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`; `s:real`] STDS_RT_RHO_LT_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]]);;

(* The step and its derivative.                                               *)

let STDS_SS_DERIV = prove
 (`!t. (smooth_step has_real_derivative real_derivative smooth_step t) (atreal t)`,
  GEN_TAC THEN MATCH_MP_TAC P2C_S1_DERIV THEN EXISTS_TAC `(:real^1)` THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_STEP_SMOOTH]);;

let STDS_SS_DZERO = prove
 (`!t. t < &0 \/ &1 < t ==> real_derivative smooth_step t = &0`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`smooth_step`; `t:real`] THEN REWRITE_TAC[STDS_SS_DERIV] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [MATCH_MP_TAC P2C_DERIV_LOCALLY_CONST THEN MAP_EVERY EXISTS_TAC [`&0`; `--t:real`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2C_DERIV_LOCALLY_CONST THEN MAP_EVERY EXISTS_TAC [`&1`; `t - &1`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC]);;

let STDS_SS_DNONNEG = prove
 (`!t. &0 <= real_derivative smooth_step t`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`smooth_step`; `real_derivative smooth_step`; `(:real)`]
         HAS_REAL_DERIVATIVE_INCREASING) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; P2C_UNIV_NOT_SING; IN_UNIV; WITHINREAL_UNIV;
              STDS_SS_DERIV] THEN
  MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_MONO THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN REWRITE_TAC[]]);;

let STDS_SS_DBOUND = prove
 (`?C. &0 < C /\ !t. &0 <= real_derivative smooth_step t /\
                     real_derivative smooth_step t <= C`,
  SUBGOAL_THEN
   `compact (IMAGE (lift o real_derivative smooth_step o drop)
                   (interval[lift(&0),lift(&1)]))`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
    MP_TAC(ISPECL [`(:real^1)`; `smooth_step`] P3S_S1_RDERIV) THEN
    SIMP_TAC[OPEN_UNIV; SMOOTH_STEP_SMOOTH];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP; o_THM; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[STDS_SS_DNONNEG] THEN X_GEN_TAC `t:real` THEN
  ASM_CASES_TAC `&0 <= t /\ t <= &1` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `lift t`) THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPEC `t:real` STDS_SS_DZERO) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* chi.                                                                       *)

let STDS_MCHI_1 = prove
 (`!h r1 r. stds_rotm h /\ r <= r1 ==> stds_mchi h r1 r = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mchi] THEN
  SUBGOAL_THEN `smooth_step(p3s_rad_rho h r - p3s_rad_rho h r1) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_0 THEN
    MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`; `r1:real`] STDS_RHO_MONO) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let STDS_MCHI_0 = prove
 (`!h r1 r. p3s_rad_rho h r1 + &1 <= p3s_rad_rho h r ==> stds_mchi h r1 r = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mchi] THEN
  SUBGOAL_THEN `smooth_step(p3s_rad_rho h r - p3s_rad_rho h r1) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let STDS_MCHI_BOUNDS = prove
 (`!h r1 r. &0 <= stds_mchi h r1 r /\ stds_mchi h r1 r <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stds_mchi] THEN
  MP_TAC(SPEC `p3s_rad_rho h r - p3s_rad_rho h r1` SMOOTH_STEP_BOUNDS) THEN
  REAL_ARITH_TAC);;

let STDS_MCHI_SMOOTH = prove
 (`!h r1. stds_rotm h /\ &0 < r1
          ==> smooth_map_on (:real^1) (lift o stds_mchi h r1 o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x:real^1` THEN
  ASM_CASES_TAC `drop x < r1` THENL
   [EXISTS_TAC `{y:real^1 | drop y < r1}` THEN
    ASM_REWRITE_TAC[P2C_OPEN_DROP_LT; IN_ELIM_THM] THEN
    MATCH_MP_TAC P2C_S1_EQ THEN EXISTS_TAC `\t:real. &1` THEN
    REWRITE_TAC[P2C_OPEN_DROP_LT; P2C_S1_CONST; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC STDS_MCHI_1 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `{y:real^1 | &0 < drop y}` THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `stds_mchi h r1 =
    (\t. (\t. &1) t -
         (\t. smooth_step((\t. p3s_rad_rho h t - (\t. p3s_rad_rho h r1) t) t)) t)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stds_mchi]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_CONST] THEN
  MATCH_MP_TAC P2C_S1_SMOOTH_STEP THEN REWRITE_TAC[P2C_OPEN_DROP_GT] THEN
  MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_CONST; ETA_AX] THEN
  ASM_SIMP_TAC[STDS_RT_RHO_SMOOTH]);;

let STDS_MCHI_DERIV = prove
 (`!h r1 r. stds_rotm h /\ &0 < r
     ==> (stds_mchi h r1 has_real_derivative
          --(real_derivative smooth_step (p3s_rad_rho h r - p3s_rad_rho h r1) *
             sqrt(p3s_rad_a h r))) (atreal r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `stds_mchi h r1 =
    (\x. (\x. &1) x - (smooth_step o (\x. p3s_rad_rho h x - p3s_rad_rho h r1)) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stds_mchi; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real. &1`; `&0`;
                 `smooth_step o (\x. p3s_rad_rho h x - p3s_rad_rho h r1)`;
                 `real_derivative smooth_step (p3s_rad_rho h r - p3s_rad_rho h r1) *
                  sqrt(p3s_rad_a h r)`; `atreal r`] HAS_REAL_DERIVATIVE_SUB) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN REWRITE_TAC[STDS_SS_DERIV] THEN
    MP_TAC(ISPECL [`p3s_rad_rho h`; `sqrt(p3s_rad_a h r)`; `\x:real. p3s_rad_rho h r1`;
                   `&0`; `atreal r`] HAS_REAL_DERIVATIVE_SUB) THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_CONST; STDS_RT_RHO_DERIV; REAL_SUB_RZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* F.                                                                         *)

let STDS_MFH_SMOOTH = prove
 (`!h. stds_rotm h ==> smooth_map_on (:real^1) (lift o stds_mFh h o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_mFh h = (\t. (\t. t) t * (\t. sqrt(p3s_rad_b h t)) t)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; stds_mFh]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_ID] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_RT_ROT_AB) THEN
  MP_TAC(ISPECL [`(:real^1)`; `lift o p3s_rad_b h o drop`] SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; o_THM; LIFT_DROP] THEN REWRITE_TAC[o_DEF]);;

let STDS_MFH_DERIV = prove
 (`!h r. stds_rotm h
         ==> (stds_mFh h has_real_derivative p3s_rs_f1 h r * sqrt(p3s_rad_a h r))
             (atreal r) /\
             real_derivative (stds_mFh h) r = p3s_rs_f1 h r * sqrt(p3s_rad_a h r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `stds_mFh h = (\r. r * sqrt(p3s_rad_b h r))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; stds_mFh]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC STDS_RT_H_DERIV THEN ASM_REWRITE_TAC[];
    MESON_TAC[HAS_REAL_DERIVATIVE_DERIVATIVE]]);;

let STDS_MFH_POS = prove
 (`!h r. stds_rotm h /\ &0 < r ==> &0 < stds_mFh h r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mFh] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_SIMP_TAC[STDS_RT_RS_AB_SQRT]);;

let STDS_MFH_DERIV_BOUNDS = prove
 (`!h r. stds_rgood h /\ &0 < r
         ==> &0 <= real_derivative (stds_mFh h) r /\
             real_derivative (stds_mFh h) r <= sqrt(p3s_rad_a h r)`,
  REWRITE_TAC[stds_rgood] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_MFH_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p3s_rs_f1 h r` ASSUME_TAC THENL
   [MATCH_MP_TAC STDS_RT_Q_NONNEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p3s_rs_f1 h r <= &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_Q_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p3s_rs_f1 h r`; `&1`] REAL_LE_SQUARE_ABS) THEN
    ASM_REWRITE_TAC[REAL_POW_ONE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* w and its integral.                                                        *)

let STDS_MW_SMOOTH = prove
 (`!h r1. stds_rotm h /\ &0 < r1
          ==> smooth_map_on (:real^1) (lift o stds_mw h r1 o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `stds_mw h r1 =
    (\t. real_derivative (stds_mFh h) t * (\t. (\t. &1) t - stds_mchi h r1 t) t)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stds_mw]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^1)`; `stds_mFh h`] P3S_S1_RDERIV) THEN
    ASM_SIMP_TAC[OPEN_UNIV; STDS_MFH_SMOOTH; ETA_AX];
    MATCH_MP_TAC P2C_S1_SUB THEN
    ASM_SIMP_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX; STDS_MCHI_SMOOTH]]);;

let STDS_MW_ZERO = prove
 (`!h r1 r. stds_rotm h /\ r <= r1 ==> stds_mw h r1 r = &0`,
  SIMP_TAC[stds_mw; STDS_MCHI_1; REAL_SUB_REFL; REAL_MUL_RZERO]);;

let STDS_MI_ZERO = prove
 (`!h r1 r. stds_rotm h /\ r <= r1
            ==> real_integral (real_interval[&0,r]) (stds_mw h r1) = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r < &0` THENL
   [SUBGOAL_THEN `real_interval[&0,r] = {}` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INTEGRAL_EMPTY]];
    TRANS_TAC EQ_TRANS `real_integral (real_interval[&0,r]) (\x:real. &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_MW_ZERO THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INTEGRAL_0]]]);;

let STDS_MI_DERIV = prove
 (`!h r1 r. stds_rotm h /\ &0 < r1
     ==> ((\r. real_integral (real_interval[&0,r]) (stds_mw h r1)) has_real_derivative
          stds_mw h r1 r) (atreal r)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r < r1` THENL
   [ASM_SIMP_TAC[STDS_MW_ZERO; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC P2C_DERIV_LOCALLY_CONST THEN
    MAP_EVERY EXISTS_TAC [`&0`; `r1 - r:real`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC STDS_MI_ZERO THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2C_INTEGRAL_DERIV_AT THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2C_S1_CONTINUOUS THEN ASM_SIMP_TAC[STDS_MW_SMOOTH]]);;

(* F_M.                                                                       *)

let STDS_MF_DERIV = prove
 (`!h r1 r. stds_rotm h /\ &0 < r1
     ==> (stds_mF h r1 has_real_derivative
          real_derivative (stds_mFh h) r * stds_mchi h r1 r) (atreal r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `stds_mF h r1 =
    (\r. stds_mFh h r - (\r. real_integral (real_interval[&0,r]) (stds_mw h r1)) r)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stds_mF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`stds_mFh h`; `real_derivative (stds_mFh h) r`;
                 `\r. real_integral (real_interval[&0,r]) (stds_mw h r1)`;
                 `stds_mw h r1 r`; `atreal r`] HAS_REAL_DERIVATIVE_SUB) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[STDS_MI_DERIV] THEN
    MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_MFH_DERIV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[stds_mw] THEN REAL_ARITH_TAC);;

let STDS_MF_SMOOTH = prove
 (`!h r1. stds_rotm h /\ &0 < r1
          ==> smooth_map_on (:real^1) (lift o stds_mF h r1 o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_REAL_DERIVATIVE_1D THEN
  EXISTS_TAC `\r. real_derivative (stds_mFh h) r * stds_mchi h r1 r` THEN
  ASM_SIMP_TAC[OPEN_UNIV; STDS_MF_DERIV] THEN
  MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^1)`; `stds_mFh h`] P3S_S1_RDERIV) THEN
    ASM_SIMP_TAC[OPEN_UNIV; STDS_MFH_SMOOTH; ETA_AX];
    ASM_SIMP_TAC[ETA_AX; STDS_MCHI_SMOOTH]]);;

let STDS_MF_LE = prove
 (`!h r1 r. stds_rotm h /\ r <= r1 ==> stds_mF h r1 r = stds_mFh h r`,
  SIMP_TAC[stds_mF; STDS_MI_ZERO; REAL_SUB_RZERO]);;

(* Constancy from a vanishing derivative on [r0,inf).                         *)

let STDS_CONST_FROM = prove
 (`!f r0 r. (!x. r0 <= x ==> (f has_real_derivative &0) (atreal x)) /\ r0 <= r
            ==> f r = f r0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `a <= b /\ --a <= --b ==> a = b`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STDS_DECR_FROM THEN EXISTS_TAC `\x:real. &0` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    MP_TAC(ISPECL [`\x. --((f:real->real) x)`; `\x:real. &0`; `r0:real`; `r:real`]
           STDS_DECR_FROM) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_NEG_0] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_SIMP_TAC[];
      REWRITE_TAC[]]]);;

let STDS_MF_MONO = prove
 (`!h r1 r s. stds_rgood h /\ &0 < r1 /\ r1 <= r /\ r <= s
              ==> stds_mF h r1 r <= stds_mF h r1 s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. --(stds_mF h r1 x)`;
                 `\x. --(real_derivative (stds_mFh h) x * stds_mchi h r1 x)`;
                 `r:real`; `s:real`] STDS_DECR_FROM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `z:real` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC STDS_MF_DERIV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ARITH `--x <= &0 <=> &0 <= x`] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[STDS_MCHI_BOUNDS] THEN
      MP_TAC(SPECL [`h:real^3->real^3^3`; `z:real`] STDS_MFH_DERIV_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    REAL_ARITH_TAC]);;

let STDS_MF_GE = prove
 (`!h r1 r. stds_rgood h /\ &0 < r1 /\ r1 <= r ==> stds_mFh h r1 <= stds_mF h r1 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`; `r1:real`; `r:real`] STDS_MF_MONO) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`; `r1:real`] STDS_MF_LE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[stds_rgood; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let STDS_MF_POS = prove
 (`!h r1 r. stds_rgood h /\ &0 < r1 /\ &0 < r ==> &0 < stds_mF h r1 r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  ASM_CASES_TAC `r <= r1` THENL
   [ASM_SIMP_TAC[STDS_MF_LE; STDS_MFH_POS];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `stds_mFh h r1` THEN
    ASM_SIMP_TAC[STDS_MFH_POS] THEN MATCH_MP_TAC STDS_MF_GE THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let STDS_MF_CONST = prove
 (`!h r1 r s. stds_rgood h /\ &0 < r1 /\ &0 <= r /\ r <= s /\
              p3s_rad_rho h r1 + &1 <= p3s_rad_rho h r
              ==> stds_mF h r1 s = stds_mF h r1 r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MATCH_MP_TAC STDS_CONST_FROM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`; `z:real`] STDS_MF_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `stds_mchi h r1 z = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC STDS_MCHI_0 THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p3s_rad_rho h r` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STDS_RHO_MONO THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_RZERO]]);;

(* The far value: c_M.                                                        *)

let STDS_MRE = prove
 (`!h r1. stds_rgood h
          ==> &0 <= stds_mre h r1 /\
              p3s_rad_rho h r1 + &1 <= p3s_rad_rho h (stds_mre h r1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stds_rgood] THEN STRIP_TAC THEN
  REWRITE_TAC[stds_mre] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `p3s_rad_rho h r1 + &1`] STDS_RT_RHO_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_LT_IMP_LE]);;

let STDS_MF_INF = prove
 (`!h r1 r. stds_rgood h /\ &0 < r1 /\ &0 <= r /\
            p3s_rad_rho h r1 + &1 <= p3s_rad_rho h r
            ==> stds_mF h r1 r pow 2 = &2 * stds_mc h r1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mc] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`] STDS_MRE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `stds_mF h r1 r = stds_mF h r1 (stds_mre h r1)` SUBST1_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH `r <= stds_mre h r1 \/ stds_mre h r1 <= r`) THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_MF_CONST THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC STDS_MF_CONST THEN ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;

let STDS_MC_POS = prove
 (`!h r1. stds_rgood h /\ &0 < r1 ==> &0 < stds_mc h r1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mc] THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`] STDS_MRE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < stds_mre h r1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `p3s_rad_rho h r1 + &1 <= p3s_rad_rho h (stds_mre h r1)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[P3S_RHO_0] THEN
    MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`] STDS_RT_RHO_POS_LE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC STDS_MF_POS THEN ASM_REWRITE_TAC[]);;

(* psi.                                                                       *)

let STDS_MPSI_0 = prove
 (`!h r1 r. p3s_rad_rho h r <= p3s_rad_rho h r1 + &2 ==> stds_mpsi h r1 r = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mpsi] THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
  ASM_REAL_ARITH_TAC);;

let STDS_MPSI_1 = prove
 (`!h r1 r. p3s_rad_rho h r1 + &3 <= p3s_rad_rho h r ==> stds_mpsi h r1 r = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mpsi] THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
  ASM_REAL_ARITH_TAC);;

let STDS_MPSI_BOUNDS = prove
 (`!h r1 r. &0 <= stds_mpsi h r1 r /\ stds_mpsi h r1 r <= &1`,
  REWRITE_TAC[stds_mpsi; SMOOTH_STEP_BOUNDS]);;

let STDS_MPSI_SMOOTH = prove
 (`!h r1. stds_rotm h /\ &0 < r1
          ==> smooth_map_on (:real^1) (lift o stds_mpsi h r1 o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x:real^1` THEN
  ASM_CASES_TAC `drop x < r1` THENL
   [EXISTS_TAC `{y:real^1 | drop y < r1}` THEN
    ASM_REWRITE_TAC[P2C_OPEN_DROP_LT; IN_ELIM_THM] THEN
    MATCH_MP_TAC P2C_S1_EQ THEN EXISTS_TAC `\t:real. &0` THEN
    REWRITE_TAC[P2C_OPEN_DROP_LT; P2C_S1_CONST; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC STDS_MPSI_0 THEN
    MP_TAC(SPECL [`h:real^3->real^3^3`; `drop(y:real^1)`; `r1:real`] STDS_RHO_MONO) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `{y:real^1 | &0 < drop y}` THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `stds_mpsi h r1 =
    (\t. smooth_step((\t. p3s_rad_rho h t - (\t. p3s_rad_rho h r1 + &2) t) t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; stds_mpsi] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_SMOOTH_STEP THEN REWRITE_TAC[P2C_OPEN_DROP_GT] THEN
  MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_CONST; ETA_AX] THEN
  ASM_SIMP_TAC[STDS_RT_RHO_SMOOTH]);;

(* A_M and B_M.                                                               *)

let STDS_MA_SMOOTH = prove
 (`!h g0 r1. stds_rotm h /\ stds_rotm g0 /\ &0 < r1
                ==> smooth_map_on (:real^1) (lift o stds_mA h g0 r1 o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `stds_mA h g0 r1 =
    (\t. (\t. (\t. &1) t - stds_mpsi h r1 t) t * p3s_rad_a h t +
         (\t. stds_mpsi h r1 t * (\t. stds_mc h r1) t) t * p3s_rad_a g0 t)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stds_mA] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `h:real^3->real^3^3` STDS_RT_ROT_AB) THEN
  MP_TAC(SPEC `g0:real^3->real^3^3` STDS_RT_ROT_AB) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2C_S1_ADD THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THEN
  MATCH_MP_TAC P2C_S1_MUL THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX] THENL
   [MATCH_MP_TAC P2C_S1_SUB THEN ASM_SIMP_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX;
                                             STDS_MPSI_SMOOTH];
    MATCH_MP_TAC P2C_S1_MUL THEN ASM_SIMP_TAC[OPEN_UNIV; P2C_S1_CONST; ETA_AX;
                                             STDS_MPSI_SMOOTH]]);;

let STDS_MA_POS = prove
 (`!h g0 r1 r. stds_rgood h /\ stds_rotm g0 /\ &0 < r1
                  ==> &0 < stds_mA h g0 r1 r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  REWRITE_TAC[stds_mA] THEN
  SUBGOAL_THEN `&0 < p3s_rad_a h r /\ &0 < stds_mc h r1 * p3s_rad_a g0 r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[STDS_RT_ROT_AB]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[STDS_MC_POS] THEN
    ASM_MESON_TAC[STDS_RT_ROT_AB];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`; `r:real`] STDS_MPSI_BOUNDS) THEN
  ABBREV_TAC `p = stds_mpsi h r1 r` THEN STRIP_TAC THEN
  ASM_CASES_TAC `p < &1` THENL
   [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    SUBGOAL_THEN `p = &1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]]);;

let STDS_MA_NEAR = prove
 (`!h g0 r1 r. p3s_rad_rho h r <= p3s_rad_rho h r1 + &2
               ==> stds_mA h g0 r1 r = p3s_rad_a h r`,
  SIMP_TAC[stds_mA; STDS_MPSI_0] THEN REAL_ARITH_TAC);;

let STDS_MA_FAR = prove
 (`!h g0 r1 r. p3s_rad_rho h r1 + &3 <= p3s_rad_rho h r
               ==> stds_mA h g0 r1 r = stds_mc h r1 * p3s_rad_a g0 r`,
  SIMP_TAC[stds_mA; STDS_MPSI_1] THEN REAL_ARITH_TAC);;

let STDS_MB_SMOOTH = prove
 (`!h r1. stds_rotm h /\ &0 < r1
          ==> smooth_map_on {s | &0 < drop s} (lift o stds_mB h r1 o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_mB h r1 = (\t. (\t. stds_mF h r1 t / (\t. t) t) t pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stds_mB]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_POW THEN REWRITE_TAC[P2C_OPEN_DROP_GT] THEN
  MATCH_MP_TAC P2C_S1_DIV THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_ID; IN_ELIM_THM; ETA_AX] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2C_S1_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; STDS_MF_SMOOTH];
    REAL_ARITH_TAC]);;

let STDS_MB_POS = prove
 (`!h r1 r. stds_rgood h /\ &0 < r1 /\ &0 < r ==> &0 < stds_mB h r1 r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mB] THEN MATCH_MP_TAC REAL_POW_LT THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[STDS_MF_POS]);;

let STDS_MB_SQRT = prove
 (`!h r1 r. stds_rgood h /\ &0 < r1 /\ &0 < r
            ==> r * sqrt(stds_mB h r1 r) = stds_mF h r1 r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mB] THEN
  SUBGOAL_THEN `&0 < stds_mF h r1 r / r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[STDS_MF_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

let STDS_MB_NEAR = prove
 (`!h r1 r. stds_rotm h /\ &0 < r /\ r <= r1 ==> stds_mB h r1 r = p3s_rad_b h r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mB] THEN ASM_SIMP_TAC[STDS_MF_LE; stds_mFh] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `sqrt(p3s_rad_b h r) pow 2 = p3s_rad_b h r` THEN
  UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The metric with radial coefficient A and tangential                      *)
(* coefficient B, B(|x|) I + ((A - B)/|x|^2) x x^T (stds_mform), and the    *)
(* modified metric stds_mod h g0 r1: h on the ball of radius r1, the form   *)
(* with A_M, B_M outside.  It is an SO(3)-invariant metric field whose      *)
(* radial profiles are A_M and B_M.                                         *)
(* ------------------------------------------------------------------------- *)

let stds_mform = new_definition
 `stds_mform (A:real->real) (B:real->real) (x:real^3) =
    B(norm x) %% mat 1 +
    ((A(norm x) - B(norm x)) / norm x pow 2) %% ((lambda i j. x$i * x$j):real^3^3)`;;

let stds_mod = new_definition
 `stds_mod (h:real^3->real^3^3) (g0:real^3->real^3^3) (r1:real) (x:real^3) =
    if norm x < r1 then h x else stds_mform (stds_mA h g0 r1) (stds_mB h r1) x`;;

let STDS_MFORM_BIL = prove
 (`!A B (x:real^3) w v.
     w dot (stds_mform A B x ** v) =
     A(norm x) * (w dot x) * (v dot x) / norm x pow 2 +
     B(norm x) * (w dot v - (w dot x) * (v dot x) / norm x pow 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stds_mform; MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL;
              MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL; DOT_RADD; DOT_RMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let STDS_MFORM_CONG = prove
 (`!A B A' B' (x:real^3). A(norm x) = A'(norm x) /\ B(norm x) = B'(norm x)
                          ==> stds_mform A B x = stds_mform A' B' x`,
  SIMP_TAC[stds_mform]);;

let STDS_MATRIX_EQ_BIL = prove
 (`!A B:real^3^3. (!w v. w dot (A ** v) = w dot (B ** v)) ==> A = B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `v:real^3` THEN
  REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN ASM_REWRITE_TAC[]);;

let STDS_ROT_MFORM = prove
 (`!h (x:real^3). stds_rotm h /\ ~(x = vec 0)
                  ==> h x = stds_mform (p3s_rad_a h) (p3s_rad_b h) x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_MATRIX_EQ_BIL THEN
  ASM_SIMP_TAC[STDS_MFORM_BIL; STDS_RT_ROT_BIL]);;

(* STDS_ORTH_DOT (orthogonal matrices preserve dot products) is in pc_p2c_stdasym. *)

let STDS_MFORM_ROT = prove
 (`!A B Q (x:real^3). orthogonal_matrix Q
                      ==> transp Q ** stds_mform A B (Q ** x) ** Q = stds_mform A B x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_MATRIX_EQ_BIL THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  REWRITE_TAC[STDS_MFORM_BIL] THEN ASM_SIMP_TAC[STDS_ORTH_DOT; ORTHOGONAL_MATRIX_NORM]);;

let STDS_OUTER_TRANSP = prove
 (`!x:real^3. transp((lambda i j. x$i * x$j):real^3^3) = (lambda i j. x$i * x$j)`,
  SIMP_TAC[CART_EQ; transp; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

(* Smoothness and the metric field property.                                  *)

let STDS_NORM_COMP_SMOOTH = prove
 (`!C. smooth_map_on {s | &0 < drop s} (lift o C o drop)
       ==> smooth_map_on ((:real^3) DELETE vec 0) (\x:real^3. lift(C(norm x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `{s:real^1 | &0 < drop s}`;
                 `\x:real^3. lift(norm x)`; `C:real->real`] SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; P2C_OPEN_DROP_GT; IN_ELIM_THM; IN_DELETE; IN_UNIV;
              LIFT_DROP; NORM_POS_LT; P3S_LIFT_NORM_SMOOTH] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let STDS_MFORM_SMOOTH = prove
 (`!A B. smooth_map_on {s | &0 < drop s} (lift o A o drop) /\
         smooth_map_on {s | &0 < drop s} (lift o B o drop)
         ==> smooth_map_on ((:real^3) DELETE vec 0)
               ((vectorize:real^3^3->real^(3,3)finite_prod) o stds_mform A B)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on {s | &0 < drop s}
                  (lift o (\r. (A r - B r) / r pow 2) o drop)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_S1_DIV THEN REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2C_S1_SUB THEN ASM_REWRITE_TAC[P2C_OPEN_DROP_GT; ETA_AX];
      MATCH_MP_TAC P2C_S1_POW THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_ID];
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; stds_mform; VECTORIZE_ADD; VECTORIZE_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[P3S_OPEN_PUNCT] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\x:real^3. lift(B(norm x))`;
                   `\x:real^3. (vectorize:real^3^3->real^(3,3)finite_prod) (mat 1)`]
                  SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; P3S_OPEN_PUNCT; SMOOTH_MAP_ON_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC STDS_NORM_COMP_SMOOTH THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`;
                   `\x:real^3. lift((A(norm x) - B(norm x)) / norm x pow 2)`;
                   `\x:real^3. (vectorize:real^3^3->real^(3,3)finite_prod)
                               ((lambda i j. x$i * x$j):real^3^3)`]
                  SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; P3S_OPEN_PUNCT] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP STDS_NORM_COMP_SMOOTH) THEN REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV; RFB_OUTER_SMOOTH]]]);;

let STDS_MFORM_POS = prove
 (`!A B (x:real^3) v. ~(x = vec 0) /\ ~(v = vec 0) /\ &0 < A(norm x) /\ &0 < B(norm x)
                      ==> &0 < v dot (stds_mform A B x ** v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STDS_MFORM_BIL] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `p = ((v:real^3) dot x) pow 2 / norm(x:real^3) pow 2` THEN
  SUBGOAL_THEN `((v:real^3) dot x) * (v dot x) / norm(x:real^3) pow 2 = p` SUBST1_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[REAL_POW_2; real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `p <= (v:real^3) dot v` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[NORM_POW_2] THEN
    MP_TAC(ISPECL [`v:real^3`; `x:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `abs a <= b ==> abs a <= abs b`)) THEN
    REWRITE_TAC[REAL_LE_SQUARE_ABS; REAL_POW_MUL; NORM_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (v:real^3) dot v` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 < p` THENL
   [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `p = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]);;

let STDS_MFORM_FIELD = prove
 (`!A B U. open U /\ U SUBSET (:real^3) DELETE vec 0 /\
           smooth_map_on {s | &0 < drop s} (lift o A o drop) /\
           smooth_map_on {s | &0 < drop s} (lift o B o drop) /\
           (!x. x IN U ==> &0 < A(norm x) /\ &0 < B(norm x))
           ==> metric_field U (stds_mform A B)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_field] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[STDS_MFORM_SMOOTH];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[stds_mform; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; TRANSP_MAT;
                STDS_OUTER_TRANSP];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_MFORM_POS THEN ASM_SIMP_TAC[]]);;

(* The modified metric.                                                       *)

let STDS_OPEN_OUTER = prove
 (`!r. open {y:real^3 | r < norm y}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{y:real^3 | r < norm y} = (:real^3) DIFF cball(vec 0,r)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_CBALL_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]]);;

let STDS_MOD_NEAR = prove
 (`!h g0 r1 (x:real^3). norm x < r1 ==> stds_mod h g0 r1 x = h x`,
  SIMP_TAC[stds_mod]);;

let STDS_MOD_FORM = prove
 (`!h g0 r1 (x:real^3).
     stds_rotm h /\ &0 < r1 /\ r1 / &2 < norm x
     ==> stds_mod h g0 r1 x = stds_mform (stds_mA h g0 r1) (stds_mB h r1) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mod] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[STDS_ROT_MFORM] THEN MATCH_MP_TAC STDS_MFORM_CONG THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_MA_NEAR THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= b + &2`) THEN
    MATCH_MP_TAC STDS_RHO_MONO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_MB_NEAR THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LT]]);;

let STDS_MOD_FIELD = prove
 (`!h g0 r1. stds_rgood h /\ stds_rotm g0 /\ &0 < r1
                ==> metric_field (:real^3) (stds_mod h g0 r1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (:real^3) h` ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_RT_METRIC_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field {x:real^3 | r1 / &2 < norm x}
                  (stds_mform (stds_mA h g0 r1) (stds_mB h r1))` ASSUME_TAC THENL
   [MATCH_MP_TAC STDS_MFORM_FIELD THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[STDS_OPEN_OUTER];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV; GSYM NORM_POS_LT] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2C_S1_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC STDS_MA_SMOOTH THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[STDS_MB_SMOOTH];
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC STDS_MA_POS THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC STDS_MB_POS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[metric_field; OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `norm(x:real^3) < r1` THENL
     [EXISTS_TAC `ball(vec 0:real^3,r1)` THEN
      ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `(vectorize:real^3^3->real^(3,3)finite_prod) o (h:real^3->real^3^3)` THEN
      REWRITE_TAC[OPEN_BALL; IN_BALL_0; o_THM] THEN CONJ_TAC THENL
       [SIMP_TAC[STDS_MOD_NEAR]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[metric_field];
      EXISTS_TAC `{y:real^3 | r1 / &2 < norm y}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `(vectorize:real^3^3->real^(3,3)finite_prod) o
                  stds_mform (stds_mA h g0 r1) (stds_mB h r1)` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_MOD_FORM THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[metric_field]]];
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `norm(x:real^3) < r1` THENL
     [ASM_SIMP_TAC[STDS_MOD_NEAR] THEN ASM_MESON_TAC[metric_field; IN_UNIV];
      SUBGOAL_THEN `stds_mod h g0 r1 x = stds_mform (stds_mA h g0 r1) (stds_mB h r1) x`
      SUBST1_TAC THENL
       [MATCH_MP_TAC STDS_MOD_FORM THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN {y:real^3 | r1 / &2 < norm y}` MP_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[metric_field]]]);;

let STDS_MOD_ROTM = prove
 (`!h g0 r1. stds_rgood h /\ stds_rotm g0 /\ &0 < r1
                ==> stds_rotm (stds_mod h g0 r1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_rotm] THEN CONJ_TAC THENL
   [MATCH_MP_TAC STDS_MOD_FIELD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Q:real^3^3`; `x:real^3`] THEN STRIP_TAC THEN
  REWRITE_TAC[stds_mod] THEN ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[STDS_MFORM_ROT] THEN
  UNDISCH_TAC `stds_rgood h` THEN REWRITE_TAC[stds_rgood; stds_rotm] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let STDS_MOD_PROFILES = prove
 (`!h g0 r1. stds_rgood h /\ &0 < r1
             ==> (!r. &0 <= r ==> p3s_rad_a (stds_mod h g0 r1) r = stds_mA h g0 r1 r) /\
                 (!r. &0 < r ==> p3s_rad_b (stds_mod h g0 r1) r = stds_mB h r1 r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 <= r ==> norm(r % basis 1:real^3) = r` ASSUME_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r (w:real^3). &0 < r ==>
        w dot (stds_mform (stds_mA h g0 r1) (stds_mB h r1) (r % basis 1) ** w) =
        stds_mA h g0 r1 r * (w$1) pow 2 + stds_mB h r1 r * (w dot w - (w$1) pow 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[STDS_MFORM_BIL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[DOT_RMUL; DOT_BASIS; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[DOT_SYM] THEN SIMP_TAC[DOT_LMUL; DOT_BASIS; DIMINDEX_3; ARITH] THEN
    SUBGOAL_THEN `~(r pow 2 = &0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `r:real` THEN DISCH_TAC THENL
   [REWRITE_TAC[p3s_rad_a; stds_mod] THEN
    SUBGOAL_THEN `norm(r % basis 1:real^3) = r` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `r < r1` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[GSYM p3s_rad_a] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_MA_NEAR THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= b + &2`) THEN
      MATCH_MP_TAC STDS_RHO_MONO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      SIMP_TAC[BASIS_COMPONENT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC];
    REWRITE_TAC[p3s_rad_b; stds_mod] THEN
    SUBGOAL_THEN `norm(r % basis 1:real^3) = r` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_CASES_TAC `r < r1` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[GSYM p3s_rad_b] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_MB_NEAR THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[] THEN
      SIMP_TAC[BASIS_COMPONENT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The curvature of the modified metric M = stds_mod h g0 r1.               *)
(* On the ball of radius r1 it is that of h.  Beyond, with q the warp       *)
(* derivative of h: r sqrt(b_M) = F_M and q_M sqrt(A_M) = F_M' = F' chi,    *)
(* so q_M = q chi while rho < rho(r1) + 2 (there A_M = a) and q_M = 0 once  *)
(* rho > rho(r1) + 1; hence K_tan(M) = (1 - (q chi)^2)/F_M^2 and            *)
(* K_rad(M) = -(q chi)'/(sqrt(a) F_M) >= 0, resp. 1/F_M^2 and 0.  With      *)
(* |sec h| <= Kh and r1 >= 1 every sectional curvature of M is bounded by   *)
(* stds_mK Kh F1, F1 = F(1).                                                *)
(* ------------------------------------------------------------------------- *)

let stds_css = new_definition
 `stds_css = @C. &0 < C /\ !t. &0 <= real_derivative smooth_step t /\
                              real_derivative smooth_step t <= C`;;

let STDS_CSS = prove
 (`&0 < stds_css /\ !t. &0 <= real_derivative smooth_step t /\
                        real_derivative smooth_step t <= stds_css`,
  REWRITE_TAC[stds_css] THEN CONV_TAC SELECT_CONV THEN REWRITE_TAC[STDS_SS_DBOUND]);;

let stds_mK = new_definition
 `stds_mK (Kh:real) (F1:real) =
    Kh * (&2 + &2 / F1) + stds_css / F1 + inv(F1 pow 2)`;;

(* Continuity of rho away from 0.                                             *)

let STDS_RHO_NEAR = prove
 (`!h r e. stds_rotm h /\ &0 < r /\ &0 < e
           ==> ?d. &0 < d /\
                   !s. abs(s - r) < d
                       ==> &0 < s /\ abs(p3s_rad_rho h s - p3s_rad_rho h r) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_RHO_DERIV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL) THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d r` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s:real = r` THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* r sqrt(b_M) = F_M and q_M sqrt(A_M) = F' chi.                              *)

let STDS_MOD_HF = prove
 (`!h g0 r1 s. stds_rgood h /\ &0 < r1 /\ &0 < s
     ==> s * sqrt(p3s_rad_b (stds_mod h g0 r1) s) = stds_mF h r1 s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `g0:real^3->real^3^3`; `r1:real`] STDS_MOD_PROFILES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[CONJUNCT2 th]) THEN
  MATCH_MP_TAC STDS_MB_SQRT THEN ASM_REWRITE_TAC[]);;

let STDS_MOD_F1 = prove
 (`!h g0 r1 s. stds_rgood h /\ stds_rotm g0 /\ &0 < r1 /\ &0 < s
     ==> p3s_rs_f1 (stds_mod h g0 r1) s * sqrt(stds_mA h g0 r1 s) =
         real_derivative (stds_mFh h) s * stds_mchi h r1 s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  SUBGOAL_THEN `stds_rotm (stds_mod h g0 r1)` ASSUME_TAC THENL
   [MATCH_MP_TAC STDS_MOD_ROTM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`stds_mod h g0 r1`; `s:real`] STDS_RT_H_DERIV) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `g0:real^3->real^3^3`; `r1:real`] STDS_MOD_PROFILES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[CONJUNCT1 th; REAL_LT_IMP_LE]) THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\s. s * sqrt(p3s_rad_b (stds_mod h g0 r1) s)`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`stds_mF h r1`; `s:real`] THEN
  ASM_SIMP_TAC[STDS_MF_DERIV] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC STDS_MOD_HF THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let STDS_MOD_F1_A = prove
 (`!h g0 r1 s. stds_rgood h /\ stds_rotm g0 /\ &0 < r1 /\ &0 < s /\
               p3s_rad_rho h s <= p3s_rad_rho h r1 + &2
     ==> p3s_rs_f1 (stds_mod h g0 r1) s = p3s_rs_f1 h s * stds_mchi h r1 s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `g0:real^3->real^3^3`; `r1:real`; `s:real`]
         STDS_MOD_F1) THEN
  ASM_SIMP_TAC[STDS_MA_NEAR] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `s:real`] STDS_MFH_DERIV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `s:real`] STDS_RT_RS_AB_SQRT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN UNDISCH_TAC `~(sqrt(p3s_rad_a h s) = &0)` THEN CONV_TAC REAL_FIELD);;

let STDS_MOD_F1_B = prove
 (`!h g0 r1 s. stds_rgood h /\ stds_rotm g0 /\ &0 < r1 /\ &0 < s /\
               p3s_rad_rho h r1 + &1 <= p3s_rad_rho h s
     ==> p3s_rs_f1 (stds_mod h g0 r1) s = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `g0:real^3->real^3^3`; `r1:real`; `s:real`]
         STDS_MOD_F1) THEN
  ASM_SIMP_TAC[STDS_MCHI_0; REAL_MUL_RZERO; REAL_ENTIRE] THEN
  SUBGOAL_THEN `&0 < sqrt(stds_mA h g0 r1 s)` (fun th -> MESON_TAC[th; REAL_LT_IMP_NZ]) THEN
  MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC STDS_MA_POS THEN ASM_REWRITE_TAC[]);;

(* The derivative of q_M in the two regions.                                  *)

let STDS_MOD_DF1_A = prove
 (`!h g0 r1 r. stds_rgood h /\ stds_rotm g0 /\ &0 < r1 /\ &0 < r /\
               p3s_rad_rho h r < p3s_rad_rho h r1 + &2
     ==> real_derivative (p3s_rs_f1 (stds_mod h g0 r1)) r =
         real_derivative (p3s_rs_f1 h) r * stds_mchi h r1 r +
         p3s_rs_f1 h r * --(real_derivative smooth_step (p3s_rad_rho h r - p3s_rad_rho h r1) *
                            sqrt(p3s_rad_a h r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`;
                `p3s_rad_rho h r1 + &2 - p3s_rad_rho h r`] STDS_RHO_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`\s. p3s_rs_f1 h s * stds_mchi h r1 s`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC STDS_MOD_F1_A THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`p3s_rs_f1 h`; `real_derivative (p3s_rs_f1 h) r`; `stds_mchi h r1`;
                   `--(real_derivative smooth_step (p3s_rad_rho h r - p3s_rad_rho h r1) *
                       sqrt(p3s_rad_a h r))`; `r:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ASM_SIMP_TAC[STDS_RT_RS_F1_DIFF; STDS_MCHI_DERIV] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let STDS_MOD_DF1_B = prove
 (`!h g0 r1 r. stds_rgood h /\ stds_rotm g0 /\ &0 < r1 /\ &0 < r /\
               p3s_rad_rho h r1 + &1 < p3s_rad_rho h r
     ==> real_derivative (p3s_rs_f1 (stds_mod h g0 r1)) r = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`;
                `p3s_rad_rho h r - (p3s_rad_rho h r1 + &1)`] STDS_RHO_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P2C_DERIV_LOCALLY_CONST THEN MAP_EVERY EXISTS_TAC [`&0`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC STDS_MOD_F1_B THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* K_tan and K_rad of M.                                                       *)

let STDS_MOD_K_A = prove
 (`!h g0 r1 r. stds_rgood h /\ stds_rotm g0 /\ &0 < r1 /\ &0 < r /\
               p3s_rad_rho h r < p3s_rad_rho h r1 + &2
     ==> p3s_rs_ktan (stds_mod h g0 r1) r =
         (&1 - (p3s_rs_f1 h r * stds_mchi h r1 r) pow 2) / stds_mF h r1 r pow 2 /\
         p3s_rs_krad (stds_mod h g0 r1) r =
         --((real_derivative (p3s_rs_f1 h) r * stds_mchi h r1 r +
             p3s_rs_f1 h r *
             --(real_derivative smooth_step (p3s_rad_rho h r - p3s_rad_rho h r1) *
                sqrt(p3s_rad_a h r))) * inv(sqrt(p3s_rad_a h r))) / stds_mF h r1 r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm (stds_mod h g0 r1)` ASSUME_TAC THENL
   [MATCH_MP_TAC STDS_MOD_ROTM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[STDS_RT_KTAN_EQ; STDS_RT_KRAD_EQ; p3s_rs_f2; STDS_MOD_HF] THEN
  ASM_SIMP_TAC[STDS_MOD_F1_A; STDS_MOD_DF1_A; REAL_LT_IMP_LE] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `g0:real^3->real^3^3`; `r1:real`] STDS_MOD_PROFILES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[CONJUNCT1 th; REAL_LT_IMP_LE]) THEN
  ASM_SIMP_TAC[STDS_MA_NEAR; REAL_LT_IMP_LE]);;

let STDS_MOD_K_B = prove
 (`!h g0 r1 r. stds_rgood h /\ stds_rotm g0 /\ &0 < r1 /\ &0 < r /\
               p3s_rad_rho h r1 + &1 < p3s_rad_rho h r
     ==> p3s_rs_ktan (stds_mod h g0 r1) r = inv(stds_mF h r1 r pow 2) /\
         p3s_rs_krad (stds_mod h g0 r1) r = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm (stds_mod h g0 r1)` ASSUME_TAC THENL
   [MATCH_MP_TAC STDS_MOD_ROTM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[STDS_RT_KTAN_EQ; STDS_RT_KRAD_EQ; p3s_rs_f2; STDS_MOD_HF;
               STDS_MOD_DF1_B; STDS_MOD_F1_B; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_NEG_0; real_div; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_SUB_RZERO; REAL_MUL_LID]);;

(* Signs.                                                                      *)

let STDS_MOD_K_NONNEG = prove
 (`!h g0 r1 r. stds_rgood h /\ stds_rotm g0 /\ &0 < r1 /\ &0 < r
     ==> &0 <= p3s_rs_ktan (stds_mod h g0 r1) r /\
         &0 <= p3s_rs_krad (stds_mod h g0 r1) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < stds_mF h r1 r` ASSUME_TAC THENL
   [MATCH_MP_TAC STDS_MF_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `p3s_rad_rho h r < p3s_rad_rho h r1 + &2` THENL
   [ALL_TAC;
    SUBGOAL_THEN `p3s_rad_rho h r1 + &1 < p3s_rad_rho h r` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[STDS_MOD_K_B; REAL_LE_REFL; REAL_LE_INV_EQ; REAL_LE_POW_2]] THEN
  ASM_SIMP_TAC[STDS_MOD_K_A] THEN
  UNDISCH_TAC `stds_rgood h` THEN REWRITE_TAC[stds_rgood] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_Q_NONNEG) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_Q_FACTS) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`; `r:real`] STDS_MCHI_BOUNDS) THEN
  MP_TAC(SPEC `p3s_rad_rho h r - p3s_rad_rho h r1` (CONJUNCT2 STDS_CSS)) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = p3s_rs_f1 h r` THEN
  ABBREV_TAC `dq = real_derivative (p3s_rs_f1 h) r` THEN
  ABBREV_TAC `ch = stds_mchi h r1 r` THEN
  ABBREV_TAC `ds = real_derivative smooth_step (p3s_rad_rho h r - p3s_rad_rho h r1)` THEN
  ABBREV_TAC `sa = sqrt(p3s_rad_a h r)` THEN
  ABBREV_TAC `fm = stds_mF h r1 r` THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2; REAL_SUB_LE] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN
    SUBGOAL_THEN `q <= &1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`q:real`; `&1`] REAL_LE_SQUARE_ABS) THEN
      ASM_REWRITE_TAC[REAL_POW_ONE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --x * c ==> &0 <= --(x * c)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `dq * ch <= &0` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= q * (ds * sa)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let STDS_MOD_SEC_NONNEG = prove
 (`!h g0 r1 (x:real^3) u v.
     stds_rgood h /\ stds_rotm g0 /\ &0 < r1 /\ ~collinear {vec 0,u,v}
     ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (stds_mod h g0 r1) x u v`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `norm(x:real^3) < r1` THENL
   [SUBGOAL_THEN `mfd_sectional (open_set_atlas (:real^3)) (stds_mod h g0 r1) x u v =
                  mfd_sectional (open_set_atlas (:real^3)) h x u v` SUBST1_TAC THENL
     [REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL] THEN MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
      EXISTS_TAC `ball(vec 0:real^3,r1)` THEN ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
      SIMP_TAC[IN_BALL_0; STDS_MOD_NEAR];
      ASM_MESON_TAC[stds_rgood]];
    SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC STDS_RT_SEC_NONNEG THEN
    ASM_SIMP_TAC[STDS_MOD_ROTM; STDS_MOD_K_NONNEG; GSYM NORM_POS_LT]]);;

(* Bounds.                                                                    *)

let STDS_MFH_MONO = prove
 (`!h a b. stds_rgood h /\ &0 < a /\ a <= b ==> stds_mFh h a <= stds_mFh h b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. --(stds_mFh h x)`; `\x. --(real_derivative (stds_mFh h) x)`;
                 `a:real`; `b:real`] STDS_DECR_FROM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `z:real` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN REWRITE_TAC[ETA_AX] THEN
      MP_TAC(SPECL [`h:real^3->real^3^3`; `z:real`] STDS_MFH_DERIV) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[REAL_ARITH `--x <= &0 <=> &0 <= x`] THEN
      MP_TAC(SPECL [`h:real^3->real^3^3`; `z:real`] STDS_MFH_DERIV_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    REAL_ARITH_TAC]);;

let STDS_MFH_RHO = prove
 (`!h a b. stds_rgood h /\ &0 < a /\ a <= b
           ==> stds_mFh h b - p3s_rad_rho h b <= stds_mFh h a - p3s_rad_rho h a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. stds_mFh h x - p3s_rad_rho h x`;
                 `\x. real_derivative (stds_mFh h) x - sqrt(p3s_rad_a h x)`;
                 `a:real`; `b:real`] STDS_DECR_FROM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `z:real` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
       [MP_TAC(SPECL [`h:real^3->real^3^3`; `z:real`] STDS_MFH_DERIV) THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC STDS_RT_RHO_DERIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      MP_TAC(SPECL [`h:real^3->real^3^3`; `z:real`] STDS_MFH_DERIV_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    REWRITE_TAC[]]);;

let STDS_DQ_BOUND = prove
 (`!h r Kh. stds_rgood h /\ &0 < r /\
            (!x u v. ~collinear {vec 0,u,v}
                     ==> abs(mfd_sectional (open_set_atlas (:real^3)) h x u v) <= Kh)
            ==> abs(real_derivative (p3s_rs_f1 h) r * inv(sqrt(p3s_rad_a h r))) <=
                Kh * stds_mFh h r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_SEC_RADIAL_PLANE) THEN
  ASM_SIMP_TAC[STDS_RT_KRAD_EQ; p3s_rs_f2] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r % basis 1:real^3`; `basis 1:real^3`; `basis 2:real^3`]) THEN
  ASM_REWRITE_TAC[P3S_NONCOLL_BASIS; GSYM stds_mFh] THEN
  SUBGOAL_THEN `&0 < stds_mFh h r` ASSUME_TAC THENL
   [MATCH_MP_TAC STDS_MFH_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NEG; REAL_ARITH `&0 < x ==> abs x = x`;
               REAL_LE_LDIV_EQ] THEN
  REAL_ARITH_TAC);;

let STDS_KRAD_ARITH = prove
 (`!Kh F1 Fr1 Fr fm css X Y.
     &0 <= Kh /\ &0 < F1 /\ F1 <= Fr1 /\ Fr1 <= fm /\ &0 <= Fr /\ Fr <= Fr1 + &2 /\
     &0 <= Y /\ Y <= css /\ abs X <= Kh * Fr
     ==> (abs X + Y) / fm <= Kh * (&2 + &2 / F1) + css / F1 + inv(F1 pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Fr1 /\ &0 < fm` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kh * (Fr1 + &2) + css` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs X + Y <= Kh * (Fr1 + &2) + css` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= b /\ c <= d ==> a + c <= b + d`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kh * Fr` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(abs X + Y) / fm <= (Kh * (Fr1 + &2) + css) / Fr1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kh * (Fr1 + &2) + css` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `Kh * (Fr1 + &2) + css = (Kh * (Fr1 + &2) + css) / Fr1 * Fr1`
    (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
     [UNDISCH_TAC `&0 < Fr1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Kh * (Fr1 + &2) + css) / Fr1` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Kh * (Fr1 + &2) + css) / Fr1 = Kh + (&2 * Kh + css) * inv Fr1`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < Fr1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * Kh + css) * inv Fr1 <= (&2 * Kh + css) * inv F1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(F1 pow 2)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC);;

let STDS_KTAN_ARITH = prove
 (`!Kh F1 fm z. &0 <= Kh /\ &0 < F1 /\ F1 <= fm /\ &0 <= z /\ z <= &1
                ==> abs((&1 - z) / fm pow 2) <= Kh * (&2 + &2 / F1) + stds_css / F1 +
                                                  inv(F1 pow 2) /\
                    abs(inv(fm pow 2)) <= Kh * (&2 + &2 / F1) + stds_css / F1 +
                                          inv(F1 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < fm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(fm pow 2) <= inv(F1 pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 / F1 /\ &0 <= stds_css / F1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; STDS_CSS; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kh * (&2 + &2 / F1) + stds_css / F1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < fm pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(fm pow 2)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `inv(fm pow 2) * fm pow 2 = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `&0 < inv(fm pow 2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN ASM_REAL_ARITH_TAC]);;

let STDS_MK_GE = prove
 (`!Kh F1. &0 <= Kh /\ &0 < F1 ==> &0 <= stds_mK Kh F1 /\ Kh <= stds_mK Kh F1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[stds_mK] THEN
  SUBGOAL_THEN `&0 <= &2 / F1 /\ &0 <= stds_css / F1 /\ &0 <= inv(F1 pow 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; STDS_CSS; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kh * &2 / F1` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[GSYM real_div];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC);;

let STDS_MOD_SEC_BOUND = prove
 (`!h g0 r1 Kh F1 (x:real^3) u v.
     stds_rgood h /\ stds_rotm g0 /\ &1 <= r1 /\ &0 <= Kh /\ &0 < F1 /\
     F1 <= stds_mFh h (&1) /\
     (!x u v. ~collinear {vec 0,u,v}
              ==> abs(mfd_sectional (open_set_atlas (:real^3)) h x u v) <= Kh) /\
     ~collinear {vec 0,u,v}
     ==> abs(mfd_sectional (open_set_atlas (:real^3)) (stds_mod h g0 r1) x u v) <=
         stds_mK Kh F1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`Kh:real`; `F1:real`] STDS_MK_GE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `norm(x:real^3) < r1` THENL
   [SUBGOAL_THEN `mfd_sectional (open_set_atlas (:real^3)) (stds_mod h g0 r1) x u v =
                  mfd_sectional (open_set_atlas (:real^3)) h x u v` SUBST1_TAC THENL
     [REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL] THEN MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
      EXISTS_TAC `ball(vec 0:real^3,r1)` THEN ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
      SIMP_TAC[IN_BALL_0; STDS_MOD_NEAR];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kh:real` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm(x:real^3)` THEN
  SUBGOAL_THEN `&0 < r /\ r1 <= r` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC STDS_RT_SEC_ABS THEN ASM_SIMP_TAC[STDS_MOD_ROTM; GSYM NORM_POS_LT] THEN
  SUBGOAL_THEN `F1 <= stds_mFh h r1 /\ stds_mFh h r1 <= stds_mF h r1 r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `stds_mFh h (&1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC STDS_MFH_MONO THEN ASM_REWRITE_TAC[REAL_LT_01];
      MATCH_MP_TAC STDS_MF_GE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `p3s_rad_rho h r < p3s_rad_rho h r1 + &2` THENL
   [ALL_TAC;
    SUBGOAL_THEN `p3s_rad_rho h r1 + &1 < p3s_rad_rho h r` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[STDS_MOD_K_B; REAL_ABS_0] THEN
    MP_TAC(SPECL [`Kh:real`; `F1:real`; `stds_mF h r1 r`; `&0`] STDS_KTAN_ARITH) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[stds_mK] THEN SIMP_TAC[]]] THEN
  ASM_SIMP_TAC[STDS_MOD_K_A] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_Q_NONNEG) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_Q_FACTS) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_RT_RS_AB_SQRT) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`; `r:real`] STDS_MCHI_BOUNDS) THEN
  MP_TAC(SPEC `p3s_rad_rho h r - p3s_rad_rho h r1` (CONJUNCT2 STDS_CSS)) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`; `Kh:real`] STDS_DQ_BOUND) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`; `r:real`] STDS_MFH_RHO) THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `r:real`] STDS_MFH_POS) THEN
  UNDISCH_TAC `stds_rgood h` THEN REWRITE_TAC[stds_rgood] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = p3s_rs_f1 h r` THEN
  ABBREV_TAC `dq = real_derivative (p3s_rs_f1 h) r` THEN
  ABBREV_TAC `ch = stds_mchi h r1 r` THEN
  ABBREV_TAC `ds = real_derivative smooth_step (p3s_rad_rho h r - p3s_rad_rho h r1)` THEN
  ABBREV_TAC `sa = sqrt(p3s_rad_a h r)` THEN
  ABBREV_TAC `fm = stds_mF h r1 r` THEN
  ABBREV_TAC `fr = stds_mFh h r` THEN
  ABBREV_TAC `fr1 = stds_mFh h r1` THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `q <= &1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`q:real`; `&1`] REAL_LE_SQUARE_ABS) THEN
      ASM_REWRITE_TAC[REAL_POW_ONE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`Kh:real`; `F1:real`; `fm:real`; `(q * ch) pow 2`] STDS_KTAN_ARITH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[stds_mK] THEN SIMP_TAC[]];
    SUBGOAL_THEN `q <= &1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`q:real`; `&1`] REAL_LE_SQUARE_ABS) THEN
      ASM_REWRITE_TAC[REAL_POW_ONE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(dq * ch + q * --(ds * sa)) * inv sa = dq * inv sa * ch - q * ds`
    SUBST1_TAC THENL [UNDISCH_TAC `~(sa = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < fm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NEG; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(abs(dq * inv sa * ch) + q * ds) / fm` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> abs(x - y) <= abs x + y`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[stds_mK] THEN MATCH_MP_TAC STDS_KRAD_ARITH THEN
      MAP_EVERY EXISTS_TAC [`fr1:real`; `fr:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * ds` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `dq * inv sa * ch = (dq * inv sa) * ch` SUBST1_TAC THENL
         [REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
        ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs(dq * inv sa) * &1` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[REAL_MUL_RID]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Far out the modified metric is c_M g0 (STDS_MOD_FAR).  The               *)
(* double of g0 (pc_p2c_stdflow) then carries any metric hd that is         *)
(* a constant multiple of g0 on the overlap of its two charts (stds_hneck): *)
(* the metric of the double with model hd has local expressions hd, is      *)
(* riemannian, has the sectional curvatures of hd and pulls back to hd by   *)
(* the embedding.  p3_std_initial g0 A0 holds for every A1 >= A0 (the       *)
(* cylinder is dilation invariant), so the overlap can be put far out.      *)
(* ------------------------------------------------------------------------- *)

let STDS_STD_ROTM = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> stds_rotm g0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_rotm] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[P3S_STD_METRIC_FIELD]; ASM_MESON_TAC[p3_std_initial]]);;

let STDS_NC_SCALE = prove
 (`!g0 A0 A1. p3_std_nc g0 A1 =
              (\w. exp((A1 - A0) / sqrt(&2)) % w) o p3_std_nc g0 A0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; p3_std_nc] THEN GEN_TAC THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let STDS_STD_INITIAL_MONO = prove
 (`!g0 A0 A1. p3_std_initial g0 A0 /\ A0 <= A1 ==> p3_std_initial g0 A1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^3) DELETE vec 0) (p3_std_nc g0 A0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P3S_NC_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 (vec 0) = &0` ASSUME_TAC THENL
   [ASM_MESON_TAC[P3S_DIST_0]; ALL_TAC] THEN
  UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `A1 < p3_std_dist g0 (vec 0)` THEN
    UNDISCH_TAC `p3_std_dist g0 (vec 0) = &0` THEN
    UNDISCH_TAC `&0 < A0` THEN UNDISCH_TAC `A0 <= A1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A1:real`] STDS_NC_SCALE) THEN
  MP_TAC(ISPECL [`p3_std_nc g0 A0`; `\w:real^3. exp((A1 - A0) / sqrt(&2)) % w`;
                 `cylinder_flow (&0)`; `x:real^3`] P2A_MPULLBACK_COMPOSE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[P3S_OPEN_PUNCT; IN_DELETE; IN_UNIV];
      MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN REWRITE_TAC[DIFFERENTIABLE_ID]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  GEN_REWRITE_TAC BINOP_CONV [mpullback] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`&0`; `exp((A1 - A0) / sqrt(&2))`; `mat 1:real^3^3`;
                 `p3_std_nc g0 A0 x`] STDS_CYL_CQ_PULLBACK) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID; ORTHOGONAL_MATRIX_ID; REAL_EXP_POS_LT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_SIMP_TAC[P3S_NC_NORM; REAL_EXP_POS_LT]);;

(* Far out, M = c_M g0.                                                        *)

let STDS_MOD_FAR = prove
 (`!h g0 A0 r1 (x:real^3).
     stds_rgood h /\ p3_std_initial g0 A0 /\ &0 < r1 /\
     p3s_rad_rho h r1 + &3 <= p3s_rad_rho h (norm x) /\ A0 < p3_std_dist g0 x
     ==> stds_mod h g0 r1 x = stds_mc h r1 %% g0 x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h /\ stds_rotm g0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[stds_rgood; STDS_STD_ROTM]; ALL_TAC] THEN
  SUBGOAL_THEN `r1 < norm(x:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`h:real^3->real^3^3`; `norm(x:real^3)`; `r1:real`] STDS_RHO_MONO) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[stds_mod; REAL_ARITH `r1 < n ==> ~(n < r1)`] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `x:real^3`] STDS_ROT_MFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[stds_mform; MATRIX_CMUL_ADD_LDISTRIB; MATRIX_CMUL_ASSOC] THEN
  ASM_SIMP_TAC[STDS_MA_FAR] THEN
  SUBGOAL_THEN `stds_mB h r1 (norm x) = stds_mc h r1 * p3s_rad_b g0 (norm(x:real^3))`
  SUBST1_TAC THENL
   [REWRITE_TAC[stds_mB] THEN
    SUBGOAL_THEN `p3s_rad_b g0 (norm(x:real^3)) = &2 / norm x pow 2` SUBST1_TAC THENL
     [MATCH_MP_TAC P3S_B_CYL THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[NORM_POS_LT] THEN ASM_MESON_TAC[P3S_ROT_DIST];
      ALL_TAC] THEN
    MP_TAC(SPECL [`h:real^3->real^3^3`; `r1:real`; `norm(x:real^3)`] STDS_MF_INF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* The double carrying hd.                                                     *)

let stds_hneck = new_definition
 `stds_hneck (g0:real^3->real^3^3) (A0:real) (R:real) (hd:real^3->real^3^3) <=>
    ?k. !z. z IN stds_neck g0 A0 R ==> hd z = k %% g0 z`;;

let stds_dmetric_h = new_definition
 `stds_dmetric_h (g0:real^3->real^3^3) (A0:real) (R:real) (hd:real^3->real^3^3)
                 (p:real^4) =
    hd(SND(chart_at (stds_atlas g0 A0 R) p) p)`;;

let STDS_REFL_ISOM_H = prove
 (`!g0 A0 R (hd:real^3->real^3^3) (x:real^3).
     p3_std_initial g0 A0 /\ A0 < R /\ x IN stds_neck g0 A0 R /\ stds_hneck g0 A0 R hd
     ==> mpullback (stds_refl g0 A0 R) hd x = hd x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stds_hneck] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `k:real`)))) THEN
  SUBGOAL_THEN `stds_refl g0 A0 R x IN stds_neck g0 A0 R` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_REFL_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[mpullback] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM mpullback] THEN
  MATCH_MP_TAC STDS_REFL_ISOM THEN ASM_REWRITE_TAC[]);;

let STDS_DMETRIC_H_LOCAL = prove
 (`!g0 A0 R (hd:real^3->real^3^3) c y.
     p3_std_initial g0 A0 /\ A0 < R /\ c IN stds_atlas g0 A0 R /\
     y IN stds_dom g0 A0 R /\ stds_hneck g0 A0 R hd
     ==> metric_local (stds_atlas g0 A0 R) c (stds_dmetric_h g0 A0 R hd) y = hd y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_ATLAS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `c:(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                 `FST(c:(real^4->bool)#(real^4->real^3))`;
                 `SND(c:(real^4->bool)#(real^4->real^3))`] CHART_INV) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  ABBREV_TAC `q = chart_inv (c:(real^4->bool)#(real^4->real^3)) y` THEN
  SUBGOAL_THEN `(q:real^4) IN FST(c:(real^4->bool)#(real^4->real^3)) /\
                SND(c:(real^4->bool)#(real^4->real^3)) q = y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                 `q:real^4`] CHART_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[metric_local; stds_dmetric_h] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `chart_at (stds_atlas g0 A0 R) q = (c:(real^4->bool)#(real^4->real^3))` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                   `FST(c:(real^4->bool)#(real^4->real^3))`;
                   `SND(c:(real^4->bool)#(real^4->real^3))`; `q:real^4`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID];
    ALL_TAC] THEN
  ABBREV_TAC `c' = chart_at (stds_atlas g0 A0 R) q` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`;
                 `c:(real^4->bool)#(real^4->real^3)`; `c':(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_TRANS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN stds_neck g0 A0 R` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `stds_neck g0 A0 R`)) THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `q:real^4` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(c':(real^4->bool)#(real^4->real^3)) q = stds_refl g0 A0 R y` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                   `FST(c:(real^4->bool)#(real^4->real^3))`;
                   `SND(c:(real^4->bool)#(real^4->real^3))`;
                   `FST(c':(real^4->bool)#(real^4->real^3))`;
                   `SND(c':(real^4->bool)#(real^4->real^3))`; `q:real^4`] CHART_TRANS_AT) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_jac (c:(real^4->bool)#(real^4->real^3)) c' q =
                frechet_derivative (stds_refl g0 A0 R) (at y)` SUBST1_TAC THENL
   [REWRITE_TAC[chart_jac] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `stds_neck g0 A0 R` THEN ASM_SIMP_TAC[STDS_NECK_OPEN];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM mpullback] THEN MATCH_MP_TAC STDS_REFL_ISOM_H THEN ASM_REWRITE_TAC[]);;

let STDS_DMETRIC_H_RIEM = prove
 (`!g0 A0 R (hd:real^3->real^3^3).
     p3_std_initial g0 A0 /\ A0 < R /\ metric_field (:real^3) hd /\ stds_hneck g0 A0 R hd
     ==> riemannian_metric (stds_atlas g0 A0 R) (stds_dmetric_h g0 A0 R hd)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric] THEN
  X_GEN_TAC `c:(real^4->bool)#(real^4->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `c:(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFB_METRIC_FIELD_EQ THEN EXISTS_TAC `hd:real^3->real^3^3` THEN
  ASM_SIMP_TAC[STDS_DMETRIC_H_LOCAL] THEN
  MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
  ASM_SIMP_TAC[STDS_DOM_OPEN; SUBSET_UNIV]);;

let STDS_DMETRIC_H_SEC = prove
 (`!g0 A0 R (hd:real^3->real^3^3) p u v.
     p3_std_initial g0 A0 /\ A0 < R /\ p IN sphere(vec 0:real^4,&1) /\
     stds_hneck g0 A0 R hd
     ==> mfd_sectional (stds_atlas g0 A0 R) (stds_dmetric_h g0 A0 R hd) p u v =
         mfd_sectional (open_set_atlas (:real^3)) hd
                       (SND(chart_at (stds_atlas g0 A0 R) p) p) u v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_ATLAS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                 `p:real^4`] CHART_AT) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (stds_atlas g0 A0 R) p` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `c:(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL] THEN
  REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `stds_dom g0 A0 R` THEN
  ASM_SIMP_TAC[STDS_DOM_OPEN; STDS_DMETRIC_H_LOCAL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && rand(concl th) = `stds_dom g0 A0 R`)) THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

let STDS_PHI_PULLBACK_H = prove
 (`!g0 A0 R (hd:real^3->real^3^3) (g:real^4->real^3^3) z.
     p3_std_initial g0 A0 /\ A0 < R /\ z IN stds_dom g0 A0 R /\ stds_hneck g0 A0 R hd /\
     (!p. p IN sphere(vec 0,&1) ==> g p = stds_dmetric_h g0 A0 R hd p)
     ==> rfs_pullback (stds_atlas g0 A0 R) (stds_phi g0 A0 R) g z = hd z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_ATLAS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_PHI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_phi g0 A0 R z IN sphere(vec 0:real^4,&1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`A0:real`; `R:real`] STDS_CDOM_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                 `stds_phi g0 A0 R z`] CHART_AT) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_pullback] THEN
  ABBREV_TAC `c = chart_at (stds_atlas g0 A0 R) (stds_phi g0 A0 R z)` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `c:(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (SND(c:(real^4->bool)#(real^4->real^3)) o stds_phi g0 A0 R) hd z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_PT THEN
    SUBGOAL_THEN `(SND(c:(real^4->bool)#(real^4->real^3)) o stds_phi g0 A0 R) z IN
                  stds_dom g0 A0 R` ASSUME_TAC THENL
     [REWRITE_TAC[o_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                   `c:(real^4->bool)#(real^4->real^3)`; `g:real^4->real^3^3`;
                   `stds_dmetric_h g0 A0 R hd`] PDE_METRIC_LOCAL_CONG) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o SPEC
      `(SND(c:(real^4->bool)#(real^4->real^3)) o stds_phi g0 A0 R) z`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC STDS_DMETRIC_H_LOCAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(c:(real^4->bool)#(real^4->real^3)) IN stds_atlas g0 A0 R` THEN
  REWRITE_TAC[STDS_ATLAS_CASES] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `mpullback (\x:real^3. x) hd z` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[P2B9_MPULLBACK_ID]] THEN
    MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN
    EXISTS_TAC `stds_dom g0 A0 R` THEN ASM_SIMP_TAC[STDS_DOM_OPEN; o_THM];
    SUBGOAL_THEN `(z:real^3) IN stds_neck g0 A0 R` ASSUME_TAC THENL
     [UNDISCH_TAC `stds_phi g0 A0 R z IN stds_cdom_s A0 R` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `mpullback (stds_refl g0 A0 R) hd z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `stds_neck g0 A0 R` THEN
      ASM_SIMP_TAC[STDS_NECK_OPEN; o_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^3) IN stds_dom g0 A0 R` ASSUME_TAC THENL
       [UNDISCH_TAC `(w:real^3) IN stds_neck g0 A0 R` THEN
        REWRITE_TAC[stds_neck; stds_dom; IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `stds_phi g0 A0 R w IN stds_cdom_n A0 R /\
                    stds_phi g0 A0 R w IN stds_cdom_s A0 R /\
                    stds_kinv g0 A0 R (stereo3_n (stds_phi g0 A0 R w)) = w`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `stds_phi g0 A0 R w`]
        STDS_TRANS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC STDS_REFL_ISOM_H THEN ASM_REWRITE_TAC[]]]);;

let STDS_DMETRIC_H_CURV = prove
 (`!g0 A0 R (hd:real^3->real^3^3) K p.
     p3_std_initial g0 A0 /\ A0 < R /\ p IN sphere(vec 0:real^4,&1) /\
     stds_hneck g0 A0 R hd /\
     (!x u v. ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) hd x u v /\
                  abs(mfd_sectional (open_set_atlas (:real^3)) hd x u v) <= K)
     ==> mfd_rm_norm (stds_atlas g0 A0 R) (stds_dmetric_h g0 A0 R hd) p <= K /\
         (!u v. ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (stds_atlas g0 A0 R) (stds_dmetric_h g0 A0 R hd) p u v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[STDS_DMETRIC_H_SEC];
    ASM_SIMP_TAC[STDS_DMETRIC_H_SEC]]);;

(* ------------------------------------------------------------------------- *)
(* Views of the flows of the doubles carrying the modified                  *)
(* metrics, with chart parameters Af n < Rf n; the exact slice limit h at   *)
(* time 0 on the exhaustion stds_W g0 (the modified metrics equal h there),  *)
(* and the region hypothesis of Prop 5.14 (as STDS_SLICE_LIMIT and          *)
(* STDS_P514_REGION of pc_p2c_stdflow).                                     *)
(* ------------------------------------------------------------------------- *)

let stds_hview = new_definition
 `stds_hview (g0:real^3->real^3^3) (Af:num->real) (Rf:num->real) (bf:num->real)
             (gf:num->real->real^4->real^3^3) (n:num) =
    rfs_flow_view (subtopology euclidean (sphere(vec 0:real^4,&1)),
                   stds_atlas g0 (Af n) (Rf n))
                  {s | &0 <= s /\ s < bf n} (gf n)`;;

let STDS_HVIEW_PARTS = prove
 (`!g0 Af Rf bf gf n s.
     rfs_vtop (stds_hview g0 Af Rf bf gf n) s =
       (if &0 <= s /\ s < bf n then subtopology euclidean (sphere(vec 0:real^4,&1))
        else discrete_topology {}) /\
     rfs_vatlas (stds_hview g0 Af Rf bf gf n) s = stds_atlas g0 (Af n) (Rf n) /\
     rfs_vmetric (stds_hview g0 Af Rf bf gf n) s = gf n s`,
  REWRITE_TAC[stds_hview; P2CF_FLOW_VIEW_PARTS; IN_ELIM_THM]);;

let STDS_HSLICE_LIMIT = prove
 (`!g0 A0 (h:real^3->real^3^3) (Af:num->real) (Rf:num->real)
    (Mf:num->real^3->real^3^3) (bf:num->real) (gf:num->real->real^4->real^3^3).
     p3_std_initial g0 A0 /\ metric_field (:real^3) h /\
     (!n. A0 <= Af n /\ Af n < Rf n) /\ (!n. &0 < bf n) /\
     (!n. stds_hneck g0 (Af n) (Rf n) (Mf n)) /\
     (!n x. x IN stds_W g0 n ==> Mf n x = h x) /\
     (!n. stds_W g0 n SUBSET stds_dom g0 (Af n) (Rf n)) /\
     (!n p. p IN sphere(vec 0,&1)
            ==> gf n (&0) p = stds_dmetric_h g0 (Af n) (Rf n) (Mf n) p)
     ==> p2c_slice_limit_with (stds_hview g0 Af Rf bf gf)
           (\n. stereo3_n_inv(vec 0)) (\n. &0) (\n. &1)
           (euclidean,open_set_atlas (:real^3)) h (vec 0) (stds_W g0)
           (\n. stds_phi g0 (Af n) (Rf n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. p3_std_initial g0 ((Af:num->real) n)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC STDS_STD_INITIAL_MONO THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_W_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2c_slice_limit_with; STDS_HVIEW_PARTS; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV; REAL_LT_01; STDS_RIEM_UNIV_EQ] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[stds_phi; STDS_K_0];
    X_GEN_TAC `k:num` THEN
    EXISTS_TAC `\p. stds_kinv g0 ((Af:num->real) k) ((Rf:num->real) k) (stereo3_n p)` THEN
    MATCH_MP_TAC STDS_PHI_DIFFEO THEN ASM_REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN];
    MAP_EVERY X_GEN_TAC [`K:real^3->bool`; `m:num`; `eta:real`] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `K:real^3->bool`] STDS_W_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(K:real^3->bool) SUBSET stds_W g0 k` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SIMP_TAC[RFB_OPEN_SET_CHART_AT; IN_UNIV; P2C_OPEN_SET_METRIC_LOCAL_UNIV] THEN
    REWRITE_TAC[STDS_CHART_INV_I; I_O_ID; MATRIX_CMUL_LID; ETA_AX] THEN
    MP_TAC(ISPECL [`m:num`; `h:real^3->real^3^3`; `h:real^3->real^3^3`;
                   `h:real^3->real^3^3`;
                   `rfs_pullback (stds_atlas g0 ((Af:num->real) k) ((Rf:num->real) k))
                                 (stds_phi g0 (Af k) (Rf k))
                                 ((gf:num->real->real^4->real^3^3) k (&0))`;
                   `stds_W g0 k`; `y:real^3`] LCK_DIST2_LOCAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(Mf:num->real^3->real^3^3) k z` THEN
      CONJ_TAC THENL [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_PHI_PULLBACK_H THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[P2BL_LCK_DIST2_REFL]]]);;

let STDS_HP514_REGION = prove
 (`!g0 A0 (Af:num->real) (Rf:num->real) c C K (bf:num->real)
    (gf:num->real->real^4->real^3^3).
     p3_std_initial g0 A0 /\ (!n. A0 <= Af n /\ Af n < Rf n) /\
     (!n. stds_W g0 n SUBSET stds_dom g0 (Af n) (Rf n)) /\ (!n. c / K < bf n) /\
     (!n t p. &0 <= t /\ t <= c / K /\ p IN sphere(vec 0,&1)
              ==> mfd_rm_norm (stds_atlas g0 (Af n) (Rf n)) (gf n t) p <= C * K)
     ==> !m a b. real_interval[a,b] SUBSET real_interval[&0,c / K]
           ==> ?CM N. !n. N <= n
                 ==> (!s. a <= s /\ s <= b
                          ==> IMAGE (stds_phi g0 (Af n) (Rf n)) (stds_W g0 m) SUBSET
                              topspace(rfs_vtop (stds_hview g0 Af Rf bf gf n) s)) /\
                     rfs_persists (stds_hview g0 Af Rf bf gf n)
                                  (IMAGE (stds_phi g0 (Af n) (Rf n)) (stds_W g0 m)) a b /\
                     !s y. a <= s /\ s <= b /\
                           y IN IMAGE (stds_phi g0 (Af n) (Rf n)) (stds_W g0 m)
                           ==> p3_vrm (stds_hview g0 Af Rf bf gf n) s y <= CM`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))))) THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:real`; `b:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> &0 <= s /\ s <= c / K` (LABEL_TAC "ab") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `s IN real_interval[&0,c / K]` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      REWRITE_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`C * K`; `m:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `p3_std_initial g0 ((Af:num->real) n) /\ Af n < (Rf:num->real) n`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STDS_STD_INITIAL_MONO THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (sphere(vec 0:real^4,&1)))
                  (IMAGE (stds_phi g0 ((Af:num->real) n) ((Rf:num->real) n)) (stds_W g0 m))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(Af:num->real) n`; `(Rf:num->real) n`;
                   `stds_W g0 m`] STDS_PHI_DIFFEO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_W_FACTS) THEN
        ASM_SIMP_TAC[OPEN_IN];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `stds_W g0 n` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_W_FACTS) THEN
        ASM_SIMP_TAC[]];
      SIMP_TAC[mfd_diffeo]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (stds_phi g0 ((Af:num->real) n) ((Rf:num->real) n)) (stds_W g0 m) SUBSET
                sphere(vec 0:real^4,&1)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
     `open_in (subtopology euclidean (sphere(vec 0:real^4,&1)))
              (IMAGE (stds_phi g0 ((Af:num->real) n) ((Rf:num->real) n)) (stds_W g0 m))`)) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b
                    ==> rfs_vtop (stds_hview g0 (Af:num->real) (Rf:num->real) bf gf n) s =
                        subtopology euclidean (sphere(vec 0:real^4,&1))` (LABEL_TAC "top") THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[STDS_HVIEW_PARTS] THEN
    SUBGOAL_THEN `&0 <= s /\ s < (bf:num->real) n` (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "ab" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `n:num` (ASSUME `!n. c / K < (bf:num->real) n`)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "top" (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= s /\ s <= b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "top" (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_SIMP_TAC[STDS_HVIEW_PARTS; STDS_ATLAS_SMOOTH];
    REWRITE_TAC[p3_vrm; STDS_HVIEW_PARTS] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^4`] THEN STRIP_TAC THEN
    USE_THEN "ab" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN USE_THEN "bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The restart.  For h with stds_rgood h, |sec h| <= Kh and                 *)
(* F1 <= F(1): the modified metrics M_n (cut at r1_n, equal to h on         *)
(* stds_W g0 n) live on doubles of g0 with the overlap pushed out (A1_n);   *)
(* the doubles flow for a time c/K, K = max 1 (stds_mK Kh F1), with         *)
(* |Rm| <= C K and sec >= 0; the limit by Prop 5.14 is a complete flow from *)
(* h on [0,c/K) with |Rm| <= C K and sec >= 0 (STDS_RESTART).               *)
(* ------------------------------------------------------------------------- *)

let STDS_RES_PARAMS = prove
 (`!g0 A0 h r1. p3_std_initial g0 A0 /\ stds_rgood h /\ &0 < r1
     ==> ?A1. A0 <= A1 /\
              (!x:real^3. norm x <= r1 ==> p3_std_dist g0 x < A1) /\
              (!x:real^3. A1 < p3_std_dist g0 x
                          ==> p3s_rad_rho h r1 + &3 <= p3s_rad_rho h (norm x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm h` ASSUME_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real^3->real^3^3`; `p3s_rad_rho h r1 + &3`] STDS_RT_RHO_UNBOUNDED) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[stds_rgood]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `r1 < r2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`h:real^3->real^3^3`; `r2:real`; `r1:real`] STDS_RHO_MONO) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `max A0 (p3s_rad_rho g0 r2) + &1` THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`; `r2:real`]
           P3S_RHO_LT_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `norm(x:real^3) < r2` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p3s_rad_rho h r2` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC STDS_RHO_MONO THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r2:real`; `norm(x:real^3)`]
           P3S_RHO_LT_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2 th)]) THEN
    UNDISCH_TAC `max A0 (p3s_rad_rho g0 r2) + &1 < p3_std_dist g0 x` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let STDS_RES_SETUP = prove
 (`!g0 A0 h Kh F1.
     p3_std_initial g0 A0 /\ stds_rgood h /\ &0 <= Kh /\ &0 < F1 /\
     F1 <= stds_mFh h (&1) /\
     (!x u v. ~collinear {vec 0,u,v}
              ==> abs(mfd_sectional (open_set_atlas (:real^3)) h x u v) <= Kh)
     ==> ?(Af:num->real) (Rf:num->real) (Mf:num->real^3->real^3^3).
           (!n. A0 <= Af n /\ Af n < Rf n) /\
           (!n. stds_hneck g0 (Af n) (Rf n) (Mf n)) /\
           (!n x. x IN stds_W g0 n ==> Mf n x = h x) /\
           (!n. stds_W g0 n SUBSET stds_dom g0 (Af n) (Rf n)) /\
           (!n. metric_field (:real^3) (Mf n)) /\
           (!n x u v. ~collinear {vec 0,u,v}
                      ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (Mf n) x u v /\
                          abs(mfd_sectional (open_set_atlas (:real^3)) (Mf n) x u v) <=
                          stds_mK Kh F1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_rotm g0` ASSUME_TAC THENL [ASM_MESON_TAC[STDS_STD_ROTM]; ALL_TAC] THEN
  ABBREV_TAC `r1 = \n:num. p3s_rad_rinv g0 (&n + &1) + &1` THEN
  SUBGOAL_THEN `!n. &1 <= (r1:num->real) n /\
                    !x:real^3. x IN stds_W g0 n ==> norm x < r1 n` (LABEL_TAC "r1f") THENL
   [GEN_TAC THEN EXPAND_TAC "r1" THEN BETA_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&n + &1`] P3S_RINV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `n:num`] STDS_W_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?A1. A0 <= A1 /\
             (!x:real^3. norm x <= (r1:num->real) n ==> p3_std_dist g0 x < A1) /\
             (!x:real^3. A1 < p3_std_dist g0 x
                         ==> p3s_rad_rho h (r1 n) + &3 <= p3s_rad_rho h (norm x))`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC STDS_RES_PARAMS THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "r1f" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `Af:num->real` (LABEL_TAC "af"))] THEN
  MAP_EVERY EXISTS_TAC [`Af:num->real`; `\n:num. (Af:num->real) n + &1`;
                        `\n:num. stds_mod h g0 ((r1:num->real) n)`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. &0 < (r1:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "r1f" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN USE_THEN "af" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
    X_GEN_TAC `n:num` THEN REWRITE_TAC[stds_hneck] THEN
    EXISTS_TAC `stds_mc h ((r1:num->real) n)` THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[stds_neck; IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC STDS_MOD_FAR THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "af" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC STDS_MOD_NEAR THEN ASM_MESON_TAC[];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[SUBSET; stds_dom; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "af" (MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[]; REAL_ARITH_TAC];
    GEN_TAC THEN MATCH_MP_TAC STDS_MOD_FIELD THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^3`; `u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC STDS_MOD_SEC_NONNEG THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC STDS_MOD_SEC_BOUND THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

(* PDE_CURVATURE_TIME on the doubles carrying hd.                             *)

let STDS_HDOUBLE_FLOWS = prove
 (`!d:real^4->bool.
     PDE_CURVATURE_TIME_STATEMENT d (:3)
     ==> ?c C. &0 < c /\ &0 < C /\
               !g0 A0 R (hd:real^3->real^3^3) K.
                 p3_std_initial g0 A0 /\ A0 < R /\ &0 < K /\ metric_field (:real^3) hd /\
                 stds_hneck g0 A0 R hd /\
                 (!x u v. ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) hd x u v /\
                              abs(mfd_sectional (open_set_atlas (:real^3)) hd x u v) <= K)
                 ==> ?b gf. c / K < b /\
                            ricci_flow_from (subtopology euclidean (sphere(vec 0,&1)),
                                             stds_atlas g0 A0 R) (&0) b gf /\
                            (!p. p IN sphere(vec 0,&1)
                                 ==> gf (&0) p = stds_dmetric_h g0 A0 R hd p) /\
                            (!t p. &0 <= t /\ t <= c / K /\ p IN sphere(vec 0,&1)
                                   ==> mfd_rm_norm (stds_atlas g0 A0 R) (gf t) p <= C * K)`,
  GEN_TAC THEN REWRITE_TAC[PDE_CURVATURE_TIME_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `C:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `R:real`;
                       `hd:real^3->real^3^3`; `K:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
     `stds_dmetric_h g0 A0 R hd`; `&0`; `K:real`]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; REAL_ADD_LID; DIMINDEX_3; ARITH] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[STDS_ATLAS_SMOOTH; STDS_DMETRIC_H_RIEM] THEN
    REWRITE_TAC[REWRITE_RULE[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] POINCARE_SMOOTH_HYPOTHESES_SPHERE_3] THEN
    X_GEN_TAC `p:real^4` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `hd:real^3->real^3^3`;
                   `K:real`; `p:real^4`] STDS_DMETRIC_H_CURV) THEN
    ASM_SIMP_TAC[];
    MESON_TAC[]]);;

(* Sectional curvatures depend only on the metric on the manifold.             *)

let STDS_MFD_SECTIONAL_CONG = prove
 (`!top atlas (g:A->real^N^N) g' x u v.
     smooth_manifold_atlas top atlas /\ x IN topspace top /\
     (!y. y IN topspace top ==> g y = g' y)
     ==> mfd_sectional atlas g x u v = mfd_sectional atlas g' x u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sectional] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFB_ATLAS_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_METRIC_LOCAL_CONG THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]]);;

(* sec >= 0 passes to limits (LIM_CURV, lower bound 0).                        *)

let STDS_LIM_SEC_NONNEG = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) (t:num->real) (Q:num->real) (J:real->bool) (top:B topology)
    (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) (xl:B)
    (W:num->B->bool) (phi:num->B->A) (s:real) (y:B).
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n. p2c_regular_view (V n)) /\
     s IN J /\ y IN topspace top /\ riemannian_metric atlas (g s) /\
     (!k z u v. z IN topspace (rfs_vtop (V k) (t k + s / Q k)) /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (rfs_vatlas (V k) (t k + s / Q k))
                                        (rfs_vmetric (V k) (t k + s / Q k)) z u v)
     ==> !u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas (g s) y u v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 (LABEL_TAC "rv")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")))))) THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o REWRITE_RULE[p2c_flow_limit_with]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n tau. ~(topspace(rfs_vtop
               ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) n) tau) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  (LABEL_TAC "reg") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `tau:real`] THEN DISCH_TAC THEN
    USE_THEN "rv" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:B)`] LIM_CURV) THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* The restart.                                                                 *)

let STDS_RESTART = prove
 (`!d:real^4->bool.
     PDE_CURVATURE_TIME_STATEMENT d (:3) /\ P2C_REQ_SEC_PRESERVED_STATEMENT d /\
     P2C_PROP_5_14_STATEMENT d (:real^3)
     ==> ?c C. &0 < c /\ &0 < C /\
           !g0 A0 h Kh F1.
             p3_std_initial g0 A0 /\ stds_rgood h /\ &0 <= Kh /\ &0 < F1 /\
             F1 <= stds_mFh h (&1) /\
             (!x u v. ~collinear {vec 0,u,v}
                      ==> abs(mfd_sectional (open_set_atlas (:real^3)) h x u v) <= Kh)
             ==> ?g. ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0)
                       (c / max (&1) (stds_mK Kh F1)) g /\
                     g (&0) = h /\
                     (!s. &0 <= s /\ s < c / max (&1) (stds_mK Kh F1)
                          ==> mfd_complete (euclidean,open_set_atlas (:real^3)) (g s)) /\
                     (!s y. &0 <= s /\ s < c / max (&1) (stds_mK Kh F1)
                            ==> mfd_rm_norm (open_set_atlas (:real^3)) (g s) y <=
                                C * max (&1) (stds_mK Kh F1)) /\
                     (!s y u v. &0 <= s /\ s < c / max (&1) (stds_mK Kh F1) /\
                                ~collinear {vec 0,u,v}
                                ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (g s) y u v)`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pde")
    (CONJUNCTS_THEN2 (LABEL_TAC "secp") (LABEL_TAC "p514"))) THEN
  USE_THEN "pde" (MP_TAC o MATCH_MP STDS_HDOUBLE_FLOWS) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fl"))))) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `C:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `h:real^3->real^3^3`;
                       `Kh:real`; `F1:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `K = max (&1) (stds_mK Kh F1)` THEN
  SUBGOAL_THEN `&0 < K /\ stds_mK Kh F1 <= K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (:real^3) h` ASSUME_TAC THENL
   [ASM_MESON_TAC[stds_rgood; STDS_RT_METRIC_FIELD]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `h:real^3->real^3^3`; `Kh:real`;
                `F1:real`] STDS_RES_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Af:num->real` (X_CHOOSE_THEN `Rf:num->real`
    (X_CHOOSE_THEN `Mf:num->real^3->real^3^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!n. p3_std_initial g0 ((Af:num->real) n)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC STDS_STD_INITIAL_MONO THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n x u v. ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional (open_set_atlas (:real^3))
                          ((Mf:num->real^3->real^3^3) n) x u v /\
                  abs(mfd_sectional (open_set_atlas (:real^3)) (Mf n) x u v) <= K`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:real^3`; `u:real^3`; `v:real^3`] o
      check (fun th -> can (find_term ((=) `stds_mK Kh F1`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?b (gg:real->real^4->real^3^3).
          c / K < b /\
          ricci_flow_from (subtopology euclidean (sphere(vec 0:real^4,&1)),
                           stds_atlas g0 ((Af:num->real) n) ((Rf:num->real) n)) (&0) b gg /\
          (!p. p IN sphere(vec 0,&1)
               ==> gg (&0) p =
                   stds_dmetric_h g0 (Af n) (Rf n) ((Mf:num->real^3->real^3^3) n) p) /\
          (!t p. &0 <= t /\ t <= c / K /\ p IN sphere(vec 0,&1)
                 ==> mfd_rm_norm (stds_atlas g0 (Af n) (Rf n)) (gg t) p <= C * K)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "fl" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `(Af:num->real) n`;
                                   `(Rf:num->real) n`; `(Mf:num->real^3->real^3^3) n`;
                                   `K:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `bf:num->real`
      (X_CHOOSE_THEN `gf:num->real->real^4->real^3^3` (LABEL_TAC "sk")))] THEN
  SUBGOAL_THEN `&0 < c / K` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < (bf:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `c / K` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* sec >= 0 on the doubles *)
  SUBGOAL_THEN
   `!n t p u v. &0 <= t /\ t < (bf:num->real) n /\ p IN sphere(vec 0:real^4,&1) /\
                ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (stds_atlas g0 ((Af:num->real) n) ((Rf:num->real) n))
                                        ((gf:num->real->real^4->real^3^3) n t) p u v`
  (LABEL_TAC "sec") THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "secp" (MP_TAC o SPECL
      [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
       `stds_atlas g0 ((Af:num->real) n) ((Rf:num->real) n)`; `&0`; `(bf:num->real) n`;
       `(gf:num->real->real^4->real^3^3) n`] o
      REWRITE_RULE[P2C_REQ_SEC_PRESERVED_STATEMENT]) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ANTS_TAC THENL
     [REWRITE_TAC[REWRITE_RULE[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]
                    POINCARE_SMOOTH_HYPOTHESES_SPHERE_3] THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`p:real^4`; `u:real^3`; `v:real^3`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
                     `stds_atlas g0 ((Af:num->real) n) ((Rf:num->real) n)`;
                     `(gf:num->real->real^4->real^3^3) n (&0)`;
                     `stds_dmetric_h g0 ((Af:num->real) n) ((Rf:num->real) n)
                                     ((Mf:num->real^3->real^3^3) n)`;
                     `p:real^4`; `u:real^3`; `v:real^3`] STDS_MFD_SECTIONAL_CONG) THEN
      ASM_SIMP_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; STDS_ATLAS_SMOOTH] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(Af:num->real) n`; `(Rf:num->real) n`;
                     `(Mf:num->real^3->real^3^3) n`; `K:real`; `p:real^4`]
                    STDS_DMETRIC_H_CURV) THEN
      ASM_SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "p514" (MP_TAC o SPECL
    [`stds_hview g0 (Af:num->real) (Rf:num->real) (bf:num->real)
                 (gf:num->real->real^4->real^3^3)`;
     `\n:num. stereo3_n_inv(vec 0)`; `\n:num. &0`; `\n:num. &1`;
     `real_interval[&0,c / K]`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
     `h:real^3->real^3^3`; `vec 0:real^3`; `stds_W g0`;
     `\n. stds_phi g0 ((Af:num->real) n) ((Rf:num->real) n)`] o
    REWRITE_RULE[P2C_PROP_5_14_STATEMENT]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_INTERVAL];
      ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `a0:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[stds_hview] THEN
      MATCH_MP_TAC(REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT]
                     (ISPEC `(:real^4)` P2C_FLOW_VIEW_REGULAR)) THEN
      ASM_REWRITE_TAC[REWRITE_RULE[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]
                        POINCARE_SMOOTH_HYPOTHESES_SPHERE_3];
      MATCH_MP_TAC STDS_HSLICE_LIMIT THEN EXISTS_TAC `A0:real` THEN
      EXISTS_TAC `Mf:num->real^3->real^3^3` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ADD_LID; REAL_DIV_1; REAL_MUL_RID] THEN
      MATCH_MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `Af:num->real`; `Rf:num->real`;
                           `c:real`; `C:real`; `K:real`; `bf:num->real`;
                           `gf:num->real->real^4->real^3^3`] STDS_HP514_REGION) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num`
    (X_CHOOSE_THEN `g:real->real^3->real^3^3` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `g:real->real^3->real^3^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (c / K)
                  (g:real->real^3->real^3^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. p2c_regular_view (stds_hview g0 (Af:num->real) (Rf:num->real) (bf:num->real)
                                     (gf:num->real->real^4->real^3^3) ((sub:num->num) n))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[stds_hview] THEN
    MATCH_MP_TAC(REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT]
                   (ISPEC `(:real^4)` P2C_FLOW_VIEW_REGULAR)) THEN
    ASM_REWRITE_TAC[REWRITE_RULE[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]
                      POINCARE_SMOOTH_HYPOTHESES_SPHERE_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. &0 <= s /\ s < c / K
          ==> mfd_rm_norm (open_set_atlas (:real^3)) ((g:real->real^3->real^3^3) s) y <=
              C * K`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
      [`\n. stds_hview g0 (Af:num->real) (Rf:num->real) (bf:num->real)
                       (gf:num->real->real^4->real^3^3) ((sub:num->num) n)`;
       `(\n:num. stereo3_n_inv(vec 0)) o (sub:num->num)`;
       `(\n:num. &0) o (sub:num->num)`; `(\n:num. &1) o (sub:num->num)`;
       `real_interval[&0,c / K]`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
       `g:real->real^3->real^3^3`; `vec 0:real^3`; `stds_W g0`;
       `(\n. stds_phi g0 ((Af:num->real) n) ((Rf:num->real) n)) o (sub:num->num)`;
       `s:real`; `y:real^3`; `C * K`] STDS_LIM_RM_BOUND) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[o_THM; REAL_ADD_LID; REAL_DIV_1; REAL_MUL_RID; STDS_HVIEW_PARTS] THEN
      MAP_EVERY X_GEN_TAC [`k:num`; `z:real^4`] THEN
      SUBGOAL_THEN `&0 <= s /\ s < (bf:num->real) ((sub:num->num) k)`
        (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `c / K` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN DISCH_TAC THEN
      USE_THEN "sk" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `(sub:num->num) k`) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `c / K`;
                   `g:real->real^3->real^3^3`; `C * K`] STDS_COMPLETE_FROM_BOUND) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_MESON_TAC[stds_rgood]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
    [`\n. stds_hview g0 (Af:num->real) (Rf:num->real) (bf:num->real)
                     (gf:num->real->real^4->real^3^3) ((sub:num->num) n)`;
     `(\n:num. stereo3_n_inv(vec 0)) o (sub:num->num)`;
     `(\n:num. &0) o (sub:num->num)`; `(\n:num. &1) o (sub:num->num)`;
     `real_interval[&0,c / K]`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
     `g:real->real^3->real^3^3`; `vec 0:real^3`; `stds_W g0`;
     `(\n. stds_phi g0 ((Af:num->real) n) ((Rf:num->real) n)) o (sub:num->num)`;
     `s:real`; `y:real^3`] STDS_LIM_SEC_NONNEG) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[o_THM; REAL_ADD_LID; REAL_DIV_1; REAL_MUL_RID; STDS_HVIEW_PARTS] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `z:real^4`; `u':real^3`; `v':real^3`] THEN
    SUBGOAL_THEN `&0 <= s /\ s < (bf:num->real) ((sub:num->num) k)`
      (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `c / K` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
    USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `c / K` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Gluing a restart.  A ricci_flow_from on [a,b) is smooth                  *)
(* through every interior time t1, so its chart jets converge as t -> t1-   *)
(* (STDS_RFF_JETS_LEFT, from the joint extension of ricci_flow_from and     *)
(* PDE_ST_UNIFORM_LEFT); a flow from G(t1), translated to start at t1,      *)
(* glues to G on [0,t1) by PDE_GLUE (STDS_GLUE).                            *)
(* ------------------------------------------------------------------------- *)

let STDS_RFF_TRANSLATE = prove
 (`!top atlas a b (g:real->A->real^N^N) s.
     ricci_flow_from (top,atlas) a b g
     ==> ricci_flow_from (top,atlas) (a + s) (b + s) (\t. g (t - s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RICCI_FLOW_TRANSLATE; REAL_ARITH `(a + s) - s = a:real`] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `\z. (Fm:real^(1,N)finite_sum->real^(N,N)finite_prod)
                  (pastecart (lift(&1 * drop(fstcart z) + --s)) (sndcart z))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFB_SMOOTH_TIME_AFFINE THEN
    MAP_EVERY EXISTS_TAC [`a - e:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFB_ATLAS_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_MESON_TAC[ricci_flow_on];
      REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REWRITE_TAC[REAL_MUL_LID; GSYM real_sub] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let STDS_RFF_JETS_LEFT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) t1.
     ricci_flow_from (top,atlas) a b g /\ a < t1 /\ t1 < b
     ==> !cc K l e. cc IN atlas /\ compact K /\ K SUBSET IMAGE (SND cc) (FST cc) /\
                    ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ &0 < e
                    ==> ?d. &0 < d /\
                            !t y. t1 - d < t /\ t < t1 /\ y IN K
                                  ==> norm(iterated_partial l
                                             ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                              metric_local atlas cc (g t)) y -
                                           iterated_partial l
                                             ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                              metric_local atlas cc (g t1)) y) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  DISCH_THEN(MP_TAC o SPEC `cc:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real`
    (X_CHOOSE_THEN `FE:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `U = IMAGE (SND(cc:(A->bool)#(A->real^N))) (FST cc)` THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC RFB_ATLAS_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_MESON_TAC[ricci_flow_from; ricci_flow_on];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. a <= t /\ t < b /\ y IN U
          ==> iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                  metric_local atlas cc ((g:real->A->real^N^N) t)) y =
              iterated_partial (MAP (\k. 1 + k) l) FE (pastecart (lift t) y)`
  (LABEL_TAC "SL") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `iterated_partial l (\y. (FE:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                         (pastecart (lift t) y)) (y:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_ST_SLICE_ITERATED THEN
      EXISTS_TAC `interval(lift(a - e0),lift b) PCROSS (U:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`iterated_partial (MAP (\k. 1 + k) l)
                    (FE:real^(1,N)finite_sum->real^(N,N)finite_prod)`;
                 `t1:real`; `t1 - a:real`; `b:real`; `U:real^N->bool`; `K:real^N->bool`]
                PDE_ST_UNIFORM_LEFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `t1 - (t1 - a) = a:real`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - e0),lift b) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_PCROSS; OPEN_INTERVAL] THEN
    MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (t1 - a)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "SL" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "SL" (MP_TAC o SPECL [`t1:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let STDS_GLUE = prove
 (`!(G:real->real^3->real^3^3) te t1 H dl.
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) te G /\ &0 < t1 /\ t1 < te /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) dl H /\ H (&0) = G t1
     ==> ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (t1 + dl)
           (\t. if t < t1 then G t else H (t - t1))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G' = \t. if t < t1 then (G:real->real^3->real^3^3) t else H (t - t1)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) t1
                  (G':real->real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_CONG THEN EXISTS_TAC `G:real->real^3->real^3^3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`&0`; `te:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "G'" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) t1 (t1 + dl)
                  (G':real->real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_CONG THEN EXISTS_TAC `\t. (H:real->real^3->real^3^3) (t - t1)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `dl:real`;
                     `H:real->real^3->real^3^3`; `t1:real`] STDS_RFF_TRANSLATE) THEN
      ASM_REWRITE_TAC[REAL_ADD_LID] THEN SUBST1_TAC(REAL_ARITH `dl + t1 = t1 + dl:real`) THEN
      SIMP_TAC[];
      EXPAND_TAC "G'" THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `~(t < t1)` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_RFF_FROM_ON THEN EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `(:3)`] PDE_GLUE) THEN REWRITE_TAC[PDE_GLUE_STATEMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `t1:real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`cc:(real^3->bool)#(real^3->real^3)`; `K:real^3->bool`;
                       `l:num list`; `e:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `te:real`;
                 `G:real->real^3->real^3^3`; `t1:real`] STDS_RFF_JETS_LEFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`cc:(real^3->bool)#(real^3->real^3)`; `K:real^3->bool`;
                             `l:num list`; `e:real`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(G':real->real^3->real^3^3) t = G t /\ G' t1 = G t1`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "G'" THEN ASM_REWRITE_TAC[REAL_LT_REFL; REAL_SUB_REFL];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* sec >= 0 of the maximal standard flow Gs on [0,Tm).  On                  *)
(* [0,T'] (T' < Tm) |sec Gs| and F(1) are uniformly controlled (the metric  *)
(* equivalence of RFA_METRIC_EQUIV), so the restarts have a uniform step    *)
(* delta; a restart at t1 = 0 is a partial standard flow, one at t1 > 0 is  *)
(* glued to Gs (STDS_GLUE), and uniqueness identifies both with Gs; an      *)
(* induction on the number of steps covers [0,T'].                          *)
(* ------------------------------------------------------------------------- *)

let stds_gs_hyps = new_definition
 `stds_gs_hyps <=>
    P2C_STD_PARTIAL_EXISTS_STATEMENT /\ P2C_STD_UNIQUE_STATEMENT /\
    P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
    P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3)`;;

let STDS_GS_BASICS = prove
 (`!g0 A0. stds_gs_hyps /\ p3_std_initial g0 A0
     ==> p3_partial_std g0 (stds_tm g0) (stds_gs g0) /\
         &0 < stds_tm g0 /\ stds_tm g0 <= &1 /\ stds_gs g0 (&0) = g0 /\
         (!t. &0 <= t /\ t < stds_tm g0
              ==> stds_rotm (stds_gs g0 t) /\
                  mfd_complete (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t)) /\
         (!te G t. p3_partial_std g0 te G /\ &0 <= t /\ t < te
                   ==> te <= stds_tm g0 /\ stds_gs g0 t = G t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stds_gs_hyps] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_FLOW) THEN
  ASM_REWRITE_TAC[p3_std_flow] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[p3_partial_std]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[p3_partial_std]] THEN
  REWRITE_TAC[stds_rotm] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM STDS_RIEM_UNIV_EQ] THEN
    UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN
    REWRITE_TAC[p3_partial_std; ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t = &0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[p3_std_initial];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_GS_SO3 THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[]]);;

(* Uniform bounds on [0,T'].                                                    *)

let STDS_GS_UNIF = prove
 (`!g0 A0 T'. stds_gs_hyps /\ p3_std_initial g0 A0 /\ &0 <= T' /\ T' < stds_tm g0
     ==> ?Kh F1. &0 <= Kh /\ &0 < F1 /\
                 !t. &0 <= t /\ t <= T'
                     ==> (!x u v. ~collinear {vec 0,u,v}
                                  ==> abs(mfd_sectional (open_set_atlas (:real^3))
                                                        (stds_gs g0 t) x u v) <= Kh) /\
                         F1 <= stds_mFh (stds_gs g0 t) (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `t2 = (T' + stds_tm g0) / &2` THEN
  SUBGOAL_THEN `T' < t2 /\ t2 < stds_tm g0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?K0. &0 <= K0 /\
                     !t x. &0 <= t /\ t <= t2
                           ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN
    REWRITE_TAC[p3_partial_std] THEN
    DISCH_THEN(MP_TAC o SPEC `t2:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K1:real`) THEN
    EXISTS_TAC `max (&0) K1` THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (stds_tm g0)
                  (stds_gs g0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_partial_std]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < stds_tm g0
                    ==> riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[STDS_RIEM_UNIV_EQ] THEN
    ASM_MESON_TAC[STDS_RT_METRIC_FIELD];
    ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_RIC_FROM_RMNORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RIC"))) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `t2:real`;
                 `stds_gs g0`; `Cr * K0`] RFA_METRIC_EQUIV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RFF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`&0`; `stds_tm g0`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "RIC" (MP_TAC o ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                                     `stds_gs g0 t`; `x:real^3`; `K0:real`; `v:real^3`]) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[REAL_MUL_ASSOC]] THEN
    REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; REAL_SUB_RZERO] THEN DISCH_THEN(LABEL_TAC "EQV")] THEN
  MAP_EVERY EXISTS_TAC
   [`K0:real`;
    `sqrt(exp(--(&2 * (Cr * K0) * T')) * p3s_rad_b g0 (&1))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_MESON_TAC[P3S_ROT_AB];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_NORM THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[stds_mFh; REAL_MUL_LID] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  SUBGOAL_THEN `&0 < p3s_rad_b g0 (&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P3S_ROT_AB]; ALL_TAC] THEN
  USE_THEN "EQV" (MP_TAC o SPECL [`t:real`; `&1 % basis 1:real^3`; `basis 2:real^3`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[GSYM p3s_rad_b] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
  SUBGOAL_THEN `(Cr * K0) * t <= (Cr * K0) * T'` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]; REAL_ARITH_TAC]);;

(* The theorem: sec >= 0 on [0,Tm).                                            *)

let STDS_GS_SEC_NONNEG = prove
 (`!d:real^4->bool.
     stds_gs_hyps /\ PDE_CURVATURE_TIME_STATEMENT d (:3) /\
     P2C_REQ_SEC_PRESERVED_STATEMENT d /\ P2C_PROP_5_14_STATEMENT d (:real^3)
     ==> !g0 A0. p3_std_initial g0 A0
                 ==> !t x u v. &0 <= t /\ t < stds_tm g0 /\ ~collinear {vec 0,u,v}
                               ==> &0 <= mfd_sectional (open_set_atlas (:real^3))
                                                       (stds_gs g0 t) x u v`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_RESTART) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rs"))))) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rc") (LABEL_TAC "un")))))) THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (stds_tm g0)
                  (stds_gs g0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_partial_std]; ALL_TAC] THEN
  (* one restart *)
  SUBGOAL_THEN
   `!Kh F1 t1.
      &0 <= Kh /\ &0 < F1 /\ &0 <= t1 /\ t1 < stds_tm g0 /\
      stds_rgood (stds_gs g0 t1) /\ F1 <= stds_mFh (stds_gs g0 t1) (&1) /\
      (!x u v. ~collinear {vec 0,u,v}
               ==> abs(mfd_sectional (open_set_atlas (:real^3)) (stds_gs g0 t1) x u v) <= Kh)
      ==> !t x u v. t1 <= t /\ t < stds_tm g0 /\
                    t < t1 + c / max (&1) (stds_mK Kh F1) /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (stds_gs g0 t) x u v`
  (LABEL_TAC "step") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "rs" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_gs g0 t1`;
                                   `Kh:real`; `F1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `dl = c / max (&1) (stds_mK Kh F1)` THEN
    ABBREV_TAC `K = max (&1) (stds_mK Kh F1)` THEN
    DISCH_THEN(X_CHOOSE_THEN `H:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["dl"; "K"] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `t1 = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `p3_partial_std g0 dl (H:real->real^3->real^3^3)` ASSUME_TAC THENL
       [REWRITE_TAC[p3_partial_std] THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `t2:real` THEN DISCH_TAC THEN EXISTS_TAC `C * K` THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      USE_THEN "un" (MP_TAC o SPECL [`dl:real`; `H:real->real^3->real^3^3`; `t:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `G' = \t. if t < t1 then stds_gs g0 t else (H:real->real^3->real^3^3) (t - t1)` THEN
    SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (t1 + dl)
                    (G':real->real^3->real^3^3)` ASSUME_TAC THENL
     [EXPAND_TAC "G'" THEN MATCH_MP_TAC STDS_GLUE THEN EXISTS_TAC `stds_tm g0` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?K1. !t x. &0 <= t /\ t <= t1
                             ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K1`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN
      REWRITE_TAC[p3_partial_std] THEN
      DISCH_THEN(MP_TAC o SPEC `t1:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p3_partial_std g0 (t1 + dl) (G':real->real^3->real^3^3)` ASSUME_TAC THENL
     [REWRITE_TAC[p3_partial_std] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "G'" THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "G'" THEN BETA_TAC THEN
        COND_CASES_TAC THENL
         [USE_THEN "rc" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
           [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        X_GEN_TAC `t2:real` THEN DISCH_TAC THEN EXISTS_TAC `max K1 (C * K)` THEN
        MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN STRIP_TAC THEN
        EXPAND_TAC "G'" THEN BETA_TAC THEN COND_CASES_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= max b c`) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= max b c`) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "un" (MP_TAC o SPECL [`t1 + dl`; `G':real->real^3->real^3^3`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN EXPAND_TAC "G'" THEN BETA_TAC THEN
    SUBGOAL_THEN `~(t < t1)` (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* induction on the number of steps *)
  MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`] STDS_GS_UNIF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kh:real` (X_CHOOSE_THEN `F1:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `dl = c / max (&1) (stds_mK Kh F1)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k s. &0 <= s /\ s <= t /\ s <= &k * (dl / &2)
          ==> !x u v. ~collinear {vec 0,u,v}
                      ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (stds_gs g0 s) x u v`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_MUL_LZERO] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[p3_std_initial];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s <= &k * (dl / &2)` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `t1 = &k * (dl / &2)` THEN
    SUBGOAL_THEN `&0 <= t1` ASSUME_TAC THENL
     [EXPAND_TAC "t1" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t1 <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "step" (MP_TAC o SPECL [`Kh:real`; `F1:real`; `t1:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[stds_rgood] THEN
        USE_THEN "rc" (MP_TAC o SPEC `t1:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `t1:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL];
        FIRST_ASSUM(MP_TAC o SPEC `t1:real` o
          check (fun th -> can (find_term ((=) `F1:real`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        FIRST_ASSUM(MP_TAC o SPEC `t1:real` o
          check (fun th -> can (find_term ((=) `F1:real`)) (concl th))) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `s <= &(SUC k) * dl / &2` THEN
    UNDISCH_TAC `~(s <= t1)` THEN UNDISCH_TAC `&0 < dl` THEN UNDISCH_TAC `s <= t` THEN
    UNDISCH_TAC `t < stds_tm g0` THEN EXPAND_TAC "t1" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `t / (dl / &2)` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `t:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `t / (dl / &2) <= &k` THEN
    SUBGOAL_THEN `&0 < dl / &2` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* MT Thm 12.5 (1) for the maximal flow: sec > 0 for 0 < t < Tm (strong      *)
(* maximum principle, the statement P2C_REQ_SMP_POS; the tip of g0 has       *)
(* sec = 1/4).                                                               *)

let STDS_GS_SEC_POS = prove
 (`!d:real^4->bool.
     stds_gs_hyps /\ PDE_CURVATURE_TIME_STATEMENT d (:3) /\
     P2C_REQ_SEC_PRESERVED_STATEMENT d /\ P2C_PROP_5_14_STATEMENT d (:real^3) /\
     P2C_REQ_SMP_POS_STATEMENT (:real^3)
     ==> !g0 A0. p3_std_initial g0 A0
                 ==> !t x u v. &0 < t /\ t < stds_tm g0 /\ ~collinear {vec 0,u,v}
                               ==> &0 < mfd_sectional (open_set_atlas (:real^3))
                                                      (stds_gs g0 t) x u v`,
  GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p3_std_dist g0 (vec 0) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_DIST_0 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?r0. &0 < r0 /\
                     !x u v. p3_std_dist g0 x < r0 /\ ~collinear {vec 0,u,v}
                             ==> mfd_sectional (open_set_atlas (:real^3)) g0 x u v = &1 / &4`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [p3_std_initial] o
                check (fun th -> concl th = `p3_std_initial g0 A0`)) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (stds_tm g0)
                  (stds_gs g0)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN
    SIMP_TAC[p3_partial_std];
    ALL_TAC] THEN
  UNDISCH_TAC `P2C_REQ_SMP_POS_STATEMENT (:real^3)` THEN
  REWRITE_TAC[P2C_REQ_SMP_POS_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                             `&0`; `stds_tm g0`; `stds_gs g0`; `vec 0:real^3`]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; HAUSDORFF_SPACE_EUCLIDEAN] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY) THEN
      REWRITE_TAC[SUBTOPOLOGY_UNIV; CONNECTED_UNIV];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^3`; `u:real^3`; `v:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
    SIMP_TAC[]]);;

