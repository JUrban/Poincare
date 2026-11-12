(* ========================================================================= *)
(* Unit pc_p2c_stdinit (Part 2C): an explicit standard initial metric on     *)
(* real^3 (MT Def 12.1) and MT Lemma 12.3 (P2_LEMMA_12_3_STATEMENT of        *)
(* pc_p3_iface), proved outright.                                            *)
(*                                                                           *)
(* The metric is radial and conformally flat, g0(x) = A(|x|^2) delta, with  *)
(*    A(u) = 16/(1+u)^2 exp(J(u)),   J(0) = 0,                              *)
(*    J'(u) = ((1-u)/(1+u)) (chi(u) - 1)/u,                                 *)
(* where chi is a smooth cutoff, 1 for u <= 1/32 and 0 for u >= 1: a convex *)
(* combination of the smooth steps chi_a (from 1 at a down to 0 at 2a) for  *)
(* a = 1/32 and a = 1/2, with weight p2c_std_theta chosen so that           *)
(* J(1) = -log 2 (J(1) is affine in the weight: no intermediate value       *)
(* argument).  Then g0 is the round metric of radius 2 for |x|^2 <= 1/32    *)
(* (curvature 1/4) and the cylinder (2/|x|^2) delta of radius sqrt 2 for    *)
(* |x| >= 1.  With m = A'/A and P = 1 + u m = chi(u)(1-u)/(1+u) (P is the   *)
(* derivative of the warping function in arclength), the curvature of a     *)
(* plane is a convex combination of the tangential value (1 - P^2)/(u A)    *)
(* and the radial value -2 P'/A, so sec >= 0 follows from |P| <= 1 and      *)
(* P' <= 0.  The distance from the tip is rho(|x|) with rho the integral of *)
(* sqrt(A(s^2)).                                                            *)
(* ========================================================================= *)

needs "src/pc_grg_vol.ml";;
needs "src/pc_lrg_evol.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_p3_iface.ml";;
needs "src/ns_cutoff.ml";;

prioritize_real();;
type_invention_error := true;;

(* The smooth step from 1 (for u <= a) down to 0 (for u >= 2a).            *)

let p2c_std_chi = new_definition
 `p2c_std_chi (a:real) (u:real) = &1 - smooth_step((u - a) / a)`;;

(* The integrand of J for the single cutoff chi_a, and its integral from 0. *)

let p2c_std_fj = new_definition
 `p2c_std_fj (a:real) (u:real) =
    ((&1 - u) / (&1 + u)) * ((p2c_std_chi a u - &1) / u)`;;

let p2c_std_ij = new_definition
 `p2c_std_ij (a:real) (u:real) =
    real_integral (real_interval[&0,u]) (p2c_std_fj a)`;;

(* The weight: J(1) = -log 2 for the combined cutoff.                       *)

let p2c_std_theta = new_definition
 `p2c_std_theta =
    (p2c_std_ij (&1 / &2) (&1) + log(&2)) /
    (p2c_std_ij (&1 / &2) (&1) - p2c_std_ij (&1 / &32) (&1))`;;

let p2c_std_cut = new_definition
 `p2c_std_cut (u:real) =
    p2c_std_theta * p2c_std_chi (&1 / &32) u +
    (&1 - p2c_std_theta) * p2c_std_chi (&1 / &2) u`;;

let p2c_std_J = new_definition
 `p2c_std_J (u:real) =
    p2c_std_theta * p2c_std_ij (&1 / &32) u +
    (&1 - p2c_std_theta) * p2c_std_ij (&1 / &2) u`;;

(* The derivative of J, and m = A'/A.                                       *)

let p2c_std_F = new_definition
 `p2c_std_F (u:real) =
    p2c_std_theta * p2c_std_fj (&1 / &32) u +
    (&1 - p2c_std_theta) * p2c_std_fj (&1 / &2) u`;;

let p2c_std_dcut = new_definition
 `p2c_std_dcut (u:real) =
    p2c_std_theta * real_derivative (p2c_std_chi (&1 / &32)) u +
    (&1 - p2c_std_theta) * real_derivative (p2c_std_chi (&1 / &2)) u`;;

let p2c_std_A = new_definition
 `p2c_std_A (u:real) = &16 / (&1 + u) pow 2 * exp(p2c_std_J u)`;;

let p2c_std_m = new_definition
 `p2c_std_m (u:real) = --(&2) / (&1 + u) + p2c_std_F u`;;

let p2c_std_dm = new_definition
 `p2c_std_dm (u:real) = &2 / (&1 + u) pow 2 + real_derivative p2c_std_F u`;;

(* The standard initial metric, the radial distance function of a radial    *)
(* conformal metric A(|x|^2) delta, and the radius beyond which g0 is the   *)
(* cylinder.                                                                 *)

let p2c_std_g0 = new_definition
 `p2c_std_g0 (x:real^3) = p2c_std_A (norm x pow 2) %% (mat 1:real^3^3)`;;

let p2c_rad_rho = new_definition
 `p2c_rad_rho (A:real->real) (r:real) =
    real_integral (real_interval[&0,r]) (\s. sqrt(A(s pow 2)))`;;

let p2c_std_A0 = new_definition
 `p2c_std_A0 = p2c_rad_rho p2c_std_A (&1)`;;

(* ------------------------------------------------------------------------- *)
(* Smooth real functions of one real variable (thin wrappers                 *)
(* of the vendored ns_smooth_elem rules for maps lift o g o drop).           *)
(* ------------------------------------------------------------------------- *)

let P2C_S1_CONST = prove
 (`!s c. smooth_map_on s (lift o (\t:real. c) o drop)`,
  REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_CONST]);;

let P2C_S1_ID = prove
 (`!s. smooth_map_on s (lift o (\t:real. t) o drop)`,
  REWRITE_TAC[o_DEF; LIFT_DROP; SMOOTH_MAP_ON_ID]);;

let P2C_S1_ADD = prove
 (`!s (f:real->real) g.
        open s /\ smooth_map_on s (lift o f o drop) /\
        smooth_map_on s (lift o g o drop)
        ==> smooth_map_on s (lift o (\t. f t + g t) o drop)`,
  REWRITE_TAC[o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. lift((f:real->real)(drop x))`;
                 `\x:real^1. lift((g:real->real)(drop x))`] SMOOTH_MAP_ON_LIFT_ADD) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2C_S1_SUB = prove
 (`!s (f:real->real) g.
        open s /\ smooth_map_on s (lift o f o drop) /\
        smooth_map_on s (lift o g o drop)
        ==> smooth_map_on s (lift o (\t. f t - g t) o drop)`,
  REWRITE_TAC[o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. lift((f:real->real)(drop x))`;
                 `\x:real^1. lift((g:real->real)(drop x))`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2C_S1_MUL = prove
 (`!s (f:real->real) g.
        open s /\ smooth_map_on s (lift o f o drop) /\
        smooth_map_on s (lift o g o drop)
        ==> smooth_map_on s (lift o (\t. f t * g t) o drop)`,
  REWRITE_TAC[o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. lift((f:real->real)(drop x))`;
                 `\x:real^1. lift((g:real->real)(drop x))`] SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2C_S1_DIV = prove
 (`!s (f:real->real) g.
        open s /\ smooth_map_on s (lift o f o drop) /\
        smooth_map_on s (lift o g o drop) /\
        (!x. x IN s ==> ~(g(drop x) = &0))
        ==> smooth_map_on s (lift o (\t. f t / g t) o drop)`,
  REWRITE_TAC[o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. lift((f:real->real)(drop x))`;
                 `\x:real^1. lift((g:real->real)(drop x))`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let P2C_S1_EXP = prove
 (`!s (f:real->real).
        open s /\ smooth_map_on s (lift o f o drop)
        ==> smooth_map_on s (lift o (\t. exp(f t)) o drop)`,
  REWRITE_TAC[o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. lift((f:real->real)(drop x))`]
    SMOOTH_MAP_ON_LIFT_EXP) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2C_S1_POW = prove
 (`!s (f:real->real) n.
        open s /\ smooth_map_on s (lift o f o drop)
        ==> smooth_map_on s (lift o (\t. f t pow n) o drop)`,
  REWRITE_TAC[o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. lift((f:real->real)(drop x))`; `n:num`]
    SMOOTH_MAP_ON_LIFT_POW) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2C_S1_SMOOTH_STEP = prove
 (`!s (f:real->real).
        open s /\ smooth_map_on s (lift o f o drop)
        ==> smooth_map_on s (lift o (\t. smooth_step(f t)) o drop)`,
  REWRITE_TAC[o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. lift((f:real->real)(drop x))`]
    SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2C_S1_SUBSET = prove
 (`!s t (f:real->real).
        s SUBSET t /\ smooth_map_on t (lift o f o drop)
        ==> smooth_map_on s (lift o f o drop)`,
  MESON_TAC[SMOOTH_MAP_ON_SUBSET]);;

let P2C_S1_EQ = prove
 (`!s (f:real->real) g.
        open s /\ (!x. x IN s ==> f(drop x) = g(drop x)) /\
        smooth_map_on s (lift o f o drop)
        ==> smooth_map_on s (lift o g o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `lift o (f:real->real) o drop` THEN ASM_SIMP_TAC[o_THM]);;

(* A smooth real function has its real_derivative as derivative. *)

let P2C_S1_DERIV = prove
 (`!s (f:real->real) x.
        open s /\ smooth_map_on s (lift o f o drop) /\ lift x IN s
        ==> (f has_real_derivative real_derivative f x) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real) real_differentiable (atreal x)` MP_TAC THENL
   [REWRITE_TAC[REAL_DIFFERENTIABLE_AT] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[real_differentiable; real_derivative] THEN
    DISCH_TAC THEN CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]]);;

(* Open half lines of real^1. *)

let P2C_OPEN_DROP_GT = prove
 (`!c. open {x:real^1 | c < drop x}`,
  REWRITE_TAC[drop; GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT]);;

let P2C_OPEN_DROP_LT = prove
 (`!c. open {x:real^1 | drop x < c}`,
  REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT]);;

(* Affine functions. *)

let P2C_S1_AFFINE = prove
 (`!s c d. smooth_map_on s (lift o (\t. c * t + d) o drop)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2C_S1_SUBSET THEN
  EXISTS_TAC `(:real^1)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\t:real. (c:real) * t + (d:real)`; `\t:real. (c:real)`]
    SMOOTH_MAP_ON_REAL_DERIVATIVE_1D) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; P2C_S1_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\t. (c:real) * t + (d:real)) has_real_derivative f') (atreal (drop(x:real^1)))`)) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;
(* ------------------------------------------------------------------------- *)
(* The smooth steps chi_a: values, bounds, monotonicity, smoothness and the  *)
(* sign of the derivative.                                                   *)
(* ------------------------------------------------------------------------- *)

let P2C_STD_CHI_1 = prove
 (`!a u. &0 < a /\ u <= a ==> p2c_std_chi a u = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_chi] THEN
  SUBGOAL_THEN `smooth_step((u - a) / a) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2C_STD_CHI_0 = prove
 (`!a u. &0 < a /\ &2 * a <= u ==> p2c_std_chi a u = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_chi] THEN
  SUBGOAL_THEN `smooth_step((u - a) / a) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2C_STD_CHI_BOUNDS = prove
 (`!a u. &0 <= p2c_std_chi a u /\ p2c_std_chi a u <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_std_chi] THEN
  MP_TAC(SPEC `(u - a) / a` SMOOTH_STEP_BOUNDS) THEN REAL_ARITH_TAC);;

let P2C_STD_CHI_MONO = prove
 (`!a u v. &0 < a /\ u <= v ==> p2c_std_chi a v <= p2c_std_chi a u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_chi] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 - y <= &1 - x`) THEN
  MATCH_MP_TAC SMOOTH_STEP_MONO THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC);;

let P2C_STD_CHI_SMOOTH = prove
 (`!s a. open s ==> smooth_map_on s (lift o p2c_std_chi a o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2c_std_chi a = (\t. (\t. &1) t - (\t. smooth_step((\t. inv a * t + --(a * inv a)) t)) t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2c_std_chi] THEN GEN_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_SUB THEN ASM_REWRITE_TAC[P2C_S1_CONST] THEN
  MATCH_MP_TAC P2C_S1_SMOOTH_STEP THEN ASM_REWRITE_TAC[P2C_S1_AFFINE]);;

(* The derivative of chi_a: nonpositive, and zero off [a,2a]. *)

let P2C_UNIV_NOT_SING = prove
 (`~(?a:real. (:real) = {a})`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_SING] THEN
  MESON_TAC[REAL_ARITH `~(a + &1 = a)`]);;

let P2C_STD_CHI_DERIV = prove
 (`!a u. (p2c_std_chi a has_real_derivative real_derivative (p2c_std_chi a) u)
         (atreal u)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2C_S1_DERIV THEN
  EXISTS_TAC `(:real^1)` THEN
  SIMP_TAC[OPEN_UNIV; IN_UNIV; P2C_STD_CHI_SMOOTH]);;

let P2C_STD_CHI_DERIV_LE = prove
 (`!a u. &0 < a ==> real_derivative (p2c_std_chi a) u <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. --(p2c_std_chi a t)`;
                 `\t. --(real_derivative (p2c_std_chi a) t)`; `(:real)`]
         HAS_REAL_DERIVATIVE_INCREASING) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; P2C_UNIV_NOT_SING; IN_UNIV; WITHINREAL_UNIV] THEN
  ANTS_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
    REWRITE_TAC[ETA_AX; P2C_STD_CHI_DERIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_NEG2] THEN
    MATCH_MP_TAC P2C_STD_CHI_MONO THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `u:real`) THEN REAL_ARITH_TAC]);;

(* A function constant near u has derivative 0 there. *)

let P2C_DERIV_LOCALLY_CONST = prove
 (`!f c u d. &0 < d /\ (!v. abs(v - u) < d ==> f v = c)
             ==> (f has_real_derivative &0) (atreal u)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\v:real. c:real`; `d:real`] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_CONST]);;

let P2C_STD_CHI_DERIV_ZERO = prove
 (`!a u. &0 < a /\ (u < a \/ &2 * a < u)
         ==> real_derivative (p2c_std_chi a) u = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`p2c_std_chi a`; `u:real`] THEN
  REWRITE_TAC[P2C_STD_CHI_DERIV] THENL
   [MATCH_MP_TAC P2C_DERIV_LOCALLY_CONST THEN
    MAP_EVERY EXISTS_TAC [`&1`; `a - u:real`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_STD_CHI_1 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2C_DERIV_LOCALLY_CONST THEN
    MAP_EVERY EXISTS_TAC [`&0`; `u - &2 * a:real`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_STD_CHI_0 THEN ASM_REAL_ARITH_TAC]);;
(* ------------------------------------------------------------------------- *)
(* The integrands fj_a and their integrals ij_a.                             *)
(* ------------------------------------------------------------------------- *)

let P2C_S1_CONTINUOUS = prove
 (`!s (f:real->real).
        smooth_map_on (:real^1) (lift o f o drop) ==> f real_continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
  ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS]);;

(* The integral of a continuous function is differentiable at interior     *)
(* points.                                                                   *)

let P2C_INTEGRAL_DERIV_AT = prove
 (`!f a x. f real_continuous_on real_interval[a,x + &1] /\ a < x
           ==> ((\u. real_integral (real_interval[a,u]) f) has_real_derivative f x)
               (atreal x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `a:real`; `x + &1`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\u. real_integral (real_interval[a,u]) (f:real->real)`; `(f:real->real) x`;
                 `x:real`; `real_interval(a,x + &1)`] HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN) THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `real_interval[a,x + &1]` THEN
  ASM_REWRITE_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED]);;

let P2C_STD_FJ_ZERO = prove
 (`!a u. &0 < a /\ u <= a ==> p2c_std_fj a u = &0`,
  SIMP_TAC[p2c_std_fj; P2C_STD_CHI_1; REAL_SUB_REFL; real_div; REAL_MUL_LZERO;
           REAL_MUL_RZERO]);;

let P2C_STD_FJ_NONPOS = prove
 (`!a u. &0 <= u /\ u <= &1 ==> p2c_std_fj a u <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_fj] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x * --y ==> x * y <= &0`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MP_TAC(SPECL [`a:real`; `u:real`] P2C_STD_CHI_BOUNDS) THEN ASM_REAL_ARITH_TAC]);;

let P2C_STD_FJ_FAR = prove
 (`!a u. &0 < a /\ &2 * a <= u ==> p2c_std_fj a u = &2 / (&1 + u) - inv u`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[p2c_std_fj; P2C_STD_CHI_0] THEN
  SUBGOAL_THEN `~(u = &0) /\ ~(&1 + u = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let P2C_STD_FJ_LOWER = prove
 (`!a u. &0 < u /\ u <= &1 ==> &2 / (&1 + u) - inv u <= p2c_std_fj a u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_fj] THEN
  SUBGOAL_THEN `&2 / (&1 + u) - inv u = ((&1 - u) / (&1 + u)) * ((&0 - &1) / u)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~(u = &0) /\ ~(&1 + u = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MP_TAC(SPECL [`a:real`; `u:real`] P2C_STD_CHI_BOUNDS) THEN REAL_ARITH_TAC]);;

let P2C_STD_FJ_SMOOTH = prove
 (`!a. &0 < a ==> smooth_map_on (:real^1) (lift o p2c_std_fj a o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x:real^1` THEN
  ASM_CASES_TAC `drop x < a` THENL
   [EXISTS_TAC `{y:real^1 | drop y < a}` THEN
    ASM_REWRITE_TAC[P2C_OPEN_DROP_LT; IN_ELIM_THM] THEN
    MATCH_MP_TAC P2C_S1_EQ THEN EXISTS_TAC `\t:real. &0` THEN
    REWRITE_TAC[P2C_OPEN_DROP_LT; P2C_S1_CONST; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2C_STD_FJ_ZERO THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `{y:real^1 | &0 < drop y}` THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_std_fj a =
    (\t. ((\t. --(&1) * t + &1) t / (\t. &1 * t + &1) t) *
         ((\t. p2c_std_chi a t - (\t. &1) t) t / (\t. t) t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2c_std_fj] THEN GEN_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[P2C_OPEN_DROP_GT] THEN
  CONJ_TAC THEN MATCH_MP_TAC P2C_S1_DIV THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_AFFINE; P2C_S1_ID; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN REAL_ARITH_TAC) THEN
  MATCH_MP_TAC P2C_S1_SUB THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_CONST; ETA_AX] THEN
  MATCH_MP_TAC P2C_STD_CHI_SMOOTH THEN REWRITE_TAC[P2C_OPEN_DROP_GT]);;

let P2C_STD_IJ_ZERO = prove
 (`!a u. &0 < a /\ u <= a ==> p2c_std_ij a u = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_ij] THEN
  ASM_CASES_TAC `u < &0` THENL
   [SUBGOAL_THEN `real_interval[&0,u] = {}` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INTEGRAL_EMPTY]];
    TRANS_TAC EQ_TRANS `real_integral (real_interval[&0,u]) (\x:real. &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_STD_FJ_ZERO THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INTEGRAL_0]]]);;

let P2C_STD_IJ_DERIV = prove
 (`!a u. &0 < a
         ==> (p2c_std_ij a has_real_derivative p2c_std_fj a u) (atreal u)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u < a` THENL
   [ASM_SIMP_TAC[P2C_STD_FJ_ZERO; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC P2C_DERIV_LOCALLY_CONST THEN
    MAP_EVERY EXISTS_TAC [`&0`; `a - u:real`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_STD_IJ_ZERO THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_std_ij a = (\u. real_integral (real_interval[&0,u]) (p2c_std_fj a))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2c_std_ij]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_INTEGRAL_DERIV_AT THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC P2C_S1_CONTINUOUS THEN ASM_SIMP_TAC[P2C_STD_FJ_SMOOTH]);;

let P2C_STD_IJ_SMOOTH = prove
 (`!a. &0 < a ==> smooth_map_on (:real^1) (lift o p2c_std_ij a o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_REAL_DERIVATIVE_1D THEN
  EXISTS_TAC `p2c_std_fj a` THEN
  ASM_SIMP_TAC[OPEN_UNIV; P2C_STD_FJ_SMOOTH; P2C_STD_IJ_DERIV]);;
(* ------------------------------------------------------------------------- *)
(* The two values ij_(1/32)(1) < -log 2 < ij_(1/2)(1), the weight theta in   *)
(* (0,1) and J(1) = -log 2.  L(u) = 2 log(1+u) - log u has derivative        *)
(* 2/(1+u) - 1/u, the value of fj_a beyond 2a.                               *)
(* ------------------------------------------------------------------------- *)

let P2C_STD_L_DERIV = prove
 (`!u. &0 < u
       ==> ((\u. &2 * log(&1 + u) - log u) has_real_derivative
            (&2 / (&1 + u) - inv u)) (atreal u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\u. &2 * log(&1 + u) - log u) has_real_derivative f') (atreal u)`)) THEN
  REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let P2C_STD_IJ_MINUS_L_CONST = prove
 (`!a b c. &0 < a /\ &2 * a <= b /\ b <= c
           ==> p2c_std_ij a c - (&2 * log(&1 + c) - log c) =
               p2c_std_ij a b - (&2 * log(&1 + b) - log b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\u. p2c_std_ij a u - (&2 * log(&1 + u) - log u)`;
                 `real_interval[b,c]`;
                 `p2c_std_ij a b - (&2 * log(&1 + b) - log b)`; `b:real`]
         HAS_REAL_DERIVATIVE_ZERO_UNIQUE) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
                  ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  SUBGOAL_THEN `&0 = p2c_std_fj a u - (&2 / (&1 + u) - inv u)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`a:real`; `u:real`] P2C_STD_FJ_FAR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
  ASM_SIMP_TAC[P2C_STD_IJ_DERIV; ETA_AX] THEN
  MATCH_MP_TAC P2C_STD_L_DERIV THEN ASM_REAL_ARITH_TAC);;

let P2C_STD_IJ_NONINCR = prove
 (`!a u v. &0 <= u /\ u <= v /\ v <= &1 /\ &0 < a
           ==> p2c_std_ij a v <= p2c_std_ij a u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\u. --(p2c_std_ij a u)`; `\u. --(p2c_std_fj a u)`;
                 `real_interval[&0,&1]`; `u:real`; `v:real`]
         HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL; REAL_LE_NEG2] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
    ASM_SIMP_TAC[P2C_STD_IJ_DERIV; ETA_AX];
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN REWRITE_TAC[REAL_NEG_GE0] THEN
    MATCH_MP_TAC P2C_STD_FJ_NONPOS THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2C_LOG_2_POS = prove
 (`&0 < log(&2)`,
  MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC);;

let P2C_STD_J1_LT = prove
 (`p2c_std_ij (&1 / &32) (&1) < --log(&2)`,
  MP_TAC(SPECL [`&1 / &32`; `&1 / &16`; `&1`] P2C_STD_IJ_MINUS_L_CONST) THEN
  MP_TAC(SPECL [`&1 / &32`; `&0`; `&1 / &16`] P2C_STD_IJ_NONINCR) THEN
  MP_TAC(SPECL [`&1 / &32`; `&0`] P2C_STD_IJ_ZERO) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[LOG_1] THEN
  SUBGOAL_THEN `log(&1 / &16) = --(&4 * log(&2)) /\ &0 < log(&17 / &16)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &16`; LOG_1] THEN
      SUBGOAL_THEN `&16 = &2 pow 4` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC P2C_LOG_2_POS THEN ASM_REAL_ARITH_TAC);;

let P2C_STD_J2_GT = prove
 (`--log(&2) < p2c_std_ij (&1 / &2) (&1)`,
  MP_TAC(ISPECL [`\u. p2c_std_ij (&1 / &2) u - (&2 * log(&1 + u) - log u)`;
                 `\u. p2c_std_fj (&1 / &2) u - (&2 / (&1 + u) - inv u)`;
                 `real_interval[&1 / &2,&1]`; `&1 / &2`; `&1`]
         HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
      SIMP_TAC[P2C_STD_IJ_DERIV; ETA_AX; REAL_ARITH `&0 < &1 / &2`] THEN
      MATCH_MP_TAC P2C_STD_L_DERIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC P2C_STD_FJ_LOWER THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1 / &2`; `&1 / &2`] P2C_STD_IJ_ZERO) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[LOG_1] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `log(&1 / &2) = --log(&2) /\ log(&3 / &2) < log(&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &2`; LOG_1] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2C_STD_THETA = prove
 (`&0 < p2c_std_theta /\ p2c_std_theta < &1`,
  REWRITE_TAC[p2c_std_theta] THEN
  MP_TAC P2C_STD_J1_LT THEN MP_TAC P2C_STD_J2_GT THEN
  SPEC_TAC(`p2c_std_ij (&1 / &2) (&1)`,`j2:real`) THEN
  SPEC_TAC(`p2c_std_ij (&1 / &32) (&1)`,`j1:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < j2 - j1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let P2C_STD_J_1 = prove
 (`p2c_std_J (&1) = --log(&2)`,
  REWRITE_TAC[p2c_std_J; p2c_std_theta] THEN
  MP_TAC P2C_STD_J1_LT THEN MP_TAC P2C_STD_J2_GT THEN
  SPEC_TAC(`p2c_std_ij (&1 / &2) (&1)`,`j2:real`) THEN
  SPEC_TAC(`p2c_std_ij (&1 / &32) (&1)`,`j1:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(j2 - j1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The combined cutoff, J and A; m = A'/A and P = 1 + u m.                   *)
(* ------------------------------------------------------------------------- *)

let P2C_S1_CMUL = prove
 (`!s c (f:real->real).
        open s /\ smooth_map_on s (lift o f o drop)
        ==> smooth_map_on s (lift o (\t. c * f t) o drop)`,
  REWRITE_TAC[o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `c:real`; `\x:real^1. lift((f:real->real)(drop x))`]
    SMOOTH_MAP_ON_LIFT_CMUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2C_STD_CUT_1 = prove
 (`!u. u <= &1 / &32 ==> p2c_std_cut u = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_cut] THEN
  SUBGOAL_THEN `p2c_std_chi (&1 / &32) u = &1 /\ p2c_std_chi (&1 / &2) u = &1`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2C_STD_CHI_1 THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2C_STD_CUT_0 = prove
 (`!u. &1 <= u ==> p2c_std_cut u = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_cut] THEN
  SUBGOAL_THEN `p2c_std_chi (&1 / &32) u = &0 /\ p2c_std_chi (&1 / &2) u = &0`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2C_STD_CHI_0 THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2C_STD_CUT_BOUNDS = prove
 (`!u. &0 <= p2c_std_cut u /\ p2c_std_cut u <= &1`,
  GEN_TAC THEN REWRITE_TAC[p2c_std_cut] THEN
  MP_TAC P2C_STD_THETA THEN
  MP_TAC(SPECL [`&1 / &32`; `u:real`] P2C_STD_CHI_BOUNDS) THEN
  MP_TAC(SPECL [`&1 / &2`; `u:real`] P2C_STD_CHI_BOUNDS) THEN
  SPEC_TAC(`p2c_std_chi (&1 / &32) u`,`c1:real`) THEN
  SPEC_TAC(`p2c_std_chi (&1 / &2) u`,`c2:real`) THEN
  SPEC_TAC(`p2c_std_theta`,`th:real`) THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `th * c1 <= th /\ (&1 - th) * c2 <= &1 - th
                             ==> th * c1 + (&1 - th) * c2 <= &1`) THEN
    CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let P2C_STD_CUT_DERIV = prove
 (`!u. (p2c_std_cut has_real_derivative p2c_std_dcut u) (atreal u)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `p2c_std_cut = (\u. p2c_std_theta * p2c_std_chi (&1 / &32) u +
                       (&1 - p2c_std_theta) * p2c_std_chi (&1 / &2) u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2c_std_cut]; ALL_TAC] THEN
  REWRITE_TAC[p2c_std_dcut] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  REWRITE_TAC[ETA_AX; P2C_STD_CHI_DERIV]);;

let P2C_STD_DCUT_LE = prove
 (`!u. p2c_std_dcut u <= &0`,
  GEN_TAC THEN REWRITE_TAC[p2c_std_dcut] THEN
  MP_TAC P2C_STD_THETA THEN
  MP_TAC(SPECL [`&1 / &32`; `u:real`] P2C_STD_CHI_DERIV_LE) THEN
  MP_TAC(SPECL [`&1 / &2`; `u:real`] P2C_STD_CHI_DERIV_LE) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 / &32 /\ &0 < &1 / &2`] THEN
  SPEC_TAC(`real_derivative (p2c_std_chi (&1 / &32)) u`,`d1:real`) THEN
  SPEC_TAC(`real_derivative (p2c_std_chi (&1 / &2)) u`,`d2:real`) THEN
  SPEC_TAC(`p2c_std_theta`,`th:real`) THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= th * --d1 /\ &0 <= (&1 - th) * --d2
                           ==> th * d1 + (&1 - th) * d2 <= &0`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let P2C_STD_DCUT_ZERO = prove
 (`!u. &1 < u ==> p2c_std_dcut u = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_dcut] THEN
  SUBGOAL_THEN `real_derivative (p2c_std_chi (&1 / &32)) u = &0 /\
                real_derivative (p2c_std_chi (&1 / &2)) u = &0`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2C_STD_CHI_DERIV_ZERO THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* F = J' in closed form, its smoothness and its zero region. *)

let P2C_STD_F_EQ = prove
 (`!u. p2c_std_F u = ((&1 - u) / (&1 + u)) * ((p2c_std_cut u - &1) / u)`,
  GEN_TAC THEN REWRITE_TAC[p2c_std_F; p2c_std_fj; p2c_std_cut; real_div] THEN
  REAL_ARITH_TAC);;

let P2C_STD_F_ZERO = prove
 (`!u. u <= &1 / &32 ==> p2c_std_F u = &0`,
  SIMP_TAC[P2C_STD_F_EQ; P2C_STD_CUT_1; REAL_SUB_REFL; real_div; REAL_MUL_LZERO;
           REAL_MUL_RZERO]);;

let P2C_STD_F_SMOOTH = prove
 (`smooth_map_on (:real^1) (lift o p2c_std_F o drop)`,
  SUBGOAL_THEN
   `p2c_std_F = (\t. (\t. p2c_std_theta * p2c_std_fj (&1 / &32) t) t +
                     (\t. (&1 - p2c_std_theta) * p2c_std_fj (&1 / &2) t) t)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2c_std_F]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_ADD THEN REWRITE_TAC[OPEN_UNIV] THEN
  CONJ_TAC THEN MATCH_MP_TAC P2C_S1_CMUL THEN REWRITE_TAC[OPEN_UNIV; ETA_AX] THEN
  MATCH_MP_TAC P2C_STD_FJ_SMOOTH THEN REAL_ARITH_TAC);;

let P2C_STD_F_DERIV = prove
 (`!u. (p2c_std_F has_real_derivative real_derivative p2c_std_F u) (atreal u)`,
  GEN_TAC THEN MATCH_MP_TAC P2C_S1_DERIV THEN EXISTS_TAC `(:real^1)` THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; P2C_STD_F_SMOOTH]);;

let P2C_STD_DF_ZERO = prove
 (`!u. u < &1 / &32 ==> real_derivative p2c_std_F u = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`p2c_std_F`; `u:real`] THEN
  REWRITE_TAC[P2C_STD_F_DERIV] THEN
  MATCH_MP_TAC P2C_DERIV_LOCALLY_CONST THEN
  MAP_EVERY EXISTS_TAC [`&0`; `&1 / &32 - u`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_STD_F_ZERO THEN ASM_REAL_ARITH_TAC);;

(* J: derivative F, smooth, zero near 0, explicit beyond 1. *)

let P2C_STD_J_DERIV = prove
 (`!u. (p2c_std_J has_real_derivative p2c_std_F u) (atreal u)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `p2c_std_J = (\u. p2c_std_theta * p2c_std_ij (&1 / &32) u +
                     (&1 - p2c_std_theta) * p2c_std_ij (&1 / &2) u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2c_std_J]; ALL_TAC] THEN
  REWRITE_TAC[p2c_std_F] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2C_STD_IJ_DERIV THEN REAL_ARITH_TAC);;

let P2C_STD_J_SMOOTH = prove
 (`smooth_map_on (:real^1) (lift o p2c_std_J o drop)`,
  MATCH_MP_TAC SMOOTH_MAP_ON_REAL_DERIVATIVE_1D THEN
  EXISTS_TAC `p2c_std_F` THEN
  REWRITE_TAC[OPEN_UNIV; P2C_STD_F_SMOOTH; P2C_STD_J_DERIV]);;

let P2C_STD_J_ZERO = prove
 (`!u. u <= &1 / &32 ==> p2c_std_J u = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_J] THEN
  SUBGOAL_THEN `p2c_std_ij (&1 / &32) u = &0 /\ p2c_std_ij (&1 / &2) u = &0`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2C_STD_IJ_ZERO THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2C_STD_J_FAR = prove
 (`!u. &1 <= u
       ==> p2c_std_J u = --log(&2) + (&2 * log(&1 + u) - log u) - &2 * log(&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&1 / &32`; `&1`; `u:real`] P2C_STD_IJ_MINUS_L_CONST) THEN
  MP_TAC(SPECL [`&1 / &2`; `&1`; `u:real`] P2C_STD_IJ_MINUS_L_CONST) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[LOG_1] THEN REPEAT DISCH_TAC THEN
  MP_TAC P2C_STD_J_1 THEN REWRITE_TAC[p2c_std_J] THEN
  SUBGOAL_THEN
   `p2c_std_ij (&1 / &32) u =
    p2c_std_ij (&1 / &32) (&1) + (&2 * log(&1 + u) - log u) - &2 * log(&2) /\
    p2c_std_ij (&1 / &2) u =
    p2c_std_ij (&1 / &2) (&1) + (&2 * log(&1 + u) - log u) - &2 * log(&2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`p2c_std_ij (&1 / &32) (&1)`,`j1:real`) THEN
  SPEC_TAC(`p2c_std_ij (&1 / &2) (&1)`,`j2:real`) THEN
  SPEC_TAC(`&2 * log(&1 + u) - log u`,`l:real`) THEN
  SPEC_TAC(`p2c_std_theta`,`th:real`) THEN
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;
(* A: values near the tip and beyond 1, positivity, smoothness, A' = A m.   *)

let P2C_STD_A_NEAR = prove
 (`!u. u <= &1 / &32 ==> p2c_std_A u = &16 / (&1 + u) pow 2`,
  SIMP_TAC[p2c_std_A; P2C_STD_J_ZERO; REAL_EXP_0; REAL_MUL_RID]);;

let P2C_STD_A_FAR = prove
 (`!u. &1 <= u ==> p2c_std_A u = &2 / u`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[p2c_std_A; P2C_STD_J_FAR] THEN
  SUBGOAL_THEN `&0 < u /\ &0 < &1 + u` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `--log(&2) + (&2 * log(&1 + u) - log u) - &2 * log(&2) =
    log((&1 + u) pow 2 / (&8 * u))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < (&1 + u) pow 2 /\ &0 < &8 * u` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_DIV; LOG_POW; LOG_MUL; REAL_ARITH `&0 < &8`] THEN
    SUBGOAL_THEN `&8 = &2 pow 3` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + u) pow 2 / (&8 * u)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN
  SUBGOAL_THEN `~(u = &0) /\ ~(&1 + u = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let P2C_STD_A_POS = prove
 (`!u. --(&1) < u ==> &0 < p2c_std_A u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_A] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC);;

let P2C_STD_A_SMOOTH = prove
 (`smooth_map_on {x:real^1 | --(&1) < drop x} (lift o p2c_std_A o drop)`,
  SUBGOAL_THEN
   `p2c_std_A =
    (\t. (\t. (\t. &16) t / (\t. (\t. &1 * t + &1) t pow 2) t) t *
         (\t. exp(p2c_std_J t)) t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2c_std_A] THEN GEN_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[P2C_OPEN_DROP_GT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2C_S1_DIV THEN
    REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_CONST; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_S1_POW THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_AFFINE];
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2C_S1_EXP THEN REWRITE_TAC[P2C_OPEN_DROP_GT; ETA_AX] THEN
    MATCH_MP_TAC P2C_S1_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV; P2C_STD_J_SMOOTH]]);;

let P2C_STD_A_DERIV = prove
 (`!u. --(&1) < u
       ==> (p2c_std_A has_real_derivative (p2c_std_A u * p2c_std_m u)) (atreal u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2c_std_A = (\u. &16 / (&1 + u) pow 2 * exp(p2c_std_J u))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2c_std_A]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\u. &16 / (&1 + u) pow 2) has_real_derivative (--(&32) / (&1 + u) pow 3))
    (atreal u)`
  ASSUME_TAC THENL
   [MP_TAC(DISCH_ALL(REAL_DIFF_CONV
      `((\u. &16 / (&1 + u) pow 2) has_real_derivative f') (atreal u)`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(&1 + u = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\u. exp(p2c_std_J u)) has_real_derivative (exp(p2c_std_J u) * p2c_std_F u))
    (atreal u)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2c_std_J`; `exp`; `p2c_std_F u`; `exp(p2c_std_J u)`; `u:real`]
                  REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[P2C_STD_J_DERIV; HAS_REAL_DERIVATIVE_EXP; o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. &16 / (&1 + u) pow 2`; `--(&32) / (&1 + u) pow 3`;
                 `\u. exp(p2c_std_J u)`; `exp(p2c_std_J u) * p2c_std_F u`;
                 `u:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p2c_std_m; p2c_std_A] THEN
  SUBGOAL_THEN `~(&1 + u = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* m: derivative dm, values near the tip. *)

let P2C_STD_M_DERIV = prove
 (`!u. --(&1) < u ==> (p2c_std_m has_real_derivative p2c_std_dm u) (atreal u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2c_std_m = (\u. --(&2) / (&1 + u) + p2c_std_F u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2c_std_m]; ALL_TAC] THEN
  REWRITE_TAC[p2c_std_dm] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
  REWRITE_TAC[ETA_AX; P2C_STD_F_DERIV] THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\u. --(&2) / (&1 + u)) has_real_derivative f') (atreal u)`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(&1 + u = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let P2C_STD_M_NEAR = prove
 (`!u. u < &1 / &32
       ==> p2c_std_m u = --(&2) / (&1 + u) /\ p2c_std_dm u = &2 / (&1 + u) pow 2`,
  SIMP_TAC[p2c_std_m; p2c_std_dm; P2C_STD_F_ZERO; P2C_STD_DF_ZERO; REAL_LT_IMP_LE;
           REAL_ADD_RID]);;

(* P = 1 + u m = cut(u) (1-u)/(1+u), its derivative, and the two signs. *)

let P2C_STD_P_EQ = prove
 (`!u. --(&1) < u
       ==> &1 + u * p2c_std_m u = p2c_std_cut u * ((&1 - u) / (&1 + u))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_m; P2C_STD_F_EQ] THEN
  ASM_CASES_TAC `u = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[P2C_STD_CUT_1; REAL_ARITH `&0 <= &1 / &32`] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `~(&1 + u = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(u = &0)` THEN CONV_TAC REAL_FIELD]);;

let P2C_STD_DP_EQ = prove
 (`!u. --(&1) < u
       ==> p2c_std_m u + u * p2c_std_dm u =
           p2c_std_dcut u * ((&1 - u) / (&1 + u)) -
           &2 * p2c_std_cut u / (&1 + u) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\u. p2c_std_cut u * ((&1 - u) / (&1 + u))`; `u:real`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\u. &1 + u * p2c_std_m u`; `&1 + u`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `v:real` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC P2C_STD_P_EQ THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`\u:real. u`; `&1`; `p2c_std_m`; `p2c_std_dm u`; `u:real`]
                    HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ID; P2C_STD_M_DERIV] THEN
      DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_ADD o
                 CONJ (SPECL [`&1`; `atreal u`] HAS_REAL_DERIVATIVE_CONST)) THEN
      BETA_TAC THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\u. (&1 - u) / (&1 + u)) has_real_derivative (--(&2) / (&1 + u) pow 2))
    (atreal u)`
  ASSUME_TAC THENL
   [MP_TAC(DISCH_ALL(REAL_DIFF_CONV
      `((\u. (&1 - u) / (&1 + u)) has_real_derivative f') (atreal u)`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(&1 + u = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2c_std_cut`; `p2c_std_dcut u`; `\u. (&1 - u) / (&1 + u)`;
                 `--(&2) / (&1 + u) pow 2`; `u:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[P2C_STD_CUT_DERIV] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let P2C_STD_P_SQ = prove
 (`!u. &0 <= u
       ==> (&1 + u * p2c_std_m u) pow 2 <= &1 /\
           (&0 < u ==> (&1 + u * p2c_std_m u) pow 2 < &1)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[P2C_STD_P_EQ; REAL_ARITH `&0 <= u ==> --(&1) < u`] THEN
  SUBGOAL_THEN `&0 < &1 + u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((&1 - u) / (&1 + u)) <= &1 /\
                (&0 < u ==> abs((&1 - u) / (&1 + u)) < &1)`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_LE_LDIV_EQ; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `u:real` P2C_STD_CUT_BOUNDS) THEN
  SPEC_TAC(`(&1 - u) / (&1 + u)`,`q:real`) THEN
  SPEC_TAC(`p2c_std_cut u`,`c:real`) THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= c /\ c <= &1 /\ abs q <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c * abs q <= abs q /\ &0 <= c * abs q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `abs q < &1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `2` REAL_POW_ONE)] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC]);;

let P2C_STD_DP_LE = prove
 (`!u. &0 <= u ==> p2c_std_m u + u * p2c_std_dm u <= &0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[P2C_STD_DP_EQ; REAL_ARITH `&0 <= u ==> --(&1) < u`] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &0 /\ &0 <= y ==> x - y <= &0`) THEN CONJ_TAC THENL
   [ASM_CASES_TAC `u <= &1` THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --d * q ==> d * q <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_ARITH `&0 <= --d <=> d <= &0`; P2C_STD_DCUT_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[P2C_STD_DCUT_ZERO; REAL_ARITH `~(u <= &1) ==> &1 < u`] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MP_TAC(SPEC `u:real` P2C_STD_CUT_BOUNDS) THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_POW_2]]]);;

let P2C_STD_M_FAR = prove
 (`!u. &1 < u ==> p2c_std_m u = --inv u /\ p2c_std_dm u = inv(u pow 2)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `--(&1) < u /\ ~(u = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `u:real` P2C_STD_P_EQ) THEN MP_TAC(SPEC `u:real` P2C_STD_DP_EQ) THEN
  ASM_SIMP_TAC[P2C_STD_CUT_0; P2C_STD_DCUT_ZERO; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_MUL_LZERO; real_div; REAL_MUL_RZERO; REAL_SUB_REFL] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `p2c_std_m u = --inv u` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 + u * p2c_std_m u = &0` THEN UNDISCH_TAC `~(u = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2c_std_m u + u * p2c_std_dm u = &0` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(u = &0)` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Radial conformal metrics G(z) = A(|z|^2) delta, for A smooth              *)
(* on (-1,inf), positive on [0,inf), with A' = A m and m' = dm on [0,inf):    *)
(* metric field, derivative, Christoffel symbols, curvature tensor; in       *)
(* real^3 the sectional and scalar curvature in closed form, with            *)
(* c1 = 2 m + m^2 |y|^2 and c2 = 2 dm - m^2 (the coefficients of             *)
(* LRG_RADIAL_RIEMANN).                                                      *)
(* ========================================================================= *)

let P2C_RAD_SMOOTH_COEFF = prove
 (`!A:real->real.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop)
     ==> smooth_map_on (:real^N) (\z. lift(A(norm z pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `{x:real^1 | --(&1) < drop x}`;
                 `\z:real^N. lift(norm z pow 2)`; `A:real->real`]
         SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; P2C_OPEN_DROP_GT; IN_UNIV; IN_ELIM_THM] THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN MP_TAC(SPEC `norm(y:real^N)` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]]);;

let P2C_RAD_METRIC = prove
 (`!A:real->real.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u)
     ==> metric_field (:real^N) (\z. A(norm z pow 2) %% mat 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_field; OPEN_UNIV; IN_UNIV] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z:real^N. A(norm z pow 2) %% mat 1) =
      (\z. drop((\z:real^N. lift(A(norm z pow 2))) z) % vectorize(mat 1:real^N^N))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; P2C_RAD_SMOOTH_COEFF];
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_VECTOR_LMUL;
                MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[DOT_POS_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LE_POW_2]]);;

let P2C_RAD_FUN_DERIV = prove
 (`!(f:real->real) f' (z:real^N).
     (!u. &0 <= u ==> (f has_real_derivative f' u) (atreal u))
     ==> ((\x. lift(f(norm x pow 2))) has_derivative
          (\h. lift((&2 * f'(norm z pow 2)) * (z dot h)))) (at z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `(f':real->real)(norm(z:real^N) pow 2)`;
                 `\x:real^N. lift(norm x pow 2)`; `\h:real^N. &2 % lift(z dot h)`;
                 `z:real^N`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_SIMP_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT; REAL_LE_POW_2] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL] THEN
  GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let P2C_RAD_MDERIV = prove
 (`!A m (z:real^N) a.
     (!u. &0 <= u ==> (A has_real_derivative (A u * m u)) (atreal u))
     ==> mderiv (\z. A(norm z pow 2) %% mat 1) z a =
         (&2 * (A(norm z pow 2) * m(norm z pow 2)) * (z dot a)) %% mat 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o
    (\z:real^N. A(norm z pow 2) %% mat 1) =
    (\x. A(norm x pow 2) % vectorize(mat 1:real^N^N))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real->real`; `\u:real. A u * m u`; `z:real^N`]
         P2C_RAD_FUN_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o ISPEC `vectorize(mat 1:real^N^N)` o
             MATCH_MP HAS_DERIVATIVE_VMUL_DROP) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE; REAL_MUL_ASSOC]);;

let P2C_RAD_CHRISTOFFEL = prove
 (`!A m (z:real^N) a b.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\
     (!u. &0 <= u ==> (A has_real_derivative (A u * m u)) (atreal u))
     ==> christoffel (\z. A(norm z pow 2) %% mat 1) z a b =
         m(norm z pow 2) % ((z dot a) % b + (z dot b) % a - (a dot b) % z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(:real^N)`; `(\z. A(norm z pow 2) %% mat 1):real^N->real^N^N`; `z:real^N`] THEN
  ASM_SIMP_TAC[P2C_RAD_METRIC; IN_UNIV] THEN X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL
   [`(:real^N)`; `(\z. A(norm z pow 2) %% mat 1):real^N->real^N^N`;
    `z:real^N`; `a:real^N`; `b:real^N`; `w:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_SIMP_TAC[P2C_RAD_METRIC; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[P2C_RAD_MDERIV; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD; DOT_RSUB] THEN REWRITE_TAC[DOT_SYM] THEN
  CONV_TAC REAL_RING);;

let P2C_RAD_RIEMANN = prove
 (`!A m dm (y:real^N) a v w.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\
     (!u. &0 <= u ==> (A has_real_derivative (A u * m u)) (atreal u)) /\
     (!u. &0 <= u ==> (m has_real_derivative dm u) (atreal u))
     ==> lriemann (\z. A(norm z pow 2) %% mat 1) y a v w =
         (&2 * m(norm y pow 2) + m(norm y pow 2) pow 2 * (y dot y)) %
         ((a dot w) % v - (v dot w) % a) +
         (&2 * dm(norm y pow 2) - m(norm y pow 2) pow 2) %
         (((y dot a) * (y dot w)) % v - ((y dot v) * (y dot w)) % a -
          ((y dot a) * (v dot w)) % y + ((y dot v) * (a dot w)) % y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\z. A(norm z pow 2) %% mat 1):real^N->real^N^N`; `(:real^N)`;
                 `\z:real^N. (m:real->real)(norm z pow 2)`;
                 `&2 * (dm:real->real)(norm(y:real^N) pow 2)`; `y:real^N`;
                 `a:real^N`; `v:real^N`; `w:real^N`] LRG_RADIAL_RIEMANN) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P2C_RAD_CHRISTOFFEL; P2C_RAD_FUN_DERIV]);;
(* Gram determinants: positive for non-collinear vectors; in real^3 the     *)
(* quantity s D - E is the square of the triple product.                     *)

let P2C_GRAM_POS = prove
 (`!u v:real^N.
     ~collinear {vec 0,u,v} ==> &0 < (u dot u) * (v dot v) - (u dot v) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(u dot v) < norm(u:real^N) * norm(v:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE; NORM_CAUCHY_SCHWARZ_ABS] THEN
    ASM_REWRITE_TAC[NORM_CAUCHY_SCHWARZ_EQUAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u dot v) pow 2 < (norm(u:real^N) * norm(v:real^N)) pow 2`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_REWRITE_TAC[ARITH_EQ; REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x < y ==> abs x < abs y`) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_MUL; NORM_POW_2] THEN REAL_ARITH_TAC]);;

let P2C_GRAM3 = prove
 (`!y u v:real^3.
     (y dot y) * ((u dot u) * (v dot v) - (u dot v) pow 2) -
     ((y dot u) pow 2 * (v dot v) - &2 * (y dot u) * (y dot v) * (u dot v) +
      (y dot v) pow 2 * (u dot u)) =
     (y$1 * (u$2 * v$3 - u$3 * v$2) + y$2 * (u$3 * v$1 - u$1 * v$3) +
      y$3 * (u$1 * v$2 - u$2 * v$1)) pow 2`,
  REWRITE_TAC[DOT_3] THEN CONV_TAC REAL_RING);;

let P2C_EFORM_POS = prove
 (`!y u v:real^N.
     &0 <= (y dot u) pow 2 * (v dot v) - &2 * (y dot u) * (y dot v) * (u dot v) +
           (y dot v) pow 2 * (u dot u)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(y dot u) pow 2 * (v dot v) - &2 * (y dot u) * (y dot v) * (u dot v) +
    (y dot v) pow 2 * (u dot u) =
    ((y dot u) % v - (y dot v) % (u:real^N)) dot ((y dot u) % v - (y dot v) % u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING;
    REWRITE_TAC[DOT_POS_LE]]);;

(* a D - b E >= 0 when a >= 0, a - b s >= 0, D > 0, 0 <= E <= s D. *)

let P2C_SEC_COMB = prove
 (`!a b d e s. &0 <= a /\ &0 <= a - b * s /\ &0 < d /\ &0 <= e /\ e <= s * d /\
               &0 <= s
               ==> &0 <= a * d - b * e`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s = &0` THENL
   [SUBGOAL_THEN `e = &0` SUBST1_TAC THENL
     [UNDISCH_TAC `e <= s * d` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s * (a * d - b * e)` MP_TAC THENL
     [SUBGOAL_THEN `s * (a * d - b * e) = a * (s * d - e) + (a - b * s) * e`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_MUL_EQ]]]);;

(* The sectional and the scalar curvature of A(|z|^2) delta on real^3.      *)

let P2C_RAD_SECTIONAL = prove
 (`!A m dm (y:real^3) u v.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\
     (!u. &0 <= u ==> (A has_real_derivative (A u * m u)) (atreal u)) /\
     (!u. &0 <= u ==> (m has_real_derivative dm u) (atreal u)) /\
     ~collinear {vec 0,u,v}
     ==> lsectional (\z. A(norm z pow 2) %% mat 1) y u v =
         (--(&2 * m(norm y pow 2) + m(norm y pow 2) pow 2 * (y dot y)) *
            ((u dot u) * (v dot v) - (u dot v) pow 2) -
          (&2 * dm(norm y pow 2) - m(norm y pow 2) pow 2) *
            ((y dot u) pow 2 * (v dot v) - &2 * (y dot u) * (y dot v) * (u dot v) +
             (y dot v) pow 2 * (u dot u))) /
         (A(norm y pow 2) * ((u dot u) * (v dot v) - (u dot v) pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN
  ASM_SIMP_TAC[P2C_RAD_RIEMANN] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD; DOT_RSUB; DOT_LMUL] THEN
  SUBGOAL_THEN `~(A(norm(y:real^3) pow 2) = &0) /\
                ~(((u:real^3) dot u) * ((v:real^3) dot v) - (u dot v) pow 2 = &0)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THENL
     [ASM_MESON_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC P2C_GRAM_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

let P2C_RAD_SCALAR = prove
 (`!A m dm (y:real^3).
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\
     (!u. &0 <= u ==> (A has_real_derivative (A u * m u)) (atreal u)) /\
     (!u. &0 <= u ==> (m has_real_derivative dm u) (atreal u))
     ==> lscalar (\z. A(norm z pow 2) %% mat 1) y =
         (--(&6) * (&2 * m(norm y pow 2) + m(norm y pow 2) pow 2 * (y dot y)) -
          &4 * (&2 * dm(norm y pow 2) - m(norm y pow 2) pow 2) * (y dot y)) /
         A(norm y pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(A(norm(y:real^3) pow 2) = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN ASM_MESON_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v w:real^3.
      lricci (\z. A(norm z pow 2) %% mat 1) y v w =
      --(&2) * (&2 * m(norm y pow 2) + m(norm y pow 2) pow 2 * (y dot y)) * (v dot w) -
      (&2 * dm(norm y pow 2) - m(norm y pow 2) pow 2) *
      ((y dot v) * (y dot w) + (y dot y) * (v dot w))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(\z. A(norm z pow 2) %% mat 1):real^3->real^3^3`; `(:real^3)`;
                   `\z:real^3. (m:real->real)(norm z pow 2)`;
                   `&2 * (dm:real->real)(norm(y:real^3) pow 2)`; `y:real^3`;
                   `v:real^3`; `w:real^3`] LRG_RADIAL_RICCI) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P2C_RAD_CHRISTOFFEL; P2C_RAD_FUN_DERIV;
                 DIMINDEX_3] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[lscalar; MATRIX_INV_CMUL; MATRIX_INV_I; MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
  SIMP_TAC[MAT_COMPONENT; DOT_BASIS_BASIS; DOT_BASIS; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[DOT_3] THEN UNDISCH_TAC `~(A(norm(y:real^3) pow 2) = &0)` THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The curvature of g0: sec >= 0, sec = 1/4 near the tip,                    *)
(* R > 0, R = 1 beyond |x| = 1; the same on the manifold real^3.             *)
(* ========================================================================= *)

let P2C_STD_G0_ALT = prove
 (`p2c_std_g0 = \z. p2c_std_A(norm z pow 2) %% mat 1`,
  REWRITE_TAC[FUN_EQ_THM; p2c_std_g0]);;

let P2C_STD_HYPS = prove
 (`smooth_map_on {x:real^1 | --(&1) < drop x} (lift o p2c_std_A o drop) /\
   (!u. &0 <= u ==> &0 < p2c_std_A u) /\
   (!u. &0 <= u
        ==> (p2c_std_A has_real_derivative (p2c_std_A u * p2c_std_m u)) (atreal u)) /\
   (!u. &0 <= u ==> (p2c_std_m has_real_derivative p2c_std_dm u) (atreal u))`,
  REWRITE_TAC[P2C_STD_A_SMOOTH] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC P2C_STD_A_POS; MATCH_MP_TAC P2C_STD_A_DERIV;
    MATCH_MP_TAC P2C_STD_M_DERIV] THEN
  ASM_REAL_ARITH_TAC);;

let P2C_STD_METRIC_FIELD = prove
 (`metric_field (:real^3) p2c_std_g0`,
  REWRITE_TAC[P2C_STD_G0_ALT] THEN MATCH_MP_TAC P2C_RAD_METRIC THEN
  REWRITE_TAC[P2C_STD_HYPS]);;

let P2C_STD_C1_NEG = prove
 (`!s. &0 <= s ==> &2 * p2c_std_m s + p2c_std_m s pow 2 * s < &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s = &0` THENL
   [ASM_SIMP_TAC[P2C_STD_M_NEAR; REAL_ARITH `&0 < &1 / &32`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `s:real` P2C_STD_P_SQ) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s * (&2 * p2c_std_m s + p2c_std_m s pow 2 * s) < &0` MP_TAC THENL
   [UNDISCH_TAC `(&1 + s * p2c_std_m s) pow 2 < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~(&0 <= s * (&2 * p2c_std_m s + p2c_std_m s pow 2 * s))` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let P2C_STD_SEC_NONNEG = prove
 (`!y u v:real^3. ~collinear {vec 0,u,v} ==> &0 <= lsectional p2c_std_g0 y u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2C_STD_G0_ALT] THEN
  MP_TAC(ISPECL [`p2c_std_A`; `p2c_std_m`; `p2c_std_dm`; `y:real^3`; `u:real^3`;
                 `v:real^3`] P2C_RAD_SECTIONAL) THEN
  ASM_REWRITE_TAC[P2C_STD_HYPS] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NORM_POW_2] THEN
  SUBGOAL_THEN `&0 <= (y:real^3) dot y` ASSUME_TAC THENL
   [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((u:real^3) dot u) * ((v:real^3) dot v) - (u dot v) pow 2`
  ASSUME_TAC THENL [MATCH_MP_TAC P2C_GRAM_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2C_SEC_COMB THEN EXISTS_TAC `(y:real^3) dot y` THEN
    ASM_REWRITE_TAC[P2C_EFORM_POS] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `(y:real^3) dot y` P2C_STD_C1_NEG) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MP_TAC(SPEC `(y:real^3) dot y` P2C_STD_DP_LE) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MP_TAC(ISPECL [`y:real^3`; `u:real^3`; `v:real^3`] P2C_GRAM3) THEN
      MP_TAC(SPEC `(y:real^3)$1 * ((u:real^3)$2 * (v:real^3)$3 - u$3 * v$2) +
                   y$2 * (u$3 * v$1 - u$1 * v$3) + y$3 * (u$1 * v$2 - u$2 * v$1)`
             REAL_LE_POW_2) THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC P2C_STD_A_POS THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

let P2C_STD_SEC_QUARTER = prove
 (`!y u v:real^3.
     norm y pow 2 < &1 / &32 /\ ~collinear {vec 0,u,v}
     ==> lsectional p2c_std_g0 y u v = &1 / &4`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2C_STD_G0_ALT] THEN
  MP_TAC(ISPECL [`p2c_std_A`; `p2c_std_m`; `p2c_std_dm`; `y:real^3`; `u:real^3`;
                 `v:real^3`] P2C_RAD_SECTIONAL) THEN
  ASM_REWRITE_TAC[P2C_STD_HYPS] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[P2C_STD_M_NEAR; P2C_STD_A_NEAR; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `~(((u:real^3) dot u) * ((v:real^3) dot v) - (u dot v) pow 2 = &0) /\
                ~(&1 + norm(y:real^3) pow 2 = &0)`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC P2C_GRAM_POS THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPEC `norm(y:real^3)` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2] THEN CONV_TAC REAL_FIELD);;

let P2C_STD_SCALAR_FORMULA = prove
 (`!y:real^3.
     lscalar p2c_std_g0 y =
     (--(&6) * (&2 * p2c_std_m(y dot y) + p2c_std_m(y dot y) pow 2 * (y dot y)) -
      &4 * (&2 * p2c_std_dm(y dot y) - p2c_std_m(y dot y) pow 2) * (y dot y)) /
     p2c_std_A(y dot y)`,
  GEN_TAC THEN REWRITE_TAC[P2C_STD_G0_ALT] THEN
  MP_TAC(ISPECL [`p2c_std_A`; `p2c_std_m`; `p2c_std_dm`; `y:real^3`]
         P2C_RAD_SCALAR) THEN
  REWRITE_TAC[P2C_STD_HYPS; NORM_POW_2]);;

let P2C_STD_SCALAR_POS = prove
 (`!y:real^3. &0 < lscalar p2c_std_g0 y`,
  GEN_TAC THEN REWRITE_TAC[P2C_STD_SCALAR_FORMULA] THEN
  SUBGOAL_THEN `&0 <= (y:real^3) dot y` ASSUME_TAC THENL
   [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
   [MP_TAC(SPEC `(y:real^3) dot y` P2C_STD_C1_NEG) THEN
    MP_TAC(SPEC `(y:real^3) dot y` P2C_STD_DP_LE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC P2C_STD_A_POS THEN ASM_REAL_ARITH_TAC]);;

let P2C_STD_SCALAR_FAR = prove
 (`!y:real^3. &1 < norm y pow 2 ==> lscalar p2c_std_g0 y = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2C_STD_SCALAR_FORMULA] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NORM_POW_2]) THEN
  ASM_SIMP_TAC[P2C_STD_M_FAR; P2C_STD_A_FAR; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `~((y:real^3) dot y = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* On the manifold real^3 with the identity chart. *)

let P2C_OPEN_SET_METRIC_LOCAL_UNIV = prove
 (`!g:real^N->real^N^N.
     metric_local (open_set_atlas (:real^N)) ((:real^N),(\x. x)) g = g`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let P2C_OPEN_SET_MFD_SECTIONAL = prove
 (`!(g:real^N->real^N^N) x u v.
     mfd_sectional (open_set_atlas (:real^N)) g x u v = lsectional g x u v`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[mfd_sectional; RFB_OPEN_SET_CHART_AT; IN_UNIV;
           P2C_OPEN_SET_METRIC_LOCAL_UNIV]);;

let P2C_OPEN_SET_MFD_SCALAR = prove
 (`!(g:real^N->real^N^N) x.
     mfd_scalar (open_set_atlas (:real^N)) g x = lscalar g x`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[mfd_scalar; RFB_OPEN_SET_CHART_AT; IN_UNIV;
           P2C_OPEN_SET_METRIC_LOCAL_UNIV]);;

let P2C_STD_RIEMANNIAN = prove
 (`riemannian_metric (open_set_atlas (:real^3)) p2c_std_g0`,
  MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN
  REWRITE_TAC[OPEN_UNIV; P2C_STD_METRIC_FIELD]);;

(* ========================================================================= *)
(* The distance from the tip.  For A smooth on (-1,inf) and                  *)
(* positive on [0,inf), rho = p2c_rad_rho A (the integral of sqrt(A(s^2))   *)
(* from 0) is continuous and strictly increasing on [0,inf), with derivative *)
(* sqrt(A(r^2)); the radial segments have length rho(|x|), and every C^1     *)
(* curve from 0 to x has length >= rho(|x|) (from the last time the curve   *)
(* is at 0, by the fundamental theorem of calculus for rho(|c(t)|)).         *)
(* ========================================================================= *)

let P2C_EUCLID_FACTS = prove
 (`hausdorff_space (euclidean:(real^N)topology) /\
   smooth_manifold_atlas (euclidean:(real^N)topology) (open_set_atlas (:real^N)) /\
   topspace (euclidean:(real^N)topology) = (:real^N) /\
   connected_space (euclidean:(real^N)topology)`,
  REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; TOPSPACE_EUCLIDEAN] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `(:real^N)` OPEN_SET_ATLAS) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
    MP_TAC(ISPEC `(:real^N)` CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY) THEN
    REWRITE_TAC[SUBTOPOLOGY_UNIV; CONNECTED_UNIV]]);;

let P2C_RAD_H_SMOOTH = prove
 (`!A:real->real.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u)
     ==> smooth_map_on (:real^1) (lift o (\s. sqrt(A(s pow 2))) o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^1) (\x. lift(A(drop x pow 2)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^1)`; `{x:real^1 | --(&1) < drop x}`;
                   `\x:real^1. lift(drop x pow 2)`; `A:real->real`]
           SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; P2C_OPEN_DROP_GT; IN_UNIV; IN_ELIM_THM] THEN
    BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^1` THEN MP_TAC(SPEC `drop y` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC;
      MP_TAC(SPECL [`(:real^1)`; `\t:real. t`; `2`] P2C_S1_POW) THEN
      REWRITE_TAC[OPEN_UNIV; P2C_S1_ID; o_DEF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(A(drop x pow 2))`]
         SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; LIFT_DROP; o_DEF] THEN
  DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

let P2C_RAD_RHO_DERIV_WITHIN = prove
 (`!A:real->real R r.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\ r IN real_interval[&0,R]
     ==> (p2c_rad_rho A has_real_derivative sqrt(A(r pow 2)))
         (atreal r within real_interval[&0,R])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p2c_rad_rho A = (\u. real_integral (real_interval[&0,u]) (\s. sqrt(A(s pow 2))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2c_rad_rho]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. sqrt((A:real->real)(s pow 2))`; `&0`; `R:real`]
         REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2C_S1_CONTINUOUS THEN MATCH_MP_TAC P2C_RAD_H_SMOOTH THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[]]);;

let P2C_RAD_RHO_DERIV = prove
 (`!A:real->real r.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\ &0 < r
     ==> (p2c_rad_rho A has_real_derivative sqrt(A(r pow 2))) (atreal r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p2c_rad_rho A = (\u. real_integral (real_interval[&0,u]) (\s. sqrt(A(s pow 2))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2c_rad_rho]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. sqrt((A:real->real)(s pow 2))`; `&0`; `r:real`]
         P2C_INTEGRAL_DERIV_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P2C_S1_CONTINUOUS THEN MATCH_MP_TAC P2C_RAD_H_SMOOTH THEN
  ASM_REWRITE_TAC[]);;

let P2C_RAD_RHO_0 = prove
 (`!A. p2c_rad_rho A (&0) = &0`,
  REWRITE_TAC[p2c_rad_rho; REAL_INTEGRAL_REFL]);;

let P2C_RAD_RHO_CONT = prove
 (`!A:real->real R.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u)
     ==> p2c_rad_rho A real_continuous_on real_interval[&0,R]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[real_differentiable_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `sqrt((A:real->real)(x pow 2))` THEN
  MATCH_MP_TAC P2C_RAD_RHO_DERIV_WITHIN THEN ASM_REWRITE_TAC[]);;

let P2C_RAD_RHO_STRICT = prove
 (`!A:real->real r1 r2.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\ &0 <= r1 /\ r1 < r2
     ==> p2c_rad_rho A r1 < p2c_rad_rho A r2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP THEN
  EXISTS_TAC `\r. sqrt((A:real->real)(r pow 2))` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[&0,r2]` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_RAD_RHO_DERIV_WITHIN THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_POW_2]]);;

let P2C_RAD_RHO_POS_LE = prove
 (`!A:real->real r.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\ &0 <= r
     ==> &0 <= p2c_rad_rho A r`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r = &0` THEN
  ASM_REWRITE_TAC[P2C_RAD_RHO_0; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `A:real->real` P2C_RAD_RHO_0)] THEN
  MATCH_MP_TAC P2C_RAD_RHO_STRICT THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_REAL_ARITH_TAC);;

let P2C_RAD_RHO_LT_EQ = prove
 (`!A:real->real r1 r2.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\ &0 <= r1 /\ &0 <= r2
     ==> (p2c_rad_rho A r1 < p2c_rad_rho A r2 <=> r1 < r2) /\
         (p2c_rad_rho A r1 <= p2c_rad_rho A r2 <=> r1 <= r2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s t. &0 <= s /\ s < t ==> p2c_rad_rho A s < p2c_rad_rho A t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_RAD_RHO_STRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_NOT_LT; REAL_LT_REFL; REAL_LE_LT]);;

(* The radial segment t -> t x has length rho(|x|). *)

let P2C_SEGMENT_C1 = prove
 (`!x:real^N.
     mfd_c1_curve (euclidean,open_set_atlas (:real^N)) (\t. t % x) (&0) (&1)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `(:real^N)`; `\x:real^N. x`; `vec 0:real^N`; `x:real^N`]
         GRGD_CHART_SEGMENT) THEN
  REWRITE_TAC[P2C_EUCLID_FACTS; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID; SUBSET_UNIV] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `\t. chart_inv ((:real^N),(\x:real^N. x)) (t % x)`;
                 `\t:real. t % (x:real^N)`; `&0`; `&1`] MFD_C1_CURVE_EQ) THEN
  ASM_SIMP_TAC[]);;

let P2C_SEGMENT_VD = prove
 (`!x:real^N t.
     t IN real_interval[&0,&1]
     ==> vector_derivative (\r. drop r % x)
           (at (lift t) within interval[lift(&0),lift(&1)]) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `x:real^N`;
                 `at (lift t) within interval[lift(&0),lift(&1)]`] GRGD_AFFINE_LINE_VD) THEN
  REWRITE_TAC[VECTOR_ADD_LID]);;

let P2C_RAD_SEGMENT = prove
 (`!A:real->real x:real^N.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u)
     ==> mfd_length (open_set_atlas (:real^N)) (\z. A(norm z pow 2) %% mat 1)
                    (\t. t % x) (&0) (&1) = p2c_rad_rho A (norm x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\z:real^N. (A:real->real)(norm z pow 2) %% (mat 1:real^N^N)`;
                 `\t:real. t % (x:real^N)`; `&0`; `&1`] MFD_LENGTH_OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; P2C_SEGMENT_C1] THEN
  DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[&0,&1])
      (\t. sqrt(A((t * norm(x:real^N)) pow 2)) * norm x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[P2C_SEGMENT_VD] THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL; NORM_MUL;
                SQRT_MUL] THEN
    SUBGOAL_THEN `abs t = t` SUBST1_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[vector_norm]];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_INTEGRAL_0; P2C_RAD_RHO_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. p2c_rad_rho A (t * norm(x:real^N))`;
                 `\t. sqrt((A:real->real)((t * norm(x:real^N)) pow 2)) * norm x`;
                 `&0`; `&1`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t. t * norm(x:real^N)`; `p2c_rad_rho A`; `norm(x:real^N)`;
                   `sqrt((A:real->real)((t * norm(x:real^N)) pow 2))`; `t:real`;
                   `real_interval[&0,&1]`] REAL_DIFF_CHAIN_WITHIN) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\t:real. t`; `&1`; `norm(x:real^N)`; `t:real`;
                     `real_interval[&0,&1]`] HAS_REAL_DERIVATIVE_RMUL_WITHIN) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_LID];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&0,norm(x:real^N)]` THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2C_RAD_RHO_DERIV_WITHIN THEN ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]]];
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; P2C_RAD_RHO_0; REAL_SUB_RZERO]]);;

(* Every C^1 curve from 0 has a last time at 0. *)

let P2C_C1_LAST_ZERO = prove
 (`!(c:real->real^N).
     mfd_c1_curve (euclidean,open_set_atlas (:real^N)) c (&0) (&1) /\
     c(&0) = vec 0 /\ ~(c(&1) = vec 0)
     ==> ?t0. &0 <= t0 /\ t0 < &1 /\ c t0 = vec 0 /\
              !t. t0 < t /\ t <= &1 ==> ~(c t = vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `(\x. mat 1):real^N->real^N^N`; `c:real->real^N`] GRGD_REVERSE_01) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `\t. (c:real->real^N)(&0 + &1 - t)`;
                 `(:real^N) DELETE vec 0`] GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `mfd_c1_curve (euclidean,open_set_atlas (:real^N))
                     (\t. (c:real->real^N) (&0 + &1 - t)) (&0) (&1)` THEN
      SIMP_TAC[mfd_c1_curve];
      REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN MATCH_MP_TAC OPEN_DELETE THEN
      REWRITE_TAC[OPEN_UNIV];
      REWRITE_TAC[IN_DELETE; IN_UNIV; REAL_ARITH `&0 + &1 - &0 = &1`] THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `&1` THEN
      REWRITE_TAC[IN_REAL_INTERVAL; IN_DELETE; IN_UNIV;
                  REAL_ARITH `&0 + &1 - &1 = &0`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&1 - t1` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE; IN_UNIV;
                              REAL_ARITH `&0 + &1 - t = &1 - t`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `t1 <= &1` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < t1` THEN REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1 - t`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `&1 - t1 < t` THEN UNDISCH_TAC `t <= &1` THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `&1 - (&1 - t) = t`]]]);;

(* The velocity of a C^1 curve at an interior time is a two-sided derivative. *)

let P2C_CURVE_VD_AT = prove
 (`!(c:real->real^N) t.
     mfd_c1_curve (euclidean,open_set_atlas (:real^N)) c (&0) (&1) /\
     &0 < t /\ t < &1
     ==> ((\r. c(drop r)) has_vector_derivative
          vector_derivative (\r. c(drop r))
            (at (lift t) within interval[lift(&0),lift(&1)])) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `c:real->real^N`; `&0`; `&1`; `((:real^N),(\x:real^N. x))`;
                 `t:real`] GRGD_C1_CHART_HAS_VD) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS; RFB_OPEN_SET_ATLAS_CASES; IN_UNIV; FST; SND;
                  IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `interval(lift(&0),lift(&1))` o
             MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET)) THEN
  REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
  REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_OPEN THEN
  REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC);;

let P2C_RHO_NORM_CURVE_DERIV = prove
 (`!A:real->real (c:real->real^N) t.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^N)) c (&0) (&1) /\
     &0 < t /\ t < &1 /\ ~(c t = vec 0)
     ==> ((\t. p2c_rad_rho A (norm(c t))) has_real_derivative
          (sqrt(A(norm(c t) pow 2)) *
           ((c t dot vector_derivative (\r. c(drop r))
                       (at (lift t) within interval[lift(&0),lift(&1)])) /
            norm(c t)))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `v = vector_derivative (\r. (c:real->real^N)(drop r))
                    (at (lift t) within interval[lift(&0),lift(&1)])` THEN
  SUBGOAL_THEN `((\r. (c:real->real^N)(drop r)) has_vector_derivative v) (at (lift t))`
  ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC P2C_CURVE_VD_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. (c:real->real^N) t dot c t) has_real_derivative (&2 * (c t dot v)))
    (atreal t)`
  ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MP_TAC(ISPECL [`\x y:real^N. lift(x dot y)`; `\r. (c:real->real^N)(drop r)`;
                   `\r. (c:real->real^N)(drop r)`; `v:real^N`; `v:real^N`;
                   `lift t`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
    ASM_REWRITE_TAC[BILINEAR_DOT; o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN REWRITE_TAC[DOT_SYM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c:real->real^N) t dot c t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. sqrt((c:real->real^N) t dot c t)) has_real_derivative
     (inv(&2 * sqrt(c t dot c t)) * (&2 * (c t dot v)))) (atreal t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. (c:real->real^N) t dot c t`; `sqrt`;
                   `&2 * ((c:real->real^N) t dot v)`;
                   `inv(&2 * sqrt((c:real->real^N) t dot c t))`; `t:real`]
           REAL_DIFF_CHAIN_ATREAL) THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt((c:real->real^N) t dot c t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. sqrt((c:real->real^N) t dot c t)`; `p2c_rad_rho A`;
                 `inv(&2 * sqrt((c:real->real^N) t dot c t)) * (&2 * (c t dot v))`;
                 `sqrt((A:real->real)(sqrt((c:real->real^N) t dot c t) pow 2))`;
                 `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2C_RAD_RHO_DERIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; GSYM vector_norm] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(norm((c:real->real^N) t) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;
let P2C_CURVE_NORM_CONT = prove
 (`!(c:real->real^N).
     mfd_c1_curve (euclidean,open_set_atlas (:real^N)) c (&0) (&1)
     ==> (\t. norm(c t)) real_continuous_on real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GRGD_CURVE_CONTINUOUS) THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`(c:real->real^N) o drop`; `interval[lift(&0),lift(&1)]`]
         CONTINUOUS_ON_LIFT_NORM_COMPOSE) THEN
  ASM_REWRITE_TAC[o_THM]);;

let P2C_RHO_NORM_CURVE_CONT = prove
 (`!A:real->real (c:real->real^N) a b.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^N)) c (&0) (&1) /\
     &0 <= a /\ b <= &1
     ==> (\t. p2c_rad_rho A (norm(c t))) real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2C_CURVE_NORM_CONT) THEN
  SUBGOAL_THEN `~(real_interval[&0,&1] = {})` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. norm((c:real->real^N) t)`; `real_interval[&0,&1]`]
         REAL_CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\t. p2c_rad_rho A (norm((c:real->real^N) t))) =
    p2c_rad_rho A o (\t. norm(c t))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[&0,norm((c:real->real^N) t1)]` THEN
    ASM_SIMP_TAC[P2C_RAD_RHO_CONT] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL; NORM_POS_LE] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

(* The speed of a curve for A(|z|^2) delta. *)

let P2C_RAD_SPEED = prove
 (`!A:real->real (c:real->real^N) t.
     (!u. &0 <= u ==> &0 < A u) /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^N)) c (&0) (&1) /\
     t IN real_interval[&0,&1]
     ==> mfd_speed (open_set_atlas (:real^N)) (\z. A(norm z pow 2) %% mat 1) c (&0) (&1) t =
         sqrt(A(norm(c t) pow 2)) *
         norm(vector_derivative (\r. c(drop r))
                (at (lift t) within interval[lift(&0),lift(&1)]))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\z:real^N. (A:real->real)(norm z pow 2) %% (mat 1:real^N^N)`;
                 `c:real->real^N`; `&0`; `&1`; `t:real`] GRGD_OPEN_SET_SPEED) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL; SQRT_MUL] THEN
  REWRITE_TAC[vector_norm]);;

(* The lower bound: every C^1 curve from 0 to x has length >= rho(|x|). *)

let P2C_RAD_LOWER = prove
 (`!A:real->real (c:real->real^N).
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u) /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^N)) c (&0) (&1) /\ c(&0) = vec 0
     ==> p2c_rad_rho A (norm(c(&1))) <=
         mfd_length (open_set_atlas (:real^N)) (\z. A(norm z pow 2) %% mat 1)
                    c (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `riemannian_metric (open_set_atlas (:real^N)) (\z:real^N. A(norm z pow 2) %% mat 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_SIMP_TAC[OPEN_UNIV; P2C_RAD_METRIC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(c:real->real^N)(&1) = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; P2C_RAD_RHO_0] THEN MATCH_MP_TAC MFD_LENGTH_POS_LE THEN
    EXISTS_TAC `euclidean:(real^N)topology` THEN ASM_REWRITE_TAC[P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:real->real^N` P2C_C1_LAST_ZERO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `v = \t. vector_derivative (\r. (c:real->real^N)(drop r))
              (at (lift t) within interval[lift(&0),lift(&1)])` THEN
  SUBGOAL_THEN
   `((\t. sqrt(A(norm((c:real->real^N) t) pow 2)) * ((c t dot v t) / norm(c t)))
     has_real_integral
     (p2c_rad_rho A (norm(c(&1))) - p2c_rad_rho A (norm(c t0))))
    (real_interval[t0,&1])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. p2c_rad_rho A (norm((c:real->real^N) t))`;
                   `\t. sqrt(A(norm((c:real->real^N) t) pow 2)) * ((c t dot v t) / norm(c t))`;
                   `t0:real`; `&1`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `t0 < &1` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P2C_RHO_NORM_CURVE_CONT THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "v" THEN BETA_TAC THEN
      MATCH_MP_TAC P2C_RHO_NORM_CURVE_DERIV THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `&0 <= t0` THEN UNDISCH_TAC `t0 < t` THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `t0 < t` THEN UNDISCH_TAC `t < &1` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(c:real->real^N) t0 = vec 0`; NORM_0;
                              P2C_RAD_RHO_0; REAL_SUB_RZERO]) THEN
  SUBGOAL_THEN
   `(mfd_speed (open_set_atlas (:real^N)) (\z:real^N. A(norm z pow 2) %% mat 1) c (&0) (&1))
    real_integrable_on real_interval[&0,&1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `real_integral (real_interval[t0,&1])
      (mfd_speed (open_set_atlas (:real^N)) (\z:real^N. A(norm z pow 2) %% mat 1)
                 c (&0) (&1))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      UNDISCH_TAC `&0 <= t0` THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`A:real->real`; `c:real->real^N`; `t:real`] P2C_RAD_SPEED) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `&0 <= t0` THEN UNDISCH_TAC `t0 <= t` THEN
        UNDISCH_TAC `t <= &1` THEN REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      EXPAND_TAC "v" THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[SQRT_POS_LE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
        ALL_TAC] THEN
      ASM_CASES_TAC `(c:real->real^N) t = vec 0` THENL
       [ASM_REWRITE_TAC[NORM_0; real_div; REAL_INV_0; REAL_MUL_RZERO; NORM_POS_LE];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT] THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        MESON_TAC[NORM_CAUCHY_SCHWARZ; REAL_LE_TRANS; REAL_LE_REFL]]];
    MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN UNDISCH_TAC `&0 <= t0` THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      UNDISCH_TAC `&0 <= t0` THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_SPEED_POS_LE THEN
      EXISTS_TAC `euclidean:(real^N)topology` THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS]]]);;
(* The distance from the tip is rho(|x|). *)

let P2C_RAD_DIST = prove
 (`!A:real->real x:real^N.
     smooth_map_on {x:real^1 | --(&1) < drop x} (lift o A o drop) /\
     (!u. &0 <= u ==> &0 < A u)
     ==> mfd_dist (euclidean,open_set_atlas (:real^N)) (\z. A(norm z pow 2) %% mat 1)
                  (vec 0) x = p2c_rad_rho A (norm x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist] THEN
  MATCH_MP_TAC REAL_INF_UNIQUE THEN REWRITE_TAC[GRGD_IN_LENGTHS] THEN CONJ_TAC THENL
   [X_GEN_TAC `L:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x:real^N = gamma(&1)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2C_RAD_LOWER THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `b:real` THEN DISCH_TAC THEN
    EXISTS_TAC `p2c_rad_rho A (norm(x:real^N))` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `\t. t % (x:real^N)` THEN
    ASM_SIMP_TAC[P2C_SEGMENT_C1; P2C_RAD_SEGMENT] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID]]);;

let P2C_RAD_JOINABLE = prove
 (`!x y:real^N. mfd_joinable (euclidean,open_set_atlas (:real^N)) x y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
  REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV]);;

(* For the standard metric: d(0,x) = rho(|x|), rho beyond 1. *)

let P2C_STD_HYP2 = prove
 (`smooth_map_on {x:real^1 | --(&1) < drop x} (lift o p2c_std_A o drop) /\
   (!u. &0 <= u ==> &0 < p2c_std_A u)`,
  REWRITE_TAC[P2C_STD_HYPS]);;

let P2C_STD_DIST = prove
 (`!x. p3_std_dist p2c_std_g0 x = p2c_rad_rho p2c_std_A (norm x)`,
  GEN_TAC THEN REWRITE_TAC[p3_std_dist; P2C_STD_G0_ALT] THEN
  MATCH_MP_TAC P2C_RAD_DIST THEN REWRITE_TAC[P2C_STD_HYP2]);;

let P2C_STD_RHO_FAR = prove
 (`!r. &1 <= r ==> p2c_rad_rho p2c_std_A r = p2c_std_A0 + sqrt(&2) * log r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_A0] THEN
  MP_TAC(ISPECL [`\r. p2c_rad_rho p2c_std_A r - sqrt(&2) * log r`; `{r:real | &1 <= r}`;
                 `p2c_rad_rho p2c_std_A (&1) - sqrt(&2) * log(&1)`; `&1`]
         HAS_REAL_DERIVATIVE_ZERO_UNIQUE) THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL; LOG_1; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN `&0 = sqrt(p2c_std_A(s pow 2)) - sqrt(&2) * inv s` SUBST1_TAC THENL
     [SUBGOAL_THEN `&1 <= s pow 2` ASSUME_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `2` REAL_POW_ONE)] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[P2C_STD_A_FAR] THEN
      SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_DIV; REAL_POW_LE; REAL_LT_IMP_LE; REAL_LE_POW_2;
                   REAL_ARITH `&0 <= &2`; POW_2_SQRT] THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC P2C_RAD_RHO_DERIV THEN REWRITE_TAC[P2C_STD_HYP2] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P2C_STD_A0_POS = prove
 (`&0 < p2c_std_A0`,
  REWRITE_TAC[p2c_std_A0] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `p2c_std_A` P2C_RAD_RHO_0)] THEN
  MATCH_MP_TAC P2C_RAD_RHO_STRICT THEN REWRITE_TAC[P2C_STD_HYP2] THEN
  REAL_ARITH_TAC);;

let P2C_STD_RHO_LT_EQ = prove
 (`!r1 r2. &0 <= r1 /\ &0 <= r2
           ==> (p2c_rad_rho p2c_std_A r1 < p2c_rad_rho p2c_std_A r2 <=> r1 < r2) /\
               (p2c_rad_rho p2c_std_A r1 <= p2c_rad_rho p2c_std_A r2 <=> r1 <= r2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2C_RAD_RHO_LT_EQ THEN
  ASM_REWRITE_TAC[P2C_STD_HYP2]);;

(* Every value is reached: rho is unbounded. *)

let P2C_STD_RHO_UNBOUNDED = prove
 (`!K. ?B. &1 <= B /\ K < p2c_rad_rho p2c_std_A B`,
  GEN_TAC THEN EXISTS_TAC `exp(abs K / sqrt(&2)) + &1` THEN
  SUBGOAL_THEN `&1 <= exp(abs K / sqrt(&2)) + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `abs K / sqrt(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[P2C_STD_RHO_FAR]] THEN
  SUBGOAL_THEN `abs K / sqrt(&2) < log(exp(abs K / sqrt(&2)) + &1)` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
    REWRITE_TAC[REAL_EXP_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN MP_TAC P2C_STD_A0_POS THEN
  REWRITE_TAC[REAL_MUL_SYM] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The cylinder end, completeness, rotations, the tip, and the               *)
(* assembly of p3_std_initial and of MT Lemma 12.3.                          *)
(* ========================================================================= *)

(* The scaled inversion z -> (K/|z|^2) z is an isometry of the cylinder     *)
(* metric (2/|z|^2) delta.                                                   *)

let P2C_INV_DERIV = prove
 (`!K x:real^N.
     ~(x = vec 0)
     ==> ((\z. (K * inv(norm z pow 2)) % z) has_derivative
          (\v. (K * inv(norm x pow 2)) % v +
               (K * --(&2) * (x dot v) * inv(norm x pow 2) pow 2) % x)) (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. K * inv t) has_real_derivative (K * --inv(norm(x:real^N) pow 2 pow 2)))
    (atreal (norm x pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(DISCH_ALL(REAL_DIFF_CONV
      `((\t. (K:real) * inv t) has_real_derivative f') (atreal (norm(x:real^N) pow 2))`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(norm(x:real^N) pow 2 = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (K:real) * inv t`; `K * --inv(norm(x:real^N) pow 2 pow 2)`;
                 `\z:real^N. lift(norm z pow 2)`; `\h:real^N. &2 % lift(x dot h)`;
                 `x:real^N`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_REWRITE_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^N. K * inv(norm z pow 2)`;
                 `\h:real^N. K * --(&2) * (x dot h) * inv(norm(x:real^N) pow 2) pow 2`;
                 `\z:real^N. z`; `\h:real^N. h`; `x:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; o_DEF] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL; LIFT_EQ] THEN
    GEN_TAC THEN REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_INV_POW] THEN REAL_ARITH_TAC;
    REWRITE_TAC[]]);;

let P2C_INV_PULLBACK = prove
 (`!K x:real^3.
     ~(K = &0) /\ ~(x = vec 0)
     ==> mpullback (\z. (K * inv(norm z pow 2)) % z) (cylinder_flow (&0)) x =
         cylinder_flow (&0) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `K:real` o MATCH_MP P2C_INV_DERIV) THEN
  REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `v:real^3` THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `w:real^3` THEN
  MP_TAC(ISPECL [`\z:real^3. (K * inv(norm z pow 2)) % z`; `cylinder_flow (&0)`;
                 `x:real^3`; `w:real^3`; `v:real^3`] LRG_MPULLBACK_DOT) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL;
              DOT_RADD; DOT_LADD; DOT_LMUL] THEN
  REWRITE_TAC[NORM_MUL] THEN REWRITE_TAC[REAL_POW_MUL; REAL_POW2_ABS] THEN
  REWRITE_TAC[NORM_POW_2] THEN
  SUBGOAL_THEN `~((x:real^3) dot x = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `~(K = &0)` THEN REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

(* Beyond |x| = 1 the neck coordinates of g0 are the scaled inversion. *)

let P2C_STD_NC_FAR = prove
 (`!z. &1 <= norm z
       ==> p3_std_nc p2c_std_g0 p2c_std_A0 z =
           (exp(&4 / sqrt(&2)) * inv(norm z pow 2)) % z`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[p3_std_nc; P2C_STD_DIST; P2C_STD_RHO_FAR] THEN
  SUBGOAL_THEN `&0 < norm(z:real^3) /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p2c_std_A0 + &4 - (p2c_std_A0 + sqrt(&2) * log(norm(z:real^3)))) / sqrt(&2) =
    &4 / sqrt(&2) - log(norm z)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EXP_SUB; EXP_LOG; VECTOR_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < norm(z:real^3)` THEN CONV_TAC REAL_FIELD);;

let P2C_STD_CYL = prove
 (`!x. p2c_std_A0 < p3_std_dist p2c_std_g0 x
       ==> p2c_std_g0 x =
           mpullback (p3_std_nc p2c_std_g0 p2c_std_A0) (cylinder_flow (&0)) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 < norm(x:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_std_A0 < p3_std_dist p2c_std_g0 x` THEN
    REWRITE_TAC[P2C_STD_DIST; p2c_std_A0] THEN
    MP_TAC(SPECL [`&1`; `norm(x:real^3)`] P2C_STD_RHO_LT_EQ) THEN
    REWRITE_TAC[NORM_POS_LE] THEN ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 < norm(x:real^3)` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `K = exp(&4 / sqrt(&2))` THEN
  SUBGOAL_THEN `~(K = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[REAL_EXP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((p3_std_nc p2c_std_g0 p2c_std_A0) has_derivative
     (\v. (K * inv(norm(x:real^3) pow 2)) % v +
          (K * --(&2) * (x dot v) * inv(norm x pow 2) pow 2) % x)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\z:real^3. (K * inv(norm z pow 2)) % z`;
                          `norm(x:real^3) - &1`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      EXPAND_TAC "K" THEN MATCH_MP_TAC P2C_STD_NC_FAR THEN
      UNDISCH_TAC `dist(y:real^3,x) < norm x - &1` THEN NORM_ARITH_TAC;
      MATCH_MP_TAC P2C_INV_DERIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mpullback (p3_std_nc p2c_std_g0 p2c_std_A0) (cylinder_flow (&0)) x =
    mpullback (\z. (K * inv(norm z pow 2)) % z) (cylinder_flow (&0)) x`
  SUBST1_TAC THENL
   [REWRITE_TAC[mpullback] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    MP_TAC(SPEC `K:real` (MATCH_MP P2C_INV_DERIV (ASSUME `~(x:real^3 = vec 0)`))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "K" THEN MATCH_MP_TAC P2C_STD_NC_FAR THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2C_INV_PULLBACK] THEN
  REWRITE_TAC[LRG_CYL0_EQ; p2c_std_g0] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P2C_STD_A_FAR THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `2` REAL_POW_ONE)] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;
(* Completeness: closed metric balls are bounded, since d(0,y) = rho(|y|)   *)
(* is unbounded.                                                             *)

let P2C_STD_COMPLETE = prove
 (`mfd_complete (euclidean,open_set_atlas (:real^3)) p2c_std_g0`,
  REWRITE_TAC[mfd_complete; P2C_EUCLID_FACTS; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `r:real`] THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CLOSED_IN_EUCLIDEAN] THEN MATCH_MP_TAC MFD_CBALL_CLOSED THEN
    REWRITE_TAC[P2C_EUCLID_FACTS; P2C_STD_RIEMANNIAN]] THEN
  MP_TAC(SPEC `p2c_rad_rho p2c_std_A (norm(x:real^3)) + r` P2C_STD_RHO_UNBOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,B)` THEN
  REWRITE_TAC[BOUNDED_BALL; SUBSET; mfd_cball; IN_ELIM_THM; IN_BALL_0] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2c_rad_rho p2c_std_A (norm(y:real^3)) <= p2c_rad_rho p2c_std_A (norm(x:real^3)) + r`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM P2C_STD_DIST; p3_std_dist] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `mfd_dist (euclidean,open_set_atlas (:real^3)) p2c_std_g0 (vec 0) x +
      mfd_dist (euclidean,open_set_atlas (:real^3)) p2c_std_g0 x y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN
      REWRITE_TAC[P2C_EUCLID_FACTS; P2C_STD_RIEMANNIAN; P2C_RAD_JOINABLE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`norm(y:real^3)`; `B:real`] P2C_STD_RHO_LT_EQ) THEN
  REWRITE_TAC[NORM_POS_LE] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REAL_ARITH_TAC);;

(* Rotations are isometries. *)

let P2C_STD_ROT = prove
 (`!Q x. orthogonal_matrix Q /\ det Q = &1
         ==> transp Q ** p2c_std_g0 (Q ** x) ** Q = p2c_std_g0 x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_std_g0] THEN
  SUBGOAL_THEN `norm((Q:real^3^3) ** (x:real^3)) = norm x` SUBST1_TAC THENL
   [UNDISCH_TAC `orthogonal_matrix(Q:real^3^3)` THEN
    REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSFORMATION; ORTHOGONAL_TRANSFORMATION] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_MUL_LID] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ORTHOGONAL_MATRIX]) THEN ASM_REWRITE_TAC[]);;

(* Curvature 1/4 near the tip. *)

let P2C_STD_TIP = prove
 (`?r0. &0 < r0 /\
        !x u v. p3_std_dist p2c_std_g0 x < r0 /\ ~collinear {vec 0,u,v}
                ==> mfd_sectional (open_set_atlas (:real^3)) p2c_std_g0 x u v = &1 / &4`,
  EXISTS_TAC `p2c_rad_rho p2c_std_A (&1 / &8)` THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `p2c_std_A` P2C_RAD_RHO_0)] THEN
    MATCH_MP_TAC P2C_RAD_RHO_STRICT THEN REWRITE_TAC[P2C_STD_HYP2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `u:real^3`; `v:real^3`] THEN
  REWRITE_TAC[P2C_STD_DIST; P2C_OPEN_SET_MFD_SECTIONAL] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2C_STD_SEC_QUARTER THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm(x:real^3) < &1 / &8` ASSUME_TAC THENL
   [MP_TAC(SPECL [`norm(x:real^3)`; `&1 / &8`] P2C_STD_RHO_LT_EQ) THEN
    REWRITE_TAC[NORM_POS_LE] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 / &8) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* The standard initial metric. *)

let P2C_STD_INITIAL = prove
 (`p3_std_initial p2c_std_g0 p2c_std_A0`,
  REWRITE_TAC[p3_std_initial; P2C_STD_RIEMANNIAN; P2C_STD_COMPLETE; P2C_STD_ROT;
              P2C_STD_TIP; P2C_STD_A0_POS; P2C_STD_CYL] THEN
  REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL; P2C_STD_SEC_NONNEG]);;

(* Scalar curvature bounds: R = 1 beyond |x| = 1, R > 0 and continuous on   *)
(* the compact ball |x| <= 1.                                                *)

let P2C_STD_SCALAR_BOUNDS = prove
 (`?D. &1 <= D /\
       !x. inv D <= mfd_scalar (open_set_atlas (:real^3)) p2c_std_g0 x /\
           mfd_scalar (open_set_atlas (:real^3)) p2c_std_g0 x <= D`,
  REWRITE_TAC[P2C_OPEN_SET_MFD_SCALAR] THEN
  SUBGOAL_THEN `(\x:real^3. lift(lscalar p2c_std_g0 x)) continuous_on cball(vec 0,&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
    MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN REWRITE_TAC[P2C_STD_METRIC_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(cball(vec 0:real^3,&1)) /\ ~(cball(vec 0:real^3,&1) = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL; CBALL_EQ_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. lscalar p2c_std_g0 x`; `cball(vec 0:real^3,&1)`]
         CONTINUOUS_ATTAINS_INF) THEN
  MP_TAC(ISPECL [`\x:real^3. lscalar p2c_std_g0 x`; `cball(vec 0:real^3,&1)`]
         CONTINUOUS_ATTAINS_SUP) THEN
  REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:real^3` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `xi:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `xi:real^3` P2C_STD_SCALAR_POS) THEN DISCH_TAC THEN
  EXISTS_TAC `max (&1) (max (lscalar p2c_std_g0 xs) (inv(lscalar p2c_std_g0 xi)))` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `x IN cball(vec 0:real^3,&1)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `lscalar p2c_std_g0 x = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC P2C_STD_SCALAR_FAR THEN
      UNDISCH_TAC `~(x IN cball(vec 0:real^3,&1))` THEN
      REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN DISCH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `2` REAL_POW_ONE)] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `lscalar p2c_std_g0 xi <= lscalar p2c_std_g0 x /\
                lscalar p2c_std_g0 x <= lscalar p2c_std_g0 xs`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lscalar p2c_std_g0 xi` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(inv(lscalar p2c_std_g0 xi))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL]]);;

(* MT Lemma 12.3 in the form P2_LEMMA_12_3_STATEMENT of pc_p3_iface. *)

let P2C_LEMMA_12_3 = prove
 (`P2_LEMMA_12_3_STATEMENT`,
  REWRITE_TAC[P2_LEMMA_12_3_STATEMENT] THEN
  MAP_EVERY EXISTS_TAC [`p2c_std_g0`; `p2c_std_A0`] THEN
  MP_TAC P2C_STD_SCALAR_BOUNDS THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `{x | p3_std_dist p2c_std_g0 x < p2c_std_A0 + &4} =
    mfd_ball (euclidean,open_set_atlas (:real^3)) p2c_std_g0 (vec 0) (p2c_std_A0 + &4)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_ball; IN_ELIM_THM; P2C_RAD_JOINABLE; p3_std_dist];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `p2c_std_g0`; `vec 0:real^3`; `p2c_std_A0 + &4`] MFD_HAS_VOLUME_BALL) THEN
  REWRITE_TAC[P2C_EUCLID_FACTS; P2C_STD_RIEMANNIAN; P2C_STD_COMPLETE] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `v = mfd_volume (euclidean,open_set_atlas (:real^3)) p2c_std_g0
          (mfd_ball (euclidean,open_set_atlas (:real^3)) p2c_std_g0 (vec 0)
                    (p2c_std_A0 + &4))` THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `p2c_std_g0`;
      `mfd_ball (euclidean,open_set_atlas (:real^3)) p2c_std_g0 (vec 0)
                (p2c_std_A0 + &4)`; `v:real`] MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; P2C_STD_RIEMANNIAN];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v + &1`; `D:real`] THEN
  ASM_REWRITE_TAC[P2C_STD_INITIAL] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* MT Lemma 12.37 for the explicit metric.  The radial map from              *)
(* the cylinder (s = sqrt 2 log|y|) to g0 is y -> R(|y|) y/|y| with          *)
(* rho(R(t)) = A0 + 4 - sqrt 2 log t; it is an isometry in the radial        *)
(* direction (A(R^2) R'^2 = 2/t^2) and does not increase tangential lengths  *)
(* since u A(u) <= 2 (the warping function is at most sqrt 2).               *)
(* ========================================================================= *)

let p2c_std_rinv = new_definition
 `p2c_std_rinv (c:real) = @r. &0 <= r /\ p2c_rad_rho p2c_std_A r = c`;;

let P2C_STD_RHO_CONT_ON = prove
 (`!R. p2c_rad_rho p2c_std_A real_continuous_on real_interval[&0,R]`,
  GEN_TAC THEN MATCH_MP_TAC P2C_RAD_RHO_CONT THEN REWRITE_TAC[P2C_STD_HYP2]);;

let P2C_STD_RINV = prove
 (`!c. &0 <= c
       ==> &0 <= p2c_std_rinv c /\ p2c_rad_rho p2c_std_A (p2c_std_rinv c) = c`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2c_std_rinv] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(SPEC `c:real` P2C_STD_RHO_UNBOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p2c_rad_rho p2c_std_A`; `&0`; `B:real`; `c:real`]
         REAL_IVT_INCREASING) THEN
  ASM_REWRITE_TAC[P2C_STD_RHO_CONT_ON; P2C_RAD_RHO_0; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MESON_TAC[]]);;

let P2C_STD_RINV_UNIQUE = prove
 (`!r. &0 <= r ==> p2c_std_rinv (p2c_rad_rho p2c_std_A r) = r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p2c_rad_rho p2c_std_A r` P2C_STD_RINV) THEN ANTS_TAC THENL
   [MATCH_MP_TAC P2C_RAD_RHO_POS_LE THEN ASM_REWRITE_TAC[P2C_STD_HYP2]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`p2c_std_rinv (p2c_rad_rho p2c_std_A r)`; `r:real`]
         P2C_STD_RHO_LT_EQ) THEN
  MP_TAC(SPECL [`r:real`; `p2c_std_rinv (p2c_rad_rho p2c_std_A r)`]
         P2C_STD_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC);;

let P2C_STD_RINV_POS = prove
 (`!c. &0 < c ==> &0 < p2c_std_rinv c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `c:real` P2C_STD_RINV) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `p2c_rad_rho p2c_std_A (p2c_std_rinv c) = c` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[P2C_RAD_RHO_0] THEN
  ASM_REAL_ARITH_TAC);;

(* The radial map in closed form. *)

let P2C_STD_RADIAL_EQ = prove
 (`!y. ~(y = vec 0) /\ sqrt(&2) * log(norm y) < p2c_std_A0 + &4
       ==> p3_std_radial p2c_std_g0 p2c_std_A0 y =
           (p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log(norm y)) * inv(norm y)) % y`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[p3_std_radial; GSYM REAL_NOT_LT] THEN
  ABBREV_TAC `c = p2c_std_A0 + &4 - sqrt(&2) * log(norm(y:real^3))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p2c_std_rinv c /\ p2c_rad_rho p2c_std_A (p2c_std_rinv c) = c`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2C_STD_RINV_POS; P2C_STD_RINV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[P2C_STD_DIST] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `norm(x:real^3) = p2c_std_rinv c` ASSUME_TAC THENL
     [SUBGOAL_THEN `p2c_rad_rho p2c_std_A (norm(x:real^3)) = c` MP_TAC THENL
       [UNDISCH_TAC `p2c_std_A0 + &4 - sqrt (&2) * log (norm(y:real^3)) = c` THEN
        ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC P2C_STD_RINV_UNIQUE THEN REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `norm(x:real^3) % (inv(norm x) % x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL
       [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
      SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID];
      ONCE_REWRITE_TAC[ASSUME `inv(norm x) % x = inv(norm y) % (y:real^3)`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC]];
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `norm((p2c_std_rinv c * inv(norm y)) % (y:real^3)) = p2c_std_rinv c`
    ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_ENTIRE; REAL_INV_EQ_0; NORM_EQ_0;
                    VECTOR_MUL_ASSOC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < p2c_std_rinv c` THEN UNDISCH_TAC `&0 < norm(y:real^3)` THEN
      CONV_TAC REAL_FIELD;
      UNDISCH_TAC `p2c_std_A0 + &4 - sqrt (&2) * log (norm(y:real^3)) = c` THEN
      REAL_ARITH_TAC]]);;

(* The warping function is at most sqrt 2: u A(u) <= 2. *)

let P2C_STD_UA_LE = prove
 (`!u. &0 <= u ==> u * p2c_std_A u <= &2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&1 <= u` THENL
   [ASM_SIMP_TAC[P2C_STD_A_FAR] THEN
    SUBGOAL_THEN `~(u = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. u * p2c_std_A u`; `\u. p2c_std_A u * (&1 + u * p2c_std_m u)`;
                 `real_interval[&0,&1]`; `u:real`; `&1`]
         HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(ISPECL [`\u:real. u`; `&1`; `p2c_std_A`; `p2c_std_A x * p2c_std_m x`;
                     `x:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ID; P2C_STD_A_DERIV;
                   REAL_ARITH `&0 <= x ==> --(&1) < x`] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC P2C_STD_A_POS THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[P2C_STD_P_EQ; REAL_ARITH `&0 <= x ==> --(&1) < x`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[P2C_STD_CUT_BOUNDS] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[P2C_STD_A_FAR; REAL_LE_REFL] THEN REAL_ARITH_TAC);;
(* The derivative of rinv (inverse function theorem in one variable). *)

let P2C_STD_RINV_DERIV = prove
 (`!c. &0 < c
       ==> (p2c_std_rinv has_real_derivative
            inv(sqrt(p2c_std_A(p2c_std_rinv c pow 2)))) (atreal c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_INVERSE_STRONG_X THEN
  MAP_EVERY EXISTS_TAC [`p2c_rad_rho p2c_std_A`; `{r:real | r > &0}`] THEN
  ASM_SIMP_TAC[P2C_STD_RINV; REAL_LT_IMP_LE; IN_ELIM_THM; real_gt;
               P2C_STD_RINV_POS; REAL_OPEN_HALFSPACE_GT] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REWRITE_TAC[real_differentiable] THEN
    EXISTS_TAC `sqrt(p2c_std_A(r pow 2))` THEN
    MATCH_MP_TAC P2C_RAD_RHO_DERIV THEN ASM_REWRITE_TAC[P2C_STD_HYP2];
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2C_STD_RINV_UNIQUE THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2C_RAD_RHO_DERIV THEN
    ASM_SIMP_TAC[P2C_STD_HYP2; P2C_STD_RINV_POS];
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT THEN
    MATCH_MP_TAC P2C_STD_A_POS THEN
    MP_TAC(SPEC `p2c_std_rinv c` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

(* The norm is differentiable away from 0. *)

let P2C_NORM_DERIV = prove
 (`!x:real^N.
     ~(x = vec 0)
     ==> ((\y. lift(norm y)) has_derivative (\h. lift((x dot h) / norm x))) (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt`; `inv(&2 * sqrt(norm(x:real^N) pow 2))`;
                 `\z:real^N. lift(norm z pow 2)`; `\h:real^N. &2 % lift(x dot h)`;
                 `x:real^N`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_SIMP_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT; HAS_REAL_DERIVATIVE_SQRT] THEN
  SIMP_TAC[POW_2_SQRT; NORM_POS_LE] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL; LIFT_EQ] THEN
  GEN_TAC THEN SUBGOAL_THEN `~(norm(x:real^N) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

(* The radial profile R(t) = rinv(A0 + 4 - sqrt 2 log t) and its derivative. *)

let P2C_STD_RPROF_DERIV = prove
 (`!t. &0 < t /\ sqrt(&2) * log t < p2c_std_A0 + &4
       ==> ((\t. p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log t)) has_real_derivative
            (inv(sqrt(p2c_std_A(p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log t) pow 2))) *
             --(sqrt(&2) * inv t))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. p2c_std_A0 + &4 - sqrt(&2) * log t`; `p2c_std_rinv`;
                 `--(sqrt(&2) * inv t)`;
                 `inv(sqrt(p2c_std_A(p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log t)
                                     pow 2)))`;
                 `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(DISCH_ALL(REAL_DIFF_CONV
      `((\t. p2c_std_A0 + &4 - sqrt(&2) * log t) has_real_derivative f') (atreal t)`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC P2C_STD_RINV_DERIV THEN ASM_REAL_ARITH_TAC]);;
(* The radial map near y: derivative and the length comparison. *)

let P2C_STD_RADMAP_DERIV = prove
 (`!y:real^3.
     ~(y = vec 0) /\ sqrt(&2) * log(norm y) < p2c_std_A0 + &4
     ==> ((\z. (p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log(norm z)) * inv(norm z)) % z)
          has_derivative
          (\h. (p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log(norm y)) * inv(norm y)) % h +
               (((inv(sqrt(p2c_std_A(p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log(norm y))
                                     pow 2))) *
                  --(sqrt(&2) * inv(norm y))) * inv(norm y) +
                 p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log(norm y)) *
                 --inv(norm y pow 2)) * ((y dot h) / norm y)) % y)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `R = \t. p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log t)` THEN
  SUBGOAL_THEN
   `((\t. R t * inv t) has_real_derivative
     ((inv(sqrt(p2c_std_A(R(norm(y:real^3)) pow 2))) * --(sqrt(&2) * inv(norm y))) *
      inv(norm y) + R(norm y) * --inv(norm y pow 2))) (atreal (norm y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R:real->real`;
                   `inv(sqrt(p2c_std_A(R(norm(y:real^3)) pow 2))) * --(sqrt(&2) * inv(norm y))`;
                   `inv:real->real`; `--inv(norm(y:real^3) pow 2)`; `norm(y:real^3)`]
                  HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "R" THEN BETA_TAC THEN MATCH_MP_TAC P2C_STD_RPROF_DERIV THEN
        ASM_REWRITE_TAC[];
        MP_TAC(SPEC `norm(y:real^3)` HAS_REAL_DERIVATIVE_INV_BASIC) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
      ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (R:real->real) t * inv t`;
                 `(inv(sqrt(p2c_std_A(R(norm(y:real^3)) pow 2))) * --(sqrt(&2) * inv(norm y))) *
                  inv(norm y) + R(norm y) * --inv(norm y pow 2)`;
                 `\z:real^3. lift(norm z)`; `\h:real^3. lift((y dot h) / norm y)`;
                 `y:real^3`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_SIMP_TAC[LIFT_DROP; P2C_NORM_DERIV] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. (R:real->real)(norm z) * inv(norm z)`;
                 `\h:real^3. ((inv(sqrt(p2c_std_A(R(norm(y:real^3)) pow 2))) *
                               --(sqrt(&2) * inv(norm y))) * inv(norm y) +
                              R(norm y) * --inv(norm y pow 2)) * ((y dot h) / norm y)`;
                 `\z:real^3. z`; `\h:real^3. h`; `y:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; o_DEF] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL];
    EXPAND_TAC "R" THEN REWRITE_TAC[]]);;

(* The algebra of the length comparison. *)

let P2C_1237_ALGEBRA = prove
 (`!R t a sa s2 n p.
     &0 < t /\ &0 < R /\ &0 < a /\ &0 < sa /\ sa pow 2 = a /\ s2 pow 2 = &2 /\
     R pow 2 * a <= &2 /\ p pow 2 <= t pow 2 * n
     ==> (R * inv t) * a *
         ((R * inv t) * n +
          (((inv sa * --(s2 * inv t)) * inv t + R * --inv(t pow 2)) * p / t) * p) +
         (((inv sa * --(s2 * inv t)) * inv t + R * --inv(t pow 2)) * p / t) * a *
         ((R * inv t) * p +
          (((inv sa * --(s2 * inv t)) * inv t + R * --inv(t pow 2)) * p / t) * t pow 2)
         <= &2 / t pow 2 * n`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!c. x = b - c /\ &0 <= c ==> x <= b`) THEN
  EXISTS_TAC `(&2 - R pow 2 * a) * ((t pow 2 * n - p pow 2) / t pow 4)` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `sa pow 2 = a` THEN UNDISCH_TAC `s2 pow 2 = &2` THEN
    SUBGOAL_THEN `~(t = &0) /\ ~(sa = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]]]);;

(* MT Lemma 12.37 for the explicit standard initial metric. *)

let P2C_LEMMA_12_37_STD = prove
 (`!y v. ~(y = vec 0) /\ sqrt(&2) * log(norm y) < p2c_std_A0 + &4
         ==> (jacobian (p3_std_radial p2c_std_g0 p2c_std_A0) (at y) ** v) dot
             (p2c_std_g0 (p3_std_radial p2c_std_g0 p2c_std_A0 y) **
              (jacobian (p3_std_radial p2c_std_g0 p2c_std_A0) (at y) ** v)) <=
             v dot (cylinder_flow (&0) y ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `E = exp((p2c_std_A0 + &4) / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. &0 < norm z
               ==> (sqrt(&2) * log(norm z) < p2c_std_A0 + &4 <=> norm z < E)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "E" THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM(MATCH_MP EXP_LOG
      (ASSUME `&0 < norm(z:real^3)`))] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(y:real^3) < E` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `Phi = \z:real^3. (p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log(norm z)) *
                      inv(norm z)) % z` THEN
  ABBREV_TAC
   `D = \h:real^3. (p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log(norm y)) *
                    inv(norm y)) % h +
                   (((inv(sqrt(p2c_std_A(p2c_std_rinv (p2c_std_A0 + &4 -
                                         sqrt(&2) * log(norm y)) pow 2))) *
                      --(sqrt(&2) * inv(norm y))) * inv(norm y) +
                     p2c_std_rinv (p2c_std_A0 + &4 - sqrt(&2) * log(norm y)) *
                     --inv(norm y pow 2)) * ((y dot h) / norm y)) % y` THEN
  SUBGOAL_THEN `((Phi:real^3->real^3) has_derivative D) (at y)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Phi"; "D"] THEN MATCH_MP_TAC P2C_STD_RADMAP_DERIV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((p3_std_radial p2c_std_g0 p2c_std_A0) has_derivative D) (at y) /\
    p3_std_radial p2c_std_g0 p2c_std_A0 y = Phi y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`Phi:real^3->real^3`; `min (norm(y:real^3)) (E - norm y)`] THEN
      ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      EXPAND_TAC "Phi" THEN MATCH_MP_TAC P2C_STD_RADIAL_EQ THEN
      SUBGOAL_THEN `&0 < norm(z:real^3) /\ norm z < E` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `dist(z:real^3,y) < norm y /\ dist(z,y) < E - norm y` THEN
        NORM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM NORM_POS_LT];
      EXPAND_TAC "Phi" THEN MATCH_MP_TAC P2C_STD_RADIAL_EQ THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(D:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT
      (ASSUME `((p3_std_radial p2c_std_g0 p2c_std_A0) has_derivative D) (at y)`))]) THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  (* the quantities *)
  ABBREV_TAC `c = p2c_std_A0 + &4 - sqrt(&2) * log(norm(y:real^3))` THEN
  ABBREV_TAC `R = p2c_std_rinv c` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC P2C_STD_RINV_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a = p2c_std_A(R pow 2)` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC P2C_STD_A_POS THEN
    MP_TAC(SPEC `R:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `R pow 2 * a <= &2` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC P2C_STD_UA_LE THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((Phi:real^3->real^3) y) = R` ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2c_std_g0; LRG_CYL0_EQ] THEN EXPAND_TAC "D" THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL; DOT_LMUL;
              DOT_RADD; DOT_LADD] THEN
  REWRITE_TAC[NORM_POW_2] THEN
  SUBGOAL_THEN `sqrt a pow 2 = a /\ sqrt(&2) pow 2 = &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt a` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) dot y = norm y pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `((y:real^3) dot v) pow 2 <= norm y pow 2 * (v dot v)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM; NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  REWRITE_TAC[ISPECL [`v:real^3`; `y:real^3`] DOT_SYM] THEN
  SUBGOAL_THEN `((v:real^3) dot y) pow 2 <= norm y pow 2 * (v dot v)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`R:real`; `norm(y:real^3)`; `a:real`; `sqrt a`; `sqrt(&2)`;
                `(v:real^3) dot v`; `(v:real^3) dot y`] P2C_1237_ALGEBRA) THEN
  ASM_REWRITE_TAC[]);;

