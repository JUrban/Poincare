(* Vendored copy of the library file src/ns_cutoff.ml from the Navier_Stokes
   development (github.com/hol-light-family/Navier_Stokes).
   Code unchanged except that its needs lines point to the vendored copies. *)

needs "src/ns_spacetime.ml";;
type_invention_error := true;;

(* ========================================================================= *)
(* Unit ns_cutoff: smooth cutoff functions.                                  *)
(*   cutoff_flat t = exp(-1/t) for t > 0 and 0 for t <= 0 is smooth;         *)
(*   smooth_step t = flat t / (flat t + flat(1 - t)) is a smooth monotone    *)
(*   step from 0 (t <= 0) to 1 (t >= 1); smooth_bump a b is a smooth radial  *)
(*   bump on real^N, equal to 1 on the ball of radius a and 0 outside the    *)
(*   ball of radius b.                                                       *)
(* Contents: definitions; exponential and polynomial growth bounds; the      *)
(* derivative of a polynomial function is a polynomial function; the        *)
(* polynomial sequence P with P 0 = 1, P (n+1) y = y^2 (P n y - P' n y).     *)
(* ========================================================================= *)

let cutoff_flat = new_definition
 `cutoff_flat t = if t <= &0 then &0 else exp(--inv t)`;;

let smooth_step = new_definition
 `smooth_step t = cutoff_flat t / (cutoff_flat t + cutoff_flat(&1 - t))`;;

let smooth_bump = new_definition
 `smooth_bump a b (x:real^N) =
    smooth_step((b pow 2 - norm x pow 2) / (b pow 2 - a pow 2))`;;

(* ------------------------------------------------------------------------- *)
(* y^m <= m^m e^y for y >= 0, from e^y = (e^(y/m))^m and 1 + z <= e^z.       *)
(* ------------------------------------------------------------------------- *)

let CUTOFF_POW_LE_EXP = prove
 (`!m y. &0 <= y ==> y pow m <= &m pow m * exp y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    MP_TAC(SPEC `y:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&m = &0) /\ &0 < &m` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp y = exp(y / &m) pow m` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `y pow m = &m pow m * (y / &m) pow m` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `y / &m` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* exp(-1/t) <= n^n t^n for t > 0.                                           *)
(* ------------------------------------------------------------------------- *)

let CUTOFF_EXP_NEG_INV_LE = prove
 (`!n t. &0 < t ==> exp(--inv t) <= &n pow n * t pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `inv t`] CUTOFF_POW_LE_EXP) THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `&0 < exp(inv t) /\ &0 < t pow n` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG; REAL_POW_INV] THEN
  SUBGOAL_THEN `inv(exp(inv t)) = &1 / exp(inv t) /\
                inv(t pow n) = &1 / t pow n`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Polynomial growth: |p y| <= c y^k for y >= 1.                             *)
(* ------------------------------------------------------------------------- *)

let CUTOFF_POLY_BOUND = prove
 (`!p. polynomial_function p
       ==> ?c k. !y. &1 <= y ==> abs(p y) <= c * y pow k`,
  GEN_TAC THEN REWRITE_TAC[polynomial_function; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:num->real`] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`sum(0..m) (\i. abs((a:num->real) i))`; `m:num`] THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  SUBGOAL_THEN `abs y = y` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* |p(1/t) exp(-1/t)| <= c t^2 for 0 < t <= 1.                              *)
(* ------------------------------------------------------------------------- *)

let CUTOFF_POLY_EXP_BOUND = prove
 (`!p. polynomial_function p
       ==> ?c. !t. &0 < t /\ t <= &1
                   ==> abs(p(inv t) * exp(--inv t)) <= c * t pow 2`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CUTOFF_POLY_BOUND) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `k:num`] THEN DISCH_TAC THEN
  EXISTS_TAC `c * &(k + 2) pow (k + 2)` THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= inv t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((p:real->real)(inv t)) <= c * inv t pow k` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--inv t) <= &(k + 2) pow (k + 2) * t pow (k + 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CUTOFF_EXP_NEG_INV_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_EXP] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(c * inv t pow k) * (&(k + 2) pow (k + 2) * t pow (k + 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
  SUBGOAL_THEN `inv t pow k * t pow k = &1` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_POW_ONE];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`t:real`; `k:num`; `2`] REAL_POW_ADD] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* The derivative of a polynomial function is a polynomial function.        *)
(* ------------------------------------------------------------------------- *)

let CUTOFF_POLY_DERIV = prove
 (`!p. polynomial_function p
       ==> ?q. polynomial_function q /\
               !x. (p has_real_derivative q x) (atreal x)`,
  SUBGOAL_THEN
   `!p. polynomial_function p
        ==> polynomial_function p /\
            ?q. polynomial_function q /\
                !x. (p has_real_derivative q x) (atreal x)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC POLYNOMIAL_FUNCTION_INDUCT THEN
  REWRITE_TAC[POLYNOMIAL_FUNCTION_ID; POLYNOMIAL_FUNCTION_CONST] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `\x:real. &1` THEN
    REWRITE_TAC[POLYNOMIAL_FUNCTION_CONST; HAS_REAL_DERIVATIVE_ID];
    X_GEN_TAC `c:real` THEN EXISTS_TAC `\x:real. &0` THEN
    REWRITE_TAC[POLYNOMIAL_FUNCTION_CONST; HAS_REAL_DERIVATIVE_CONST];
    MAP_EVERY X_GEN_TAC [`p:real->real`; `q:real->real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `p':real->real` STRIP_ASSUME_TAC))
     (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `q':real->real` STRIP_ASSUME_TAC))) THEN
    ASM_SIMP_TAC[POLYNOMIAL_FUNCTION_ADD] THEN
    EXISTS_TAC `\x. (p':real->real) x + q' x` THEN
    ASM_SIMP_TAC[POLYNOMIAL_FUNCTION_ADD; HAS_REAL_DERIVATIVE_ADD];
    MAP_EVERY X_GEN_TAC [`p:real->real`; `q:real->real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `p':real->real` STRIP_ASSUME_TAC))
     (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `q':real->real` STRIP_ASSUME_TAC))) THEN
    ASM_SIMP_TAC[POLYNOMIAL_FUNCTION_MUL] THEN
    EXISTS_TAC `\x. (p:real->real) x * q' x + p' x * q x` THEN
    ASM_SIMP_TAC[POLYNOMIAL_FUNCTION_ADD; POLYNOMIAL_FUNCTION_MUL;
                 HAS_REAL_DERIVATIVE_MUL_ATREAL]]);;

(* ------------------------------------------------------------------------- *)
(* The polynomial sequence of the derivatives of exp(-1/t).                  *)
(* ------------------------------------------------------------------------- *)

let CUTOFF_POLY_SEQUENCE = prove
 (`?P P':num->real->real.
      P 0 = (\y. &1) /\
      (!n. polynomial_function (P n)) /\
      (!n y. (P n has_real_derivative P' n y) (atreal y)) /\
      (!n y. P (SUC n) y = y pow 2 * (P n y - P' n y))`,
  X_CHOOSE_TAC `D:(real->real)->real->real`
   (REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] CUTOFF_POLY_DERIV) THEN
  MP_TAC(ISPECL [`\y:real. &1`;
                 `\(p:real->real) (n:num) (y:real). y pow 2 * (p y - D p y)`]
         num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num->real->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!n. polynomial_function ((P:num->real->real) n)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[POLYNOMIAL_FUNCTION_CONST] THEN
    MATCH_MP_TAC POLYNOMIAL_FUNCTION_MUL THEN
    ASM_SIMP_TAC[POLYNOMIAL_FUNCTION_POW; POLYNOMIAL_FUNCTION_ID;
                 POLYNOMIAL_FUNCTION_SUB; ETA_AX];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`P:num->real->real`; `\n:num. (D:(real->real)->real->real) (P n)`] THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Smoothness of cutoff_flat.  The n-th derivative of the flat               *)
(* function is t |-> P n (1/t) exp(-1/t) for t > 0 and 0 for t <= 0; at 0   *)
(* every such function is O(t^2), so its derivative there is 0.              *)
(* ========================================================================= *)

(* d/dt [p(1/t) exp(-1/t)] = (1/t)^2 (p(1/t) - p'(1/t)) exp(-1/t), t <> 0.   *)

let CUTOFF_HAS_DERIVATIVE_POLY_EXP = prove
 (`!(p:real->real) p' x.
     ~(x = &0) /\ (!y. (p has_real_derivative p' y) (atreal y))
     ==> ((\x. p(inv x) * exp(--inv x)) has_real_derivative
          (inv x pow 2 * (p(inv x) - p'(inv x)) * exp(--inv x)))
         (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. (p:real->real)(inv x) * exp(--inv x)) has_real_derivative
     (p(inv x) * (exp(--inv x) * inv(x pow 2)) +
      ((p':real->real)(inv x) * --inv(x pow 2)) * exp(--inv x))) (atreal x)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`inv:real->real`; `p:real->real`; `--inv(x pow 2)`;
                     `(p':real->real)(inv x)`; `x:real`]
                    REAL_DIFF_CHAIN_ATREAL) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_INV_BASIC; o_DEF];
      REAL_DIFF_TAC THEN UNDISCH_TAC `~(x = &0)` THEN CONV_TAC REAL_FIELD];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_POW_INV] THEN REAL_ARITH_TAC]);;

(* A function vanishing for t <= 0 and O(t^2) on (0,1] has derivative 0 at 0. *)

let CUTOFF_DERIV_AT_0 = prove
 (`!f c. (!t. t <= &0 ==> f t = &0) /\
         (!t. &0 < t /\ t <= &1 ==> abs(f t) <= c * t pow 2)
         ==> (f has_real_derivative &0) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `min (&1) (e / (abs c + &1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[REAL_SUB_RZERO; REAL_LT_MIN] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real)(&0) = &0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  ASM_CASES_TAC `x <= &0` THENL
   [ASM_SIMP_TAC[real_div; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  SUBGOAL_THEN `abs x = x` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                                      REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((f:real->real) x) <= c * x pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `x * (abs c + &1) < e` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < abs c + &1` ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `x < e / (abs c + &1)` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x * (abs c + &1)) * x < e * x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c * x pow 2 <= abs c * x pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= x pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The derivative sequence of the flat function.                            *)

let CUTOFF_FLAT_SEQ_DERIV = prove
 (`!P P':num->real->real.
      (!n. polynomial_function (P n)) /\
      (!n y. (P n has_real_derivative P' n y) (atreal y)) /\
      (!n y. P (SUC n) y = y pow 2 * (P n y - P' n y))
      ==> !n x. ((\t. if t <= &0 then &0 else P n (inv t) * exp(--inv t))
                 has_real_derivative
                 (if x <= &0 then &0 else P (SUC n) (inv x) * exp(--inv x)))
                (atreal x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `n:num` THEN X_GEN_TAC `x:real` THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC CUTOFF_DERIV_AT_0 THEN
    MP_TAC(SPEC `(P:num->real->real) n` CUTOFF_POLY_EXP_BOUND) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN CONJ_TAC THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(t <= &0)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `x < &0` THENL
   [SUBGOAL_THEN `x <= &0` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\t:real. &0`; `--x:real`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `y <= &0` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(x <= &0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC
   [`\t. (P:num->real->real) n (inv t) * exp(--inv t)`; `x:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y <= &0)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(P:num->real->real) n`; `(P':num->real->real) n`;
                   `x:real`] CUTOFF_HAS_DERIVATIVE_POLY_EXP) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The heart: cutoff_flat is smooth on the real line.                        *)
(* ------------------------------------------------------------------------- *)

let CUTOFF_FLAT_SMOOTH = prove
 (`smooth_map_on (:real^1) (lift o cutoff_flat o drop)`,
  X_CHOOSE_THEN `P:num->real->real`
   (X_CHOOSE_THEN `P':num->real->real` STRIP_ASSUME_TAC)
   CUTOFF_POLY_SEQUENCE THEN
  MP_TAC(ISPECL
   [`(:real)`;
    `\n:num t:real. if t <= &0 then &0
                    else (P:num->real->real) n (inv t) * exp(--inv t)`]
   SMOOTH_MAP_ON_REAL_SEQUENCE) THEN
  REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV; IMAGE_LIFT_UNIV] THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`P:num->real->real`; `P':num->real->real`]
                 CUTOFF_FLAT_SEQ_DERIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM cutoff_flat; ETA_AX]);;

(* ========================================================================= *)
(* The smooth step function.                                                 *)
(* ========================================================================= *)

(* Elementary properties of cutoff_flat.                                     *)

let CUTOFF_FLAT_ZERO = prove
 (`!t. t <= &0 ==> cutoff_flat t = &0`,
  SIMP_TAC[cutoff_flat]);;

let CUTOFF_FLAT_POS_LE = prove
 (`!t. &0 <= cutoff_flat t`,
  GEN_TAC THEN REWRITE_TAC[cutoff_flat] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_EXP_POS_LE]);;

let CUTOFF_FLAT_POS_LT = prove
 (`!t. &0 < cutoff_flat t <=> &0 < t`,
  GEN_TAC THEN REWRITE_TAC[cutoff_flat] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_LT_REFL; REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC);;

let CUTOFF_FLAT_MONO = prove
 (`!s t. s <= t ==> cutoff_flat s <= cutoff_flat t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cutoff_flat] THEN
  ASM_CASES_TAC `s <= &0` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t <= &0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

let CUTOFF_FLAT_DENOM_POS = prove
 (`!t. &0 < cutoff_flat t + cutoff_flat(&1 - t)`,
  GEN_TAC THEN
  MP_TAC(SPEC `t:real` CUTOFF_FLAT_POS_LE) THEN
  MP_TAC(SPEC `&1 - t` CUTOFF_FLAT_POS_LE) THEN
  MP_TAC(SPEC `t:real` CUTOFF_FLAT_POS_LT) THEN
  MP_TAC(SPEC `&1 - t` CUTOFF_FLAT_POS_LT) THEN
  REAL_ARITH_TAC);;

(* Two real lemmas on ratios a / (a + b).                                    *)

let CUTOFF_RATIO_BOUNDS = prove
 (`!a b. &0 <= a /\ &0 <= b /\ &0 < a + b
         ==> &0 <= a / (a + b) /\ a / (a + b) <= &1`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let CUTOFF_RATIO_MONO = prove
 (`!a b c d. &0 <= a /\ &0 <= b /\ &0 <= c /\ &0 <= d /\
             &0 < a + b /\ &0 < c + d /\ a <= c /\ d <= b
             ==> a / (a + b) <= c / (c + d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `c / (c + d) - a / (a + b) = (c * b - a * d) / ((a + b) * (c + d))`
  MP_TAC THENL
   [SUBGOAL_THEN `~(a + b = &0) /\ ~(c + d = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c * b - a * d) / ((a + b) * (c + d))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [SUBGOAL_THEN `a * d <= c * d /\ c * d <= c * b` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* The values and bounds of smooth_step.                                     *)

let SMOOTH_STEP_0 = prove
 (`!t. t <= &0 ==> smooth_step t = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_step] THEN
  ASM_SIMP_TAC[CUTOFF_FLAT_ZERO; real_div; REAL_MUL_LZERO]);;

let SMOOTH_STEP_1 = prove
 (`!t. &1 <= t ==> smooth_step t = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_step] THEN
  SUBGOAL_THEN `cutoff_flat(&1 - t) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC CUTOFF_FLAT_ZERO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
  MATCH_MP_TAC REAL_LT_IMP_NZ THEN REWRITE_TAC[CUTOFF_FLAT_POS_LT] THEN
  ASM_REAL_ARITH_TAC);;

let SMOOTH_STEP_BOUNDS = prove
 (`!t. &0 <= smooth_step t /\ smooth_step t <= &1`,
  GEN_TAC THEN REWRITE_TAC[smooth_step] THEN
  MATCH_MP_TAC CUTOFF_RATIO_BOUNDS THEN
  REWRITE_TAC[CUTOFF_FLAT_POS_LE; CUTOFF_FLAT_DENOM_POS]);;

let SMOOTH_STEP_MONO = prove
 (`!s t. s <= t ==> smooth_step s <= smooth_step t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_step] THEN
  MATCH_MP_TAC CUTOFF_RATIO_MONO THEN
  REWRITE_TAC[CUTOFF_FLAT_POS_LE; CUTOFF_FLAT_DENOM_POS] THEN
  CONJ_TAC THEN MATCH_MP_TAC CUTOFF_FLAT_MONO THEN ASM_REAL_ARITH_TAC);;

(* Smoothness.                                                               *)

let CUTOFF_SMOOTH_MAP_ON_LIFT_INV = prove
 (`!s (f:real^M->real^1).
      open s /\ smooth_map_on s f /\ (!x. x IN s ==> ~(drop(f x) = &0))
      ==> smooth_map_on s (\x. lift(inv(drop(f x))))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LIFT_INV_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_STEP_SMOOTH = prove
 (`smooth_map_on (:real^1) (lift o smooth_step o drop)`,
  SUBGOAL_THEN `smooth_map_on (:real^1) (\x. lift(cutoff_flat(drop x)))`
  ASSUME_TAC THENL
   [MP_TAC CUTOFF_FLAT_SMOOTH THEN REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^1) (\x. lift(cutoff_flat(&1 - drop x)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. lift(cutoff_flat(&1 - drop x))) =
                  (lift o cutoff_flat o drop) o (\x:real^1. vec 1 - x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_SUB; DROP_VEC]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; CUTOFF_FLAT_SMOOTH] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^1)
     (\x. lift(inv(drop(lift(cutoff_flat(drop x)) +
                        lift(cutoff_flat(&1 - drop x))))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CUTOFF_SMOOTH_MAP_ON_LIFT_INV THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
      REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN GEN_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN REWRITE_TAC[CUTOFF_FLAT_DENOM_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lift o smooth_step o drop =
    (\x. lift(drop(lift(cutoff_flat(drop x))) *
              drop(lift(inv(drop(lift(cutoff_flat(drop x)) +
                                 lift(cutoff_flat(&1 - drop x))))))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; smooth_step; LIFT_DROP; DROP_ADD;
                real_div];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_LIFT_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV]);;

let SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE = prove
 (`!s (f:real^M->real^1).
      open s /\ smooth_map_on s f
      ==> smooth_map_on s (\x. lift(smooth_step(drop(f x))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(smooth_step(drop((f:real^M->real^1) x)))) =
                (lift o smooth_step o drop) o f`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_STEP_SMOOTH]);;

(* ========================================================================= *)
(* The radial smooth bump on real^N.                                         *)
(* ========================================================================= *)

let SMOOTH_BUMP_SMOOTH = prove
 (`!a b. &0 <= a /\ a < b
         ==> smooth_map_on (:real^N) (\x. lift(smooth_bump a b x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_bump] THEN
  SUBGOAL_THEN
   `(\x:real^N. lift(smooth_step((b pow 2 - norm x pow 2) /
                                 (b pow 2 - a pow 2)))) =
    (\x. lift(smooth_step(drop((\x. inv(b pow 2 - a pow 2) %
                                     (lift(b pow 2) - lift(norm x pow 2)))
                               x))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DROP_CMUL; DROP_SUB; LIFT_DROP; real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE THEN
  REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]);;

let CUTOFF_BUMP_DENOM_POS = prove
 (`!a b. &0 <= a /\ a < b ==> &0 < b pow 2 - a pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a pow 2 < b pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REAL_ARITH_TAC]);;

let SMOOTH_BUMP_1 = prove
 (`!a b (x:real^N). &0 <= a /\ a < b /\ norm x <= a
                    ==> smooth_bump a b x = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_bump] THEN
  MATCH_MP_TAC SMOOTH_STEP_1 THEN
  SUBGOAL_THEN `&0 < b pow 2 - a pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC CUTOFF_BUMP_DENOM_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
  SUBGOAL_THEN `norm(x:real^N) pow 2 <= a pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    REAL_ARITH_TAC]);;

let SMOOTH_BUMP_0 = prove
 (`!a b (x:real^N). &0 <= a /\ a < b /\ b <= norm x
                    ==> smooth_bump a b x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_bump] THEN
  MATCH_MP_TAC SMOOTH_STEP_0 THEN
  SUBGOAL_THEN `&0 < b pow 2 - a pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC CUTOFF_BUMP_DENOM_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN
  SUBGOAL_THEN `b pow 2 <= norm(x:real^N) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let SMOOTH_BUMP_BOUNDS = prove
 (`!a b (x:real^N). &0 <= smooth_bump a b x /\ smooth_bump a b x <= &1`,
  REWRITE_TAC[smooth_bump; SMOOTH_STEP_BOUNDS]);;

