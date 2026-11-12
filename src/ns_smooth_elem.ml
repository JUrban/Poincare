(* Vendored copy of the library file src/ns_smooth_elem.ml from the Navier_Stokes
   development (github.com/hol-light-family/Navier_Stokes).
   Code unchanged except that its needs lines point to the vendored copies. *)

needs "src/ns_spacetime.ml";;
type_invention_error := true;;

(* ========================================================================= *)
(* Elementary smooth functions, part 0: algebraic closure of smooth_map_on   *)
(* for real^1-valued maps (lifted products, quotients, powers, sums),        *)
(* components and coordinates, the componentwise criterion, and a            *)
(* criterion for smoothness of a real function of one real variable from     *)
(* the smoothness of its derivative.  Everything is built on the C^k         *)
(* calculus of ns_smooth.ml (continuously_differentiable, smooth_map_on).    *)
(* ========================================================================= *)

let SMOOTH_MAP_ON_EQ_OPEN = prove
 (`!s (f:real^M->real^N) g.
     open s /\ (!x. x IN s ==> f x = g x) /\ smooth_map_on s f
     ==> smooth_map_on s g`,
  REWRITE_TAC[smooth_map_on] THEN
  MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN]);;

(* ------------------------------------------------------------------------- *)
(* Coordinates and components.                                               *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_MAP_ON_LIFT_COORDINATE = prove
 (`!s k. open s ==> smooth_map_on s (\x:real^M. lift(x$k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
  ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT]);;

let SMOOTH_MAP_ON_LIFT_COMPONENT = prove
 (`!s (f:real^M->real^N) k.
     open s /\ smooth_map_on s f ==> smooth_map_on s (\x. lift(f x$k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^M. lift((f:real^M->real^N) x$k)) =
                (\y:real^N. lift(y$k)) o f` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT]);;

let SMOOTH_MAP_ON_LAMBDA = prove
 (`!s (g:num->real^M->real^1).
     open s /\ (!k. 1 <= k /\ k <= dimindex(:N) ==> smooth_map_on s (g k))
     ==> smooth_map_on s (\x. (lambda k. drop(g k x)):real^N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^M. (lambda k. drop((g:num->real^M->real^1) k x)):real^N) =
    (\x. vsum (1..dimindex(:N)) (\k. drop(g k x) % basis k))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_NUMSEG; LAMBDA_BETA];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`;
                 `\(k:num) (x:real^M).
                    drop((g:num->real^M->real^1) k x) % (basis k:real^N)`;
                 `1..dimindex(:N)`] SMOOTH_MAP_ON_VSUM_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `(g:num->real^M->real^1) k`;
                 `\x:real^M. (basis k:real^N)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST]);;

let SMOOTH_MAP_ON_COMPONENTWISE = prove
 (`!s (f:real^M->real^N).
     open s
     ==> (smooth_map_on s f <=>
          !k. 1 <= k /\ k <= dimindex(:N)
              ==> smooth_map_on s (\x. lift(f x$k)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(f:real^M->real^N) = (\x. (lambda k. drop(lift(f x$k))):real^N)`
  SUBST1_TAC THENL
   [SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA; LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`;
                 `\(k:num) (x:real^M). lift((f:real^M->real^N) x$k)`]
    SMOOTH_MAP_ON_LAMBDA) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lifted arithmetic on real^1-valued smooth maps.                           *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_MAP_ON_LIFT_MUL = prove
 (`!s (f:real^M->real^1) g.
     open s /\ smooth_map_on s f /\ smooth_map_on s g
     ==> smooth_map_on s (\x. lift(drop(f x) * drop(g x)))`,
  MATCH_ACCEPT_TAC SMOOTH_MAP_ON_MUL_LIFT_OPEN);;

let SMOOTH_MAP_ON_LIFT_ADD = prove
 (`!s (f:real^M->real^1) g.
     open s /\ smooth_map_on s f /\ smooth_map_on s g
     ==> smooth_map_on s (\x. lift(drop(f x) + drop(g x)))`,
  REWRITE_TAC[LIFT_ADD; LIFT_DROP] THEN
  MATCH_ACCEPT_TAC SMOOTH_MAP_ON_ADD_OPEN);;

let SMOOTH_MAP_ON_LIFT_SUB = prove
 (`!s (f:real^M->real^1) g.
     open s /\ smooth_map_on s f /\ smooth_map_on s g
     ==> smooth_map_on s (\x. lift(drop(f x) - drop(g x)))`,
  REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN
  MATCH_ACCEPT_TAC SMOOTH_MAP_ON_SUB_OPEN);;

let SMOOTH_MAP_ON_LIFT_CMUL = prove
 (`!s c (f:real^M->real^1).
     open s /\ smooth_map_on s f
     ==> smooth_map_on s (\x. lift(c * drop(f x)))`,
  REWRITE_TAC[LIFT_CMUL; LIFT_DROP] THEN
  MATCH_ACCEPT_TAC SMOOTH_MAP_ON_CMUL_OPEN);;

let SMOOTH_MAP_ON_LIFT_NEG = prove
 (`!s (f:real^M->real^1).
     open s /\ smooth_map_on s f
     ==> smooth_map_on s (\x. lift(--drop(f x)))`,
  REWRITE_TAC[LIFT_NEG; LIFT_DROP] THEN
  MATCH_ACCEPT_TAC SMOOTH_MAP_ON_NEG_OPEN);;

let SMOOTH_MAP_ON_LIFT_INV = prove
 (`!s (f:real^M->real^1).
     open s /\ smooth_map_on s f /\ (!x. x IN s ==> ~(drop(f x) = &0))
     ==> smooth_map_on s (\x. lift(inv(drop(f x))))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LIFT_INV_OPEN THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_LIFT_DIV = prove
 (`!s (f:real^M->real^1) g.
     open s /\ smooth_map_on s f /\ smooth_map_on s g /\
     (!x. x IN s ==> ~(drop(g x) = &0))
     ==> smooth_map_on s (\x. lift(drop(f x) / drop(g x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  SUBGOAL_THEN
   `smooth_map_on s (\x:real^M. lift(inv(drop((g:real^M->real^1) x))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^1`;
                 `\x:real^M. lift(inv(drop((g:real^M->real^1) x)))`]
    SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SMOOTH_MAP_ON_LIFT_POW = prove
 (`!s (f:real^M->real^1) n.
     open s /\ smooth_map_on s f
     ==> smooth_map_on s (\x. lift(drop(f x) pow n))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[real_pow; SMOOTH_MAP_ON_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s (\x:real^M. lift(drop((f:real^M->real^1) x) pow n))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^1`;
                 `\x:real^M. lift(drop((f:real^M->real^1) x) pow n)`]
    SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SMOOTH_MAP_ON_LIFT_SUM = prove
 (`!s (f:A->real^M->real^1) k.
     open s /\ FINITE k /\ (!i. i IN k ==> smooth_map_on s (f i))
     ==> smooth_map_on s (\x. lift(sum k (\i. drop(f i x))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF; LIFT_DROP] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:A->real^M->real^1`; `k:A->bool`]
    SMOOTH_MAP_ON_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[]);;

let SMOOTH_MAP_ON_LIFT_PRODUCT = prove
 (`!s (f:A->real^M->real^1) k.
     open s /\ FINITE k /\ (!i. i IN k ==> smooth_map_on s (f i))
     ==> smooth_map_on s (\x. lift(product k (\i. drop(f i x))))`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PRODUCT_OPEN THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Real functions of one variable: smooth when the derivative is smooth.     *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUSLY_DIFFERENTIABLE_SUC_REAL_1D = prove
 (`!n t (g:real->real) (g':real->real).
     open t /\
     (!x. x IN t ==> (g has_real_derivative g'(drop x)) (atreal (drop x))) /\
     continuously_differentiable n t (lift o g' o drop)
     ==> continuously_differentiable (SUC n) t (lift o g o drop)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `\(x:real^1) (h:real^1). drop h % lift((g':real->real)(drop x))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
    ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_DROP] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `h:real^1` THEN BETA_TAC THEN
    SUBGOAL_THEN `(\x:real^1. drop h % lift((g':real->real)(drop x))) =
                  (\x. drop h % (lift o g' o drop) x)` SUBST1_TAC THENL
     [REWRITE_TAC[o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN
    ASM_REWRITE_TAC[ETA_AX]]);;

let SMOOTH_MAP_ON_REAL_DERIVATIVE_1D = prove
 (`!t (g:real->real) (g':real->real).
     open t /\
     (!x. x IN t ==> (g has_real_derivative g'(drop x)) (atreal (drop x))) /\
     smooth_map_on t (lift o g' o drop)
     ==> smooth_map_on t (lift o g o drop)`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUC_IMP THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUC_REAL_1D THEN
  EXISTS_TAC `g':real->real` THEN ASM_REWRITE_TAC[]);;

(* Composition of a smooth real^1-valued map with a real function that is   *)
(* smooth on an open set containing the values of the map.                  *)

let SMOOTH_MAP_ON_LIFT_COMPOSE_1D = prove
 (`!s t (f:real^M->real^1) (g:real->real).
     open s /\ open t /\ (!x. x IN s ==> f x IN t) /\
     smooth_map_on s f /\ smooth_map_on t (lift o g o drop)
     ==> smooth_map_on s (\x. lift(g(drop(f x))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^M. lift((g:real->real)(drop((f:real^M->real^1) x)))) =
    (lift o g o drop) o f` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `t:real^1->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]);;

let OPEN_DROP_POSITIVE = prove
 (`open {x:real^1 | &0 < drop x}`,
  REWRITE_TAC[drop; GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT]);;

(* ========================================================================= *)
(* Elementary smooth functions, part 1: exp, sin, cos, log, rpow and sqrt,   *)
(* first as real functions of one variable on an open subset of real^1,      *)
(* then composed with a smooth real^1-valued map on an open set.             *)
(* ========================================================================= *)

let SIN_ADD_PI2_EQ_COS = prove
 (`!y. sin(y + pi / &2) = cos y`,
  REWRITE_TAC[SIN_ADD; SIN_PI2; COS_PI2] THEN REAL_ARITH_TAC);;

(* The derivative sequence of sin: the n-th derivative is a shift by n      *)
(* quarter periods, so one family covers both sin and cos.                  *)

let SMOOTH_MAP_ON_SIN_SHIFT_1D = prove
 (`!n. smooth_map_on (:real^1) (lift o (\x. sin(x + &n * pi / &2)) o drop)`,
  MP_TAC(ISPECL [`(:real)`; `\(n:num) (x:real). sin(x + &n * pi / &2)`]
    SMOOTH_MAP_ON_REAL_SEQUENCE) THEN
  REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV; IMAGE_LIFT_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:real`] THEN
  SUBGOAL_THEN
   `sin(x + &(SUC n) * pi / &2) = (&1 + &0) * cos(x + &n * pi / &2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ADD_ASSOC; SIN_ADD_PI2_EQ_COS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_DIFF_CONV);;

let SMOOTH_MAP_ON_SIN_1D = prove
 (`smooth_map_on (:real^1) (lift o sin o drop)`,
  MP_TAC(SPEC `0` SMOOTH_MAP_ON_SIN_SHIFT_1D) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; REAL_MUL_LZERO; REAL_ADD_RID]);;

let SMOOTH_MAP_ON_COS_1D = prove
 (`smooth_map_on (:real^1) (lift o cos o drop)`,
  MP_TAC(SPEC `1` SMOOTH_MAP_ON_SIN_SHIFT_1D) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; REAL_MUL_LID; SIN_ADD_PI2_EQ_COS]);;

let SMOOTH_MAP_ON_LOG_1D = prove
 (`smooth_map_on {x:real^1 | &0 < drop x} (lift o log o drop)`,
  MATCH_MP_TAC SMOOTH_MAP_ON_REAL_DERIVATIVE_1D THEN
  EXISTS_TAC `real_inv` THEN
  REWRITE_TAC[OPEN_DROP_POSITIVE; IN_ELIM_THM] THEN CONJ_TAC THENL
   [SIMP_TAC[HAS_REAL_DERIVATIVE_LOG]; ALL_TAC] THEN
  SUBGOAL_THEN `(lift o real_inv o drop) =
                (\x:real^1. lift(inv(drop((\x:real^1. x) x))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_INV THEN
  REWRITE_TAC[OPEN_DROP_POSITIVE; SMOOTH_MAP_ON_ID; IN_ELIM_THM] THEN
  SIMP_TAC[REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* Composition with a smooth real^1-valued map.                              *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_MAP_ON_LIFT_EXP = prove
 (`!s (f:real^M->real^1).
     open s /\ smooth_map_on s f
     ==> smooth_map_on s (\x. lift(exp(drop(f x))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPOSE_1D THEN
  EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_EXP_1D]);;

let SMOOTH_MAP_ON_LIFT_SIN = prove
 (`!s (f:real^M->real^1).
     open s /\ smooth_map_on s f
     ==> smooth_map_on s (\x. lift(sin(drop(f x))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPOSE_1D THEN
  EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_SIN_1D]);;

let SMOOTH_MAP_ON_LIFT_COS = prove
 (`!s (f:real^M->real^1).
     open s /\ smooth_map_on s f
     ==> smooth_map_on s (\x. lift(cos(drop(f x))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPOSE_1D THEN
  EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_COS_1D]);;

let SMOOTH_MAP_ON_LIFT_LOG = prove
 (`!s (f:real^M->real^1).
     open s /\ smooth_map_on s f /\ (!x. x IN s ==> &0 < drop(f x))
     ==> smooth_map_on s (\x. lift(log(drop(f x))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPOSE_1D THEN
  EXISTS_TAC `{x:real^1 | &0 < drop x}` THEN
  ASM_SIMP_TAC[OPEN_DROP_POSITIVE; SMOOTH_MAP_ON_LOG_1D; IN_ELIM_THM]);;

(* For a positive base, x rpow a = exp(a * log x).                           *)

let SMOOTH_MAP_ON_LIFT_RPOW = prove
 (`!s (f:real^M->real^1) a.
     open s /\ smooth_map_on s f /\ (!x. x IN s ==> &0 < drop(f x))
     ==> smooth_map_on s (\x. lift(drop(f x) rpow a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on s (\x:real^M. lift(log(drop((f:real^M->real^1) x))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_LOG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s (\x:real^M. lift(a * log(drop((f:real^M->real^1) x))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `a:real`;
                   `\x:real^M. lift(log(drop((f:real^M->real^1) x)))`]
      SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s
      (\x:real^M. lift(exp(a * log(drop((f:real^M->real^1) x)))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`;
                   `\x:real^M. lift(a * log(drop((f:real^M->real^1) x)))`]
      SMOOTH_MAP_ON_LIFT_EXP) THEN
    ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\x:real^M. lift(exp(a * log(drop((f:real^M->real^1) x))))` THEN
  ASM_SIMP_TAC[rpow]);;

let SMOOTH_MAP_ON_LIFT_SQRT = prove
 (`!s (f:real^M->real^1).
     open s /\ smooth_map_on s f /\ (!x. x IN s ==> &0 < drop(f x))
     ==> smooth_map_on s (\x. lift(sqrt(drop(f x))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\x:real^M. lift(drop((f:real^M->real^1) x) rpow (&1 / &2))` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_RPOW; RPOW_SQRT; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* One-variable forms of rpow and sqrt on the open positive half-line.       *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_MAP_ON_RPOW_1D = prove
 (`!a. smooth_map_on {x:real^1 | &0 < drop x} (lift o (\x. x rpow a) o drop)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`{x:real^1 | &0 < drop x}`; `\x:real^1. x`; `a:real`]
    SMOOTH_MAP_ON_LIFT_RPOW) THEN
  REWRITE_TAC[OPEN_DROP_POSITIVE; SMOOTH_MAP_ON_ID; IN_ELIM_THM; o_DEF]);;

let SMOOTH_MAP_ON_SQRT_1D = prove
 (`smooth_map_on {x:real^1 | &0 < drop x} (lift o sqrt o drop)`,
  MP_TAC(ISPECL [`{x:real^1 | &0 < drop x}`; `\x:real^1. x`]
    SMOOTH_MAP_ON_LIFT_SQRT) THEN
  REWRITE_TAC[OPEN_DROP_POSITIVE; SMOOTH_MAP_ON_ID; IN_ELIM_THM; o_DEF]);;

(* ------------------------------------------------------------------------- *)
(* The Euclidean norm is smooth away from the origin.                        *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_MAP_ON_LIFT_NORM = prove
 (`!s (f:real^M->real^N).
     open s /\ smooth_map_on s f /\ (!x. x IN s ==> ~(f x = vec 0))
     ==> smooth_map_on s (\x. lift(norm(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`;
                 `\x:real^M. lift(norm((f:real^M->real^N) x) pow 2)`]
    SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN; LIFT_DROP; REAL_POW_LT;
               NORM_POS_LT; POW_2_SQRT; NORM_POS_LE]);;

