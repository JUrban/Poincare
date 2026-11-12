(* ========================================================================= *)
(* pc_p2a_frv: FL5 P2A_FLOW_RV (MT Thm 7.26, the reduced volume of a         *)
(* complete flow of bounded curvature) at N = 3.  Gaussian integrals         *)
(* without Multivariate/gamma.ml, the weighted area formula on manifolds     *)
(* (adapted from pc_grg_area) and for the L-exponential map, initial vectors *)
(* of minimizers, the bounds at a fixed time, positivity and monotonicity,   *)
(* the lower bound at small times and the assembly.  The main theorem is an  *)
(* implication from the statement constants FL2 and W3; pc_p2a_flfin and     *)
(* pc_p2a_flw3 discharge these.                                              *)
(* ========================================================================= *)

needs "src/pc_p2a_flow2.ml";;
needs "src/pc_p2a_t81u.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Gaussian integrals without Multivariate/gamma.ml.  The half line         *)
(* integral of r exp(-r^2) (monotone convergence over [0,k]), the plane     *)
(* Gaussian by polar coordinates (FUBINI_POLAR), the line Gaussian by       *)
(* Fubini on the plane, and the space Gaussian pi^(3/2).                    *)
(* ------------------------------------------------------------------------- *)

let P2AU_XEXP_INTERVAL = prove
 (`!c. &0 <= c
       ==> ((\r. r * exp(--(r pow 2))) has_real_integral
            (inv(&2) - exp(--(c pow 2)) / &2)) (real_interval[&0,c])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. --(inv(&2) * exp(--(r pow 2)))`; `\r. r * exp(--(r pow 2))`;
                 `&0`; `c:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ARITH `&0 pow 2 = &0`; REAL_NEG_0; REAL_EXP_0] THEN
  REAL_ARITH_TAC);;

(* exp(-k^2) tends to 0.                                                      *)

let P2AU_EXP_NEG_SQ_LIM = prove
 (`((\k. exp(--(&k pow 2))) ---> &0) sequentially`,
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN EXISTS_TAC `\k. inv(&k)` THEN
  REWRITE_TAC[REALLIM_1_OVER_N; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG; REAL_ABS_INV; REAL_ABS_EXP] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&k pow 2` REAL_EXP_LE_X) THEN
  SUBGOAL_THEN `&k <= &k pow 2` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* The half-line integral of r exp(-r^2) is 1/2.                             *)

let P2AU_XEXP_HALFLINE = prove
 (`((\r. r * exp(--(r pow 2))) has_real_integral inv(&2)) {r | &0 <= r}`,
  ABBREV_TAC `f = \k r. if r IN real_interval[&0,&k] then r * exp(--(r pow 2)) else &0` THEN
  SUBGOAL_THEN `!k. ((f:num->real->real) k has_real_integral
                     (inv(&2) - exp(--(&k pow 2)) / &2)) {r | &0 <= r}`
  (LABEL_TAC "FK") THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN
    SUBGOAL_THEN `real_interval[&0,&k] SUBSET {r | &0 <= r}` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT] THEN
    MATCH_MP_TAC P2AU_XEXP_INTERVAL THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->real->real`; `\r. r * exp(--(r pow 2))`; `{r | &0 <= r}`]
                REAL_MONOTONE_CONVERGENCE_INCREASING) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[real_integrable_on] THEN
      EXISTS_TAC `inv(&2) - exp(--(&k pow 2)) / &2` THEN
      USE_THEN "FK" (ACCEPT_TAC o SPEC `k:num`);
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[IN_REAL_INTERVAL; GSYM REAL_OF_NUM_SUC] THEN
      SUBGOAL_THEN `&0 <= x * exp(--(x pow 2))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC REALLIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      SUBGOAL_THEN `x <= &k` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN EXISTS_TAC `inv(&2)` THEN
      X_GEN_TAC `k:num` THEN
      USE_THEN "FK" (SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE o SPEC `k:num`) THEN
      MP_TAC(SPEC `--(&k pow 2)` REAL_EXP_POS_LT) THEN
      SUBGOAL_THEN `exp(--(&k pow 2)) <= &1` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE; REAL_NEG_LE0; REAL_LE_POW_2];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `!k. real_integral {r | &0 <= r} ((f:num->real->real) k) =
                    inv(&2) - exp(--(&k pow 2)) / &2` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    USE_THEN "FK" (ACCEPT_TAC o SPEC `k:num`);
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `((\k. inv(&2) - exp(--(&k pow 2)) / &2) ---> inv(&2)) sequentially`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((\k. inv(&2) - exp(--(&k pow 2)) / &2) ---> inv(&2) - &0 / &2)
                  sequentially` MP_TAC THENL
     [MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
      MATCH_MP_TAC REALLIM_DIV THEN REWRITE_TAC[REALLIM_CONST; P2AU_EXP_NEG_SQ_LIM] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `inv(&2) - &0 / &2 = inv(&2)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral {r | &0 <= r} (\r. r * exp(--(r pow 2))) = inv(&2)`
  (fun th -> SUBST1_TAC(SYM th) THEN ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\k. inv(&2) - exp(--(&k pow 2)) / &2` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]);;

(* The same in real^1 form, times 2 pi.                                       *)

let P2AU_XEXP_HALFLINE_VEC = prove
 (`((\r:real^1. lift(&2 * pi * drop r * exp(--(drop r pow 2)))) has_integral lift pi)
   {r | &0 <= drop r}`,
  SUBGOAL_THEN `IMAGE lift {r | &0 <= r} = {r:real^1 | &0 <= drop r}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE_LIFT_DROP; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[has_real_integral] P2AU_XEXP_HALFLINE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * pi` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[o_DEF; GSYM LIFT_CMUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    AP_TERM_TAC THEN CONV_TAC REAL_FIELD]);;

(* Continuity of the standard Gaussian (as P2A_T81_GAUSS_CONT, pc_p2a_t81). *)

let P2AU_GAUSS_CONT = prove
 (`!s. (\Z:real^N. lift(exp(--(Z dot Z)))) continuous_on s`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `Z0:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\Z:real^N. lift(exp(--(Z dot Z)))) =
                (lift o exp o drop) o (\Z. --(lift(Z dot Z)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_NEG; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_NEG THEN MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN
    REWRITE_TAC[CONTINUOUS_AT_ID];
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL; REAL_CONTINUOUS_AT_EXP]]);;

(* The plane Gaussian: integral pi, by polar coordinates.                    *)

let P2AU_GAUSS_PLANE = prove
 (`(\z:real^2. lift(exp(--(z dot z)))) absolutely_integrable_on (:real^2) /\
   integral (:real^2) (\z:real^2. lift(exp(--(z dot z)))) = lift pi`,
  SUBGOAL_THEN
   `!r t. drop r % lift(exp(--((Cx(drop r) * cexp(ii * Cx(drop t))) dot
                                (Cx(drop r) * cexp(ii * Cx(drop t)))))) =
          lift(drop r * exp(--(drop r pow 2)))`
  (LABEL_TAC "POL") THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[DOT_SQUARE_NORM; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_CEXP_II;
                REAL_MUL_RID; REAL_POW2_ABS; GSYM LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. integral (interval[vec 0,lift(&2 * pi)])
          (\t. drop r % lift(exp(--((Cx(drop r) * cexp(ii * Cx(drop t))) dot
                                     (Cx(drop r) * cexp(ii * Cx(drop t))))))) =
        lift(&2 * pi * drop r * exp(--(drop r pow 2)))`
  (LABEL_TAC "INN") THENL
   [GEN_TAC THEN USE_THEN "POL" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INTEGRAL_CONST] THEN
    SUBGOAL_THEN `drop(vec 0:real^1) <= drop(lift(&2 * pi))` ASSUME_TAC THENL
     [REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CONTENT_1; DROP_VEC; LIFT_DROP; GSYM LIFT_CMUL] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^2. lift(exp(--(z dot z)))) absolutely_integrable_on (:real^2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `\z:real^2. lift(exp(--(z dot z)))` FUBINI_TONELLI_POLAR) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN REWRITE_TAC[P2AU_GAUSS_CONT]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "POL" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_CONST; EMPTY_GSPEC; NEGLIGIBLE_EMPTY] THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_EXP] THEN
    USE_THEN "INN" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[integrable_on] THEN EXISTS_TAC `lift pi` THEN
    REWRITE_TAC[P2AU_XEXP_HALFLINE_VEC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_POLAR) THEN
  DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
  USE_THEN "INN" (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN REWRITE_TAC[P2AU_XEXP_HALFLINE_VEC]);;

(* Transfer of the Gaussian between real^M and real^N of equal dimension     *)
(* (HAS_INTEGRAL_TWIZZLE_EQ with the identity permutation).                  *)

let P2AU_GAUSS_TWIZZLE = prove
 (`!y. dimindex(:M) = dimindex(:N)
       ==> (((\Z:real^N. lift(exp(--(Z dot Z)))) has_integral y) (:real^N) <=>
            ((\Z:real^M. lift(exp(--(Z dot Z)))) has_integral y) (:real^M)) /\
           ((\Z:real^N. lift(exp(--(Z dot Z)))) absolutely_integrable_on (:real^N) <=>
            (\Z:real^M. lift(exp(--(Z dot Z)))) absolutely_integrable_on (:real^M))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (\x:real^M. (lambda i. x$i):real^N) (:real^M) = (:real^N)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `z:real^N` THEN
    EXISTS_TAC `(lambda i. (z:real^N)$i):real^M` THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `1 <= i /\ i <= dimindex(:M)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[LAMBDA_BETA]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^M. ((lambda i. x$i):real^N) dot (lambda i. x$i) = x dot x`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[dot] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && p2au_mentions "dimindex" th
                          then SUBST1_TAC th else NO_TAC) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= i /\ i <= dimindex(:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[LAMBDA_BETA]];
    ALL_TAC] THEN
  (* rewriting with assumptions that contain type variables fails here, so *)
  (* the assumptions are used through SUBST1_TAC and EQT_INTRO            *)
  MP_TAC(ISPECL [`\Z:real^N. lift(exp(--(Z dot Z)))`; `(:real^M)`; `y:real^1`; `I:num->num`]
                HAS_INTEGRAL_TWIZZLE_EQ) THEN
  MP_TAC(ISPECL [`\Z:real^N. lift(exp(--(Z dot Z)))`; `(:real^M)`; `I:num->num`]
                ABSOLUTELY_INTEGRABLE_TWIZZLE_EQ) THEN
  REWRITE_TAC[PERMUTES_I; I_THM] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && p2au_mentions "dimindex" th
                        then REWRITE_TAC[EQT_INTRO th] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && p2au_mentions "IMAGE" th
                        then SUBST1_TAC th else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) then REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN REWRITE_TAC[]);;

(* The Gaussian on a product splits: slices exp(-x.x) times the factor.     *)

let P2AU_GAUSS_PASTECART = prove
 (`!(x:real^M) (y:real^N).
     lift(exp(--(pastecart x y dot pastecart x y))) =
     exp(--(x dot x)) % lift(exp(--(y dot y)))`,
  REWRITE_TAC[DOT_PASTECART; REAL_NEG_ADD; REAL_EXP_ADD; GSYM LIFT_CMUL]);;

let P2AU_GAUSS_PRODUCT = prove
 (`!a b. (\x:real^M. lift(exp(--(x dot x)))) absolutely_integrable_on (:real^M) /\
         ((\x:real^M. lift(exp(--(x dot x)))) has_integral lift a) (:real^M) /\
         (\y:real^N. lift(exp(--(y dot y)))) absolutely_integrable_on (:real^N) /\
         ((\y:real^N. lift(exp(--(y dot y)))) has_integral lift b) (:real^N)
         ==> (\w:real^(M,N)finite_sum. lift(exp(--(w dot w))))
               absolutely_integrable_on (:real^(M,N)finite_sum) /\
             ((\w:real^(M,N)finite_sum. lift(exp(--(w dot w)))) has_integral lift(a * b))
               (:real^(M,N)finite_sum)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^M. integral (:real^N)
                 (\y. lift(exp(--(pastecart x y dot pastecart x y)))) =
               b % lift(exp(--(x dot x)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[P2AU_GAUSS_PASTECART] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE o check (fun th ->
      p2au_mentions "has_integral" th && can (find_term (fun t -> t = `b:real`)) (concl th))) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\w:real^(M,N)finite_sum. lift(exp(--(w dot w))))
                  absolutely_integrable_on (:real^(M,N)finite_sum)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `\w:real^(M,N)finite_sum. lift(exp(--(w dot w)))` FUBINI_TONELLI) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN REWRITE_TAC[P2AU_GAUSS_CONT];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_EXP] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[P2AU_GAUSS_PASTECART] THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_CMUL; EMPTY_GSPEC; NEGLIGIBLE_EMPTY];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lift(a * b) = b % lift a` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `integral (:real^(M,N)finite_sum) (\w. lift(exp(--(w dot w)))) = b % lift a`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_UNIQUE THEN
    EXISTS_TAC `\x:real^M. b % lift(exp(--(x dot x)))` THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let P2AU_GAUSS_PLANE_HAS = prove
 (`((\z:real^2. lift(exp(--(z dot z)))) has_integral lift pi) (:real^2)`,
  MP_TAC P2AU_GAUSS_PLANE THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

(* The line Gaussian: integrable (its slices of the plane Gaussian are     *)
(* integrable almost everywhere) with integral sqrt(pi) (the product of two *)
(* copies is the plane Gaussian).                                           *)

let P2AU_GAUSS_LINE = prove
 (`(\x:real^1. lift(exp(--(x dot x)))) absolutely_integrable_on (:real^1) /\
   ((\x:real^1. lift(exp(--(x dot x)))) has_integral lift(sqrt pi)) (:real^1)`,
  MP_TAC(SPEC `lift pi` (INST_TYPE [`:(1,1)finite_sum`,`:M`; `:2`,`:N`] P2AU_GAUSS_TWIZZLE)) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2; ARITH; P2AU_GAUSS_PLANE_HAS;
              CONJUNCT1 P2AU_GAUSS_PLANE] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^1. lift(exp(--(x dot x)))) absolutely_integrable_on (:real^1)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE o check (fun th ->
      p2au_mentions "absolutely_integrable_on" th)) THEN
    REWRITE_TAC[P2AU_GAUSS_PASTECART] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[NOT_NEGLIGIBLE_UNIV]
      `negligible s ==> ~(s = (:real^1))`)) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV; NOT_FORALL_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^1`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `exp((x:real^1) dot x)` o MATCH_MP ABSOLUTELY_INTEGRABLE_CMUL) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0;
                VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = drop(integral (:real^1) (\x:real^1. lift(exp(--(x dot x)))))` THEN
  SUBGOAL_THEN `((\x:real^1. lift(exp(--(x dot x)))) has_integral lift c) (:real^1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[LIFT_DROP; GSYM HAS_INTEGRAL_INTEGRAL] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `c:real`] (INST_TYPE [`:1`,`:M`; `:1`,`:N`] P2AU_GAUSS_PRODUCT)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c * c = pi` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LIFT_EQ] THEN
    MATCH_MP_TAC(ISPEC `\w:real^(1,1)finite_sum. lift(exp(--(w dot w)))`
                       HAS_INTEGRAL_UNIQUE) THEN
    EXISTS_TAC `(:real^(1,1)finite_sum)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt pi = c` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SQRT_UNIQUE THEN ASM_REWRITE_TAC[REAL_POW_2]);;

(* The space Gaussian: integral pi^(3/2) = pi sqrt(pi).                      *)

let P2AU_GAUSS_SPACE = prove
 (`(\x:real^3. lift(exp(--(x dot x)))) absolutely_integrable_on (:real^3) /\
   ((\x:real^3. lift(exp(--(x dot x)))) has_integral lift(pi * sqrt pi)) (:real^3)`,
  MP_TAC(SPECL [`sqrt pi`; `pi`] (INST_TYPE [`:1`,`:M`; `:2`,`:N`] P2AU_GAUSS_PRODUCT)) THEN
  REWRITE_TAC[P2AU_GAUSS_LINE; P2AU_GAUSS_PLANE_HAS; CONJUNCT1 P2AU_GAUSS_PLANE] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `lift(pi * sqrt pi)` (INST_TYPE [`:(1,2)finite_sum`,`:M`; `:3`,`:N`]
    P2AU_GAUSS_TWIZZLE)) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The weighted area formula on manifolds: for a continuous weight hh >= 0   *)
(* on M, hh is integrable over Fm(S) with integral at most the integral over *)
(* S of |det Fm'| dens hh(Fm), with equality for injective Fm.  Adapted      *)
(* with the same proof from GRGA_AREA_PIECE and GRGA_AREA_FORMULA            *)
(* (pc_grg_area; the volume case hh = 1), the weight entering through        *)
(* GRGA_WEIGHTED_AREA_LE and HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES.      *)
(* Generic in N.                                                             *)
(* ------------------------------------------------------------------------- *)

(* The weight in a chart is continuous on the chart image.                   *)

let P2AU_WEIGHT_CHART_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N) (V:A->bool) (psi:A->real^N) hh.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ (V,psi) IN atlas /\
     continuous_map (top,euclideanreal) hh
     ==> (\y. lift(hh(chart_inv (V,psi) y) * mfd_density atlas (V,psi) g y))
         continuous_on IMAGE psi V`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\y:real^N. (hh:A->real)(chart_inv (V:A->bool,psi:A->real^N) y)) =
                  hh o chart_inv (V,psi)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN; GSYM CONTINUOUS_MAP_EQ_LIFT] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_CHART_INV_CONTINUOUS THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `(V:A->bool,psi:A->real^N)`] GRGV_DENSITY_CONTINUOUS) THEN
    ASM_REWRITE_TAC[FST; SND]]);;

(* The chart piece (GRGA_AREA_PIECE with the weight).                        *)

let P2AU_WAREA_PIECE = prove
 (`!top atlas (g:A->real^N^N) (Fm:real^N->A) Fm' S P (V:A->bool) (psi:A->real^N) hh.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\
       IMAGE Fm S SUBSET topspace top /\
       continuous_map (subtopology euclidean S,top) Fm /\
       (!Z. Z IN S
            ==> ((\W. SND(chart_at atlas (Fm Z)) (Fm W)) has_derivative Fm' Z)
                (at Z within S)) /\
       continuous_map (top,euclideanreal) hh /\ (!q. q IN topspace top ==> &0 <= hh q) /\
       (\Z. lift(abs(det(matrix(Fm' Z))) *
                 mfd_density atlas (chart_at atlas (Fm Z)) g
                             (SND(chart_at atlas (Fm Z)) (Fm Z)) * hh(Fm Z)))
       absolutely_integrable_on S /\
       (V,psi) IN atlas /\ P SUBSET S /\ lebesgue_measurable P /\ IMAGE Fm P SUBSET V
       ==> lebesgue_measurable (IMAGE psi (IMAGE Fm P)) /\
           (\y. lift(hh(chart_inv (V,psi) y) * mfd_density atlas (V,psi) g y))
           absolutely_integrable_on IMAGE psi (IMAGE Fm P) /\
           drop(integral (IMAGE psi (IMAGE Fm P))
                  (\y. lift(hh(chart_inv (V,psi) y) * mfd_density atlas (V,psi) g y))) <=
           drop(integral P
                 (\Z. lift(abs(det(matrix(Fm' Z))) *
                           mfd_density atlas (chart_at atlas (Fm Z)) g
                                       (SND(chart_at atlas (Fm Z)) (Fm Z)) * hh(Fm Z)))) /\
           ((!Z Z'. Z IN S /\ Z' IN S /\ Fm Z = Fm Z' ==> Z = Z')
            ==> drop(integral (IMAGE psi (IMAGE Fm P))
                       (\y. lift(hh(chart_inv (V,psi) y) * mfd_density atlas (V,psi) g y))) =
                drop(integral P
                      (\Z. lift(abs(det(matrix(Fm' Z))) *
                                mfd_density atlas (chart_at atlas (Fm Z)) g
                                            (SND(chart_at atlas (Fm Z)) (Fm Z)) *
                                hh(Fm Z)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (psi:A->real^N) (IMAGE (Fm:real^N->A) P) = IMAGE (\W.
      (psi:A->real^N)((Fm:real^N->A) W)) P`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. Z IN P
        ==> chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z) IN atlas /\
            Fm Z IN FST(chart_at atlas (Fm Z)) /\ Fm Z IN V /\ Z IN S`
  (LABEL_TAC "CZ") THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(Fm:real^N->A) Z`] CHART_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. Z IN P ==> ((\W. (psi:A->real^N)((Fm:real^N->A) W)) has_derivative (chart_jac
       (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))
       (V:A->bool,psi:A->real^N) (Fm Z) o (Fm':real^N->real^N->real^N) Z)) (at Z within P)`
  (LABEL_TAC "DK") THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    USE_THEN "CZ" (MP_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN P`)) THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN EXISTS_TAC `S:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Fm:real^N->A`;
      `(Fm':real^N->real^N->real^N) Z`; `S:real^N->bool`;
      `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))`;
      `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))`;
      `V:A->bool`; `psi:A->real^N`; `Z:real^N`] GRGA_CHART_COMPOSITE_DERIV) THEN
    REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. Z IN P ==> chart_inv (V:A->bool,psi:A->real^N) (psi((Fm:real^N->A) Z)) = Fm Z`
  (LABEL_TAC "CI") THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    USE_THEN "CZ" (MP_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN P`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(V:A->bool),(psi:A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. Z IN P
        ==> abs(det(matrix(chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
            ((Fm:real^N->A) Z)) (V:A->bool,psi:A->real^N) (Fm Z) o
            (Fm':real^N->real^N->real^N) Z))) *
            ((hh:A->real)(chart_inv (V,psi) (psi(Fm Z))) *
             mfd_density atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N) (psi(Fm Z))) =
            abs(det(matrix(Fm' Z))) *
            mfd_density atlas (chart_at atlas (Fm Z)) g (SND(chart_at atlas (Fm Z)) (Fm Z)) *
            hh(Fm Z)`
  (LABEL_TAC "IE") THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    USE_THEN "CZ" (MP_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN P`)) THEN STRIP_TAC THEN
    USE_THEN "CI" (SUBST1_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN P`)) THEN
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))`;
      `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))`;
      `V:A->bool`; `psi:A->real^N`; `(Fm:real^N->A) Z`;
      `(Fm':real^N->real^N->real^N) Z`] GRGA_DENSITY_JAC) THEN
    REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      MATCH_MP_TAC LRG_HAS_DERIVATIVE_IMP_LINEAR THEN
      MAP_EVERY EXISTS_TAC
       [`\W. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z))
                (Fm W)`;
        `at (Z:real^N) within S`] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_ACCEPT_TAC(REAL_RING
      `!a b d e h:real. a * d = b * e ==> a * (h * d) = b * e * h`);
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) *
      mfd_density atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N)
                  (SND(chart_at atlas (Fm Z)) (Fm Z)) * (hh:A->real)(Fm Z)))
      absolutely_integrable_on P` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable (IMAGE (\W. (psi:A->real^N)((Fm:real^N->A) W)) P)`
      ASSUME_TAC THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE THEN
    ASM_REWRITE_TAC[LE_REFL; differentiable_on] THEN
    X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A)
        Z)) (V:A->bool,psi:A->real^N) (Fm Z) o (Fm':real^N->real^N->real^N) Z` THEN
        USE_THEN "DK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(\W. (psi:A->real^N)((Fm:real^N->A) W))`; `(\Z. chart_jac (chart_at
       (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z)) (V:A->bool,psi:A->real^N)
       (Fm Z) o (Fm':real^N->real^N->real^N) Z)`; `P:real^N->bool`;
    `\y. (hh:A->real)(chart_inv (V:A->bool,psi:A->real^N) y) *
         mfd_density atlas (V,psi) (g:A->real^N^N) y`]
   GRGA_WEIGHTED_AREA_LE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "DK" ACCEPT_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2AU_WEIGHT_CHART_CONTINUOUS THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
      USE_THEN "CI" (SUBST1_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN P`)) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                       `(V:A->bool,psi:A->real^N)`; `(psi:A->real^N)((Fm:real^N->A) Z)`]
                      GRGV_DENSITY_POS) THEN
        REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN EXISTS_TAC `(\Z.
          lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas
          (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z))
          (Fm Z)) * (hh:A->real)(Fm Z)))` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral P (\x. lift(abs(det(matrix(chart_jac (chart_at atlas ((Fm:real^N->A) x))
                                    (V:A->bool,psi:A->real^N) (Fm x) o
                                  (Fm':real^N->real^N->real^N) x))) *
                         ((hh:A->real)(chart_inv (V,psi) (psi(Fm x))) *
                          mfd_density atlas (V,psi) (g:A->real^N^N) (psi(Fm x))))) =
    integral P (\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density
        atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm
        Z)) (Fm Z)) * hh(Fm Z)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`(\y. lift((hh:A->real)(chart_inv (V:A->bool,psi:A->real^N) y) *
                             mfd_density atlas (V,psi) (g:A->real^N^N) y))`;
                 `(\W. (psi:A->real^N)((Fm:real^N->A) W))`; `(\Z. chart_jac (chart_at
      (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) Z)) (V:A->bool,psi:A->real^N)
      (Fm Z) o (Fm':real^N->real^N->real^N) Z)`; `P:real^N->bool`; `integral P (\Z.
      lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas (chart_at
      atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z)) (Fm Z)) *
      (hh:A->real)(Fm Z)))`]
                HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "DK" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && p2au_mentions "IN" th &&
        can (find_term (fun t -> t = `S:real^N->bool`)) (concl th) &&
        not (p2au_mentions "has_derivative" th))) THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM SET_TAC[];
        MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                              `V:A->bool`; `psi:A->real^N`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [MP_TAC(ISPECL
     [`\x. abs(det(matrix(chart_jac (chart_at atlas ((Fm:real^N->A) x))
                                    (V:A->bool,psi:A->real^N) (Fm x) o
                          (Fm':real^N->real^N->real^N) x))) %
           lift((hh:A->real)(chart_inv (V,psi) (psi(Fm x))) *
                mfd_density atlas (V,psi) (g:A->real^N^N) (psi(Fm x)))`;
      `(\Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) * mfd_density atlas
          (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N) (SND(chart_at atlas (Fm Z))
          (Fm Z)) * (hh:A->real)(Fm Z)))`; `P:real^N->bool`] GRGV_AI_EQ) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM LIFT_CMUL] THEN
      AP_TERM_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* The chart integrand as a function.                                        *)

let P2AU_CHART_INTEGRAND_FUN = prove
 (`!atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N)).
     mfd_chart_integrand atlas g f c =
     (\y. lift(f(chart_inv c y) * mfd_density atlas c g y))`,
  REWRITE_TAC[FUN_EQ_THM; mfd_chart_integrand]);;

(* The weighted area formula (GRGA_AREA_FORMULA with the weight).           *)

let P2AU_MFD_WEIGHTED_AREA = prove
 (`!top atlas g (Fm:real^N->A) Fm' S hh.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\
       lebesgue_measurable S /\ IMAGE Fm S SUBSET topspace top /\
       continuous_map (subtopology euclidean S,top) Fm /\
       (!Z. Z IN S
            ==> ((\W. SND(chart_at atlas (Fm Z)) (Fm W)) has_derivative Fm' Z)
                (at Z within S)) /\
       continuous_map (top,euclideanreal) hh /\ (!q. q IN topspace top ==> &0 <= hh q) /\
       (\Z. lift(abs(det(matrix(Fm' Z))) *
                 mfd_density atlas (chart_at atlas (Fm Z)) g
                             (SND(chart_at atlas (Fm Z)) (Fm Z)) * hh(Fm Z)))
       integrable_on S
       ==> ?v. mfd_has_integral (top,atlas) g hh (IMAGE Fm S) v /\
               v <= drop(integral S
                      (\Z. lift(abs(det(matrix(Fm' Z))) *
                                mfd_density atlas (chart_at atlas (Fm Z)) g
                                            (SND(chart_at atlas (Fm Z)) (Fm Z)) *
                                hh(Fm Z)))) /\
               ((!Z Z'. Z IN S /\ Z' IN S /\ Fm Z = Fm Z' ==> Z = Z')
                ==> v = drop(integral S
                           (\Z. lift(abs(det(matrix(Fm' Z))) *
                                     mfd_density atlas (chart_at atlas (Fm Z)) g
                                                 (SND(chart_at atlas (Fm Z)) (Fm Z)) *
                                     hh(Fm Z)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `src = \Z. lift(abs(det(matrix((Fm':real^N->real^N->real^N) Z))) *
                 mfd_density atlas (chart_at atlas ((Fm:real^N->A) Z)) (g:A->real^N^N)
                             (SND(chart_at atlas (Fm Z)) (Fm Z)) * (hh:A->real)(Fm Z))` THEN
  SUBGOAL_THEN
   `!Z. Z IN S ==> &0 <= drop((src:real^N->real^1) Z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "src" THEN
    REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(Fm:real^N->A) Z`] CHART_AT) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(src:real^N->real^1) absolutely_integrable_on S` ASSUME_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[DIMINDEX_1] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM drop];
    ALL_TAC] THEN
  ASM_CASES_TAC `S:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; INTEGRAL_EMPTY; DROP_VEC] THEN
    EXISTS_TAC `&0` THEN REWRITE_TAC[MFD_HAS_INTEGRAL_EMPTY; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Fm:real^N->A`; `S:real^N->bool`] GRGA_CHART_COVER_SEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->(A->bool)#(A->real^N)` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `P = \k. {Z | Z IN S /\
                 (Fm:real^N->A) Z IN FST((d:num->(A->bool)#(A->real^N)) k) /\
                 !j. j < k ==> ~(Fm Z IN FST(d j))}` THEN
  SUBGOAL_THEN
   `!k Z. Z IN (P:num->real^N->bool) k <=>
          Z IN S /\ (Fm:real^N->A) Z IN FST((d:num->(A->bool)#(A->real^N)) k) /\
          !j. j < k ==> ~(Fm Z IN FST(d j))`
  ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `Fm:real^N->A`;
                 `\k. FST((d:num->(A->bool)#(A->real^N)) k)`; `P:num->real^N->bool`]
                GRGA_FIRST_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. lebesgue_measurable ((P:num->real^N->bool) k)` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN
     `!j. lebesgue_measurable
            {Z | Z IN S /\
                 (Fm:real^N->A) Z IN FST((d:num->(A->bool)#(A->real^N)) j)}`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN_IN THEN
      EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `continuous_map (subtopology euclidean S,top) (Fm:real^N->A)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST((d:num->(A->bool)#(A->real^N)) j)`;
                     `SND((d:num->(A->bool)#(A->real^N)) j)`]
                    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(P:num->real^N->bool) k =
      {Z | Z IN S /\ (Fm:real^N->A) Z IN FST((d:num->(A->bool)#(A->real^N)) k)} DIFF
      UNIONS (IMAGE (\j. {Z | Z IN S /\ Fm Z IN FST(d j)}) {j | j < k})`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  ABBREV_TAC `tgt = \k y. lift((hh:A->real)(chart_inv ((d:num->(A->bool)#(A->real^N)) k) y) *
                               mfd_density atlas (d k) (g:A->real^N^N) y)` THEN
  SUBGOAL_THEN
   `!k. lebesgue_measurable (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
                                   (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k))) /\
        (tgt:num->real^N->real^1) k absolutely_integrable_on
        IMAGE (SND(d k)) (IMAGE Fm (P k)) /\
        drop(integral (IMAGE (SND(d k)) (IMAGE Fm (P k))) (tgt k)) <=
        drop(integral (P k) (src:real^N->real^1)) /\
        ((!Z Z'. Z IN S /\ Z' IN S /\ Fm Z = Fm Z' ==> Z = Z') ==>
         drop(integral (IMAGE (SND(d k)) (IMAGE Fm (P k))) (tgt k)) =
         drop(integral (P k) src))`
  (LABEL_TAC "PC") THENL
   [X_GEN_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["tgt"; "src"] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `Fm:real^N->A`; `Fm':real^N->real^N->real^N`;
                   `S:real^N->bool`; `(P:num->real^N->bool) k`;
                   `FST((d:num->(A->bool)#(A->real^N)) k)`;
                   `SND((d:num->(A->bool)#(A->real^N)) k)`; `hh:A->real`]
                  P2AU_WAREA_PIECE) THEN
    REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. &0 <= drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
                                   (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k)))
                            ((tgt:num->real^N->real^1) k)) /\
        drop(integral (IMAGE (SND(d k)) (IMAGE Fm (P k))) (\y. lift(norm(tgt k y)))) =
        drop(integral (IMAGE (SND(d k)) (IMAGE Fm (P k))) (tgt k))`
  (LABEL_TAC "NN") THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN
     `!y. y IN IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
                     (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k))
          ==> &0 <= drop((tgt:num->real^N->real^1) k y)`
    ASSUME_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
      EXPAND_TAC "tgt" THEN REWRITE_TAC[LIFT_DROP] THEN
      SUBGOAL_THEN `(Z:real^N) IN S /\
                    (Fm:real^N->A) Z IN FST((d:num->(A->bool)#(A->real^N)) k)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `chart_inv ((d:num->(A->bool)#(A->real^N)) k)
                      (SND(d k) ((Fm:real^N->A) Z)) = Fm Z` SUBST1_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `(d:num->(A->bool)#(A->real^N)) k`] MFDM_CHART) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN CONJ_TAC THENL
       [USE_THEN "PC" (MP_TAC o SPEC `k:num`) THEN
        SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
        ASM_REWRITE_TAC[]];
      AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN
      DISCH_TAC THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LIFT_DROP] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. drop(integral ((P:num->real^N->bool) k) (src:real^N->real^1))) real_sums
     drop(integral S src)) (from 0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`src:real^N->real^1`; `P:num->real^N->bool`] GRGV_SUMS_PIECES) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 0) (\k. drop(integral
      (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
             (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k)))
      ((tgt:num->real^N->real^1) k)))` MP_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\k. drop(integral ((P:num->real^N->bool) k) (src:real^N->real^1))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_summable] THEN EXISTS_TAC `drop(integral S (src:real^N->real^1))` THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `0` THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "NN" (MP_TAC o CONJUNCT1 o SPEC `k:num`) THEN
      USE_THEN "PC" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o SPEC `k:num`) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_summable] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_has_integral; P2AU_CHART_INTEGRAND_FUN] THEN
    MAP_EVERY EXISTS_TAC
     [`d:num->(A->bool)#(A->real^N)`;
      `\k. IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k)`] THEN
    SUBGOAL_THEN `!k y. lift((hh:A->real)
                     (chart_inv ((d:num->(A->bool)#(A->real^N)) k) y) *
                     mfd_density atlas (d k) (g:A->real^N^N) y) =
                      (tgt:num->real^N->real^1) k y` (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN EXPAND_TAC "tgt" THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[mfd_chart_partition] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      GEN_TAC THEN USE_THEN "PC" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
      USE_THEN "NN" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC_ALL th)]) THEN
      REWRITE_TAC[real_summable] THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_SERIES_LE THEN
    MAP_EVERY EXISTS_TAC [`\k. drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
        (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k))) ((tgt:num->real^N->real^1) k))`;
        `\k. drop(integral ((P:num->real^N->bool) k) (src:real^N->real^1))`;
        `from 0`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "PC" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`\k. drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k))
        (IMAGE (Fm:real^N->A) ((P:num->real^N->bool) k))) ((tgt:num->real^N->real^1) k))`;
        `from 0`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\k. drop(integral (IMAGE (SND((d:num->(A->bool)#(A->real^N)) k)) (IMAGE
        (Fm:real^N->A) ((P:num->real^N->bool) k))) ((tgt:num->real^N->real^1) k))) =
        (\k. drop(integral (P k) (src:real^N->real^1)))`
        (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
    USE_THEN "PC" (MP_TAC o SPEC `k:num`) THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC(last(CONJUNCTS th))) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The weighted area formula for the L-exponential map at time tt - b (as    *)
(* P2A_T81_AREA_APPLY of pc_p2a_t81, with a weight): int over Lexp(S) of     *)
(* hh <= zdens int_S J hh(Lexp), equality for injective Lexp on S.           *)
(* Generic in N.                                                             *)
(* ------------------------------------------------------------------------- *)

let P2AU_WAREA_LEXP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b S hh.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     lebesgue_measurable S /\ S SUBSET p2a_Ldom V tt x b /\ ~(S = {}) /\
     continuous_map (p2a_vtop V (tt - b),euclideanreal) hh /\
     (!q. q IN topspace(p2a_vtop V (tt - b)) ==> &0 <= hh q) /\
     (\Z. lift(p2a_J V tt x b Z * hh(p2a_Lexp V tt x b Z))) integrable_on S
     ==> ?v. mfd_has_integral (p2a_vtop V (tt - b),p2a_vatlas V (tt - b))
                              (p2a_vmetric V (tt - b)) hh (IMAGE (p2a_Lexp V tt x b) S) v /\
             v <= p2a_zdens V tt x *
                  drop(integral S (\Z. lift(p2a_J V tt x b Z * hh(p2a_Lexp V tt x b Z)))) /\
             ((!Z Z'. Z IN S /\ Z' IN S /\ p2a_Lexp V tt x b Z = p2a_Lexp V tt x b Z'
                      ==> Z = Z')
              ==> v = p2a_zdens V tt x *
                      drop(integral S
                             (\Z. lift(p2a_J V tt x b Z * hh(p2a_Lexp V tt x b Z)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?Z0:real^N. Z0 IN S` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^N. Z IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#
                  (A->real^N))->bool)#(real->A->real^N^N)) tt x b
                  ==> &0 < b /\ p2a_Lexp V tt x b Z IN topspace(p2a_vtop V (tt - b))`
  ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LGEO_PROP) THEN
    REWRITE_TAC[p2a_Lgeod_from; p2a_Lgeod; p2a_Lexp] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#(real->((A->bool)#
                  (A->real^N))->bool)#(real->A->real^N^N)) (tt - b)) (p2a_vatlas V (tt - b)) /\
                riemannian_metric (p2a_vatlas V (tt - b)) (p2a_vmetric V (tt - b))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N))` THEN REWRITE_TAC[p2a_svs] THEN
    DISCH_THEN(MP_TAC o SPEC `tt - b`) THEN
    MATCH_MP_TAC(TAUT `p ==> (q /\ (p ==> r) ==> r)`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b Z0` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\Z:real^N. lift(abs(det(matrix(frechet_derivative
        (\W. SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#
                (A->real^N))->bool)#(real->A->real^N^N)) (tt - b)) (p2a_Lexp V tt x b Z))
                (p2a_Lexp V tt x b W)) (at Z)))) *
        mfd_density (p2a_vatlas V (tt - b))
          (chart_at (p2a_vatlas V (tt - b)) (p2a_Lexp V tt x b Z))
          (p2a_vmetric V (tt - b))
          (SND(chart_at (p2a_vatlas V (tt - b)) (p2a_Lexp V tt x b Z))
              (p2a_Lexp V tt x b Z)) * (hh:A->real)(p2a_Lexp V tt x b Z))) =
    (\Z. p2a_zdens V tt x % lift(p2a_J V tt x b Z * hh(p2a_Lexp V tt x b Z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ] THEN X_GEN_TAC `Z:real^N` THEN
    REWRITE_TAC[p2a_J; GSYM p2a_zdens] THEN
    UNDISCH_TAC `&0 < abs(det(A0:real^N^N))` THEN
    UNDISCH_TAC `p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N)) tt x = abs(det(A0:real^N^N))` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) (tt - b)`;
    `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) (tt - b)`;
    `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N)) (tt - b)`;
    `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) tt x b`;
    `\Z:real^N. frechet_derivative
        (\W. SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#
                (A->real^N))->bool)#(real->A->real^N^N)) (tt - b)) (p2a_Lexp V tt x b Z))
                (p2a_Lexp V tt x b W)) (at Z)`;
    `S:real^N->bool`; `hh:A->real`] P2AU_MFD_WEIGHTED_AREA) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
      REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `O:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
      EXISTS_TAC `{Z | Z IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#
                    (A->real^N))->bool)#(real->A->real^N^N)) tt x b /\
                    p2a_Lexp V tt x b Z IN O}` THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN
      X_GEN_TAC `Z1:real^N` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Z1:real^N`;
                     `O:A->bool`] P2A_T81_LEXP_CONT) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[];
      X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC P2A_LEXP_DIFFERENTIABLE THEN ASM SET_TAC[];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* Initial vectors of minimizers.  Minimality depends only on the curve on  *)
(* [0,b]; Smin(b) is inside Smin(b1) for b1 <= b (restriction of            *)
(* minimizers, P2A_MIN_RESTRICT_GEN, and of L-geodesics,                    *)
(* P2A_LDOM_RESTRICT); on Smin, lx(Lexp Z) = l~(Z) (P2A_MIN_LX) and J(Z)    *)
(* exp(-lx(Lexp Z)) / b^(3/2) = rvi(Z) (P2A_T81_J_RVI).                     *)
(* ------------------------------------------------------------------------- *)

let P2AU_MIN_CONG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) gamma'.
     p2a_min V tt x b gamma /\ (!s. &0 <= s /\ s <= b ==> gamma' s = gamma s)
     ==> p2a_min V tt x b gamma'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_min] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MIN"))
    (LABEL_TAC "EQ")) THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `gamma':real->A`] P2AU_ADM_CONG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `g2:real->A` THEN STRIP_TAC THEN
  USE_THEN "MIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma':real->A) b = gamma b` (fun th -> ASM_REWRITE_TAC[th]) THEN
  USE_THEN "EQ" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2AU_SMIN_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b b1 Z.
     p2a_svs V /\ Z IN p2a_Smin V tt x b /\ &0 < b1 /\ b1 <= b
     ==> Z IN p2a_Smin V tt x b1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Smin; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`; `b:real`;
                 `b1:real`] P2A_LDOM_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AU_MIN_CONG THEN
  EXISTS_TAC `p2a_Lgeo (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) tt x Z b` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MIN_RESTRICT_GEN THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let P2AU_LX_SMIN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b Z.
     Z IN p2a_Smin V tt x b
     ==> p2a_lx V tt x b (p2a_Lexp V tt x b Z) = p2a_ltil V tt x b Z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Smin; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_lx; p2a_ltil; p2a_Ltil; p2a_Lexp] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_MIN_LX) THEN SIMP_TAC[]);;

let P2AU_RVI_WEIGHT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b Z.
     &0 < b /\ Z IN p2a_Smin V tt x b
     ==> p2a_J V tt x b Z *
         (exp(--(p2a_lx V tt x b (p2a_Lexp V tt x b Z))) / sqrt b pow 3) =
         p2a_rvi V tt x b Z`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[P2AU_LX_SMIN; P2A_T81_J_RVI; DIMINDEX_3] THEN
  SUBGOAL_THEN `&0 < sqrt b pow 3` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; SQRT_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `p2a_ltil (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) tt x b Z` REAL_EXP_POS_LT) THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* FL5 at a fixed backward time tau (MT Thm 7.26, first part). Every point  *)
(* of M is Lexp(tau) of an initial vector in Smin(tau) (FL2,                *)
(* P2A_T81_SMIN_OF_MIN); the reduced-volume integrand                       *)
(* h = exp(-l)/tau^(3/2) is continuous (FL3); by the weighted area          *)
(* formula h is integrable over M with integral at most zdens times the     *)
(* integral of rvi over Smin(tau).                                          *)
(* ------------------------------------------------------------------------- *)

(* The flow view at N = 3 (FL0 = P2AW_FLOW_VIEW_3 and the view components).  *)

let P2AU_FLOW_VIEW_FACTS_3 = prove
 (`!top atlas a b (g:real->A->real^3^3).
     p2a_cbflow (top,atlas) a b g
     ==> p2a_svs (p2a_flow_view (top,atlas) (real_interval[a,b]) g) /\
         p2a_atlas_lc (p2a_flow_view (top,atlas) (real_interval[a,b]) g) /\
         (!y. y IN topspace top
              ==> p2a_bsmooth (p2a_flow_view (top,atlas) (real_interval[a,b]) g) y b) /\
         (!t. a <= t /\ t <= b
              ==> p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = top /\
                  p2a_vatlas (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = atlas /\
                  p2a_vmetric (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = g t /\
                  rfs_vtop (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = top)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`(:A)`; `(:3)`] P2AW_FLOW_VIEW_3) THEN
  REWRITE_TAC[P2A_FLOW_VIEW_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `a:real`; `b:real`; `g:real->A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[P2A_ATLAS_LC_FLOW_VIEW] THEN
  REWRITE_TAC[GSYM P2A_VIEW_PROJ_3; P2AU_FLOW_VIEW_PARTS; IN_REAL_INTERVAL] THEN
  SIMP_TAC[]);;

(* The slices of the flow view at times in [a,b].                            *)

let P2AU_FLOW_SLICE_3 = prove
 (`!top atlas a b (g:real->A->real^3^3) t.
     a <= t /\ t <= b
     ==> p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = top /\
         p2a_vatlas (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = atlas /\
         p2a_vmetric (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = g t /\
         rfs_vtop (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = top /\
         rfs_vatlas (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = atlas /\
         rfs_vmetric (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = g t`,
  REWRITE_TAC[GSYM P2A_VIEW_PROJ_3; P2AU_FLOW_VIEW_PARTS; IN_REAL_INTERVAL] THEN SIMP_TAC[]);;

(* exp of a continuous real function is continuous.                          *)

let P2AU_CONT_MAP_EXP = prove
 (`!top (f:A->real).
     continuous_map (top,euclideanreal) f
     ==> continuous_map (top,euclideanreal) (\x. exp(f x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT] THEN
  SUBGOAL_THEN `lift o (\x. exp((f:A->real) x)) = (lift o exp o drop) o (lift o f)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^1)topology` THEN
  ASM_REWRITE_TAC[GSYM CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_UNIV; GSYM REAL_CONTINUOUS_ON; REAL_CONTINUOUS_ON_EXP]);;

(* The reduced-volume integrand is continuous on M (FL3).                    *)

let P2AU_FRV_WEIGHT_CONT = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p tau.
     P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau /\ tau < b - a
     ==> continuous_map (top,euclideanreal)
           (\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                              b p tau q)) / sqrt tau pow 3)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL3") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
  MATCH_MP_TAC P2AU_CONT_MAP_EXP THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN
  MATCH_MP_TAC P2AU_CONT_MAP_REAL THEN
  MAP_EVERY X_GEN_TAC [`q0:A`; `e:real`] THEN STRIP_TAC THEN
  USE_THEN "FL3" (MP_TAC o REWRITE_RULE[P2A_FLOW_LX_CONT_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `tau:real`;
                            `q0:A`; `e:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `O:A->bool` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]);;

(* M is the image of Smin(tau) under Lexp(tau), and Smin(tau) is Lebesgue   *)
(* measurable and nonempty.                                                  *)

let P2AU_SMIN_COVER = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p tau.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau /\ tau < b - a
     ==> IMAGE (p2a_Lexp (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau)
               (p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau) =
         topspace top /\
         lebesgue_measurable
           (p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau) /\
         ~(p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL2") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `a <= b - tau /\ b - tau <= b /\ a <= b /\ b <= b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b - tau`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b) /\ p2a_bsmooth V p b`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!q:A. q IN topspace top
          ==> ?Z. Z IN p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) b p tau /\
                  p2a_Lexp V b p tau Z = q`
  (LABEL_TAC "REP") THENL
   [X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    USE_THEN "FL2" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                   `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `q:A`;
                                   `tau:real`] o REWRITE_RULE[P2A_FLOW_MIN_EXISTS_STATEMENT]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `gamma:real->A`]
                  P2A_T81_SMIN_OF_MIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Z:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. Z IN p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) b p tau
        ==> p2a_Lexp V b p tau Z IN topspace top`
  (LABEL_TAC "TOP") THENL
   [X_GEN_TAC `Z:real^3` THEN REWRITE_TAC[p2a_Smin; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `Z:real^3`]
                  P2A_T81_LEXP_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `q:A` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `Z:real^3` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN USE_THEN "REP" (MP_TAC o SPEC `q:A`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]];
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`;
                   `topspace top:A->bool`] P2A_T81_S_MEASURABLE) THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    USE_THEN "REP" (MP_TAC o SPEC `p:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The reduced volume at a fixed tau is finite with V(tau) <= zdens         *)
(* int_{Smin(tau)} rvi(tau) <= (4 pi)^(3/2): rvi is below the Gaussian 8    *)
(* exp(-Z.GZ) on Smin (P2A_T81_RVI_GAUSS), whose integral is 8              *)
(* pi^(3/2) / zdens (P2A_T81_GAUSS_LINEAR and P2AU_GAUSS_SPACE).            *)
(* ------------------------------------------------------------------------- *)

let P2AU_FRV_UPPER = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p tau.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau /\ tau < b - a
     ==> (\Z. lift(p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau Z))
         absolutely_integrable_on
         p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau /\
         ?v. mfd_has_integral (top,atlas) (g(b - tau))
               (\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                  b p tau q)) / sqrt tau pow 3)
               (topspace top) v /\
             v <= p2a_zdens (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p *
                  drop(integral (p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                          b p tau)
                         (\Z. lift(p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                           b p tau Z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`] P2AU_SMIN_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`] P2AU_FRV_WEIGHT_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  SUBGOAL_THEN `a <= b - tau /\ b - tau <= b /\ a <= b /\ b <= b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  ABBREV_TAC `S = p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b p tau` THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b - tau`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b) /\
                p IN topspace(p2a_vtop V b) /\ p2a_bsmooth V p b`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b p tau Z))
                absolutely_integrable_on S` ASSUME_TAC THENL
   [MP_TAC(SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `tau:real`;
                  `S:real^3->bool`] P2A_T81_RVI_INTEGRABLE) THEN
    REWRITE_TAC[P2A_RVI_MONO; P2AV_RVI_ASYMP; P2AG_GAUSS_TAIL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!Z. Z IN S
        ==> p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b p tau Z *
            (\q. exp(--(p2a_lx V b p tau q)) / sqrt tau pow 3) (p2a_Lexp V b p tau Z) =
            p2a_rvi V b p tau Z`
  (LABEL_TAC "WT") THENL
   [X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AU_RVI_WEIGHT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Z:real^3) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `S:real^3->bool`;
                 `\q:A. exp(--(p2a_lx (V:(real->A topology)#(real->((A->bool)#
                         (A->real^3))->bool)#(real->A->real^3^3)) b p tau q)) /
                        sqrt tau pow 3`] P2AU_WAREA_LEXP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[p2a_Smin; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
      X_GEN_TAC `q:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_EXP_POS_LE; REAL_POW_LE; SQRT_POS_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC INTEGRABLE_EQ THEN
      EXISTS_TAC `\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
                    (A->real^3))->bool)#(real->A->real^3^3)) b p tau Z)` THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN USE_THEN "WT" (MP_TAC o SPEC `Z:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC
    (K ALL_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN EXISTS_TAC `v:real` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `integral S (\Z. lift(p2a_J (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b p tau Z *
                 (\q. exp(--(p2a_lx V b p tau q)) / sqrt tau pow 3) (p2a_Lexp V b p tau Z))) =
    integral S (\Z. lift(p2a_rvi V b p tau Z))`
  (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  USE_THEN "WT" (MP_TAC o SPEC `Z:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

(* The Gaussian bound: zdens int_{Smin} rvi <= 8 pi^(3/2).                   *)

let P2AU_FRV_GAUSS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b.
     p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\ &0 < b /\
     lebesgue_measurable (p2a_Smin V tt x b)
     ==> p2a_zdens V tt x *
         drop(integral (p2a_Smin V tt x b) (\Z. lift(p2a_rvi V tt x b Z))) <=
         &8 * pi * sqrt pi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2A_T81_DENS_X) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[P2A_VIEW_PROJ_3]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^3^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `G8 = \Z:real^3. lift(&8 * exp(--(Z dot ((transp(A0:real^3^3) ** A0) ** Z))))` THEN
  SUBGOAL_THEN `IMAGE (\Z:real^3. (A0:real^3^3) ** Z) (:real^3) = (:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `z:real^3` THEN
    EXISTS_TAC `matrix_inv(A0:real^3^3) ** z` THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\Z:real^3. lift(&8 * exp(--(Z dot Z)))) has_integral
                 lift(&8 * pi * sqrt pi)) (:real^3) /\
                (\Z:real^3. lift(&8 * exp(--(Z dot Z)))) absolutely_integrable_on (:real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `&8` (MATCH_MP HAS_INTEGRAL_CMUL (CONJUNCT2 P2AU_GAUSS_SPACE))) THEN
      REWRITE_TAC[GSYM LIFT_CMUL];
      MP_TAC(SPEC `&8` (MATCH_MP ABSOLUTELY_INTEGRABLE_CMUL (CONJUNCT1 P2AU_GAUSS_SPACE))) THEN
      REWRITE_TAC[GSYM LIFT_CMUL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A0:real^3^3`; `(:real^3)`] P2A_T81_GAUSS_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(det(A0:real^3^3)) * drop(integral (:real^3) (G8:real^3->real^1)) =
                &8 * pi * sqrt pi` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_CMUL] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && p2au_mentions "integral" th && p2au_mentions "det" th)) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE o check (fun th ->
      p2au_mentions "has_integral" th)) THEN
    REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G8:real^3->real^1) absolutely_integrable_on (:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "G8" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) tt x b Z))
                absolutely_integrable_on p2a_Smin V tt x b` ASSUME_TAC THENL
   [MP_TAC(SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `tt:real`; `x:A`; `b:real`; `b:real`;
                  `p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) tt x b`] P2A_T81_RVI_INTEGRABLE) THEN
    REWRITE_TAC[P2A_RVI_MONO; P2AV_RVI_ASYMP; P2AG_GAUSS_TAIL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; SUBSET_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(det(A0:real^3^3)) * drop(integral (:real^3) (G8:real^3->real^1))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (p2a_Smin (V:(real->A topology)#(real->((A->bool)#
                (A->real^3))->bool)#(real->A->real^3^3)) tt x b) (G8:real^3->real^1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "G8" THEN
      REWRITE_TAC[LIFT_DROP] THEN
      SUBGOAL_THEN `Z dot ((transp(A0:real^3^3) ** A0) ** Z) =
                    p2a_znorm2 (V:(real->A topology)#(real->((A->bool)#
                      (A->real^3))->bool)#(real->A->real^3^3)) tt x Z` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[p2a_znorm2]; ALL_TAC] THEN
      MATCH_MP_TAC P2A_T81_RVI_GAUSS THEN EXISTS_TAC `b:real` THEN
      REWRITE_TAC[P2A_RVI_MONO; P2AV_RVI_ASYMP] THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "G8" THEN
      REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Integrals of nonnegative functions over subsets, positivity of the       *)
(* integral of a positive continuous function (the ball of a complete       *)
(* metric has finite positive volume, MFD_HAS_VOLUME_BALL), and the         *)
(* monotonicity of the reduced volume (MT Thm 6.80 in the form of MT p.     *)
(* 165: rvi(tau, Z) is non-increasing in tau on Smin(tau2) (L5) and Lexp at *)
(* the earlier time is injective there (L4)).                               *)
(* ------------------------------------------------------------------------- *)

let P2AU_MFD_INTEGRAL_SUBSET_LE = prove
 (`!top atlas (g:A->real^N^N) f S Tt v w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_has_integral (top,atlas) g f S v /\ mfd_has_integral (top,atlas) g f Tt w /\
     S SUBSET Tt /\ (!x. x IN Tt ==> &0 <= f x)
     ==> v <= w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool)
                  ((Tt:A->bool) DIFF S)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN ASM_MESON_TAC[MFD_HAS_INTEGRAL_IMP_MEASURABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_integrable_on (top,atlas) (g:A->real^N^N) f ((Tt:A->bool) DIFF S)`
  MP_TAC THENL
   [MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN EXISTS_TAC `Tt:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_DIFF; mfd_integrable_on] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `(Tt:A->bool) DIFF S`; `u:real`; `&0`]
                  MFD_HAS_INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_TAC THEN
    MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `\x:A. &0 * f x`; `f:A->real`;
                          `(Tt:A->bool) DIFF S`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `S:A->bool`; `(Tt:A->bool) DIFF S`;
                 `v:real`; `u:real`] MFD_HAS_INTEGRAL_UNION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) UNION (Tt DIFF S) = Tt` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `w = v + u` (fun th -> ASM_REWRITE_TAC[th] THEN ASM_REAL_ARITH_TAC) THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `f:A->real`; `Tt:A->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* A positive continuous function has positive integral over M.             *)

let P2AU_MFD_INTEGRAL_POS = prove
 (`!top atlas (g:A->real^N^N) f p w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p IN topspace top /\
     continuous_map (top,euclideanreal) f /\ (!x. x IN topspace top ==> &0 < f x) /\
     mfd_has_integral (top,atlas) g f (topspace top) w
     ==> &0 < w`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = (f:A->real) p / &2` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_HALF] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `O = {x:A | x IN topspace top /\ (c:real) < (f:A->real) x} INTER
                  mfd_ball (top,atlas) (g:A->real^N^N) p (&1)` THEN
  SUBGOAL_THEN `open_in top (O:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN] THEN
    MP_TAC(ISPECL [`f:A->real`; `top:A topology`; `euclideanreal`;
                   `{x:real | x > c}`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_GT] THEN
    REWRITE_TAC[IN_ELIM_THM; real_gt];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "c" THEN
      SUBGOAL_THEN `&0 < (f:A->real) p` MP_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `&1`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `O:A->bool`;
                 `mfd_ball (top,atlas) (g:A->real^N^N) p (&1)`;
                 `mfd_volume (top,atlas) (g:A->real^N^N)
                    (mfd_ball (top,atlas) g p (&1))`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN] THEN EXPAND_TAC "O" THEN SET_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `vO = mfd_volume (top,atlas) (g:A->real^N^N) O` THEN
  SUBGOAL_THEN `&0 < vO` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_OPEN_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `O:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_integrable_on (top,atlas) (g:A->real^N^N) f O` MP_TAC THENL
   [MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN EXISTS_TAC `topspace top:A->bool` THEN
    ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN; mfd_integrable_on] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `wO:real`) THEN
  SUBGOAL_THEN `(c:real) * vO <= wO` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `\x:A. (c:real)`; `f:A->real`; `O:A->bool`] THEN
    ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CONST] THEN
    EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `wO <= w` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_MFD_INTEGRAL_SUBSET_LE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `f:A->real`; `O:A->bool`;
                          `topspace top:A->bool`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c:real) * vO` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Monotonicity of the reduced volume (tau1 < tau2).                         *)

let P2AU_FRV_MONO = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p tau1 tau2 v1 v2.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau1 /\ tau1 < tau2 /\ tau2 < b - a /\
     mfd_has_integral (top,atlas) (g(b - tau1))
       (\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau1 q)) /
            sqrt tau1 pow 3) (topspace top) v1 /\
     mfd_has_integral (top,atlas) (g(b - tau2))
       (\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau2 q)) /
            sqrt tau2 pow 3) (topspace top) v2
     ==> v2 <= v1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau2:real`] P2AU_FRV_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v2':real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau2:real`] P2AU_SMIN_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau1:real`] P2AU_FRV_WEIGHT_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  SUBGOAL_THEN `a <= b - tau1 /\ b - tau1 <= b /\ a <= b - tau2 /\ b - tau2 <= b /\
                a <= b /\ b <= b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3)(b - tau2))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v2:real = v2'` SUBST1_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_HAS_INTEGRAL_UNIQUE) THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `(g:real->A->real^3^3)(b - tau2)`;
                          `\q:A. exp(--(p2a_lx (p2a_flow_view (top,atlas)
                             (real_interval[a,b]) (g:real->A->real^3^3)) b p tau2 q)) /
                             sqrt tau2 pow 3`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  ABBREV_TAC `S2 = p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b p tau2` THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b - tau1`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b) /\
                p IN topspace(p2a_vtop V b) /\ p2a_bsmooth V p b`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. Z IN S2
        ==> Z IN p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b p tau1 /\
            Z IN p2a_Ldom V b p tau1`
  (LABEL_TAC "S12") THENL
   [X_GEN_TAC `Z:real^3` THEN EXPAND_TAC "S2" THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AU_SMIN_RESTRICT THEN EXISTS_TAC `tau2:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2A_T81_SMIN_LDOM THEN EXISTS_TAC `tau2:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b p tau1 Z))
                absolutely_integrable_on S2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `b:real`; `p:A`; `tau2:real`; `tau1:real`;
                  `S2:real^3->bool`] P2A_T81_RVI_INTEGRABLE) THEN
    REWRITE_TAC[P2A_RVI_MONO; P2AV_RVI_ASYMP; P2AG_GAUSS_TAIL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXPAND_TAC "S2" THEN REWRITE_TAC[SUBSET_REFL]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `p:A`; `tau1:real`; `S2:real^3->bool`;
                 `\q:A. exp(--(p2a_lx (V:(real->A topology)#(real->((A->bool)#
                         (A->real^3))->bool)#(real->A->real^3^3)) b p tau1 q)) /
                        sqrt tau1 pow 3`] P2AU_WAREA_LEXP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      X_GEN_TAC `q:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_EXP_POS_LE; REAL_POW_LE; SQRT_POS_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC INTEGRABLE_EQ THEN
      EXISTS_TAC `\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
                    (A->real^3))->bool)#(real->A->real^3^3)) b p tau1 Z)` THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AU_RVI_WEIGHT THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC))) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`Z:real^3`; `Z':real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `u:A->bool` P2A_INJ_FIX) THEN REWRITE_TAC[P2A_INJ_FIX_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)`; `b:real`; `p:A`; `tau2:real`;
                          `tau1:real`] THEN
    UNDISCH_TAC `(Z:real^3) IN S2` THEN UNDISCH_TAC `(Z':real^3) IN S2` THEN
    EXPAND_TAC "S2" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `integral S2 (\Z. lift(p2a_J (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b p tau1 Z *
                 exp(--(p2a_lx V b p tau1 (p2a_Lexp V b p tau1 Z))) / sqrt tau1 pow 3)) =
    integral S2 (\Z. lift(p2a_rvi V b p tau1 Z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC P2AU_RVI_WEIGHT THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w <= v1` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] P2AU_MFD_INTEGRAL_SUBSET_LE) THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `(g:real->A->real^3^3)(b - tau1)`;
                          `\q:A. exp(--(p2a_lx (V:(real->A topology)#(real->((A->bool)#
                             (A->real^3))->bool)#(real->A->real^3^3)) b p tau1 q)) /
                             sqrt tau1 pow 3`;
                          `IMAGE (p2a_Lexp (V:(real->A topology)#(real->((A->bool)#
                             (A->real^3))->bool)#(real->A->real^3^3)) b p tau1) S2`;
                          `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `b:real`; `p:A`; `tau1:real`; `Z:real^3`]
                    P2A_T81_LEXP_TOPSPACE) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `q:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_EXP_POS_LE; REAL_POW_LE; SQRT_POS_LE; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral S2 (\Z. lift(p2a_rvi (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b p tau2 Z))) <=
    drop(integral S2 (\Z. lift(p2a_rvi V b p tau1 Z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP] THEN
    X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `u:A->bool` P2A_RVI_MONO) THEN REWRITE_TAC[P2A_RVI_MONO_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `tau2:real` THEN
    UNDISCH_TAC `(Z:real^3) IN S2` THEN EXPAND_TAC "S2" THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p2a_zdens (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) b p` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `b:real`; `p:A`] P2A_T81_DENS_X) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p2a_zdens (V:(real->A topology)#(real->((A->bool)#
                (A->real^3))->bool)#(real->A->real^3^3)) b p *
              drop(integral S2 (\Z. lift(p2a_rvi V b p tau2 Z)))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `w:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && p2au_mentions "p2a_zdens" th
                          then SUBST1_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The metric of a complete flow of bounded curvature near (b, z0) in a     *)
(* chart is close to G0 = g(b) at z0 as a quadratic form (the smooth        *)
(* extension clause of p2a_flow_upto and RFA_POSDEF_LOWER), and the density *)
(* is at least (1 - e)^(3/2) times the density at (b, z0)                   *)
(* (GRGA_SQRT_DET_QF_LE).  Generic in N except where stated.                *)
(* ------------------------------------------------------------------------- *)

let P2AU_QF_VEC_BOUND = prove
 (`!(A:real^N^N) v. abs(v dot (A ** v)) <= norm(vectorize A) * norm v pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(v:real^N) * norm((A:real^N^N) ** v)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN REWRITE_TAC[REAL_POW_2] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `a * b * b = b * (a * b)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE; COMPATIBLE_NORM_VECTORIZE]);;

let P2AU_FLOW_METRIC_NEAR = prove
 (`!top atlas a b (g:real->A->real^N^N) c z0 e.
     p2a_cbflow (top,atlas) a b g /\ c IN atlas /\ z0 IN IMAGE (SND c) (FST c) /\ &0 < e
     ==> ?d. &0 < d /\
             !t z v. b - d < t /\ t <= b /\ z IN IMAGE (SND c) (FST c) /\ norm(z - z0) < d
                     ==> abs(v dot (metric_local atlas c (g t) z ** v) -
                             v dot (metric_local atlas c (g b) z0 ** v)) <=
                         e * (v dot (metric_local atlas c (g b) z0 ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) b)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[riemannian_metric; metric_field] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `z0:real^N` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RFA_POSDEF_LOWER) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `p2a_flow_upto (top,atlas) a b (g:real->A->real^N^N)` THEN
  REWRITE_TAC[p2a_flow_upto] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN
    `Fx:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fx:real^(1,N)finite_sum->real^(N,N)finite_prod) continuous
                at (pastecart (lift b) z0)` MP_TAC THENL
   [MP_TAC(ISPECL [`Fx:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `interval(lift a,lift(b + e1)) PCROSS
                    IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`]
                  CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e * m`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d1 / &2) (b - a)` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`; `v:real^N`] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift t) z:real^(1,N)finite_sum`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[dist; PASTECART_SUB] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm(lift t - lift b) + norm(z - z0:real^N)` THEN
    REWRITE_TAC[NORM_PASTECART_LE; GSYM LIFT_SUB; NORM_LIFT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Fx:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) z) =
    vectorize(metric_local atlas c ((g:real->A->real^N^N) t) z) /\
    Fx (pastecart (lift b) z0) = vectorize(metric_local atlas c (g b) z0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[dist; GSYM VECTORIZE_SUB] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize(metric_local atlas c ((g:real->A->real^N^N) t) z -
                             metric_local atlas c (g b) z0)) * norm(v:real^N) pow 2` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`metric_local atlas c ((g:real->A->real^N^N) t) z -
                    metric_local atlas c (g b) z0`; `v:real^N`] P2AU_QF_VEC_BOUND) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(e * m) * norm(v:real^N) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* The chord curve.  For the flow view the region metric of the whole       *)
(* manifold is the chart metric (P2A_RLOCAL_SLICE with the chart itself);   *)
(* from (p,b) the curve that stays at p up to s1^2 and then runs along the  *)
(* chart chord from c(p) to y in the variable s = sqrt(tau) is admissible   *)
(* (P2A_CONST_SMALL_TIME, P2A_CHART_CURVE_SEG, P2A_SEG_GLUE, as in          *)
(* P2AU_ADM_EXISTS) with L-length L(const) + cL(chord).                     *)
(* ------------------------------------------------------------------------- *)

let P2AU_RLOCAL_FLOW = prove
 (`!top atlas a b (g:real->A->real^N^N) (U:A->bool) (phi:A->real^N) t y.
     p2a_cbflow (top,atlas) a b g /\ (U,phi) IN atlas /\ a < t /\ t <= b /\
     y IN IMAGE phi U /\
     p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b]) g) (topspace top) a b
     ==> p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) (topspace top) b
                    (U INTER topspace top,phi) t y =
         metric_local atlas (U,phi) (g t) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(U:A->bool),(phi:A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) INTER topspace top = U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(y:real^N) IN IMAGE (phi:A->real^N) U` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^N^N)`;
                 `topspace top:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^N`;
                 `t:real`; `(U:A->bool),(phi:A->real^N)`; `x:A`] P2A_RLOCAL_SLICE) THEN
  SUBGOAL_THEN `t IN real_interval[a,b] /\ b IN real_interval[a,b]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2AU_FLOW_VIEW_PARTS; FST] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P2CF_MPULLBACK_LOCAL_ID THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[chart_trans; SND] THEN ASM_SIMP_TAC[]);;

(* The affine chart chord has constant velocity.                             *)

let P2AU_LINE_VD = prove
 (`!(z0:real^N) w u x. ((\s:real^1. z0 + (drop s - u) % w) has_vector_derivative w) (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  MP_TAC(ISPECL [`\s:real^1. (z0:real^N) - u % w`; `\h:real^1. vec 0:real^N`;
                 `\s:real^1. drop s % (w:real^N)`; `\h:real^1. drop h % (w:real^N)`;
                 `at (x:real^1)`] HAS_DERIVATIVE_ADD) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
    REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC);;

(* The chord curve from (p,b) to chart_inv y at backward time s2^2.          *)

let P2AU_CHORD_CURVE = prove
 (`!top atlas a b (g:real->A->real^3^3) p t0 Kr s1 s2 (y:real^3) rho.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\
     (!tau. &0 < tau /\ tau < t0
            ==> p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau (\s. p) /\
                p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b (\s. p) tau
                <= Kr * tau * sqrt tau) /\
     &0 < s1 /\ s1 < s2 /\ s1 pow 2 < t0 /\ s2 pow 2 < b - a /\
     ball(SND(chart_at atlas p) p,rho) SUBSET
       IMAGE (SND(chart_at atlas p)) (FST(chart_at atlas p)) /\
     y IN ball(SND(chart_at atlas p) p,rho)
     ==> ?gamma. p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                         (s2 pow 2) gamma /\
                 gamma (s2 pow 2) = chart_inv (chart_at atlas p) y /\
                 p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma
                              (s2 pow 2) <=
                 Kr * s1 pow 2 * s1 +
                 p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                    (topspace top) b
                                    (FST(chart_at atlas p) INTER topspace top,
                                     SND(chart_at atlas p)))
                        b (\s. SND(chart_at atlas p) p +
                               (drop s - s1) % (inv(s2 - s1) % (y - SND(chart_at atlas p) p)))
                        s1 s2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CONST") STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)` THEN
  SUBGOAL_THEN `?(U:A->bool) (phi:A->real^3). c = U,phi`
  (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(U:A->bool),(phi:A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) INTER topspace top = U` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (topspace top) a b` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `w = inv(s2 - s1) % (y - (phi:A->real^3) p)` THEN
  ABBREV_TAC `sol = \s:real^1. (phi:A->real^3) p + (drop s - s1) % w` THEN
  SUBGOAL_THEN `!x. ((sol:real^1->real^3) has_vector_derivative w) (at x)` ASSUME_TAC THENL
   [EXPAND_TAC "sol" THEN REWRITE_TAC[P2AU_LINE_VD]; ALL_TAC] THEN
  SUBGOAL_THEN `(sol:real^1->real^3)(lift s1) = phi(p:A) /\ sol(lift s2) = y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sol" THEN EXPAND_TAC "w" THEN REWRITE_TAC[LIFT_DROP; REAL_SUB_REFL] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(s2 - s1) * inv(s2 - s1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2
                    ==> (sol:real^1->real^3)(lift s) IN ball((phi:A->real^3) p,rho)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "sol" THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[IN_BALL; LIFT_DROP; dist; VECTOR_ARITH `z - (z + v:real^N) = --v`;
                NORM_NEG; VECTOR_MUL_ASSOC; NORM_MUL] THEN
    SUBGOAL_THEN `norm(y - (phi:A->real^3) p) < rho` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN ball((phi:A->real^3) p,rho)` THEN
      REWRITE_TAC[IN_BALL; dist] THEN MESON_TAC[NORM_SUB];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(y - (phi:A->real^3) p)` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_ARITH `s1 <= s ==> abs(s - s1) = s - s1`] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 < sqrt(b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LT_IMP_LE; REAL_SUB_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `topspace top:A->bool`; `a:real`; `b:real`;
                 `U:A->bool`; `phi:A->real^3`; `sol:real^1->real^3`; `s1:real`; `s2:real`;
                 `s1 / &2`; `(s2 + sqrt(b - a)) / &2`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[P2AU_FLOW_VIEW_PARTS] THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < s /\ s < sqrt(b - a)` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `s pow 2 < b - a` MP_TAC THENL
       [SUBGOAL_THEN `s pow 2 < sqrt(b - a) pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_SUB_LT]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < s pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        REWRITE_TAC[differentiable] THEN EXISTS_TAC `\h:real^1. drop h % (w:real^3)` THEN
        ASM_MESON_TAC[has_vector_derivative];
        SUBGOAL_THEN `(\v. vector_derivative (sol:real^1->real^3) (at v)) = (\v. w)`
        SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
          MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[CONTINUOUS_CONST]]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `seg = \tau'. chart_inv ((U:A->bool),(phi:A->real^3))
                                     ((sol:real^1->real^3)(lift(sqrt tau')))` THEN
  SUBGOAL_THEN `(seg:real->A)(s1 pow 2) = p /\
                seg(s2 pow 2) = chart_inv ((U:A->bool),(phi:A->real^3)) (y:real^3)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "seg" THEN
    SUBGOAL_THEN `&0 <= s1 /\ &0 <= s2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[POW_2_SQRT];
    ALL_TAC] THEN
  USE_THEN "CONST" (MP_TAC o SPEC `s1 pow 2`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `p:A`; `seg:real->A`; `\s:real. (p:A)`;
                 `\tau'. if tau' <= s1 pow 2 then (p:A) else seg tau'`;
                 `s2 pow 2`; `s1 pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `tau':real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `tau' = s1 pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(s2 pow 2 <= s1 pow 2)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\tau'. if tau' <= s1 pow 2 then (p:A) else seg tau'` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE o check (fun th ->
    p2au_mentions "has_real_integral" th)) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The L-length of the chord.  On the chord the s-Lagrangian (1/2) w.G      *)
(* w + 2 s^2 R is at most (1/2)(1 + e) w.G0 w + 12 K s2^2 when the          *)
(* chart metric is e-close to G0 (P2AU_FLOW_METRIC_NEAR) and abs R <= 6 K   *)
(* (P2AU_MFD_SCALAR_ABS_3, P2AZ_RLOCAL_SLICE_FACTS); the Lagrangian is      *)
(* continuous along the chord (P2A_REGION_LSMOOTH,                          *)
(* P2A_LLAG_CURVE_CONTINUOUS).                                              *)
(* ------------------------------------------------------------------------- *)

let P2AU_CHORD_CL_BOUND = prove
 (`!top atlas a b (g:real->A->real^3^3) p K s1 s2 (y:real^3) rho e d.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ &0 <= K /\
     (!t q. a <= t /\ t <= b /\ q IN topspace top ==> mfd_rm_norm atlas (g t) q <= K) /\
     &0 < s1 /\ s1 < s2 /\ s2 pow 2 < b - a /\ s2 pow 2 < d /\ rho <= d /\
     ball(SND(chart_at atlas p) p,rho) SUBSET
       IMAGE (SND(chart_at atlas p)) (FST(chart_at atlas p)) /\
     y IN ball(SND(chart_at atlas p) p,rho) /\
     (!t z v. b - d < t /\ t <= b /\
              z IN IMAGE (SND(chart_at atlas p)) (FST(chart_at atlas p)) /\
              norm(z - SND(chart_at atlas p) p) < d
              ==> abs(v dot (metric_local atlas (chart_at atlas p) (g t) z ** v) -
                      v dot (metric_local atlas (chart_at atlas p) (g b)
                                          (SND(chart_at atlas p) p) ** v)) <=
                  e * (v dot (metric_local atlas (chart_at atlas p) (g b)
                                           (SND(chart_at atlas p) p) ** v)))
     ==> p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                            (topspace top) b
                            (FST(chart_at atlas p) INTER topspace top,SND(chart_at atlas p)))
                b (\s. SND(chart_at atlas p) p +
                       (drop s - s1) % (inv(s2 - s1) % (y - SND(chart_at atlas p) p)))
                s1 s2 <=
         (s2 - s1) *
         (inv(&2) * (&1 + e) *
          ((inv(s2 - s1) % (y - SND(chart_at atlas p) p)) dot
           (metric_local atlas (chart_at atlas p) (g b) (SND(chart_at atlas p) p) **
            (inv(s2 - s1) % (y - SND(chart_at atlas p) p)))) +
          &12 * K * s2 pow 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "RM") STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)` THEN
  SUBGOAL_THEN `?(U:A->bool) (phi:A->real^3). c = U,phi`
  (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(U:A->bool),(phi:A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) INTER topspace top = U` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (topspace top) a b` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `w = inv(s2 - s1) % (y - (phi:A->real^3) p)` THEN
  ABBREV_TAC `sol = \s:real^1. (phi:A->real^3) p + (drop s - s1) % w` THEN
  ABBREV_TAC `G0 = metric_local atlas ((U:A->bool),(phi:A->real^3))
                     ((g:real->A->real^3^3) b) (phi(p:A))` THEN
  SUBGOAL_THEN `!x. ((sol:real^1->real^3) has_vector_derivative w) (at x)` ASSUME_TAC THENL
   [EXPAND_TAC "sol" THEN REWRITE_TAC[P2AU_LINE_VD]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2
                    ==> (sol:real^1->real^3)(lift s) IN ball((phi:A->real^3) p,rho)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "sol" THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[IN_BALL; LIFT_DROP; dist; VECTOR_ARITH `z - (z + v:real^N) = --v`;
                NORM_NEG; VECTOR_MUL_ASSOC; NORM_MUL] THEN
    SUBGOAL_THEN `norm(y - (phi:A->real^3) p) < rho` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN ball((phi:A->real^3) p,rho)` THEN
      REWRITE_TAC[IN_BALL; dist] THEN MESON_TAC[NORM_SUB];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(y - (phi:A->real^3) p)` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_ARITH `s1 <= s ==> abs(s - s1) = s - s1`] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 < sqrt(b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LT_IMP_LE; REAL_SUB_LT];
    ALL_TAC] THEN
  (* the Lagrangian is continuous along the chord, hence integrable *)
  SUBGOAL_THEN
   `(\s. p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) (topspace top) b (U,phi)) b s
          ((sol:real^1->real^3)(lift s)) (vector_derivative sol (at (lift s))))
    real_integrable_on real_interval[s1,s2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `s1 / &2`; `(s2 + sqrt(b - a)) / &2`;
                   `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) (topspace top) b (U,phi)`;
                   `b:real`; `sol:real^1->real^3`; `\x:real^1. (w:real^3)`;
                   `s1:real`; `s2:real`] P2A_LLAG_CURVE_CONTINUOUS) THEN
    SUBGOAL_THEN `!s. vector_derivative (sol:real^1->real^3) (at (lift s)) = w`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `topspace top:A->bool`; `a:real`; `b:real`;
                     `U:A->bool`; `phi:A->real^3`; `b:real`; `s1 / &2`;
                     `(s2 + sqrt(b - a)) / &2`] P2A_REGION_LSMOOTH) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "V" THEN REWRITE_TAC[P2AU_FLOW_VIEW_PARTS] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < s /\ s < sqrt(b - a)` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `s pow 2 < b - a` MP_TAC THENL
       [SUBGOAL_THEN `s pow 2 < sqrt(b - a) pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_SUB_LT]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < s pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[differentiable_on] THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h:real^1. drop h % (w:real^3)` THEN
      ASM_MESON_TAC[has_vector_derivative];
      REWRITE_TAC[CONTINUOUS_ON_CONST];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(sol:real^1->real^3)(lift s) IN ball((phi:A->real^3) p,rho)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_cL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[s1,s2])
                (\s. inv(&2) * (&1 + e) * (w dot ((G0:real^3^3) ** w)) + &12 * K * s2 pow 2)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `s1 <= s2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `vector_derivative (sol:real^1->real^3) (at (lift s)) = w` SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sol:real^1->real^3)(lift s) IN ball((phi:A->real^3) p,rho)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sol:real^1->real^3)(lift s) IN IMAGE (phi:A->real^3) U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s /\ s pow 2 <= s2 pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b - s pow 2 /\ b - s pow 2 <= b /\ b - d < b - s pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < s pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_llag] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`; `b - s pow 2`;
                 `(sol:real^1->real^3)(lift s)`] P2AU_RLOCAL_FLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN TRY ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `lscalar (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (topspace top) b (U,phi) (b - s pow 2))
                  ((sol:real^1->real^3)(lift s)) <= &6 * K`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `?x:A. x IN U /\ (sol:real^1->real^3)(lift s) = phi x`
    (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `topspace top:A->bool`; `a:real`; `b:real`;
                   `b - s pow 2`; `U:A->bool`; `phi:A->real^3`; `x:A`]
                  P2AZ_RLOCAL_SLICE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(ASM SET_TAC[] THEN NO_TAC) THEN
      EXPAND_TAC "V" THEN REWRITE_TAC[GSYM P2A_VIEW_PROJ_3; P2AU_FLOW_VIEW_PARTS] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) (b - s pow 2) = atlas /\
                  rfs_vmetric V (b - s pow 2) = g(b - s pow 2)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[GSYM P2A_VIEW_PROJ_3; P2AU_FLOW_VIEW_PARTS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `!x y z. abs x <= y /\ y <= z ==> x <= z`) THEN
    EXISTS_TAC `&6 * mfd_rm_norm atlas ((g:real->A->real^3^3)(b - s pow 2)) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AU_MFD_SCALAR_ABS_3 THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
        ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      USE_THEN "RM" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `w dot (metric_local atlas ((U:A->bool),(phi:A->real^3))
                         ((g:real->A->real^3^3)(b - s pow 2)) ((sol:real^1->real^3)(lift s)) ** w)
                <= (&1 + e) * (w dot ((G0:real^3^3) ** w))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`b - s pow 2`; `(sol:real^1->real^3)(lift s)`; `w:real^3`] o
      check (fun th -> is_forall(concl th) && p2au_mentions "metric_local" th &&
                       can (find_term (fun t -> t = `e:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `norm((sol:real^1->real^3)(lift s) - (phi:A->real^3) p) < rho` MP_TAC THENL
       [UNDISCH_TAC `(sol:real^1->real^3)(lift s) IN ball((phi:A->real^3) p,rho)` THEN
        REWRITE_TAC[IN_BALL; dist] THEN MESON_TAC[NORM_SUB];
        ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * s pow 2 * lscalar (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) (topspace top) b (U,phi)
                  (b - s pow 2)) ((sol:real^1->real^3)(lift s)) <= &12 * K * s2 pow 2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * s pow 2 * (&6 * K)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      SUBGOAL_THEN `s pow 2 * K <= s2 pow 2 * K` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `w dot (metric_local atlas ((U:A->bool),(phi:A->real^3))
                         ((g:real->A->real^3^3)(b - s pow 2)) ((sol:real^1->real^3)(lift s)) ** w)
                <= (&1 + e) * (w dot ((G0:real^3^3) ** w))` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The chord bound for lx.  For 0 < e <= 1/2 there are a chart ball and     *)
(* tau1 such that for 0 < tau < tau1, with s2 = sqrt(tau) and               *)
(* s1 = e s2, lx(chart_inv y, tau) <= C tau + (1 + e)/(1 - e)               *)
(* (y - c p).G0 (y - c p) / (4 tau).                                        *)
(* ------------------------------------------------------------------------- *)

let P2AU_CHORD_LX = prove
 (`!top atlas a b (g:real->A->real^3^3) p e.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ &0 < e /\ e <= inv(&2)
     ==> ?rho tau1 C.
           &0 < rho /\ &0 < tau1 /\ tau1 < b - a /\ &0 <= C /\
           ball(SND(chart_at atlas p) p,rho) SUBSET
             IMAGE (SND(chart_at atlas p)) (FST(chart_at atlas p)) /\
           !tau y. &0 < tau /\ tau < tau1 /\ y IN ball(SND(chart_at atlas p) p,rho)
                   ==> p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                              (chart_inv (chart_at atlas p) y) <=
                       C * tau +
                       ((&1 + e) / (&1 - e)) *
                       ((y - SND(chart_at atlas p) p) dot
                        (metric_local atlas (chart_at atlas p) (g b) (SND(chart_at atlas p) p) **
                         (y - SND(chart_at atlas p) p))) / (&4 * tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `CL:real` STRIP_ASSUME_TAC o MATCH_MP P2AU_L_LOWER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)` THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) p IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST(c:(A->bool)#(A->real^3)))` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^3))) (FST(c:(A->bool)#(A->real^3))))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`;
                 `SND(c:(A->bool)#(A->real^3)) p`; `e:real`] P2AU_FLOW_METRIC_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "NEAR"))) THEN
  UNDISCH_TAC `open(IMAGE (SND(c:(A->bool)#(A->real^3))) (FST(c:(A->bool)#(A->real^3))))` THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `SND(c:(A->bool)#(A->real^3)) p`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                  (g:real->A->real^3^3)) (topspace top) a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `topspace top:A->bool`; `a:real`] P2A_CONST_SMALL_TIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `Kr:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`min rho0 d`; `min (min (d / &2) ((b - a) / &2)) (t0 / &2)`;
    `max Kr (&0) / &2 + &6 * K`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MIN_LT] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(SND(c:(A->bool)#(A->real^3)) p,rho0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tau:real`; `y:real^3`] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  ABBREV_TAC `r = sqrt tau` THEN
  SUBGOAL_THEN `&0 < r /\ r pow 2 = tau` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e * r /\ e * r < r /\ (e * r) pow 2 < t0` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `tau:real` THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `inv(&2) * inv(&2)` THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
          ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `y IN ball(SND(c:(A->bool)#(A->real^3)) p,rho0) /\ norm(y - SND(c:(A->bool)#(A->real^3)) p) < d`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN ball(SND(c:(A->bool)#(A->real^3)) p,min rho0 d)` THEN
    REWRITE_TAC[IN_BALL; dist; REAL_LT_MIN] THEN MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `t0:real`; `Kr:real`; `e * r`; `r:real`;
                 `y:real^3`; `min rho0 d`] P2AU_CHORD_CURVE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           MATCH_MP_TAC SUBSET_TRANS THEN
           EXISTS_TAC `ball(SND(c:(A->bool)#(A->real^3)) p,rho0)` THEN
           ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
           ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `K:real`; `e * r`; `r:real`; `y:real^3`;
                 `min rho0 d`; `e:real`; `d:real`] P2AU_CHORD_CL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           USE_THEN "NEAR" ACCEPT_TAC;
           MATCH_MP_TAC SUBSET_TRANS THEN
           EXISTS_TAC `ball(SND(c:(A->bool)#(A->real^3)) p,rho0)` THEN
           ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
           ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `v = y - SND(c:(A->bool)#(A->real^3)) p` THEN
  ABBREV_TAC `G0 = metric_local atlas c ((g:real->A->real^3^3) b) (SND(c:(A->bool)#(A->real^3)) p)` THEN
  ABBREV_TAC `Q = v dot ((G0:real^3^3) ** v)` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `!w:real^3. ~(w = vec 0) ==> &0 < w dot ((G0:real^3^3) ** w)` ASSUME_TAC THENL
     [SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) b)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric; metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `SND(c:(A->bool)#(A->real^3)) p` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "Q" THEN
    ASM_CASES_TAC `v:real^3 = vec 0` THENL
     [POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* lx is at most L(gamma) / (2 sqrt tau) *)
  SUBGOAL_THEN
   `p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p tau
           (chart_inv (c:(A->bool)#(A->real^3)) (y:real^3)) <=
    p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2a_Lx] THEN MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
     [EXISTS_TAC `--(CL * tau * sqrt tau)` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `gm:real->A` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `CL:real`)) (concl th))) THEN
      EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lx] THEN
  SUBGOAL_THEN `sqrt tau = r` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r - e * r = (&1 - e) * r /\ &0 < &1 - e /\ &0 < (&1 - e) * r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(inv((&1 - e) * r) % v) dot ((G0:real^3^3) ** (inv((&1 - e) * r) % v)) =
                Q / ((&1 - e) * r) pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    UNDISCH_TAC `&0 < (&1 - e) * r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `Kr * (e * r) pow 2 * e * r <= max Kr (&0) * r pow 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `Kr * (e * r) pow 2 * e * r = (Kr * e pow 3) * r pow 3` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < e pow 3 /\ e pow 3 <= &1` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `&0 <= Kr` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kr:real` THEN CONJ_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
          REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]];
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&12 * K * ((&1 - e) * r) * tau <= &12 * K * r pow 3` ASSUME_TAC THENL
   [UNDISCH_TAC `r pow 2 = tau` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&12 * K * ((&1 - e) * r) * r pow 2 = ((&1 - e) * (&12 * K)) * r pow 3`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (e * &12 * K) * r pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p tau
           (chart_inv (c:(A->bool)#(A->real^3)) (y:real^3)) <=
    max Kr (&0) * r pow 3 + (&1 + e) * Q / (&2 * (&1 - e) * r) + &12 * K * r pow 3`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((&1 - e) * r) * (inv(&2) * (&1 + e) * Q / ((&1 - e) * r) pow 2) =
                  (&1 + e) * Q / (&2 * (&1 - e) * r)` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < &1 - e` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      p2au_mentions "p2a_L_length" th && p2au_mentions "p2a_cL" th)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      p2au_mentions "p2a_cL" th && not (p2au_mentions "p2a_L_length" th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(max Kr (&0) * r pow 3 + (&1 + e) * Q / (&2 * (&1 - e) * r) +
               &12 * K * r pow 3) / (&2 * r)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(max Kr (&0) * r pow 3 + (&1 + e) * Q / (&2 * (&1 - e) * r) +
                 &12 * K * r pow 3) / (&2 * r) =
                (max Kr (&0) / &2 + &6 * K) * tau +
                ((&1 + e) / (&1 - e)) * Q / (&4 * tau)` SUBST1_TAC THENL
   [UNDISCH_TAC `r pow 2 = tau` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < &1 - e` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The Gaussian exp(-k (y - z0).G0 (y - z0) / (4 tau)) over the             *)
(* ellipsoid z0 + M(ball(0,R)), M = 2 sqrt(tau/k) S^-1 for G0 = S^T         *)
(* S, is |det M| times the standard Gaussian over ball(0,R) (translation    *)
(* and INTEGRAL_CHANGE_OF_VARIABLES_LINEAR).                                *)
(* ------------------------------------------------------------------------- *)

let P2AU_GAUSS_ELLIPSOID = prove
 (`!(S:real^3^3) (z0:real^3) k tau R.
     invertible S /\ &0 < k /\ &0 < tau
     ==> (\y. lift(exp(--(k * ((y - z0) dot ((transp S ** S) ** (y - z0))) / (&4 * tau)))))
         absolutely_integrable_on
         IMAGE (\u. z0 + ((&2 * sqrt(tau / k)) %% matrix_inv S) ** u) (ball(vec 0,R)) /\
         integral (IMAGE (\u. z0 + ((&2 * sqrt(tau / k)) %% matrix_inv S) ** u)
                         (ball(vec 0,R)))
                  (\y. lift(exp(--(k * ((y - z0) dot ((transp S ** S) ** (y - z0))) /
                                   (&4 * tau))))) =
         ((&2 * sqrt(tau / k)) pow 3 / abs(det S)) %
         integral (ball(vec 0,R)) (\u:real^3. lift(exp(--(u dot u))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `M = (&2 * sqrt(tau / k)) %% matrix_inv(S:real^3^3)` THEN
  SUBGOAL_THEN `&0 < sqrt(tau / k) /\ sqrt(tau / k) pow 2 = tau / k` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_DIV; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_DIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3^3) ** (M:real^3^3) = (&2 * sqrt(tau / k)) %% mat 1` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[MATRIX_MUL_RMUL] THEN ASM_SIMP_TAC[MATRIX_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:real^3. (\y. lift(exp(--(k * ((y - z0) dot ((transp(S:real^3^3) ** S) ** (y - z0))) /
                                  (&4 * tau))))) ((z0:real^3) + (M:real^3^3) ** u) =
               lift(exp(--(u dot u)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[VECTOR_ARITH `(z0 + x) - z0:real^N = x`] THEN
    REWRITE_TAC[GSYM P2A_T81_DOT_COV; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_LMUL; DOT_RMUL] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(&2 * sqrt(tau / k)) * (&2 * sqrt(tau / k)) * ((u:real^3) dot u) =
                  (&4 * (tau / k)) * (u dot u)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `sqrt(tau / k) pow 2 = tau / k` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    UNDISCH_TAC `&0 < k` THEN UNDISCH_TAC `&0 < tau` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\u:real^3. (z0:real^3) + (M:real^3^3) ** u) (ball(vec 0,R)) =
                IMAGE (\x. z0 + x) (IMAGE (\u:real^3. (M:real^3^3) ** u) (ball(vec 0,R)))`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_TRANSLATION; GSYM INTEGRAL_TRANSLATION] THEN
  SUBGOAL_THEN `det(M:real^3^3) = (&2 * sqrt(tau / k)) pow 3 / det(S:real^3^3)`
  ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[DET_CMUL; DIMINDEX_3; DET_MATRIX_INV; real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(det(M:real^3^3) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INVERTIBLE_DET_NZ]) THEN
    SUBGOAL_THEN `&0 < (&2 * sqrt(tau / k)) pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\u:real^3. lift(exp(--(u dot u)))) absolutely_integrable_on ball(vec 0,R)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_BALL; P2AU_GAUSS_SPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. lift(exp(--(k * (x dot ((transp(S:real^3^3) ** S) ** x)) / (&4 * tau))))`;
                 `\u:real^3. (M:real^3^3) ** u`; `ball(vec 0:real^3,R)`]
                ABSOLUTELY_INTEGRABLE_ON_LINEAR_IMAGE) THEN
  MP_TAC(ISPECL [`\x:real^3. lift(exp(--(k * (x dot ((transp(S:real^3^3) ** S) ** x)) / (&4 * tau))))`;
                 `\u:real^3. (M:real^3^3) ** u`; `ball(vec 0:real^3,R)`]
                INTEGRAL_CHANGE_OF_VARIABLES_LINEAR) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  REWRITE_TAC[o_DEF; VECTOR_ADD_SUB] THEN
  SUBGOAL_THEN
   `!u:real^3. lift(exp(--(k * (((M:real^3^3) ** u) dot ((transp(S:real^3^3) ** S) ** (M ** u))) /
                           (&4 * tau)))) = lift(exp(--(u dot u)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `u:real^3` o check (fun th ->
      is_forall(concl th) && p2au_mentions "exp" th)) THEN
    REWRITE_TAC[VECTOR_ARITH `(z0 + x) - z0:real^N = x`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_MUL; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`]);;

(* ------------------------------------------------------------------------- *)
(* Three auxiliary facts for the lower bound: the density under a           *)
(* quadratic-form comparison (GRGA_SQRT_DET_QF_LE), the Gaussian over large *)
(* balls (P2AG_GAUSS_TAIL), and the loss factor of the chord constant.      *)
(* ------------------------------------------------------------------------- *)

let P2AU_DENS_LOWER = prove
 (`!(G:real^N^N) G0 e.
     positive_semidefinite G /\ positive_semidefinite G0 /\ &0 <= e /\ e < &1 /\
     (!v. abs(v dot (G ** v) - v dot (G0 ** v)) <= e * (v dot (G0 ** v)))
     ==> sqrt(&1 - e) pow dimindex(:N) * sqrt(det G0) <= sqrt(det G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`G0:real^N^N`; `G:real^N^N`; `inv(&1 - e)`] GRGA_SQRT_DET_QF_LE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN X_GEN_TAC `w:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&1 - e) * ((&1 - e) * (w dot ((G0:real^N^N) ** w)))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&1 - e) pow dimindex(:N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 - e) pow dimindex(:N) * sqrt(inv(&1 - e)) pow dimindex(:N) = &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL; GSYM SQRT_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; SQRT_1; REAL_POW_ONE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 - e) pow dimindex(:N) *
              (sqrt(inv(&1 - e)) pow dimindex(:N) * sqrt(det(G:real^N^N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID; REAL_LE_REFL]]);;

(* The standard Gaussian over large balls.                                   *)

let P2AU_GAUSS_BALL_LARGE = prove
 (`!eta. &0 < eta
         ==> ?R. &0 < R /\
                 (&1 - eta) * (pi * sqrt pi) <=
                 drop(integral (ball(vec 0:real^3,R)) (\u:real^3. lift(exp(--(u dot u)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC P2AG_GAUSS_TAIL THEN REWRITE_TAC[P2A_GAUSS_TAIL_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T"))) THEN
  SUBGOAL_THEN `&0 < pi * sqrt pi` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS];
    ALL_TAC] THEN
  ABBREV_TAC `eps = min eps0 (min (&1) (&8 * eta * pi * sqrt pi))` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= eps0 /\ eps <= &1 /\ eps <= &8 * eta * pi * sqrt pi`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "T" (MP_TAC o SPEC `eps:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `inv(&8 * sqrt eps)` THEN
  SUBGOAL_THEN `&0 < sqrt eps` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{Z:real^3 | &1 <= &64 * eps * (Z dot Z)} =
                (:real^3) DIFF ball(vec 0,inv(&8 * sqrt eps))` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_BALL_0; REAL_NOT_LT] THEN
    X_GEN_TAC `Z:real^3` THEN
    SUBGOAL_THEN `&0 < &8 * sqrt eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&64 * eps * (Z dot Z) = (&8 * sqrt eps * norm(Z:real^3)) pow 2`
    SUBST1_TAC THENL
     [REWRITE_TAC[DOT_SQUARE_NORM; REAL_POW_MUL] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&8 * sqrt eps) <= norm(Z:real^3) <=> &1 <= &8 * sqrt eps * norm Z`
    SUBST1_TAC THENL
     [MP_TAC(SPECL [`inv(&8 * sqrt eps)`; `norm(Z:real^3)`; `&8 * sqrt eps`]
                   REAL_LE_LMUL_EQ) THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &8 * sqrt eps * norm(Z:real^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE; NORM_POS_LE]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`&1`; `&8 * sqrt eps * norm(Z:real^3)`] REAL_LE_SQUARE_ABS) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ABS_NUM; REAL_POW_ONE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\u:real^3. lift(exp(--(u dot u)))) absolutely_integrable_on (:real^3)`
  ASSUME_TAC THENL [REWRITE_TAC[P2AU_GAUSS_SPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `integral ((:real^3) DIFF ball(vec 0,inv(&8 * sqrt eps))) (\u:real^3. lift(exp(--(u dot u)))) =
    integral (:real^3) (\u:real^3. lift(exp(--(u dot u)))) -
    integral (ball(vec 0,inv(&8 * sqrt eps))) (\u:real^3. lift(exp(--(u dot u))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DIFF THEN
    REWRITE_TAC[SET_RULE `s DIFF (:real^3) = {}`; NEGLIGIBLE_EMPTY] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral (:real^3) (\u:real^3. lift(exp(--(u dot u)))) =
                lift(pi * sqrt pi)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNIQUE THEN REWRITE_TAC[P2AU_GAUSS_SPACE]; ALL_TAC] THEN
  UNDISCH_TAC `drop(integral {Z:real^3 | &1 <= &64 * eps * (Z dot Z)}
                  (\Z. lift(&8 * exp(--(Z dot Z))))) <= eps * sqrt eps` THEN
  ASM_REWRITE_TAC[LIFT_CMUL] THEN
  SUBGOAL_THEN `(\u:real^3. lift(exp(--(u dot u)))) integrable_on
                (:real^3) DIFF ball(vec 0,inv(&8 * sqrt eps))` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_UNIV;
                 LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; DROP_SUB; LIFT_DROP] THEN
  SUBGOAL_THEN `eps * sqrt eps <= eps` MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `I0 = integral (ball(vec 0:real^3,inv(&8 * sqrt eps)))
                            (\u. lift(exp(--(u dot u))))` THEN
  ASM_REAL_ARITH_TAC);;

(* The loss factor of the chord constant k = (1 + e)/(1 - e) and the        *)
(* density factor: at least 1 - 9 e.                                         *)

let P2AU_CHORD_FACTOR = prove
 (`!e. &0 <= e /\ e <= inv(&9)
       ==> &1 - &9 * e <= (sqrt(&1 - e) * sqrt((&1 - e) / (&1 + e))) pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&1 - e) * sqrt((&1 - e) / (&1 + e)) =
                sqrt((&1 - e) pow 2 / (&1 + e))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 < &1 + e` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `x = (&1 - e) pow 2 / (&1 + e)` THEN
  SUBGOAL_THEN `&1 - &3 * e <= x /\ x <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    SUBGOAL_THEN `&0 < &1 + e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= e * e /\ &0 <= e ==>
         (&1 - &3 * e) * (&1 + e) <= (&1 - e) pow 2`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL];
      MATCH_MP_TAC(REAL_ARITH `&0 <= e /\ e * e <= e ==>
         (&1 - e) pow 2 <= &1 * (&1 + e)`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `e * e <= e * &1 ==> e * e <= e`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - &3 * e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x <= sqrt x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - &3 * e) pow 3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= e * e * (&27 - &27 * e) ==>
       &1 - &9 * e <= (&1 - &3 * e) pow 3`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The reduced volume at each fixed tau: its value as a manifold integral,   *)
(* positivity and the upper bound (4 pi)^(3/2) (P2AU_FRV_UPPER,              *)
(* P2AU_FRV_GAUSS, P2AU_MFD_INTEGRAL_POS); used by the lower bound at small  *)
(* times and by FL5.                                                         *)
(* ------------------------------------------------------------------------- *)

let P2AU_SQRT_4PI_POW3 = prove
 (`sqrt(&4 * pi) pow 3 = &8 * pi * sqrt pi`,
  SUBGOAL_THEN `&0 <= pi` ASSUME_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&4) = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_MUL; REAL_POS] THEN
  SUBGOAL_THEN `sqrt pi pow 2 = pi` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  CONV_TAC REAL_RING);;

let P2AU_FRV_VALUE = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p tau.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau /\ tau < b - a
     ==> mfd_has_integral (top,atlas) (g(b - tau))
           (\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                              b p tau q)) / sqrt tau pow 3)
           (topspace top) (p2a_frv (top,atlas) a b g p tau) /\
         mfd_integrable_on (top,atlas) (g(b - tau))
           (\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                              b p tau q)) / sqrt tau pow 3)
           (topspace top) /\
         &0 < p2a_frv (top,atlas) a b g p tau /\
         p2a_frv (top,atlas) a b g p tau <= sqrt(&4 * pi) pow 3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`] P2AU_FRV_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`] P2AU_SMIN_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`] P2AU_FRV_WEIGHT_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FLOW_VIEW_FACTS_3) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3)(b - tau)) /\
                mfd_complete (top,atlas) (g(b - tau))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_frv (top,atlas) a b (g:real->A->real^3^3) p tau = v` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_frv; DIMINDEX_3] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3)(b - tau)`;
                   `\q:A. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                             (g:real->A->real^3^3)) b p tau q)) / sqrt tau pow 3`;
                   `topspace top:A->bool`; `v:real`] MFD_HAS_INTEGRAL_INTEGRAL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_integrable_on] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] P2AU_MFD_INTEGRAL_POS) THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `(g:real->A->real^3^3)(b - tau)`;
                          `\q:A. exp(--(p2a_lx (p2a_flow_view (top,atlas)
                             (real_interval[a,b]) (g:real->A->real^3^3)) b p tau q)) /
                             sqrt tau pow 3`; `p:A`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_POW_LT; SQRT_POS_LT];
    REWRITE_TAC[P2AU_SQRT_4PI_POW3] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2a_zdens (p2a_flow_view (top,atlas) (real_interval[a,b])
                  (g:real->A->real^3^3)) b p *
                drop(integral (p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                        b p tau)
                       (\Z. lift(p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                         b p tau Z)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AU_FRV_GAUSS THEN ASM_SIMP_TAC[] THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                  `g:real->A->real^3^3`; `b:real`] P2AU_FLOW_SLICE_3) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_SIMP_TAC[]]);;

(* The limit at 0 from the bounds.                                           *)


(* ------------------------------------------------------------------------- *)
(* The lower bound at small times (MT Thm 7.26, the limit; MT uses Cor 6.79, *)
(* here an explicit chord estimate).  In the chart c at p, with z0 = c p     *)
(* and G0 = S^T S the metric of g(b) at z0:                                  *)
(*   lx(c^-1 y,tau) <= C tau + k (y - z0).G0 (y - z0) / (4 tau)             *)
(* (P2AU_CHORD_LX, k = (1 + e1)/(1 - e1)), the density of g(b - tau) is at  *)
(* least (1 - e1)^(3/2) sqrt(det G0) near z0 (P2AU_FLOW_METRIC_NEAR,         *)
(* P2AU_DENS_LOWER), and the Gaussian over the ellipsoid                     *)
(* z0 + 2 sqrt(tau/k) S^-1 ball(0,R) is computed exactly                     *)
(* (P2AU_GAUSS_ELLIPSOID).  The ellipsoid lies in the chart for small tau.  *)
(* ------------------------------------------------------------------------- *)

(* The metric in a chart is positive definite. *)

let P2AU_METRIC_LOCAL_PD = prove
 (`!atlas (g:A->real^N^N) c y.
     riemannian_metric atlas g /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> positive_definite(metric_local atlas c g y)`,
  REWRITE_TAC[riemannian_metric; metric_field; positive_definite; symmetric_matrix] THEN
  MESON_TAC[]);;

(* A lower bound by the Gaussian over an ellipsoid. *)

let P2AU_ELLIPSOID_LOWER = prove
 (`!(ff:real^3->real^1) (S:real^3^3) (z0:real^3) k tau R A.
     invertible S /\ &0 < k /\ &0 < tau /\ &0 <= A /\
     ff absolutely_integrable_on
       IMAGE (\u. z0 + ((&2 * sqrt(tau / k)) %% matrix_inv S) ** u) (ball(vec 0,R)) /\
     (!y. y IN IMAGE (\u. z0 + ((&2 * sqrt(tau / k)) %% matrix_inv S) ** u) (ball(vec 0,R))
          ==> A * exp(--(k * ((y - z0) dot ((transp S ** S) ** (y - z0))) / (&4 * tau))) <=
              drop(ff y))
     ==> A * ((&2 * sqrt(tau / k)) pow 3 / abs(det S)) *
         drop(integral (ball(vec 0,R)) (\u:real^3. lift(exp(--(u dot u))))) <=
         drop(integral (IMAGE (\u. z0 + ((&2 * sqrt(tau / k)) %% matrix_inv S) ** u)
                              (ball(vec 0,R))) ff)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`S:real^3^3`; `z0:real^3`; `k:real`; `tau:real`; `R:real`]
               P2AU_GAUSS_ELLIPSOID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (IMAGE (\u. z0 + ((&2 * sqrt(tau / k)) %% matrix_inv S) ** u)
                         (ball(vec 0,R)))
           (\y:real^3. A % lift(exp(--(k * ((y - z0) dot
                                     ((transp(S:real^3^3) ** S) ** (y - z0))) /
                                     (&4 * tau))))))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[DROP_CMUL; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_SIMP_TAC[]);;

(* For small tau the ellipsoid is open and lies in a given ball. *)

let P2AU_ELLIPSOID_BALL = prove
 (`!(S:real^3^3) (z0:real^3) R r.
     invertible S /\ &0 < r
     ==> ?t3. &0 < t3 /\
              !tau k. &0 < tau /\ tau < t3 /\ &1 <= k
                      ==> open(IMAGE (\u. z0 + ((&2 * sqrt(tau / k)) %% matrix_inv S) ** u)
                                     (ball(vec 0,R))) /\
                          IMAGE (\u. z0 + ((&2 * sqrt(tau / k)) %% matrix_inv S) ** u)
                                (ball(vec 0,R)) SUBSET ball(z0,r)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = onorm (\u:real^3. matrix_inv(S:real^3^3) ** u)` THEN
  SUBGOAL_THEN `&0 <= B /\ !u:real^3. norm(matrix_inv(S:real^3^3) ** u) <= B * norm u`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    MP_TAC(ISPEC `\u:real^3. matrix_inv(S:real^3^3) ** u` ONORM) THEN
    MP_TAC(ISPEC `\u:real^3. matrix_inv(S:real^3^3) ** u` ONORM_POS_LE) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q = r / (&2 * (B + &1) * (abs R + &1))` THEN
  SUBGOAL_THEN `&0 < q /\ &2 * q * (B + &1) * (abs R + &1) = r` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * (B + &1) * (abs R + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `&0 < &2 * (B + &1) * (abs R + &1)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  EXISTS_TAC `q pow 2` THEN CONJ_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tau:real`; `k:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `m = &2 * sqrt(tau / k)` THEN
  SUBGOAL_THEN `&0 < m /\ m < &2 * q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    SUBGOAL_THEN `&0 < tau / k /\ tau / k <= tau` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x < q ==> &2 * x < &2 * q`) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt tau` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `q = sqrt(q pow 2)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^3. norm u < R ==> norm((m %% matrix_inv(S:real^3^3)) ** u) < r`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; NORM_MUL] THEN
    SUBGOAL_THEN `abs m = m` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `m * B * norm(u:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `m * (B + &1) * (abs R + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (B + &1) * (abs R + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `m * ((B + &1) * (abs R + &1)) < (&2 * q) * ((B + &1) * (abs R + &1))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&2 * q * (B + &1) * (abs R + &1) = r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (\u:real^3. z0 + (m %% matrix_inv(S:real^3^3)) ** u) (ball(vec 0,R)) =
                  IMAGE (\x. z0 + x) (IMAGE (\u. (m %% matrix_inv S) ** u) (ball(vec 0,R)))`
    SUBST1_TAC THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_TRANSLATION THEN
    SUBGOAL_THEN `(inv m %% (S:real^3^3)) ** (m %% matrix_inv S) = mat 1 /\
                  (m %% matrix_inv S) ** (inv m %% S) = mat 1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC] THEN
      ASM_SIMP_TAC[MATRIX_INV; REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[MATRIX_CMUL_LID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\u:real^3. (m %% matrix_inv(S:real^3^3)) ** u`; `ball(vec 0:real^3,R)`]
                  OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
    REWRITE_TAC[OPEN_BALL; MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^3`; `x':real^3`] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. (inv m %% (S:real^3^3)) ** v`) THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
      X_GEN_TAC `y:real^3` THEN EXISTS_TAC `(inv m %% (S:real^3^3)) ** y` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0; IN_BALL] THEN
    X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN ASM_SIMP_TAC[]]);;

(* The chart integral over an open subset of the chart image is at most     *)
(* the reduced volume.                                                       *)

let P2AU_FRV_CHART_INT = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p tau E.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < tau /\ tau < b - a /\
     open E /\ E SUBSET IMAGE (SND(chart_at atlas p)) (FST(chart_at atlas p))
     ==> (\y. lift(exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                                  (chart_inv (chart_at atlas p) y))) / sqrt tau pow 3 *
                   mfd_density atlas (chart_at atlas p) (g(b - tau)) y))
         absolutely_integrable_on E /\
         drop(integral E
                (\y. lift(exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                         b p tau (chart_inv (chart_at atlas p) y))) /
                          sqrt tau pow 3 *
                          mfd_density atlas (chart_at atlas p) (g(b - tau)) y))) <=
         p2a_frv (top,atlas) a b g p tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`] P2AU_FRV_VALUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)` THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3)(b - tau))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `W = {q:A | q IN FST(c:(A->bool)#(A->real^3)) /\ SND c q IN E}` THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2AU_CHART_PREIMAGE_OPEN) THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace top /\ W SUBSET FST(c:(A->bool)#(A->real^3)) /\
                IMAGE (SND c) W = E` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET];
      EXPAND_TAC "W" THEN SET_TAC[];
      EXPAND_TAC "W" THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3)(b - tau)`;
                 `\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                                      (g:real->A->real^3^3)) b p tau q)) / sqrt tau pow 3`;
                 `W:A->bool`; `topspace top:A->bool`] MFD_INTEGRABLE_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_integrable_on] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3)(b - tau)`;
                 `\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                                      (g:real->A->real^3^3)) b p tau q)) / sqrt tau pow 3`;
                 `c:(A->bool)#(A->real^3)`; `W:A->bool`; `w:real`] MFD_HAS_INTEGRAL_CHART) THEN
  ASM_REWRITE_TAC[P2AU_CHART_INTEGRAND_FUN] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2AU_MFD_INTEGRAL_SUBSET_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `(g:real->A->real^3^3)(b - tau)`;
    `\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                         (g:real->A->real^3^3)) b p tau q)) / sqrt tau pow 3`;
    `W:A->bool`; `topspace top:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_SIMP_TAC[REAL_EXP_POS_LE; REAL_POW_LE; SQRT_POS_LE; REAL_LT_IMP_LE]);;

(* The final arithmetic: three factors at least 1 - eta. *)

let P2AU_FRV_ARITH = prove
 (`!P eta x1 x2 i0.
     &0 < P /\ &0 <= eta /\ eta <= &1 /\
     &1 - eta <= x1 /\ &1 - eta <= x2 /\ (&1 - eta) * P <= i0
     ==> &8 * P - &3 * (&8 * P) * eta <= &8 * x1 * x2 * i0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&1 - eta) * (&1 - eta) <= x1 * x2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((&1 - eta) * (&1 - eta)) * ((&1 - eta) * P) <= (x1 * x2) * i0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P * (eta * eta) * (&3 - eta)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* MT Thm 7.26, the limit at tau = 0: liminf V(tau) >= (4 pi)^(3/2). *)

let P2AU_FRV_LIMINF = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p e.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
     &0 < e
     ==> ?d. &0 < d /\ d <= b - a /\
             !tau. &0 < tau /\ tau < d
                   ==> sqrt(&4 * pi) pow 3 - e <= p2a_frv (top,atlas) a b g p tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  REWRITE_TAC[P2AU_SQRT_4PI_POW3] THEN
  ABBREV_TAC `P = pi * sqrt pi` THEN
  SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS];
    ALL_TAC] THEN
  ABBREV_TAC `eta = min (inv(&2)) (e / (&3 * (&8 * P)))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= inv(&2) /\ &3 * (&8 * P) * eta <= e` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &3 * (&8 * P)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta /\ eta <= inv(&2) /\ eta <= e / (&3 * (&8 * P))` MP_TAC THENL
     [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_LT_DIV] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e1 = eta / &9` THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 <= inv(&2) /\ e1 <= inv(&9) /\ &1 - &9 * e1 = &1 - eta /\
                e1 < &1`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "e1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the chord bound for lx *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `e1:real`] P2AU_CHORD_LX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `tau1:real`
    (X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)` THEN
  ABBREV_TAC `z0 = SND(c:(A->bool)#(A->real^3)) p` THEN
  SUBGOAL_THEN `(z0:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the metric of g(b - tau) near z0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `z0:real^3`; `e1:real`]
                P2AU_FLOW_METRIC_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEAR"))) THEN
  ABBREV_TAC `G0 = metric_local atlas c ((g:real->A->real^3^3) b) (z0:real^3)` THEN
  SUBGOAL_THEN `positive_definite(G0:real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "G0" THEN MATCH_MP_TAC P2AU_METRIC_LOCAL_PD THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [POSITIVE_DEFINITE_COVARIANCE_EQ]) THEN
  SUBGOAL_THEN `sqrt(det(G0:real^3^3)) = abs(det(S:real^3^3)) /\ &0 < abs(det S)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `transp(S:real^3^3) ** S = G0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[DET_MUL; DET_TRANSP; GSYM REAL_POW_2; POW_2_SQRT_ABS] THEN
    REWRITE_TAC[GSYM REAL_ABS_NZ] THEN ASM_MESON_TAC[INVERTIBLE_DET_NZ];
    ALL_TAC] THEN
  (* the Gaussian over a large ball *)
  MP_TAC(SPEC `eta:real` P2AU_GAUSS_BALL_LARGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  (* the ellipsoid lies in the chart ball *)
  MP_TAC(ISPECL [`S:real^3^3`; `z0:real^3`; `R:real`; `min rho d1`] P2AU_ELLIPSOID_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ELL"))) THEN
  EXISTS_TAC `min (min tau1 d1) (min t3 (eta / (C + &1)))` THEN
  SUBGOAL_THEN `&0 < eta / (C + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  ABBREV_TAC `k = (&1 + e1) / (&1 - e1)` THEN
  SUBGOAL_THEN `&1 <= k /\ &0 < k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN SUBGOAL_THEN `&0 < &1 - e1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_ARITH `&0 < e1 ==> &0 < &1 + e1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "ELL" (MP_TAC o SPECL [`tau:real`; `k:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `E = IMAGE (\u. z0 + ((&2 * sqrt(tau / k)) %% matrix_inv(S:real^3^3)) ** u)
                        (ball(vec 0:real^3,R))` THEN
  SUBGOAL_THEN `(E:real^3->bool) SUBSET IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^3,min rho d1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(z0:real^3,rho)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the chart integral over E is at most the reduced volume *)
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `E:real^3->bool`]
                P2AU_FRV_CHART_INT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the pointwise lower bound on the chart ball *)
  SUBGOAL_THEN
   `!y:real^3. y IN ball(z0,min rho d1)
      ==> (exp(--(C * tau)) * sqrt(&1 - e1) pow 3 * abs(det(S:real^3^3)) / sqrt tau pow 3) *
          exp(--(k * ((y - z0) dot ((G0:real^3^3) ** (y - z0))) / (&4 * tau))) <=
          exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                        (chart_inv c y))) / sqrt tau pow 3 *
          mfd_density atlas c ((g:real->A->real^3^3)(b - tau)) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN ball(z0,rho) /\ norm(y - z0) < d1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN ball(z0,min rho d1)` THEN
      REWRITE_TAC[IN_BALL; REAL_LT_MIN; dist] THEN MESON_TAC[NORM_SUB];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
     [MP_TAC(ASSUME `ball(z0:real^3,rho) SUBSET IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "CH" (MP_TAC o SPECL [`tau:real`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `exp(--(C * tau)) * exp(--(k * ((y - z0) dot ((G0:real^3^3) ** (y - z0))) / (&4 * tau))) <=
      exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                    b p tau (chart_inv (c:(A->bool)#(A->real^3)) y)))`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(&1 - e1) pow 3 * abs(det(S:real^3^3)) <=
      mfd_density atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3)(b - tau)) y`
    ASSUME_TAC THENL
     [REWRITE_TAC[mfd_density] THEN
      UNDISCH_TAC `sqrt(det(G0:real^3^3)) = abs(det(S:real^3^3))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`metric_local atlas (c:(A->bool)#(A->real^3))
                        ((g:real->A->real^3^3)(b - tau)) y`;
                     `G0:real^3^3`; `e1:real`] P2AU_DENS_LOWER) THEN
      REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN
        MATCH_MP_TAC P2AU_METRIC_LOCAL_PD THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `v:real^3` THEN
        USE_THEN "NEAR" (MP_TAC o SPECL [`b - tau`; `y:real^3`; `v:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt tau pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN
     `((exp(--(C * tau)) * sqrt(&1 - e1) pow 3 * abs(det(S:real^3^3)) / sqrt tau pow 3) *
       exp(--(k * ((y - z0) dot ((G0:real^3^3) ** (y - z0))) / (&4 * tau))) =
       ((exp(--(C * tau)) * exp(--(k * ((y - z0) dot (G0 ** (y - z0))) / (&4 * tau)))) *
        (sqrt(&1 - e1) pow 3 * abs(det S))) / sqrt tau pow 3) /\
      (exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                     b p tau (chart_inv (c:(A->bool)#(A->real^3)) y))) / sqrt tau pow 3 *
       mfd_density atlas c (g(b - tau)) y =
       (exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                      b p tau (chart_inv c y))) *
        mfd_density atlas c (g(b - tau)) y) / sqrt tau pow 3)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[real_div] THEN CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* integrate the pointwise bound over E *)
  MP_TAC(ISPECL
   [`\y. lift(exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) b p tau
                              (chart_inv (c:(A->bool)#(A->real^3)) y))) / sqrt tau pow 3 *
              mfd_density atlas c (g(b - tau)) y)`;
    `S:real^3^3`; `z0:real^3`; `k:real`; `tau:real`; `R:real`;
    `exp(--(C * tau)) * sqrt(&1 - e1) pow 3 * abs(det(S:real^3^3)) / sqrt tau pow 3`]
   P2AU_ELLIPSOID_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && p2au_mentions "mfd_density" th &&
        p2au_mentions "ball" th)) THEN
      UNDISCH_TAC `(y:real^3) IN E` THEN
      UNDISCH_TAC `(E:real^3->bool) SUBSET ball(z0,min rho d1)` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the final arithmetic *)
  ABBREV_TAC `i0 = drop(integral (ball(vec 0:real^3,R)) (\u. lift(exp(--(u dot u)))))` THEN
  ABBREV_TAC `x1 = exp(--(C * tau))` THEN
  ABBREV_TAC `x2 = (sqrt(&1 - e1) * sqrt((&1 - e1) / (&1 + e1))) pow 3` THEN
  SUBGOAL_THEN `&1 - eta <= x1` ASSUME_TAC THENL
   [EXPAND_TAC "x1" THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + --(C * tau)` THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN
    SUBGOAL_THEN `tau * (C + &1) < eta` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= C ==> &0 < C + &1`]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < tau` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 - eta <= x2` ASSUME_TAC THENL
   [MP_TAC(SPEC `e1:real` P2AU_CHORD_FACTOR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(x1 * sqrt(&1 - e1) pow 3 * abs(det(S:real^3^3)) / sqrt tau pow 3) *
    ((&2 * sqrt(tau / k)) pow 3 / abs(det S)) * i0 = &8 * x1 * x2 * i0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(tau / k) = sqrt tau * sqrt((&1 - e1) / (&1 + e1))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SQRT_MUL] THEN AP_TERM_TAC THEN EXPAND_TAC "k" THEN
      REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "x2" THEN
    SUBGOAL_THEN `&0 < sqrt tau` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < abs(det(S:real^3^3))` THEN
    SPEC_TAC(`abs(det(S:real^3^3))`,`dd:real`) THEN
    SPEC_TAC(`sqrt tau`,`st:real`) THEN
    SPEC_TAC(`sqrt((&1 - e1) / (&1 + e1))`,`qq:real`) THEN
    SPEC_TAC(`sqrt(&1 - e1)`,`r1:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    UNDISCH_TAC `&0 < dd` THEN UNDISCH_TAC `&0 < st` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(SPECL [`P:real`; `eta:real`; `x1:real`; `x2:real`; `i0:real`] P2AU_FRV_ARITH) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* FL5 (MT Thm 7.26) from the pieces: value and bounds at each tau           *)
(* (P2AU_FRV_VALUE), monotonicity (P2AU_FRV_MONO) and the limit at 0 from    *)
(* the lower bound P2AU_FRV_LIMINF.  The main theorem: FL2 and W3 imply FL5. *)
(* ------------------------------------------------------------------------- *)

let P2AU_FRV_LIMIT = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p.
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2A_FLOW_LX_CONT_STATEMENT u n /\
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top
     ==> ((\tau. p2a_frv (top,atlas) a b g p tau) ---> sqrt(&4 * pi) pow 3)
         (atreal (&0) within {tau | &0 < tau})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `e / &2`] P2AU_FRV_LIMINF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`] P2AU_FRV_VALUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th ->
    is_forall(concl th) && p2au_mentions "p2a_frv" th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC);;

(* FL5: FL2 and W3 imply FL5.                                                 *)

let P2AU_FLOW_RV = prove
 (`!(u:A->bool) (n:3->bool).
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\ P2B_REQ_P2A_WEAK_STATEMENT u
     ==> P2A_FLOW_RV_STATEMENT u n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `P2A_FLOW_LX_CONT_STATEMENT (u:A->bool) (n:3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_FLOW_LX_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[P2A_FLOW_RV_STATEMENT; DIMINDEX_3] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `tau:real`] P2AU_FRV_VALUE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`tau1:real`; `tau2:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `tau1:real = tau2` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `tau1:real`] P2AU_FRV_VALUE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `tau2:real`] P2AU_FRV_VALUE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC P2AU_FRV_MONO THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `n:3->bool`; `top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                          `g:real->A->real^3^3`; `p:A`; `tau1:real`; `tau2:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2AU_FRV_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `n:3->bool`] THEN ASM_REWRITE_TAC[]]);;

