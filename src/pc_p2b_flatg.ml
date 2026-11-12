(* ========================================================================= *)
(* Unit pc_p2b_flatg: the statement P2B_REQ_FLAT_GAUSS_STATEMENT             *)
(* (pc_p2b_gaussreq), proved as P2AU_FLAT_GAUSS, the Gaussian reduced volume *)
(* of the flat soliton: on a nonempty complete connected flat 3-manifold     *)
(* with Hess f = g/(2 tau) and |grad f|^2 = f/tau the integral of            *)
(* tau^(-3/2) exp(-f) is (4 pi)^(3/2).                                       *)
(*                                                                           *)
(* Route.  Along a geodesic f is quadratic,                                 *)
(* (f o gamma)'' = Hess f(v,v) = |v|^2/(2 tau).  From any x, the point       *)
(* p0 = exp_x(-2 tau grad f(x)) has f(p0) = 0, hence grad f(p0) = 0, and     *)
(* f o exp_p0 = |v|^2/(4 tau).  exp_p0 is a local isometry (flat Jacobi      *)
(* fields), onto (Hopf-Rinow) and injective (grad f(exp v) is the end        *)
(* velocity of the geodesic over 2 tau), so it is an isometry from R^3 with *)
(* the constant metric g(p0), and the integral is the Gaussian.             *)
(* ========================================================================= *)

needs "src/pc_p2b_gaussreq.ml";;
needs "src/pc_geo_iface.ml";;

prioritize_real();;
type_invention_error := true;;

(* Assumption selection by constant name (as p2au_mentions of pc_p2a_flow). *)

let p2au_fg_mentions name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

(* ------------------------------------------------------------------------- *)
(* Gaussian integrals, copied from pc_p2a_frv under new names, to keep this  *)
(* load closure free of the Part 2A L-geometry.  The half line integral of r *)
(* exp(-r^2), the plane Gaussian by polar coordinates, the line Gaussian by  *)
(* Fubini, and the space Gaussian pi^(3/2).                                  *)
(* ------------------------------------------------------------------------- *)

let P2AU_FG_XEXP_INTERVAL = prove
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

let P2AU_FG_EXP_NEG_SQ_LIM = prove
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

let P2AU_FG_XEXP_HALFLINE = prove
 (`((\r. r * exp(--(r pow 2))) has_real_integral inv(&2)) {r | &0 <= r}`,
  ABBREV_TAC `f = \k r. if r IN real_interval[&0,&k] then r * exp(--(r pow 2)) else &0` THEN
  SUBGOAL_THEN `!k. ((f:num->real->real) k has_real_integral
                     (inv(&2) - exp(--(&k pow 2)) / &2)) {r | &0 <= r}`
  (LABEL_TAC "FK") THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN
    SUBGOAL_THEN `real_interval[&0,&k] SUBSET {r | &0 <= r}` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT] THEN
    MATCH_MP_TAC P2AU_FG_XEXP_INTERVAL THEN REWRITE_TAC[REAL_POS];
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
      MATCH_MP_TAC REALLIM_DIV THEN REWRITE_TAC[REALLIM_CONST; P2AU_FG_EXP_NEG_SQ_LIM] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `inv(&2) - &0 / &2 = inv(&2)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral {r | &0 <= r} (\r. r * exp(--(r pow 2))) = inv(&2)`
  (fun th -> SUBST1_TAC(SYM th) THEN ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\k. inv(&2) - exp(--(&k pow 2)) / &2` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]);;

(* The same in real^1 form, times 2 pi.                                       *)

let P2AU_FG_XEXP_HALFLINE_VEC = prove
 (`((\r:real^1. lift(&2 * pi * drop r * exp(--(drop r pow 2)))) has_integral lift pi)
   {r | &0 <= drop r}`,
  SUBGOAL_THEN `IMAGE lift {r | &0 <= r} = {r:real^1 | &0 <= drop r}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE_LIFT_DROP; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[has_real_integral] P2AU_FG_XEXP_HALFLINE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * pi` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[o_DEF; GSYM LIFT_CMUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    AP_TERM_TAC THEN CONV_TAC REAL_FIELD]);;

(* Continuity of the standard Gaussian (as P2A_T81_GAUSS_CONT, pc_p2a_t81). *)

let P2AU_FG_GAUSS_CONT = prove
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

let P2AU_FG_GAUSS_PLANE = prove
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
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN REWRITE_TAC[P2AU_FG_GAUSS_CONT]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "POL" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_CONST; EMPTY_GSPEC; NEGLIGIBLE_EMPTY] THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_EXP] THEN
    USE_THEN "INN" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[integrable_on] THEN EXISTS_TAC `lift pi` THEN
    REWRITE_TAC[P2AU_FG_XEXP_HALFLINE_VEC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_POLAR) THEN
  DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
  USE_THEN "INN" (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN REWRITE_TAC[P2AU_FG_XEXP_HALFLINE_VEC]);;

(* Transfer of the Gaussian between real^M and real^N of equal dimension     *)
(* (HAS_INTEGRAL_TWIZZLE_EQ with the identity permutation).                  *)

let P2AU_FG_GAUSS_TWIZZLE = prove
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
    FIRST_ASSUM(fun th -> if is_eq(concl th) && p2au_fg_mentions "dimindex" th
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
  FIRST_ASSUM(fun th -> if is_eq(concl th) && p2au_fg_mentions "dimindex" th
                        then REWRITE_TAC[EQT_INTRO th] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && p2au_fg_mentions "IMAGE" th
                        then SUBST1_TAC th else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) then REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN REWRITE_TAC[]);;

(* The Gaussian on a product splits: slices exp(-x.x) times the factor.     *)

let P2AU_FG_GAUSS_PASTECART = prove
 (`!(x:real^M) (y:real^N).
     lift(exp(--(pastecart x y dot pastecart x y))) =
     exp(--(x dot x)) % lift(exp(--(y dot y)))`,
  REWRITE_TAC[DOT_PASTECART; REAL_NEG_ADD; REAL_EXP_ADD; GSYM LIFT_CMUL]);;

let P2AU_FG_GAUSS_PRODUCT = prove
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
   [GEN_TAC THEN REWRITE_TAC[P2AU_FG_GAUSS_PASTECART] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE o check (fun th ->
      p2au_fg_mentions "has_integral" th && can (find_term (fun t -> t = `b:real`)) (concl th))) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\w:real^(M,N)finite_sum. lift(exp(--(w dot w))))
                  absolutely_integrable_on (:real^(M,N)finite_sum)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `\w:real^(M,N)finite_sum. lift(exp(--(w dot w)))` FUBINI_TONELLI) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN REWRITE_TAC[P2AU_FG_GAUSS_CONT];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_EXP] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[P2AU_FG_GAUSS_PASTECART] THEN
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

let P2AU_FG_GAUSS_PLANE_HAS = prove
 (`((\z:real^2. lift(exp(--(z dot z)))) has_integral lift pi) (:real^2)`,
  MP_TAC P2AU_FG_GAUSS_PLANE THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

(* The line Gaussian: integrable (its slices of the plane Gaussian are     *)
(* integrable almost everywhere) with integral sqrt(pi) (the product of two *)
(* copies is the plane Gaussian).                                           *)

let P2AU_FG_GAUSS_LINE = prove
 (`(\x:real^1. lift(exp(--(x dot x)))) absolutely_integrable_on (:real^1) /\
   ((\x:real^1. lift(exp(--(x dot x)))) has_integral lift(sqrt pi)) (:real^1)`,
  MP_TAC(SPEC `lift pi` (INST_TYPE [`:(1,1)finite_sum`,`:M`; `:2`,`:N`] P2AU_FG_GAUSS_TWIZZLE)) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2; ARITH; P2AU_FG_GAUSS_PLANE_HAS;
              CONJUNCT1 P2AU_FG_GAUSS_PLANE] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^1. lift(exp(--(x dot x)))) absolutely_integrable_on (:real^1)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE o check (fun th ->
      p2au_fg_mentions "absolutely_integrable_on" th)) THEN
    REWRITE_TAC[P2AU_FG_GAUSS_PASTECART] THEN
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
  MP_TAC(SPECL [`c:real`; `c:real`] (INST_TYPE [`:1`,`:M`; `:1`,`:N`] P2AU_FG_GAUSS_PRODUCT)) THEN
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

let P2AU_FG_GAUSS_SPACE = prove
 (`(\x:real^3. lift(exp(--(x dot x)))) absolutely_integrable_on (:real^3) /\
   ((\x:real^3. lift(exp(--(x dot x)))) has_integral lift(pi * sqrt pi)) (:real^3)`,
  MP_TAC(SPECL [`sqrt pi`; `pi`] (INST_TYPE [`:1`,`:M`; `:2`,`:N`] P2AU_FG_GAUSS_PRODUCT)) THEN
  REWRITE_TAC[P2AU_FG_GAUSS_LINE; P2AU_FG_GAUSS_PLANE_HAS; CONJUNCT1 P2AU_FG_GAUSS_PLANE] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `lift(pi * sqrt pi)` (INST_TYPE [`:(1,2)finite_sum`,`:M`; `:3`,`:N`]
    P2AU_FG_GAUSS_TWIZZLE)) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Chart level: a smooth h along a chart curve sig with velocity V.  With    *)
(* grad h the vector of partial derivatives,                                 *)
(*   (h o sig)' = grad h(sig) . V,                                           *)
(*   (grad h(sig) . V)' = D(grad h)(sig)(V) . V + grad h(sig) . V',           *)
(* and for V' = -Gamma(V,V) this is the lnabla Hessian of p2b_mfd_hess       *)
(* (P2AU_FG_LNABLA_HESS).                                                     *)
(* ------------------------------------------------------------------------- *)

let p2au_fg_grad = new_definition
 `p2au_fg_grad (h:real^N->real) (z:real^N) =
    (lambda i. drop(frechet_derivative (\y. lift(h y)) (at z) (basis i))):real^N`;;

let P2AU_FG_DH_DOT = prove
 (`!(h:real^N->real) z w.
     (\y. lift(h y)) differentiable (at z)
     ==> drop(frechet_derivative (\y. lift(h y)) (at z) w) = p2au_fg_grad h z dot w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  REWRITE_TAC[drop] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[p2au_fg_grad; dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[matrix; LAMBDA_BETA; DIMINDEX_1; LE_REFL; drop]);;

let P2AU_FG_GRAD_SMOOTH = prove
 (`!U (h:real^N->real).
     open U /\ smooth_map_on U (\y. lift(h y)) ==> smooth_map_on U (p2au_fg_grad h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p2au_fg_grad (h:real^N->real)`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[p2au_fg_grad; LAMBDA_BETA] THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

(* First and second derivatives of h along a chart curve sig with velocity *)
(* V: (h o sig)' = grad h . V, and (grad h(sig) . V)' = D grad h (V) . V +    *)
(* grad h . V'.                                                               *)

let P2AU_FG_CURVE_D1 = prove
 (`!(h:real^N->real) (sig:real^1->real^N) vv t.
     (\y. lift(h y)) differentiable (at (sig(lift t))) /\
     (sig has_vector_derivative vv) (at (lift t))
     ==> ((\r. h(sig(lift r))) has_real_derivative (p2au_fg_grad h (sig(lift t)) dot vv))
         (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  MP_TAC(ISPECL [`sig:real^1->real^N`; `\y:real^N. lift(h y)`; `vv:real^N`;
                 `frechet_derivative (\y:real^N. lift(h y)) (at (sig(lift t)))`;
                 `lift t`; `(:real^1)`] GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
  ASM_REWRITE_TAC[WITHIN_UNIV; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  SUBGOAL_THEN `(\y:real^N. lift(h y)) o (sig:real^1->real^N) =
                lift o (\r. h(sig(lift r))) o drop` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y:real^N. lift(h y)) (at ((sig:real^1->real^N)(lift t))) vv =
    lift(p2au_fg_grad h (sig(lift t)) dot vv)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN MATCH_MP_TAC P2AU_FG_DH_DOT THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

let P2AU_FG_CURVE_D2 = prove
 (`!U (h:real^N->real) (sig:real^1->real^N) (V:real->real^N) a t.
     open U /\ smooth_map_on U (\y. lift(h y)) /\ sig(lift t) IN U /\
     (sig has_vector_derivative V t) (at (lift t)) /\
     ((\s. V(drop s)) has_vector_derivative a) (at (lift t))
     ==> ((\r. p2au_fg_grad h (sig(lift r)) dot V r) has_real_derivative
          (frechet_derivative (p2au_fg_grad h) (at (sig(lift t))) (V t) dot V t +
           p2au_fg_grad h (sig(lift t)) dot a)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p2au_fg_grad (h:real^N->real)) differentiable
                (at ((sig:real^1->real^N)(lift t)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[P2AU_FG_GRAD_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. p2au_fg_grad (h:real^N->real) ((sig:real^1->real^N) s)) has_vector_derivative
     frechet_derivative (p2au_fg_grad h) (at (sig(lift t))) ((V:real->real^N) t))
    (at (lift t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sig:real^1->real^N`; `p2au_fg_grad (h:real^N->real)`;
                   `(V:real->real^N) t`;
                   `frechet_derivative (p2au_fg_grad (h:real^N->real))
                      (at ((sig:real^1->real^N)(lift t)))`;
                   `lift t`; `(:real^1)`] GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[WITHIN_UNIV; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. p2au_fg_grad (h:real^N->real) ((sig:real^1->real^N)(lift r))`;
                 `V:real->real^N`;
                 `frechet_derivative (p2au_fg_grad (h:real^N->real))
                    (at ((sig:real^1->real^N)(lift t))) ((V:real->real^N) t)`;
                 `a:real^N`; `t:real`] CMPF_DOT_DERIV) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP];
    AP_TERM_TAC THEN REAL_ARITH_TAC]);;

(* The lnabla form of the Hessian in terms of grad h.                         *)

let P2AU_FG_LNABLA_HESS = prove
 (`!U (G:real^N->real^N^N) (h:real^N->real) y u v.
     open U /\ smooth_map_on U (\z. lift(h z)) /\ y IN U
     ==> lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(h x)) (at z) (w 1))) y
                (\m. if m = 1 then u else v) =
         frechet_derivative (p2au_fg_grad h) (at y) v dot u -
         p2au_fg_grad h y dot christoffel G y v u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN U ==> (\x. lift((h:real^N->real) x)) differentiable (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lnabla; SUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  BETA_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[P2AU_FG_DH_DOT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(p2au_fg_grad (h:real^N->real)) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[P2AU_FG_GRAD_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift(drop(frechet_derivative (\x. lift((h:real^N->real) x)) (at z) u)))
     has_derivative
     (\w. lift(u dot frechet_derivative (p2au_fg_grad h) (at y) w))) (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. lift((u:real^N) dot p2au_fg_grad (h:real^N->real) z)` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open(U:real^N->bool)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[DOT_SYM] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC P2AU_FG_DH_DOT THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM];
      MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_DROP; DOT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The function f along a geodesic.  On a time window around s the chart     *)
(* curve of gamma in a chart c and its chart velocity V solve the geodesic   *)
(* equation (p2au_fg_win).  The derivative of f o gamma at r is              *)
(* p2au_fg_df (grad of f in the chart at gamma r, dotted with the velocity), *)
(* and the derivative of p2au_fg_df at s is the Hessian on (vel, vel).  With *)
(* Hess f = g/(2 tau) this is constant along the geodesic, so f o gamma is   *)
(* a quadratic polynomial (P2AU_FG_GEOD_QUAD).                               *)
(* ------------------------------------------------------------------------- *)

let p2au_fg_win = new_definition
 `p2au_fg_win (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
              (gamma:real->A) J c s d (V:real->real^N) <=>
    &0 < d /\
    !r. abs(r - s) < d
        ==> r IN J /\ gamma r IN FST c /\
            ((\t. SND c (gamma(drop t))) has_vector_derivative V r) (at (lift r)) /\
            ((\t. V(drop t)) has_vector_derivative
             --(christoffel (metric_local atlas c g) (SND c (gamma r)) (V r) (V r)))
            (at (lift r))`;;

let p2au_fg_df = new_definition
 `p2au_fg_df (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) (gamma:real->A) r =
    p2au_fg_grad (\y. f(chart_inv (chart_at atlas (gamma r)) y))
                 (SND(chart_at atlas (gamma r)) (gamma r)) dot mfd_vel atlas gamma r`;;

let P2AU_FG_GEOD_WINDOW = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J c s.
     smooth_manifold_atlas top atlas /\ mfd_geodesic (top,atlas) g gamma J /\
     c IN atlas /\ s IN J /\ gamma s IN FST c
     ==> ?d V. p2au_fg_win atlas g gamma J c s d V`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_open {t | t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))}`
  MP_TAC THENL
   [MATCH_MP_TAC GEOL_CURVE_OPEN_TIMES THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_open; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `mfd_geodesic (top,atlas) (g:A->real^N^N) (gamma:real->A) J` THEN
  REWRITE_TAC[mfd_geodesic] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `V:real->real^N`) THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `V:real->real^N`] THEN
  ASM_REWRITE_TAC[p2au_fg_win] THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(r:real) IN J /\ (gamma:real->A) r IN FST (c:(A->bool)#(A->real^N))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[]);;

let P2AU_FG_WIN_AT = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J c s d (V:real->real^N).
     p2au_fg_win atlas g gamma J c s d V
     ==> &0 < d /\ s IN J /\ gamma s IN FST c /\
         ((\t. SND c (gamma(drop t))) has_vector_derivative V s) (at (lift s)) /\
         ((\t. V(drop t)) has_vector_derivative
          --(christoffel (metric_local atlas c g) (SND c (gamma s)) (V s) (V s)))
         (at (lift s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2au_fg_win] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM]);;

let P2AU_FG_WIN_VEL = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J s d (V:real->real^N).
     p2au_fg_win atlas g gamma J (chart_at atlas (gamma s)) s d V
     ==> mfd_vel atlas gamma s = V s`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2AU_FG_WIN_AT) THEN
  STRIP_TAC THEN REWRITE_TAC[mfd_vel] THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  ASM_REWRITE_TAC[]);;

(* f in a chart is smooth on the chart image. *)

let P2AU_FG_FCHART_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) c.
     smooth_manifold_atlas top atlas /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\ c IN atlas
     ==> open (IMAGE (SND c) (FST c)) /\
         smooth_map_on (IMAGE (SND c) (FST c)) (\y. lift(f(chart_inv c y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST (c:(A->bool)#(A->real^N)) INTER topspace top = FST c`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) (topspace top)
                 (\x. lift((f:A->real) x))` THEN
  REWRITE_TAC[mfd_smooth_on] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* The derivative of f o gamma at r computed in a chart window. *)

let P2AU_FG_CHART_D1 = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (gamma:real->A) J c s d (V:real->real^N) r.
     smooth_manifold_atlas top atlas /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\ c IN atlas /\
     p2au_fg_win atlas g gamma J c s d V /\ abs(r - s) < d
     ==> ((\t. f(gamma t)) has_real_derivative
          p2au_fg_grad (\y. f(chart_inv c y)) (SND c (gamma r)) dot V r) (atreal r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2au_fg_win] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real`; `c:(A->bool)#(A->real^N)`] P2AU_FG_FCHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
    is_forall(concl th) && p2au_fg_mentions "christoffel" th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)`;
                 `\t. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop t))`;
                 `(V:real->real^N) r`; `r:real`] P2AU_FG_CURVE_D1) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\t. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N))
                                (SND c ((gamma:real->A) t)))` THEN
  EXISTS_TAC `d - abs(r - s)` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall(concl th) && p2au_fg_mentions "christoffel" th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let P2AU_FG_PHI_D1 = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (gamma:real->A) J r.
     smooth_manifold_atlas top atlas /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     mfd_geodesic (top,atlas) g gamma J /\ r IN J
     ==> ((\t. f(gamma t)) has_real_derivative p2au_fg_df atlas f gamma r) (atreal r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) r IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) r`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) r)`;
                 `r:real`] P2AU_FG_GEOD_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_TAC `V:real->real^N`)) THEN
  REWRITE_TAC[p2au_fg_df] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP P2AU_FG_WIN_VEL) THEN
  MATCH_MP_TAC P2AU_FG_CHART_D1 THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `J:real->bool`; `r:real`; `d:real`] THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
  FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o MATCH_MP P2AU_FG_WIN_AT));;

(* The derivative of p2au_fg_df along the geodesic is the Hessian. *)

let P2AU_FG_PHI_D2 = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (gamma:real->A) J s.
     smooth_manifold_atlas top atlas /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     mfd_geodesic (top,atlas) g gamma J /\ s IN J
     ==> (p2au_fg_df atlas f gamma has_real_derivative
          p2b_mfd_hess atlas g f (gamma s) (mfd_vel atlas gamma s) (mfd_vel atlas gamma s))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) s IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) s`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s)`;
                 `s:real`] P2AU_FG_GEOD_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_TAC `V:real->real^N`)) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP P2AU_FG_WIN_VEL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_FG_WIN_AT) THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real`; `c:(A->bool)#(A->real^N)`] P2AU_FG_FCHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* p2au_fg_df agrees with the c-chart expression near s *)
  SUBGOAL_THEN
   `!r. abs(r - s) < d
        ==> p2au_fg_grad (\y. (f:A->real)(chart_inv c y)) (SND c ((gamma:real->A) r)) dot
            (V:real->real^N) r =
            p2au_fg_df (atlas:((A->bool)#(A->real^N))->bool) f gamma r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\t. (f:A->real)((gamma:real->A) t)`; `r:real`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AU_FG_CHART_D1 THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `J:real->bool`; `s:real`; `d:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2AU_FG_PHI_D1 THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o CONJUNCT2 o
        GEN_REWRITE_RULE I [p2au_fg_win]) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the Hessian in the chart c *)
  SUBGOAL_THEN
   `p2b_mfd_hess atlas (g:A->real^N^N) (f:A->real) ((gamma:real->A) s)
      ((V:real->real^N) s) (V s) =
    frechet_derivative (p2au_fg_grad (\y. f(chart_inv (c:(A->bool)#(A->real^N)) y)))
      (at (SND c (gamma s))) (V s) dot V s +
    p2au_fg_grad (\y. f(chart_inv c y)) (SND c (gamma s)) dot
      --(christoffel (metric_local atlas c g) (SND c (gamma s)) (V s) (V s))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[p2b_mfd_hess] THEN
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                   `\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)`;
                   `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) s)`;
                   `(V:real->real^N) s`; `(V:real->real^N) s`] P2AU_FG_LNABLA_HESS) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[DOT_RNEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)`;
                 `\t. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop t))`;
                 `V:real->real^N`;
                 `--(christoffel (metric_local atlas (c:(A->bool)#(A->real^N))
                                   (g:A->real^N^N))
                      (SND c ((gamma:real->A) s)) ((V:real->real^N) s) (V s))`;
                 `s:real`] P2AU_FG_CURVE_D2) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\r. p2au_fg_grad (\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))
                    (SND c ((gamma:real->A) r)) dot (V:real->real^N) r` THEN
  EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[]);;

(* Constant second derivative: a quadratic polynomial. *)

let P2AU_FG_QUAD_ODE = prove
 (`!phi d K. (!t. (phi has_real_derivative d t) (atreal t)) /\
             (!t. (d has_real_derivative K) (atreal t))
             ==> !t. phi t = phi(&0) + d(&0) * t + K / &2 * t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. (d:real->real) t = d(&0) + K * t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. (d:real->real) t - K * t`; `(:real)`]
      HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
    REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; WITHINREAL_UNIV] THEN ANTS_TAC THENL
     [X_GEN_TAC `t:real` THEN
      SUBGOAL_THEN `((\t. (d:real->real) t - K * t) has_real_derivative (K - K)) (atreal t)`
      MP_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
         [FIRST_ASSUM(ACCEPT_TAC o SPEC `t:real`); REAL_DIFF_TAC THEN REAL_ARITH_TAC];
        REWRITE_TAC[REAL_SUB_REFL]];
      DISCH_THEN(X_CHOOSE_TAC `c0:real`) THEN X_GEN_TAC `t:real` THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:real` th) THEN MP_TAC(SPEC `&0` th)) THEN
      REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (phi:real->real) t - ((d:real->real)(&0) * t + K / &2 * t pow 2)`;
                 `(:real)`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; WITHINREAL_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN
    SUBGOAL_THEN
     `((\t. (phi:real->real) t - ((d:real->real)(&0) * t + K / &2 * t pow 2))
       has_real_derivative (d t - (d(&0) + K * t))) (atreal t)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [FIRST_ASSUM(ACCEPT_TAC o SPEC `t:real`);
        REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC];
      REWRITE_TAC[GSYM(SPEC `t:real` (ASSUME `!t. (d:real->real) t = d(&0) + K * t`))] THEN
      REWRITE_TAC[REAL_SUB_REFL]];
    DISCH_THEN(X_CHOOSE_TAC `c0:real`) THEN X_GEN_TAC `t:real` THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:real` th) THEN MP_TAC(SPEC `&0` th)) THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* f along the maximal geodesic from x with velocity v, when Hess f is      *)
(* g/(2 tau) and the geodesic is defined for all times.                      *)

let P2AU_FG_GEOD_QUAD = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) tau x v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     (!x u v. x IN topspace top
              ==> p2b_mfd_hess atlas g f x u v = inv(&2 * tau) * (u dot (g x ** v))) /\
     x IN topspace top /\ mfd_geo_maxint (top,atlas) g x v = (:real)
     ==> !t. f(mfd_geo (top,atlas) g x v t) =
             f x +
             (p2au_fg_grad (\y. f(chart_inv (chart_at atlas x) y))
                           (SND(chart_at atlas x) x) dot v) * t +
             (inv(&2 * tau) * (v dot (g x ** v))) / &2 * t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  SUBGOAL_THEN
   `!t. (gam:real->A) t IN topspace top /\
        mfd_vel atlas gam t dot ((g:A->real^N^N)(gam t) ** mfd_vel atlas gam t) =
        v dot (g x ** v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN
    SUBGOAL_THEN `(gam:real->A) t IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `(:real)`] THEN
      ASM_MESON_TAC[IN_UNIV];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `(:real)`; `t:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[IN_UNIV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gam:real->A) t`] GEOD_TNORM_BASIC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(el 2 (CONJUNCTS th))]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(el 2 (CONJUNCTS th))]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (f:A->real)((gam:real->A) t)`;
                 `p2au_fg_df (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) (gam:real->A)`;
                 `inv(&2 * tau) * ((v:real^N) dot ((g:A->real^N^N) x ** v))`]
    P2AU_FG_QUAD_ODE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `t:real` THENL
     [MATCH_MP_TAC P2AU_FG_PHI_D1 THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `(:real)`] THEN
      ASM_MESON_TAC[IN_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `gam:real->A`; `(:real)`; `t:real`]
      P2AU_FG_PHI_D2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[IN_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `t:real` o check (fun th ->
      is_forall(concl th) && p2au_fg_mentions "mfd_vel" th &&
      p2au_fg_mentions "topspace" th)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `t:real` THEN GEN_REWRITE_TAC LAND_CONV [th]) THEN
  ASM_REWRITE_TAC[p2au_fg_df]);;

(* ------------------------------------------------------------------------- *)
(* A zero of f.  |grad f|^2 = lgrad2 = f/tau.  From any x the                *)
(* point p0 = exp_x(-2 tau grad f(x)) has f(p0) = f(x) - tau |grad f(x)|^2   *)
(* = 0 (P2AU_FG_GEOD_QUAD at t = 1), hence grad f(p0) = 0, and then         *)
(* f(exp_p0 v) = v.g(p0)v/(4 tau) for all v (P2AU_FG_EXP_QUAD).              *)
(* ------------------------------------------------------------------------- *)

let P2AU_FG_G_PD = prove
 (`!top atlas (g:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> positive_definite(g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
  REWRITE_TAC[riemannian_metric] THEN
  DISCH_THEN(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`) THEN
  ASM_REWRITE_TAC[metric_field] THEN
  DISCH_THEN(MP_TAC o SPEC `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x` o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  REWRITE_TAC[positive_definite; symmetric_matrix]);;

let P2AU_FG_LGRAD2 = prove
 (`!(G:real^N->real^N^N) (h:real^N->real) y.
     lgrad2 G h y = p2au_fg_grad h y dot (matrix_inv(G y) ** p2au_fg_grad h y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lgrad2; dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[matrix_vector_mul; p2au_fg_grad; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!m n p:real. m * n * p = n * m * p`));;

let P2AU_FG_PD_QUAD_ZERO = prove
 (`!(G:real^N^N) b.
     positive_definite G /\ b dot (matrix_inv G ** b) = &0 ==> b = vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POSITIVE_DEFINITE_IMP_INVERTIBLE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  SUBGOAL_THEN `(G:real^N^N) ** (matrix_inv G ** b) = b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  ASM_CASES_TAC `matrix_inv(G:real^N^N) ** (b:real^N) = vec 0` THENL
   [UNDISCH_TAC `(G:real^N^N) ** (matrix_inv G ** b) = b` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `matrix_inv(G:real^N^N) ** (b:real^N)` o CONJUNCT2 o
      GEN_REWRITE_RULE I [positive_definite]) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    ASM_REWRITE_TAC[REAL_LT_REFL]]);;

let P2AU_FG_ZERO_POINT = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) tau.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ ~(topspace top = {}) /\ &0 < tau /\
     (!x v. x IN topspace top ==> mfd_geo_maxint (top,atlas) g x v = (:real)) /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     (!x u v. x IN topspace top
              ==> p2b_mfd_hess atlas g f x u v = inv(&2 * tau) * (u dot (g x ** v))) /\
     (!x. x IN topspace top
          ==> lgrad2 (metric_local atlas (chart_at atlas x) g)
                     (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x) =
              f x / tau)
     ==> ?p0. p0 IN topspace top /\ f p0 = &0 /\
              p2au_fg_grad (\y. f(chart_inv (chart_at atlas p0) y))
                           (SND(chart_at atlas p0) p0) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `~(tau = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* lgrad2 in gradient form *)
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> p2au_fg_grad (\y. (f:A->real)(chart_inv (chart_at atlas x) y))
                         (SND(chart_at atlas x) x) dot
            (matrix_inv((g:A->real^N^N) x) **
             p2au_fg_grad (\y. f(chart_inv (chart_at atlas x) y))
                          (SND(chart_at atlas x) x)) =
            f x / tau`
  (LABEL_TAC "lg") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> p2au_fg_mentions "lgrad2" th)) THEN
    ASM_REWRITE_TAC[P2AU_FG_LGRAD2; o_DEF] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)` THEN
  ABBREV_TAC `b = p2au_fg_grad (\y. (f:A->real)(chart_inv c0 y))
                               (SND (c0:(A->bool)#(A->real^N)) x0)` THEN
  ABBREV_TAC `G = (g:A->real^N^N) x0` THEN
  ABBREV_TAC `v0 = --(&2 * tau) % (matrix_inv(G:real^N^N) ** (b:real^N))` THEN
  SUBGOAL_THEN `(b:real^N) dot (matrix_inv(G:real^N^N) ** b) = (f:A->real) x0 / tau`
  ASSUME_TAC THENL
   [USE_THEN "lg" (MP_TAC o C MATCH_MP (ASSUME `(x0:A) IN topspace top`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `positive_definite(G:real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC P2AU_FG_G_PD THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POSITIVE_DEFINITE_IMP_INVERTIBLE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  SUBGOAL_THEN
   `(b:real^N) dot v0 = --(&2 * tau) * (b dot (matrix_inv(G:real^N^N) ** b)) /\
    v0 dot ((G:real^N^N) ** v0) = (&2 * tau) pow 2 * (b dot (matrix_inv G ** b))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v0" THEN
    REWRITE_TAC[DOT_RMUL; DOT_LMUL; MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[ASSUME `(G:real^N^N) ** matrix_inv G = mat 1`; MATRIX_VECTOR_MUL_LID] THEN
    SUBGOAL_THEN `(matrix_inv(G:real^N^N) ** (b:real^N)) dot b = b dot (matrix_inv G ** b)`
    SUBST1_TAC THENL [MATCH_ACCEPT_TAC DOT_SYM; ALL_TAC] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `tau:real`; `x0:A`; `v0:real^N`]
    P2AU_FG_GEOD_QUAD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o SPEC `&1`)] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; REAL_POW_ONE] THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN `(f:A->real)(mfd_geo (top,atlas) (g:A->real^N^N) x0 v0 (&1)) = &0`
    ASSUME_TAC THENL
     [REWRITE_TAC[th] THEN UNDISCH_TAC `~(tau = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC]) THEN
  EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^N^N) x0 v0 (&1)` THEN
  ABBREV_TAC `p0 = mfd_geo (top,atlas) (g:A->real^N^N) x0 v0 (&1)` THEN
  SUBGOAL_THEN `(p0:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `(:real)`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x0:A`; `v0:real^N`] MFD_GEO_MAXIMAL) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AU_FG_PD_QUAD_ZERO THEN EXISTS_TAC `(g:A->real^N^N) p0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AU_FG_G_PD THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "lg" (MP_TAC o C MATCH_MP (ASSUME `(p0:A) IN topspace top`)) THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

let P2AU_FG_EXP_QUAD = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) tau p0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ &0 < tau /\
     (!x v. x IN topspace top ==> mfd_geo_maxint (top,atlas) g x v = (:real)) /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     (!x u v. x IN topspace top
              ==> p2b_mfd_hess atlas g f x u v = inv(&2 * tau) * (u dot (g x ** v))) /\
     p0 IN topspace top /\ f p0 = &0 /\
     p2au_fg_grad (\y. f(chart_inv (chart_at atlas p0) y))
                  (SND(chart_at atlas p0) p0) = vec 0
     ==> !v. f(mfd_exp (top,atlas) g p0 v) = (v dot (g p0 ** v)) / (&4 * tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `tau:real`; `p0:A`; `v:real^N`]
    P2AU_FG_GEOD_QUAD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o SPEC `&1`)] THEN
  ASM_REWRITE_TAC[mfd_exp; DOT_LZERO; REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_RID;
                  REAL_POW_ONE] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(tau = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Flat manifolds and d(exp).  If the sectional curvature is 0               *)
(* then t E(t), E parallel along a geodesic, is a Jacobi field (the k = 0    *)
(* analogue of MFD_JACOBI_CONST1 of pc_geo_const), so                        *)
(* d exp_x(v) w = E(1) with E(0) = w (MFD_EXP_DIFFERENTIAL_JACOBI) and       *)
(* d exp_x(v) preserves inner products (P2AU_FG_EXP_DIFF_INNER).  Without a *)
(* curvature assumption, d exp_x(v) v is the end velocity of the geodesic    *)
(* (tangential Jacobi field t gamma'(t), P2AU_FG_EXP_DIFF_RADIAL).          *)
(* ------------------------------------------------------------------------- *)

let P2AU_FG_JACOBI_FLAT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:real->real^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas g x u v = &0) /\
     mfd_geodesic (top,atlas) g gamma J /\ mfd_parallel atlas g gamma J E
     ==> mfd_jacobi atlas g gamma J (\t. t % E t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t. t IN J ==> (gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `mfd_parallel (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                              (gamma:real->A) J (E:real->real^N)`) THEN
  REWRITE_TAC[mfd_parallel] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
              (\t. t % (E:real->real^N) t) t = E t`
  (LABEL_TAC "c1") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `E:real->real^N`; `\t:real. t`; `&1`; `t:real`]
      CMPG_COVD_SCALAR) THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ID; VECTOR_MUL_RZERO; VECTOR_ADD_RID;
                 VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_jacobi] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPG_FIELD_DIFF_SCALAR THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[REAL_DIFFERENTIABLE_ID];
    MATCH_MP_TAC CMPG_FIELD_DIFF_LOCAL THEN EXISTS_TAC `E:real->real^N` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "c1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
      (mfd_covd atlas g gamma (\t. t % (E:real->real^N) t)) t =
    mfd_covd atlas g gamma E t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPG_COVD_LOCAL THEN
    MP_TAC(ASSUME `real_open (J:real->bool)`) THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "c1" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`; `&0`]
    MFD_SECTIONAL_CONST_RIEMANN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID]);;

let P2AU_FG_EXP_DIFF_PAR = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas g x u v = &0) /\
     x IN topspace top /\ v IN mfd_exp_dom (top,atlas) g x
     ==> ?E. mfd_parallel atlas g (mfd_geo (top,atlas) g x v)
                          (mfd_geo_maxint (top,atlas) g x v) E /\
             E(&0) = w /\
             mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) g x) v w = E(&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `I0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN (I0:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "I0" THEN
    MP_TAC(ASSUME `(v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`) THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`; `&0`; `w:real^N`]
    MFD_PARALLEL_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  EXISTS_TAC `E:real->real^N` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `mfd_parallel atlas (g:A->real^N^N) (gam:real->A) I0 (E:real->real^N)`) THEN
  REWRITE_TAC[mfd_parallel] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `w:real^N`;
                 `\t. t % (E:real->real^N) t`] MFD_EXP_DIFFERENTIAL_JACOBI) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2AU_FG_JACOBI_FLAT THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`;
                     `E:real->real^N`; `\t:real. t`; `&1`; `&0`] CMPG_COVD_SCALAR) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ID; VECTOR_MUL_LZERO; VECTOR_ADD_RID;
                   VECTOR_MUL_LID]];
    SIMP_TAC[]]);;

let P2AU_FG_EXP_DIFF_INNER = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w1 w2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas g x u v = &0) /\
     x IN topspace top /\ v IN mfd_exp_dom (top,atlas) g x
     ==> mfd_differential (open_set_atlas (:real^N)) atlas
           (mfd_exp (top,atlas) g x) v w1 dot
         (g(mfd_exp (top,atlas) g x v) **
          mfd_differential (open_set_atlas (:real^N)) atlas
            (mfd_exp (top,atlas) g x) v w2) =
         w1 dot (g x ** w2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `w1:real^N`] P2AU_FG_EXP_DIFF_PAR) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `w2:real^N`] P2AU_FG_EXP_DIFF_PAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E2:real->real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `E1:real->real^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` ASSUME_TAC THENL
   [MP_TAC(ASSUME `(v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`) THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x v`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_exp] THEN
  TRANS_TAC EQ_TRANS
   `(E1:real->real^N)(&0) dot
    ((g:A->real^N^N)(mfd_geo (top,atlas) g x v (&0)) ** (E2:real->real^N)(&0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARALLEL_INNER THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let P2AU_FG_EXP_DIFF_RADIAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\
     v IN mfd_exp_dom (top,atlas) g x
     ==> mfd_differential (open_set_atlas (:real^N)) atlas
           (mfd_exp (top,atlas) g x) v v =
         mfd_vel atlas (mfd_geo (top,atlas) g x v) (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `I0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN (I0:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "I0" THEN
    MP_TAC(ASSUME `(v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`) THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`]
    MFD_GEODESIC_VEL_PARALLEL) THEN
  ASM_REWRITE_TAC[mfd_parallel] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `v:real^N`;
                 `\t. t % mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) t`]
    MFD_EXP_DIFFERENTIAL_JACOBI) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`; `&0`; `&1`]
        MFD_JACOBI_TANGENTIAL) THEN
      ASM_REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LID];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`;
                     `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A)`;
                     `\t:real. t`; `&1`; `&0`]
        CMPG_COVD_SCALAR) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ID; VECTOR_MUL_LZERO; VECTOR_ADD_RID;
                   VECTOR_MUL_LID]];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Injectivity of exp_p0.  Differentiating f o exp_p0 = Q,                   *)
(* Q(v) = v.G0 v/(4 tau), in the chart at exp(v) gives                       *)
(* grad f(exp v) . d exp_v(h) = v.G0 h/(2 tau) (P2AU_FG_GRAD_EXP_DIR); with  *)
(* d exp_v an isometry (onto, being injective and linear) this is            *)
(* grad f(exp v) = g(exp v) d exp_v(v)/(2 tau) (P2AU_FG_GRAD_EXP_VEC).  If    *)
(* exp v1 = exp v2 the two geodesics have the same end point and end        *)
(* velocity d exp_v(v) (P2AU_FG_EXP_DIFF_RADIAL), so they agree and         *)
(* v1 = v2 (P2AU_FG_EXP_INJ).                                                *)
(* ------------------------------------------------------------------------- *)

let p2au_fg_hyp = new_definition
 `p2au_fg_hyp (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
              (g:A->real^N^N) (f:A->real) tau <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas g /\ &0 < tau /\
    (!x v. x IN topspace top ==> mfd_geo_maxint (top,atlas) g x v = (:real)) /\
    (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
             ==> mfd_sectional atlas g x u v = &0) /\
    mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
    (!x u v. x IN topspace top
             ==> p2b_mfd_hess atlas g f x u v = inv(&2 * tau) * (u dot (g x ** v)))`;;

let P2AU_FG_GEO_BASIC = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\
     mfd_geo_maxint (top,atlas) g x v = (:real)
     ==> mfd_geodesic (top,atlas) g (mfd_geo (top,atlas) g x v) (:real) /\
         mfd_geo (top,atlas) g x v (&0) = x /\
         mfd_vel atlas (mfd_geo (top,atlas) g x v) (&0) = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P2AU_FG_MATVEC_CANCEL = prove
 (`!(A:real^N^N) x y. invertible A /\ A ** x = A ** y ==> x = y`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^N. matrix_inv(A:real^N^N) ** z` o check
    (fun th -> concl th = `(A:real^N^N) ** (x:real^N) = A ** y`)) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;

(* exp in the chart at exp(v): an open set of v's and the derivative. *)

let P2AU_FG_EXP_CHART_DIFF = prove
 (`!top atlas (g:A->real^N^N) (p:A) v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ p IN topspace top /\
     mfd_exp_dom (top,atlas) g p = (:real^N)
     ==> mfd_exp (top,atlas) g p v IN topspace top /\
         open {w | mfd_exp (top,atlas) g p w IN
                   FST(chart_at atlas (mfd_exp (top,atlas) g p v))} /\
         ((\w. SND(chart_at atlas (mfd_exp (top,atlas) g p v))
                  (mfd_exp (top,atlas) g p w))
          has_derivative
          mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g p) v)
         (at v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `E = mfd_exp (top,atlas) (g:A->real^N^N) p` THEN
  SUBGOAL_THEN `(E:real^N->A) v IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map]) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(E:real^N->A) v`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((E:real^N->A) v)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(SND (c:(A->bool)#(A->real^N)) o (E:real^N->A) o
                 chart_inv ((:real^N),(\x:real^N. x))) = (\w. SND c (E w))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `((:real^N),(\x:real^N. x)) IN open_set_atlas (:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(:real^N)`; `E:real^N->A`; `((:real^N),(\x:real^N. x))`;
                 `c:(A->bool)#(A->real^N)`; `v:real^N`] GEOI_SMOOTH_REP_DIFF) THEN
  ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_UNIV;
                  FST; SND; IN_UNIV; INTER_UNIV; IMAGE_ID; IN_ELIM_THM] THEN
  SIMP_TAC[]);;

(* The derivative of the quadratic form k v.G v. *)

let P2AU_FG_QFORM_DERIV = prove
 (`!(G:real^N^N) k v.
     ((\w. lift(k * (w dot (G ** w)))) has_derivative
      (\h. lift(k * (v dot (G ** h) + h dot (G ** v))))) (at v)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\(x:real^N) (y:real^N). lift(x dot ((G:real^N^N) ** y))`;
                 `\w:real^N. w`; `\w:real^N. w`; `\h:real^N. h`; `\h:real^N. h`;
                 `v:real^N`] HAS_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[GEOG_DOT_BILINEAR; HAS_DERIVATIVE_ID] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM LIFT_ADD]) THEN
  MP_TAC(ISPECL [`\x:real^N. lift(x dot ((G:real^N^N) ** x))`;
                 `\d:real^N. lift(v dot ((G:real^N^N) ** d) + d dot (G ** v))`;
                 `at (v:real^N)`; `k:real`] HAS_DERIVATIVE_CMUL) THEN
  ASM_REWRITE_TAC[GSYM LIFT_CMUL]);;

(* grad f(exp v) . d exp_v(h) = v.G0 h/(2 tau). *)

let P2AU_FG_GRAD_EXP_DIR = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) tau p0 v h.
     p2au_fg_hyp top atlas g f tau /\ p0 IN topspace top /\
     (!v. f(mfd_exp (top,atlas) g p0 v) = (v dot (g p0 ** v)) / (&4 * tau))
     ==> p2au_fg_grad
           (\y. f(chart_inv (chart_at atlas (mfd_exp (top,atlas) g p0 v)) y))
           (SND(chart_at atlas (mfd_exp (top,atlas) g p0 v))
               (mfd_exp (top,atlas) g p0 v)) dot
         mfd_differential (open_set_atlas (:real^N)) atlas
           (mfd_exp (top,atlas) g p0) v h =
         inv(&2 * tau) * (v dot (g p0 ** h))`,
  REWRITE_TAC[p2au_fg_hyp] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) p0 = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `v:real^N`] P2AU_FG_EXP_CHART_DIFF) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `E = mfd_exp (top,atlas) (g:A->real^N^N) p0` THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((E:real^N->A) v)` THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^N))
                    (atlas:((A->bool)#(A->real^N))->bool) (E:real^N->A) v` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(E:real^N->A) v`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real`; `c:(A->bool)#(A->real^N)`] P2AU_FG_FCHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) has_derivative
     frechet_derivative (\y. lift(f(chart_inv c y))) (at (SND c ((E:real^N->A) v))))
    (at (SND c (E v)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift((f:A->real)((E:real^N->A) w))) has_derivative
     (frechet_derivative (\y. lift(f(chart_inv (c:(A->bool)#(A->real^N)) y)))
                         (at (SND c (E v))) o (D:real^N->real^N))) (at v)`
  (LABEL_TAC "d1") THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `(\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) o
                (\w. SND c ((E:real^N->A) w))` THEN
    EXISTS_TAC `{w | (E:real^N->A) w IN FST (c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[o_THM];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift((f:A->real)((E:real^N->A) w))) has_derivative
     (\h. lift(inv(&4 * tau) * (v dot ((g:A->real^N^N) p0 ** h) + h dot (g p0 ** v)))))
    (at v)`
  (LABEL_TAC "d2") THENL
   [SUBGOAL_THEN `(\w. lift((f:A->real)((E:real^N->A) w))) =
                  (\w. lift(inv(&4 * tau) * (w dot ((g:A->real^N^N) p0 ** w))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^N` THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[real_div] THEN MATCH_ACCEPT_TAC REAL_MUL_SYM;
      REWRITE_TAC[P2AU_FG_QFORM_DERIV]];
    ALL_TAC] THEN
  USE_THEN "d1" (fun th1 -> USE_THEN "d2" (fun th2 ->
    MP_TAC(MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT (CONJ th1 th2)))) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop` o SPEC `h:real^N`) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)`;
                 `SND (c:(A->bool)#(A->real^N)) ((E:real^N->A) v)`;
                 `(D:real^N->real^N) h`] P2AU_FG_DH_DOT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(h:real^N) dot ((g:A->real^N^N) p0 ** v) = v dot (g p0 ** h)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`] GEOG_G_SYM_POS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`h:real^N`; `v:real^N`] o CONJUNCT1) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(tau = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* The gradient of f at exp(v) in vector form. *)

let P2AU_FG_GRAD_EXP_VEC = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) tau p0 v.
     p2au_fg_hyp top atlas g f tau /\ p0 IN topspace top /\
     (!v. f(mfd_exp (top,atlas) g p0 v) = (v dot (g p0 ** v)) / (&4 * tau))
     ==> p2au_fg_grad
           (\y. f(chart_inv (chart_at atlas (mfd_exp (top,atlas) g p0 v)) y))
           (SND(chart_at atlas (mfd_exp (top,atlas) g p0 v))
               (mfd_exp (top,atlas) g p0 v)) =
         inv(&2 * tau) %
         (g(mfd_exp (top,atlas) g p0 v) **
          mfd_differential (open_set_atlas (:real^N)) atlas
            (mfd_exp (top,atlas) g p0) v v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2au_fg_hyp]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) p0 = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `tau:real`; `p0:A`; `v:real^N`]
    P2AU_FG_GRAD_EXP_DIR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `v:real^N`] P2AU_FG_EXP_CHART_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `v:real^N`] P2AU_FG_EXP_DIFF_INNER) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_exp (top,atlas) (g:A->real^N^N) p0 v`]
    GEOG_G_SYM_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `E = mfd_exp (top,atlas) (g:A->real^N^N) p0` THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^N))
                    (atlas:((A->bool)#(A->real^N))->bool) (E:real^N->A) v` THEN
  ABBREV_TAC `B = p2au_fg_grad
                    (\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                     ((E:real^N->A) v)) y))
                    (SND(chart_at atlas (E v)) (E v))` THEN
  ABBREV_TAC `Gz = (g:A->real^N^N)((E:real^N->A) v)` THEN
  SUBGOAL_THEN `linear(D:real^N->real^N)` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative] o
      check (fun th -> p2au_fg_mentions "has_derivative" th));
    ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. (D:real^N->real^N) y1 = D y2 ==> y1 = y2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_INJECTIVE_0] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `y:real^N = vec 0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`] GEOD_G_POS_DEF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`y:real^N`; `y:real^N`] o check (fun th ->
      is_forall(concl th) && p2au_fg_mentions "dot" th &&
      can (find_term ((=) `D:real^N->real^N`)) (concl th))) THEN
    REWRITE_TAC[ASSUME `(D:real^N->real^N) y = vec 0`; DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `D:real^N->real^N` LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  ABBREV_TAC `u = (B:real^N) - inv(&2 * tau) % ((Gz:real^N^N) ** (D:real^N->real^N) v)` THEN
  SUBGOAL_THEN `!h. (u:real^N) dot (D:real^N->real^N) h = &0` ASSUME_TAC THENL
   [X_GEN_TAC `h:real^N` THEN EXPAND_TAC "u" THEN
    REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN
    SUBGOAL_THEN
     `((Gz:real^N^N) ** (D:real^N->real^N) v) dot D h = v dot ((g:A->real^N^N) p0 ** h)`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS `(D:real^N->real^N) v dot ((Gz:real^N^N) ** D h)` THEN
      CONJ_TAC THENL
       [TRANS_TAC EQ_TRANS `(D:real^N->real^N) h dot ((Gz:real^N^N) ** D v)` THEN
        CONJ_TAC THENL
         [MATCH_ACCEPT_TAC DOT_SYM;
          FIRST_ASSUM(MATCH_ACCEPT_TAC o check (fun th ->
            is_forall(concl th) && p2au_fg_mentions "dot" th &&
            can (find_term ((=) `Gz:real^N^N`)) (concl th) &&
            not (p2au_fg_mentions "mfd_differential" th) &&
            not (can (find_term ((=) `D:real^N->real^N`)) (concl th))))];
        FIRST_ASSUM(MATCH_ACCEPT_TAC o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `D:real^N->real^N`)) (concl th) &&
          can (find_term ((=) `Gz:real^N^N`)) (concl th)))];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
    is_forall(concl th) && is_exists(snd(strip_forall(concl th))))) THEN
  DISCH_THEN(X_CHOOSE_TAC `h0:real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h0:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `u:real^N`)) (concl th))) THEN
  ASM_REWRITE_TAC[DOT_EQ_0]);;

(* exp_p0 is injective. *)

let P2AU_FG_EXP_INJ = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) tau p0 v1 v2.
     p2au_fg_hyp top atlas g f tau /\ p0 IN topspace top /\
     (!v. f(mfd_exp (top,atlas) g p0 v) = (v dot (g p0 ** v)) / (&4 * tau)) /\
     mfd_exp (top,atlas) g p0 v1 = mfd_exp (top,atlas) g p0 v2
     ==> v1 = v2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2au_fg_hyp]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) p0 = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) (g:A->real^N^N) p0) v1 v1 =
    mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) g p0) v2 v2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_FG_MATVEC_CANCEL THEN
    EXISTS_TAC `(g:A->real^N^N)(mfd_exp (top,atlas) g p0 v2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC POSITIVE_DEFINITE_IMP_INVERTIBLE THEN MATCH_MP_TAC P2AU_FG_G_PD THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p0:A`; `v2:real^N`] P2AU_FG_EXP_CHART_DIFF) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `tau:real`; `p0:A`; `v1:real^N`]
      P2AU_FG_GRAD_EXP_VEC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `tau:real`; `p0:A`; `v2:real^N`]
      P2AU_FG_GRAD_EXP_VEC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0; REAL_ENTIRE; REAL_OF_NUM_EQ;
                ARITH_EQ] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^N^N) p0 v1) (&1) =
    mfd_vel atlas (mfd_geo (top,atlas) g p0 v2) (&1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `v1:real^N`] P2AU_FG_EXP_DIFF_RADIAL) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `v2:real^N`] P2AU_FG_EXP_DIFF_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `v1:real^N`] P2AU_FG_GEO_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `v2:real^N`] P2AU_FG_GEO_BASIC) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. mfd_geo (top,atlas) (g:A->real^N^N) p0 v1 t = mfd_geo (top,atlas) g p0 v2 t`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p0 v1`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p0 v2`; `(:real)`; `(:real)`;
                   `&1`] MFD_GEODESIC_UNIQUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_UNIV] THEN
      UNDISCH_TAC `mfd_exp (top,atlas) (g:A->real^N^N) p0 v1 = mfd_exp (top,atlas) g p0 v2` THEN
      REWRITE_TAC[mfd_exp];
      REWRITE_TAC[IN_UNIV; INTER_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p0 v1 = mfd_geo (top,atlas) g p0 v2`
  MP_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM
    `\gm:real->A. mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gm (&0)`) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The map exp_p0 is an isometry from real^N with the constant metric        *)
(* g(p0) onto the manifold.  It is a local isometry (P2AU_FG_EXP_DIFF_INNER  *)
(* and GEOI_LISOM_FROM_DIFF), so its differentials are invertible            *)
(* (GEOH_LISOM_DET); it is onto (MFD_COMPLETE_EXP_ONTO) and injective        *)
(* (P2AU_FG_EXP_INJ), hence a diffeomorphism (GEO_BIJECTIVE_LOCAL_DIFFEO).   *)
(* ------------------------------------------------------------------------- *)

let P2AU_FG_EUCLID_METRIC_LOCAL = prove
 (`!S (g:real^N->real^N^N) y.
     open S /\ y IN S ==> metric_local {(S,\x:real^N. x)} (S,\x. x) g y = g y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean S) {(S,\x:real^N. x)}`
  ASSUME_TAC THENL [ASM_SIMP_TAC[GRGD_EUCLID_ATLAS]; ALL_TAC] THEN
  REWRITE_TAC[metric_local] THEN
  SUBGOAL_THEN `chart_inv (S:real^N->bool,\x:real^N. x) y = y` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MFDM_CHART_INV_ID]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_at {(S,\x:real^N. x)} (y:real^N) = (S,\x. x)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`; `{(S:real^N->bool,\x:real^N. x)}`;
                   `y:real^N`] CHART_AT) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_SING] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`; `{(S:real^N->bool,\x:real^N. x)}`;
                 `S:real^N->bool`; `\x:real^N. x`; `y:real^N`] CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let P2AU_FG_CONST_METRIC = prove
 (`!G:real^N^N. positive_definite G ==> riemannian_metric (open_set_atlas (:real^N)) (\x. G)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric; open_set_atlas; IN_SING] THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; metric_field; OPEN_UNIV] THEN
  SIMP_TAC[P2AU_FG_EUCLID_METRIC_LOCAL; OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\y:real^N. (vectorize:real^N^N->real^(N,N)finite_prod) G` THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; o_THM; IN_UNIV] THEN
    SIMP_TAC[P2AU_FG_EUCLID_METRIC_LOCAL; OPEN_UNIV; IN_UNIV];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [positive_definite]) THEN
    REWRITE_TAC[symmetric_matrix] THEN SIMP_TAC[]]);;

let P2AU_FG_EXP_LISOM = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) tau p0.
     p2au_fg_hyp top atlas g f tau /\ p0 IN topspace top
     ==> mfd_local_isometry (euclidean,open_set_atlas (:real^N)) (\x. g p0)
                            (top,atlas) g (:real^N) (mfd_exp (top,atlas) g p0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2au_fg_hyp]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) p0 = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN
  ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_UNIV;
                  IN_UNIV] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AU_FG_CONST_METRIC THEN MATCH_MP_TAC P2AU_FG_G_PD THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `v:real^N`] P2AU_FG_EXP_CHART_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `v:real^N`] P2AU_FG_EXP_DIFF_INNER) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^N))
                    (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) (g:A->real^N^N) p0) v` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `linear(D:real^N->real^N)` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative] o
      check (fun th -> p2au_fg_mentions "has_derivative" th));
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `w2:real^N` THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `w1:real^N` THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let P2AU_FG_EXP_ISOMETRY = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) tau p0.
     p2au_fg_hyp top atlas g f tau /\ mfd_complete (top,atlas) g /\
     connected_space top /\ p0 IN topspace top /\
     (!v. f(mfd_exp (top,atlas) g p0 v) = (v dot (g p0 ** v)) / (&4 * tau))
     ==> ?Ei. mfd_isometry (euclidean,open_set_atlas (:real^N)) (\x. g p0)
                           (top,atlas) g (mfd_exp (top,atlas) g p0) Ei`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2au_fg_hyp]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) p0 = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `tau:real`; `p0:A`] P2AU_FG_EXP_LISOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^N)) (\x:real^N. (g:A->real^N^N) p0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_FG_CONST_METRIC THEN MATCH_MP_TAC P2AU_FG_G_PD THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) p0`] GEO_BIJECTIVE_LOCAL_DIFFEO) THEN
  ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_COMPLETE_EXP_ONTO THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AU_FG_EXP_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `f:A->real`; `tau:real`; `p0:A`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^N` THEN MATCH_MP_TAC GEOH_LISOM_DET THEN
      MAP_EVERY EXISTS_TAC [`euclidean:(real^N)topology`; `\x:real^N. (g:A->real^N^N) p0`;
                            `top:A topology`; `g:A->real^N^N`; `(:real^N)`] THEN
      ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; IN_UNIV]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Ei:A->real^N`) THEN EXISTS_TAC `Ei:A->real^N` THEN
  REWRITE_TAC[mfd_isometry] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN]; ALL_TAC] THEN
  UNDISCH_TAC `mfd_local_isometry (euclidean,open_set_atlas (:real^N))
                 (\x:real^N. (g:A->real^N^N) p0) (top,atlas) g (:real^N)
                 (mfd_exp (top,atlas) g p0)` THEN
  REWRITE_TAC[mfd_local_isometry; INTER_UNIV] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Gaussian on (real^3, G0).  With G0 = S^T S and the                    *)
(* linear change y = M u, M = 2 sqrt(tau) S^-1, the integral of              *)
(* exp(-y.G0 y/(4 tau)) is |det M| pi^(3/2) (P2AU_FG_GAUSS_G0, the whole-     *)
(* space version of P2AU_GAUSS_ELLIPSOID of pc_p2a_frv); P2AU_FG_DOT_COV is  *)
(* P2A_T81_DOT_COV of pc_p2a_t81.  The density of (real^3, G0) is            *)
(* sqrt(det G0) = |det S|, so tau^(-3/2) exp(-y.G0 y/(4 tau)) has integral   *)
(* (4 pi)^(3/2) (P2AU_FG_MODEL_INTEGRAL).                                    *)
(* ------------------------------------------------------------------------- *)

let P2AU_FG_DOT_COV = prove
 (`!(A:real^N^N) Z. (A ** Z) dot (A ** Z) = Z dot ((transp A ** A) ** Z)`,
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

let P2AU_FG_GAUSS_G0 = prove
 (`!(S:real^3^3) tau.
     invertible S /\ &0 < tau
     ==> (\y. lift(exp(--((y dot ((transp S ** S) ** y)) / (&4 * tau)))))
         absolutely_integrable_on (:real^3) /\
         integral (:real^3)
           (\y. lift(exp(--((y dot ((transp S ** S) ** y)) / (&4 * tau))))) =
         lift((&2 * sqrt tau) pow 3 / abs(det S) * (pi * sqrt pi))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `M = (&2 * sqrt tau) %% matrix_inv(S:real^3^3)` THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3^3) ** (M:real^3^3) = (&2 * sqrt tau) %% mat 1` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[MATRIX_MUL_RMUL] THEN ASM_SIMP_TAC[MATRIX_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:real^3. lift(exp(--((((M:real^3^3) ** u) dot
                              ((transp(S:real^3^3) ** S) ** (M ** u))) / (&4 * tau)))) =
               lift(exp(--(u dot u)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM P2AU_FG_DOT_COV; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_LMUL; DOT_RMUL] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `sqrt tau pow 2 = tau` THEN UNDISCH_TAC `&0 < tau` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(det(M:real^3^3)) = (&2 * sqrt tau) pow 3 / abs(det(S:real^3^3)) /\
                ~(det M = &0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `det(M:real^3^3) = (&2 * sqrt tau) pow 3 / det(S:real^3^3)` SUBST1_TAC THENL
     [EXPAND_TAC "M" THEN REWRITE_TAC[DET_CMUL; DIMINDEX_3; DET_MATRIX_INV; real_div];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INVERTIBLE_DET_NZ]) THEN
    SUBGOAL_THEN `&0 < (&2 * sqrt tau) pow 3` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_DIV_EQ_0; REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\u:real^3. (M:real^3^3) ** u) (:real^3) = (:real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^3` THEN
    EXISTS_TAC `matrix_inv(M:real^3^3) ** (y:real^3)` THEN
    SUBGOAL_THEN `invertible(M:real^3^3)` MP_TAC THENL
     [ASM_REWRITE_TAC[INVERTIBLE_DET_NZ]; ALL_TAC] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^3. lift(exp(--((y dot ((transp(S:real^3^3) ** S) ** y)) /
                                          (&4 * tau))))`;
                 `\u:real^3. (M:real^3^3) ** u`; `(:real^3)`]
                ABSOLUTELY_INTEGRABLE_ON_LINEAR_IMAGE) THEN
  MP_TAC(ISPECL [`\y:real^3. lift(exp(--((y dot ((transp(S:real^3^3) ** S) ** y)) /
                                          (&4 * tau))))`;
                 `\u:real^3. (M:real^3^3) ** u`; `(:real^3)`]
                INTEGRAL_CHANGE_OF_VARIABLES_LINEAR) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  REWRITE_TAC[P2AU_FG_GAUSS_SPACE] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC P2AU_FG_GAUSS_SPACE THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE o CONJUNCT2) THEN
  REWRITE_TAC[GSYM LIFT_CMUL]);;

(* The reduced-volume integrand on (real^3, G0). *)

let P2AU_FG_MODEL_INTEGRAL = prove
 (`!(G0:real^3^3) tau.
     positive_definite G0 /\ &0 < tau
     ==> mfd_has_integral (euclidean,open_set_atlas (:real^3)) (\x. G0)
           (\v. exp(--((v dot (G0 ** v)) / (&4 * tau))) / sqrt tau pow 3) (:real^3)
           (sqrt(&4 * pi) pow 3)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [POSITIVE_DEFINITE_COVARIANCE_EQ]) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^3^3`; `tau:real`] P2AU_FG_GAUSS_G0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(det(G0:real^3^3)) = abs(det(S:real^3^3)) /\ &0 < abs(det S)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INVERTIBLE_DET_NZ]) THEN
    UNDISCH_TAC `transp(S:real^3^3) ** S = G0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[DET_MUL; DET_TRANSP; GSYM REAL_POW_2; POW_2_SQRT_ABS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(\x:real^3. G0):real^3->real^3^3`;
                 `\v:real^3. exp(--((v dot ((G0:real^3^3) ** v)) / (&4 * tau))) /
                             sqrt tau pow 3`;
                 `((:real^3),(\x:real^3. x))`; `(:real^3)`; `sqrt(&4 * pi) pow 3`]
    MFD_HAS_INTEGRAL_CHART) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; FST; SUBSET_REFL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AU_FG_CONST_METRIC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[open_set_atlas; IN_SING]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SND; IMAGE_ID; LEBESGUE_MEASURABLE_UNIV] THEN
  SUBGOAL_THEN
   `mfd_chart_integrand (open_set_atlas (:real^3)) (\x:real^3. G0)
      (\v. exp(--((v dot ((G0:real^3^3) ** v)) / (&4 * tau))) / sqrt tau pow 3)
      ((:real^3),(\x:real^3. x)) =
    (\y. (abs(det(S:real^3^3)) / sqrt tau pow 3) %
         lift(exp(--((y dot (G0 ** y)) / (&4 * tau)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; mfd_chart_integrand; mfd_density] THEN
    X_GEN_TAC `y:real^3` THEN
    SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV; open_set_atlas; P2AU_FG_EUCLID_METRIC_LOCAL;
             OPEN_UNIV] THEN
    ASM_REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_CMUL; INTEGRAL_CMUL;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN
  SUBGOAL_THEN `sqrt(&4 * pi) = &2 * sqrt pi /\ sqrt pi pow 2 = pi` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_MUL; REAL_POS; PI_POS_LE; SQRT_POW_2] THEN
    REWRITE_TAC[REAL_ARITH `&4 = &2 pow 2`] THEN
    SIMP_TAC[POW_2_SQRT; REAL_POS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < sqrt tau` THEN UNDISCH_TAC `&0 < abs(det(S:real^3^3))` THEN
  UNDISCH_TAC `sqrt pi pow 2 = pi` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The main theorem.  Completeness gives complete geodesics                  *)
(* (MFD_HOPF_RINOW); p0 is the zero of f (P2AU_FG_ZERO_POINT); exp_p0 is an *)
(* isometry from (real^3, g(p0)) (P2AU_FG_EXP_ISOMETRY), which moves the    *)
(* integral to the model (MFD_HAS_INTEGRAL_ISOMETRY), where it is the        *)
(* Gaussian (4 pi)^(3/2) (P2AU_FG_MODEL_INTEGRAL).  So the integral equals   *)
(* sqrt(4 pi)^3 and the inequality of the statement holds with equality.     *)
(* ------------------------------------------------------------------------- *)

let P2AU_FLAT_GAUSS = prove
 (`!w:B->bool. P2B_REQ_FLAT_GAUSS_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_FLAT_GAUSS_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `f:B->real`; `tau:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2au_fg_hyp (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                            (g:B->real^3^3) f tau`
  ASSUME_TAC THENL [REWRITE_TAC[p2au_fg_hyp] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `f:B->real`; `tau:real`] P2AU_FG_ZERO_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `f:B->real`; `tau:real`; `p0:B`] P2AU_FG_EXP_QUAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `f:B->real`; `tau:real`; `p0:B`]
    P2AU_FG_EXP_ISOMETRY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Ei:B->real^3`) THEN
  SUBGOAL_THEN `positive_definite((g:B->real^3^3) p0)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_FG_G_PD THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) (g:B->real^3^3)
      (\y. exp(--((f:B->real) y)) / sqrt tau pow 3) (topspace top)
      (sqrt(&4 * pi) pow 3)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `(\x:real^3. (g:B->real^3^3) p0)`;
                   `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `mfd_exp (top,atlas) (g:B->real^3^3) p0`;
                   `Ei:B->real^3`; `\y:B. exp(--((f:B->real) y)) / sqrt tau pow 3`;
                   `(:real^3)`; `sqrt(&4 * pi) pow 3`] MFD_HAS_INTEGRAL_ISOMETRY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; TOPSPACE_EUCLIDEAN; SUBSET_REFL] THEN
      MATCH_MP_TAC P2AU_FG_CONST_METRIC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `p0:B`] MFD_COMPLETE_EXP_ONTO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `(\y:B. exp(--((f:B->real) y)) / sqrt tau pow 3) o
      mfd_exp (top,atlas) (g:B->real^3^3) p0 =
      (\v. exp(--((v dot (g p0 ** v)) / (&4 * tau))) / sqrt tau pow 3)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2AU_FG_MODEL_INTEGRAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `\y:B. exp(--((f:B->real) y)) / sqrt tau pow 3`;
                 `topspace (top:B topology)`; `sqrt(&4 * pi) pow 3`]
    MFD_HAS_INTEGRAL_INTEGRAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

