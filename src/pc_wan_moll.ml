(* ========================================================================= *)
(* pc_wan_moll: mollifiers on real^M. The kernel wan_mk is a normalised      *)
(* smooth bump, equal to a constant on the ball of radius 1/2 and zero       *)
(* outside the unit ball; wan_mke e is its rescaling to the ball of radius   *)
(* e; wan_kconv k u is the convolution of a locally integrable u with a      *)
(* kernel k; wan_moll e u = wan_kconv (wan_mke e) u. The dimension M is      *)
(* general, so space-time real^(N,1)finite_sum is covered.                   *)
(*   - the kernel;                                                           *)
(*   - kernels as test functions on the whole space, reflection;             *)
(*   - uniform differentiability, the derivative of a convolution,           *)
(*     smoothness, partial derivatives, commutation with weak partials;      *)
(*   - bounds, supports, convergence almost everywhere and uniform           *)
(*     convergence on compact sets;                                          *)
(*   - localisation; L^2 estimates; the Friedrichs commutator estimate;      *)
(*   - the forms of wan_moll used in the other files; convergence in L^2.    *)
(* ========================================================================= *)

needs "src/pc_wan_weak.ml";;

prioritize_real();;
type_invention_error := true;;

let wan_mk = new_definition
 `wan_mk (x:real^M) =
    smooth_bump (&1 / &2) (&1) x /
    drop(integral (:real^M) (\y. lift(smooth_bump (&1 / &2) (&1) y)))`;;

let wan_mke = new_definition
 `wan_mke (e:real) (x:real^M) = inv(e) pow dimindex(:M) * wan_mk(inv(e) % x)`;;

let wan_kconv = new_definition
 `wan_kconv (k:real^M->real) (u:real^M->real^K) (x:real^M) =
    integral (:real^M) (\y. k(x - y) % u y)`;;

let wan_moll = new_definition
 `wan_moll (e:real) (u:real^M->real^K) = wan_kconv (wan_mke e) u`;;

(* ------------------------------------------------------------------------- *)
(* The bump and its integral.                                                *)
(* ------------------------------------------------------------------------- *)

let WAN_BUMP_HALF = prove
 (`smooth_map_on (:real^M) (\x:real^M. lift(smooth_bump (&1 / &2) (&1) x)) /\
   (!x:real^M. &0 <= smooth_bump (&1 / &2) (&1) x) /\
   (!x:real^M. norm x <= &1 / &2 ==> smooth_bump (&1 / &2) (&1) x = &1) /\
   (!x:real^M. &1 <= norm x ==> smooth_bump (&1 / &2) (&1) x = &0) /\
   (!x:real^M. smooth_bump (&1 / &2) (&1) (--x) = smooth_bump (&1 / &2) (&1) x)`,
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN REAL_ARITH_TAC;
    REWRITE_TAC[SMOOTH_BUMP_BOUNDS];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[smooth_bump; NORM_NEG]]);;

let WAN_BUMP_INTEGRAL = prove
 (`(\x:real^M. lift(smooth_bump (&1 / &2) (&1) x)) integrable_on (:real^M) /\
   &0 < drop(integral (:real^M) (\x:real^M. lift(smooth_bump (&1 / &2) (&1) x)))`,
  SUBGOAL_THEN `(\x:real^M. lift(smooth_bump (&1 / &2) (&1) x)) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN
    EXISTS_TAC `cball(vec 0:real^M,&1)` THEN
    REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[WAN_BUMP_HALF];
      SIMP_TAC[WAN_BUMP_HALF; REAL_LT_IMP_LE; LIFT_NUM]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x:real^M. lift(smooth_bump (&1 / &2) (&1) x)) integrable_on cball(vec 0,&1 / &2) /\
    integral (cball(vec 0:real^M,&1 / &2)) (\x. lift(smooth_bump (&1 / &2) (&1) x)) =
    integral (cball(vec 0:real^M,&1 / &2)) (\x. vec 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_EQ THEN EXISTS_TAC `\x:real^M. vec 1:real^1` THEN
      SIMP_TAC[IN_CBALL_0; WAN_BUMP_HALF; LIFT_NUM; INTEGRABLE_ON_CONST;
               MEASURABLE_CBALL];
      MATCH_MP_TAC INTEGRAL_EQ THEN SIMP_TAC[IN_CBALL_0; WAN_BUMP_HALF; LIFT_NUM]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `drop(integral (cball(vec 0:real^M,&1 / &2))
                            (\x. lift(smooth_bump (&1 / &2) (&1) x)))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `cball(vec 0:real^M,&1 / &2)` MEASURE_INTEGRAL) THEN
    REWRITE_TAC[MEASURABLE_CBALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MEASURE_CBALL_POS] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; LIFT_DROP; WAN_BUMP_HALF]]);;

(* ------------------------------------------------------------------------- *)
(* The kernel wan_mk.                                                        *)
(* ------------------------------------------------------------------------- *)

let WAN_MK_PROPS = prove
 (`smooth_map_on (:real^M) (\x:real^M. lift(wan_mk x)) /\
   (!x:real^M. &0 <= wan_mk x) /\
   (!x:real^M. &1 <= norm x ==> wan_mk x = &0) /\
   (!x:real^M. wan_mk(--x) = wan_mk x) /\
   ((\x:real^M. lift(wan_mk x)) has_integral lift(&1)) (:real^M)`,
  REWRITE_TAC[wan_mk] THEN
  MP_TAC(INST_TYPE [`:M`,`:M`] WAN_BUMP_INTEGRAL) THEN
  ABBREV_TAC `c = drop(integral (:real^M) (\y. lift(smooth_bump (&1 / &2) (&1) y)))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^M. lift(smooth_bump (&1 / &2) (&1) x / c)) =
    (\x. inv c % lift(smooth_bump (&1 / &2) (&1) x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div; GSYM LIFT_CMUL] THEN
    REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; WAN_BUMP_HALF];
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[WAN_BUMP_HALF; REAL_LT_IMP_LE];
    SIMP_TAC[WAN_BUMP_HALF; real_div; REAL_MUL_LZERO];
    REWRITE_TAC[WAN_BUMP_HALF];
    SUBGOAL_THEN
     `integral (:real^M) (\x. lift(smooth_bump (&1 / &2) (&1) x)) = lift c`
    ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN `lift(&1) = inv c % lift c` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]]);;

(* ------------------------------------------------------------------------- *)
(* The rescaled kernels wan_mke e.                                           *)
(* ------------------------------------------------------------------------- *)

let WAN_MKE_PROPS = prove
 (`!e. &0 < e
       ==> smooth_map_on (:real^M) (\x:real^M. lift(wan_mke e x)) /\
           (!x:real^M. &0 <= wan_mke e x) /\
           (!x:real^M. e <= norm x ==> wan_mke e x = &0) /\
           (!x:real^M. wan_mke e (--x) = wan_mke e x) /\
           ((\x:real^M. lift(wan_mke e x)) has_integral lift(&1)) (:real^M)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wan_mke] THEN
  STRIP_ASSUME_TAC(INST_TYPE [`:M`,`:M`] WAN_MK_PROPS) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    REWRITE_TAC[OPEN_UNIV] THEN
    SUBGOAL_THEN `(\x:real^M. lift(wan_mk(inv e % x))) =
                  (\x. lift(wan_mk x)) o (\x. inv e % x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `wan_mk(inv e % (x:real^M)) = &0`
     (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
    MATCH_MP_TAC(ASSUME `!x:real^M. &1 <= norm x ==> wan_mk x = &0`) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID];
    ASM_REWRITE_TAC[VECTOR_MUL_RNEG];
    MP_TAC(ISPECL [`\x:real^M. lift(wan_mk x)`; `lift(&1)`; `(:real^M)`;
                   `inv e`; `vec 0:real^M`] HAS_INTEGRAL_AFFINITY) THEN
    ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ; VECTOR_ADD_RID; VECTOR_MUL_RZERO;
                 VECTOR_NEG_0; REAL_INV_INV] THEN
    SUBGOAL_THEN `IMAGE (\x:real^M. e % x) (:real^M) = (:real^M)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^M` THEN
      EXISTS_TAC `inv e % y:real^M` THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `inv e pow dimindex(:M)` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
    SUBGOAL_THEN `inv e pow dimindex(:M) * inv(abs(inv e) pow dimindex(:M)) = &1`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < e ==> abs e = e`] THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN
      ASM_SIMP_TAC[REAL_POW_NZ; REAL_INV_EQ_0; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_LID; LIFT_CMUL]]);;

let WAN_MKE_TEST = prove
 (`!e. &0 < e ==> wan_test (:real^M) (wan_mke e)`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP WAN_MKE_PROPS) THEN
  ASM_REWRITE_TAC[wan_test] THEN EXISTS_TAC `cball(vec 0:real^M,e)` THEN
  ASM_SIMP_TAC[COMPACT_CBALL; SUBSET_UNIV; IN_CBALL_0; REAL_NOT_LE; REAL_LT_IMP_LE]);;

(* ========================================================================= *)
(* Kernels are test functions on the whole space; reflection                *)
(* y |-> k(x - y); integrability of the convolution integrand; derivatives *)
(* of kernels are kernels.                                                   *)
(* ========================================================================= *)

let WAN_TEST_UNIV_REFLECT = prove
 (`!(k:real^M->real) x. wan_test (:real^M) k ==> wan_test (:real^M) (\y. k(x - y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_test; SUBSET_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(\y. lift((k:real^M->real)(x - y))) = (\y. lift(k y)) o (\y. x - y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
    EXISTS_TAC `IMAGE (\z:real^M. x - z) c` THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      X_GEN_TAC `y:real^M` THEN REWRITE_TAC[IN_IMAGE] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[VECTOR_ARITH `x - (x - y):real^M = y`]]]);;

let WAN_REFLECT_DERIV = prove
 (`!(k:real^M->real) x y.
     (\z. lift(k z)) differentiable at (x - y)
     ==> frechet_derivative (\y. lift(k(x - y))) (at y) =
         (\h. --(frechet_derivative (\z. lift(k z)) (at (x - y)) h))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  SUBGOAL_THEN `(\y. lift((k:real^M->real)(x - y))) = (\z. lift(k z)) o (\y. x - y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. --(frechet_derivative (\z. lift((k:real^M->real) z)) (at (x - y)) h)) =
    frechet_derivative (\z. lift(k z)) (at (x - y)) o (\h. vec 0 - h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_SUB_LZERO] THEN GEN_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_NEG THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let WAN_REFLECT_DPART = prove
 (`!(k:real^M->real) x y i.
     wan_test (:real^M) k
     ==> wan_dpart i (\y. k(x - y)) y = --(wan_dpart i k (x - y))`,
  REWRITE_TAC[wan_test] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart] THEN
  MP_TAC(ISPECL [`k:real^M->real`; `x:real^M`; `y:real^M`] WAN_REFLECT_DERIV) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_NEG]]);;

let WAN_KCONV_INTEGRABLE = prove
 (`!(k:real^M->real) (u:real^M->real^K) x.
     wan_test (:real^M) k /\ wan_lloc (:real^M) u
     ==> (\y. k(x - y) % u y) absolutely_integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `\y:real^M. (k:real^M->real)(x - y)`; `u:real^M->real^K`]
                WAN_TEST_PAIRING) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[WAN_TEST_UNIV_REFLECT]; ALL_TAC] THEN
  DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o BETA_RULE));;

let WAN_TEST_DERIV_TEST = prove
 (`!(k:real^M->real) h.
     wan_test (:real^M) k
     ==> wan_test (:real^M) (\z. drop(frechet_derivative (\v. lift(k v)) (at z) h))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_test; SUBSET_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:real^M->real`; `c:real^M->bool`; `h:real^M`; `z:real^M`]
                  WAN_TEST_DERIV_ZERO) THEN
    ASM_SIMP_TAC[DROP_VEC]]);;

let WAN_TEST_DPART_TEST = prove
 (`!(k:real^M->real) i. wan_test (:real^M) k ==> wan_test (:real^M) (wan_dpart i k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^M->real`; `basis i:real^M`] WAN_TEST_DERIV_TEST) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; wan_dpart]);;

let WAN_KCONV_DERIV_INTEGRABLE = prove
 (`!(k:real^M->real) (u:real^M->real^K) h x.
     wan_test (:real^M) k /\ wan_lloc (:real^M) u
     ==> (\y. drop(frechet_derivative (\v. lift(k v)) (at (x - y)) h) % u y)
           integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MP_TAC(ISPECL [`\z. drop(frechet_derivative (\v. lift((k:real^M->real) v)) (at z) h)`;
                 `u:real^M->real^K`; `x:real^M`] WAN_KCONV_INTEGRABLE) THEN
  ASM_SIMP_TAC[WAN_TEST_DERIV_TEST]);;

(* ========================================================================= *)
(* Uniform differentiability of test functions on the whole                 *)
(* space; the Frechet derivative of a convolution with a kernel (the        *)
(* derivative falls on the kernel); smoothness and partial derivatives of   *)
(* convolutions; commutation with weak partials; translations.              *)
(* ========================================================================= *)

let WAN_SUPPORT_UNIFORMLY_CONTINUOUS = prove
 (`!(f:real^M->real^N) c.
     f continuous_on (:real^M) /\ compact c /\ (!x. ~(x IN c) ==> f x = vec 0)
     ==> !e. &0 < e
             ==> ?d. &0 < d /\ !x y. norm(y - x) < d ==> norm(f y - f x) < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `cc = {x + y:real^M | x IN c /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact(cc:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN MATCH_MP_TAC COMPACT_SUMS THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^M. x IN c /\ norm(y - x) < &1 ==> x IN cc /\ y IN cc`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "cc" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`x:real^M`; `vec 0:real^M`] THEN
      ASM_REWRITE_TAC[NORM_0; REAL_POS; VECTOR_ADD_RID];
      MAP_EVERY EXISTS_TAC [`x:real^M`; `y - x:real^M`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) uniformly_continuous_on cc` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^M) IN c \/ (y:real^M) IN c` THENL
   [SUBGOAL_THEN `(x:real^M) IN cc /\ (y:real^M) IN cc` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[NORM_SUB]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[dist];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0]]);;

let WAN_TEST_GRADIENT = prove
 (`!(k:real^M->real) z h.
     wan_test (:real^M) k
     ==> frechet_derivative (\v. lift(k v)) (at z) h =
         lift((lambda i. wan_dpart i k z):real^M dot h)`,
  REWRITE_TAC[wan_test] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (\v. lift((k:real^M->real) v)) (at z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
  REWRITE_TAC[dot; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_NUMSEG; LAMBDA_BETA; wan_dpart] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN
  MATCH_ACCEPT_TAC REAL_MUL_SYM);;

let WAN_TEST_UNIFORM_DIFF = prove
 (`!(k:real^M->real). wan_test (:real^M) k
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !z h. norm h < d
                           ==> abs(k(z + h) - k z -
                                   drop(frechet_derivative (\v. lift(k v)) (at z) h))
                               <= e * norm h`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `G = \z:real^M. (lambda i. wan_dpart i (k:real^M->real) z):real^M` THEN
  SUBGOAL_THEN
   `!z h:real^M. frechet_derivative (\v. lift((k:real^M->real) v)) (at z) h =
                 lift((G:real^M->real^M) z dot h)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ASM_SIMP_TAC[WAN_TEST_GRADIENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^M->real^M) continuous_on (:real^M)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    SIMP_TAC[LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(:real^M)`; `k:real^M->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^M. ~(z IN c) ==> (G:real^M->real^M) z = vec 0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; VEC_COMPONENT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN EXISTS_TAC `c:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^M->real^M`; `c:real^M->bool`]
                WAN_SUPPORT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^M`; `h:real^M`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\w:real^M. lift((k:real^M->real) w) - lift((G:real^M->real^M) z dot w)`;
                 `\w:real^M v. lift((G:real^M->real^M) w dot v) - lift(G z dot v)`;
                 `segment[z:real^M,z + h]`; `e:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(\v. lift((G:real^M->real^M) w dot v)) =
          frechet_derivative (\v. lift((k:real^M->real) v)) (at w)`
        SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
        MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
                       SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
        EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]];
      MP_TAC(ISPEC `\v. lift((G:real^M->real^M) w dot v) - lift(G z dot v)` ONORM) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL] THEN
        CONJ_TAC THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN X_GEN_TAC `v:real^M` THEN
      REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; GSYM DOT_LSUB] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((G:real^M->real^M) w - G z) * norm(v:real^M)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP DIST_IN_CLOSED_SEGMENT) THEN
      REWRITE_TAC[dist; VECTOR_ARITH `z - (z + h):real^M = --h`; NORM_NEG] THEN
      UNDISCH_TAC `norm(h:real^M) < d` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`z + h:real^M`; `z:real^M`]) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT; VECTOR_ARITH `(z + h) - z:real^M = h`] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
  REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; DOT_RADD] THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

let WAN_INTEGRAL_KERNEL_BOUND = prove
 (`!(g:real^M->real) (u:real^M->real^K) cc B.
     compact cc /\ wan_lloc (:real^M) u /\
     (!y. ~(y IN cc) ==> g y = &0) /\ (!y. abs(g y) <= B) /\
     (\y. g y % u y) integrable_on (:real^M)
     ==> norm(integral (:real^M) (\y. g y % u y)) <=
         B * drop(integral cc (\y. lift(norm(u y))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift(norm((u:real^M->real^K) y))) integrable_on cc` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
    UNDISCH_TAC `wan_lloc (:real^M) (u:real^M->real^K)` THEN REWRITE_TAC[wan_lloc] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. (g:real^M->real) y % (u:real^M->real^K) y`;
                 `\y. if y IN cc then B % lift(norm((u:real^M->real^K) y))
                      else vec 0:real^1`;
                 `(:real^M)`] INTEGRAL_NORM_BOUND_INTEGRAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV] THEN CONJ_TAC THENL
     [REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^M` THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[DROP_VEC; DROP_CMUL; LIFT_DROP; NORM_MUL; VECTOR_MUL_LZERO; NORM_0;
                   REAL_ABS_NUM; REAL_MUL_LZERO;
                   REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]);;

let WAN_KCONV_HAS_DERIVATIVE = prove
 (`!(k:real^M->real) (u:real^M->real^K) x.
     wan_test (:real^M) k /\ wan_lloc (:real^M) u
     ==> (wan_kconv k u has_derivative
          (\h. wan_kconv (\z. drop(frechet_derivative (\v. lift(k v)) (at z) h)) u x))
         (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. linear(frechet_derivative (\v. lift((k:real^M->real) v)) (at z))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^M)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ASM_MESON_TAC[wan_test];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; wan_kconv] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; DROP_ADD; DROP_CMUL; VECTOR_ADD_RDISTRIB;
                 GSYM VECTOR_MUL_ASSOC; INTEGRAL_ADD; INTEGRAL_CMUL;
                 WAN_KCONV_DERIV_INTEGRABLE; INTEGRABLE_CMUL];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ASSUME `wan_test (:real^M) (k:real^M->real)`) THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC
   `cc = IMAGE (\w:real^M. x - w) {a + b:real^M | a IN c /\ b IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact(cc:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL]];
    ALL_TAC] THEN
  ABBREV_TAC `mu = drop(integral cc (\y. lift(norm((u:real^M->real^K) y))))` THEN
  SUBGOAL_THEN `&0 <= mu` ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
    UNDISCH_TAC `wan_lloc (:real^M) (u:real^M->real^K)` THEN REWRITE_TAC[wan_lloc] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(SPEC `k:real^M->real` WAN_TEST_UNIFORM_DIFF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (mu + &1)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ud"))) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  X_GEN_TAC `w:real^M` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a:real^M. (\y. (k:real^M->real)(a - y) % (u:real^M->real^K) y) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h a:real^M. (\y. drop(frechet_derivative (\v. lift((k:real^M->real) v)) (at (a - y)) h) %
                      (u:real^M->real^K) y) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC WAN_KCONV_DERIV_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. (k:real^M->real)(w - y) % (u:real^M->real^K) y - k(x - y) % u y)
      integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_kconv k u (w:real^M) - wan_kconv k (u:real^M->real^K) x -
    wan_kconv (\z. drop(frechet_derivative (\v. lift((k:real^M->real) v)) (at z) (w - x)))
              u x =
    integral (:real^M)
      (\y. (k(w - y) - k(x - y) -
            drop(frechet_derivative (\v. lift(k v)) (at (x - y)) (w - x))) % u y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[wan_kconv; VECTOR_SUB_RDISTRIB] THEN ASM_SIMP_TAC[INTEGRAL_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(e / (mu + &1) * norm(w - x:real^M)) * mu` THEN CONJ_TAC THENL
   [EXPAND_TAC "mu" THEN MATCH_MP_TAC WAN_INTEGRAL_KERNEL_BOUND THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((x - y:real^M) IN c) /\ ~((w - y:real^M) IN c)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~((y:real^M) IN cc)` THEN
        EXPAND_TAC "cc" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_CBALL_0] THEN
        EXISTS_TAC `x - y:real^M` THEN
        REWRITE_TAC[VECTOR_ARITH `x - (x - y):real^M = y`] THENL
         [MAP_EVERY EXISTS_TAC [`x - y:real^M`; `vec 0:real^M`] THEN
          ASM_REWRITE_TAC[NORM_0; REAL_POS; VECTOR_ADD_RID];
          MAP_EVERY EXISTS_TAC [`w - y:real^M`; `x - w:real^M`] THEN
          ASM_REWRITE_TAC[VECTOR_ARITH `(w - y) + (x - w):real^M = x - y`] THEN
          ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`k:real^M->real`; `c:real^M->bool`; `w - x:real^M`; `x - y:real^M`]
                    WAN_TEST_DERIV_ZERO) THEN
      ASM_SIMP_TAC[DROP_VEC] THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real^M` THEN
      USE_THEN "ud" (fun th -> MP_TAC(MP (SPECL [`x - y:real^M`; `w - x:real^M`] th)
                                        (ASSUME `norm(w - x:real^M) < d`))) THEN
      REWRITE_TAC[VECTOR_ARITH `(x - y) + (w - x):real^M = w - y`];
      REWRITE_TAC[VECTOR_SUB_RDISTRIB] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `e / (mu + &1) * mu <= e` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a / b * c = (a * c) / b`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= mu ==> &0 < mu + &1`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`e / (mu + &1) * mu`; `e:real`; `norm(w - x:real^M)`] REAL_LE_RMUL) THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC]);;

let WAN_KCONV_CD = prove
 (`!n (k:real^M->real) (u:real^M->real^K).
     wan_test (:real^M) k /\ wan_lloc (:real^M) u
     ==> continuously_differentiable n (:real^M) (wan_kconv k u)`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[differentiable_on; IN_UNIV] THEN X_GEN_TAC `x:real^M` THEN
    MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[WAN_KCONV_HAS_DERIVATIVE];
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
    EXISTS_TAC `\x h. wan_kconv (\z. drop(frechet_derivative (\v. lift((k:real^M->real) v))
                                          (at z) h)) (u:real^M->real^K) x` THEN
    REWRITE_TAC[WITHIN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_KCONV_HAS_DERIVATIVE THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[WAN_TEST_DERIV_TEST]]]);;

let WAN_KCONV_SMOOTH = prove
 (`!(k:real^M->real) (u:real^M->real^K).
     wan_test (:real^M) k /\ wan_lloc (:real^M) u
     ==> smooth_map_on (:real^M) (wan_kconv k u)`,
  SIMP_TAC[smooth_map_on; WAN_KCONV_CD]);;

let WAN_KCONV_PARTIAL = prove
 (`!(k:real^M->real) (u:real^M->real^K) i x.
     wan_test (:real^M) k /\ wan_lloc (:real^M) u
     ==> partial_derivative i (wan_kconv k u) x = wan_kconv (wan_dpart i k) u x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  MP_TAC(SPECL [`k:real^M->real`; `u:real^M->real^K`; `x:real^M`]
               WAN_KCONV_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[wan_kconv; wan_dpart]);;

let WAN_KCONV_WPD = prove
 (`!(k:real^M->real) (u:real^M->real^K) v i x.
     wan_test (:real^M) k /\ wan_wpd (:real^M) i u v
     ==> partial_derivative i (wan_kconv k u) x = wan_kconv k v x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_wpd]) THEN
  ASM_SIMP_TAC[WAN_KCONV_PARTIAL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\y:real^M. (k:real^M->real)(x - y)`) THEN
  ASM_SIMP_TAC[WAN_TEST_UNIV_REFLECT; WAN_REFLECT_DPART] THEN
  REWRITE_TAC[wan_kconv; VECTOR_MUL_LNEG] THEN
  SUBGOAL_THEN
   `(\y. wan_dpart i (k:real^M->real) (x - y) % (u:real^M->real^K) y) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_TEST_DPART_TEST];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_NEG; VECTOR_EQ_NEG2]);;

let WAN_KCONV_TRANSLATE = prove
 (`!(k:real^M->real) (u:real^M->real^K) c x.
     wan_kconv k (\y. u(y + c)) x = wan_kconv k u (x + c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_kconv] THEN
  MP_TAC(ISPECL [`\y:real^M. (k:real^M->real)((x + c) - y) % (u:real^M->real^K) y`;
                 `(:real^M)`; `c:real^M`] INTEGRAL_TRANSLATION) THEN
  REWRITE_TAC[TRANSLATION_UNIV; VECTOR_ARITH `(x + c) - (c + y):real^M = x - y`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VECTOR_ADD_SYM]);;

(* ========================================================================= *)
(* Bounds for the kernel, supports, mollification minus the                  *)
(* function as an integral, convergence at Lebesgue points (hence almost    *)
(* everywhere) for locally integrable maps, and uniform convergence on      *)
(* compact sets for continuous maps.                                         *)
(* ========================================================================= *)

let WAN_MK_BOUND = prove
 (`?B. &0 < B /\ !x:real^M. wan_mk x <= B`,
  EXISTS_TAC `inv(drop(integral (:real^M) (\y. lift(smooth_bump (&1 / &2) (&1) y))))` THEN
  MP_TAC(INST_TYPE [`:M`,`:M`] WAN_BUMP_INTEGRAL) THEN
  ABBREV_TAC `c = drop(integral (:real^M) (\y. lift(smooth_bump (&1 / &2) (&1) y)))` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
  REWRITE_TAC[wan_mk] THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; SMOOTH_BUMP_BOUNDS]);;

let WAN_MKE_BOUND = prove
 (`?B. &0 < B /\
       !e x:real^M. &0 < e ==> wan_mke e x <= B * inv(e) pow dimindex(:M)`,
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:M`,`:M`] WAN_MK_BOUND) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[wan_mke] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let WAN_MKE_INTEGRAL_AT = prove
 (`!e x:real^M. &0 < e ==> ((\y. lift(wan_mke e (x - y))) has_integral lift(&1)) (:real^M)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WAN_MKE_PROPS) THEN
  SUBGOAL_THEN `(\y. lift(wan_mke e (x - y))) = (\y:real^M. lift(wan_mke e (--x + y)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV
     [GSYM(ASSUME `!x:real^M. wan_mke e (--x) = wan_mke e x`)] THEN
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^M. lift(wan_mke e z)`; `lift(&1)`; `(:real^M)`; `--x:real^M`]
                HAS_INTEGRAL_TRANSLATION) THEN
  ASM_REWRITE_TAC[TRANSLATION_UNIV]);;

let WAN_KCONV_SUPPORT = prove
 (`!(k:real^M->real) (u:real^M->real^K) r t.
     (!z. r <= norm z ==> k z = &0) /\ (!y. ~(y IN t) ==> u y = vec 0)
     ==> !x. ~(x IN {a + b | a IN t /\ b IN ball(vec 0,r)}) ==> wan_kconv k u x = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_kconv] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `integral (:real^M) (\y. vec 0:real^K)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTEGRAL_0]] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
  ASM_CASES_TAC `(y:real^M) IN t` THENL
   [SUBGOAL_THEN `(k:real^M->real)(x - y) = &0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:real^M) IN {a + b | a IN t /\ b IN ball(vec 0,r)})` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_BALL_0] THEN
    MAP_EVERY EXISTS_TAC [`y:real^M`; `x - y:real^M`] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ASM_SIMP_TAC[VECTOR_MUL_RZERO]]);;

let WAN_MOLL_SUB = prove
 (`!e (u:real^M->real^K) x.
     &0 < e /\ wan_lloc (:real^M) u
     ==> wan_moll e u x - u x =
         integral (:real^M) (\y. wan_mke e (x - y) % (u y - u x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_moll; wan_kconv; VECTOR_SUB_LDISTRIB] THEN
  SUBGOAL_THEN `(\y. wan_mke e (x - y) % (u:real^M->real^K) y) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. wan_mke e (x - y) % (u:real^M->real^K) x) has_integral u x) (:real^M)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:real^M. lift(wan_mke e (x - y))`; `lift(&1)`; `(:real^M)`;
                   `\v:real^1. drop v % (u:real^M->real^K) x`] HAS_INTEGRAL_LINEAR) THEN
    ASM_SIMP_TAC[WAN_MKE_INTEGRAL_AT; LINEAR_VMUL_DROP; LINEAR_ID; o_DEF; LIFT_DROP;
                 VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. wan_mke e (x - y) % (u:real^M->real^K) x) integrable_on (:real^M)`
  ASSUME_TAC THENL [ASM_MESON_TAC[integrable_on]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_SUB] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]);;

let WAN_MKE_ZERO = prove
 (`!e x:real^M. &0 < e /\ e <= norm x ==> wan_mke e x = &0`,
  MESON_TAC[WAN_MKE_PROPS]);;

let WAN_MKE_POS = prove
 (`!e x:real^M. &0 < e ==> &0 <= wan_mke e x`,
  MESON_TAC[WAN_MKE_PROPS]);;

let WAN_CUBE_CONTENT = prove
 (`!(x:real^M) e. &0 <= e
     ==> content(interval[x - e % vec 1,x + e % vec 1]) = (&2 * e) pow dimindex(:M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:M)
                    ==> (x - e % vec 1:real^M)$i <= (x + e % vec 1)$i`
  ASSUME_TAC THENL
   [SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
             VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
           VEC_COMPONENT] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ARITH `(x + e) - (x - e) = &2 * e`;
              PRODUCT_CONST_NUMSEG_1]);;

let WAN_NOT_IN_CUBE = prove
 (`!(x:real^M) y e. ~(y IN interval[x - e % vec 1,x + e % vec 1]) ==> e < norm(x - y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTERVAL; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `abs((x - y:real^M)$i)` THEN
  REWRITE_TAC[COMPONENT_LE_NORM] THEN
  POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
               VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let WAN_MOLL_DIFF_BOUND = prove
 (`?B. &0 < B /\
       !e (u:real^M->real^K) x.
         &0 < e /\ wan_lloc (:real^M) u
         ==> norm(wan_moll e u x - u x) <=
             (B * inv(e) pow dimindex(:M)) *
             drop(integral (interval[x - e % vec 1,x + e % vec 1])
                           (\y. lift(norm(u y - u x))))`,
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:M`,`:M`] WAN_MKE_BOUND) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WAN_MOLL_SUB] THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (\y. (u:real^M->real^K) y - u x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_SUB THEN ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_INTEGRAL_KERNEL_BOUND THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_THEN(MP_TAC o MATCH_MP WAN_NOT_IN_CUBE) THEN
    DISCH_TAC THEN MATCH_MP_TAC WAN_MKE_ZERO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `y:real^M` THEN ASM_SIMP_TAC[WAN_MKE_POS; real_abs];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`wan_mke e:real^M->real`; `\y. (u:real^M->real^K) y - u x`;
                   `x:real^M`] WAN_KCONV_INTEGRABLE) THEN
    ASM_SIMP_TAC[WAN_MKE_TEST]]);;

let WAN_AE_ARITH = prove
 (`!B c P E qq eps.
     &0 < B /\ &0 < P /\ &0 < E /\ c = P * E /\ &0 <= qq /\
     abs(inv c) * abs qq < eps / (B * P)
     ==> (B * inv E) * qq < eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(inv c) * abs qq = inv(P * E) * qq` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_INV; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_ARITH `&0 <= x ==> abs x = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B * inv E) * qq = (B * P) * (inv(P * E) * qq)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < P` THEN UNDISCH_TAC `&0 < E` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps = (B * P) * (eps / (B * P))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < B` THEN UNDISCH_TAC `&0 < P` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN ASM_MESON_TAC[]);;

let WAN_MOLL_AE_CONV = prove
 (`!(u:real^M->real^K).
     wan_lloc (:real^M) u
     ==> ?t. negligible t /\
             !x eps. ~(x IN t) /\ &0 < eps
                     ==> ?d. &0 < d /\
                             !e. &0 < e /\ e < d ==> norm(wan_moll e u x - u x) < eps`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))
    (INST_TYPE [`:M`,`:M`; `:K`,`:K`] WAN_MOLL_DIFF_BOUND) THEN
  MP_TAC(ISPEC `u:real^M->real^K` ABSOLUTELY_INTEGRABLE_LEBESGUE_POINTS) THEN
  ANTS_TAC THENL
   [REPEAT GEN_TAC THEN UNDISCH_TAC `wan_lloc (:real^M) (u:real^M->real^K)` THEN
    REWRITE_TAC[wan_lloc] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[COMPACT_INTERVAL; SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^M->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "leb")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `eps:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps / (B * &2 pow dimindex(:M))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  USE_THEN "leb" (fun th -> MP_TAC(MP (SPECL [`x:real^M`; `eps / (B * &2 pow dimindex(:M))`] th)
                     (CONJ (ASSUME `~((x:real^M) IN t)`)
                           (ASSUME `&0 < eps / (B * &2 pow dimindex(:M))`)))) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "avg")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  USE_THEN "avg" (fun th -> MP_TAC(MP (SPEC `e:real` th)
                     (CONJ (ASSUME `&0 < e`) (ASSUME `e < d`)))) THEN
  REWRITE_TAC[NORM_MUL; NORM_1] THEN DISCH_TAC THEN
  USE_THEN "bd" (fun th -> MP_TAC(MP (SPECL [`e:real`; `u:real^M->real^K`; `x:real^M`] th)
                     (CONJ (ASSUME `&0 < e`) (ASSUME `wan_lloc (:real^M) (u:real^M->real^K)`)))) THEN
  MATCH_MP_TAC(REAL_ARITH `y < eps ==> x <= y ==> x < eps`) THEN
  REWRITE_TAC[REAL_POW_INV] THEN MATCH_MP_TAC WAN_AE_ARITH THEN
  EXISTS_TAC `content(interval[x - e % vec 1:real^M,x + e % vec 1])` THEN
  EXISTS_TAC `&2 pow dimindex(:M)` THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH; WAN_CUBE_CONTENT; REAL_LT_IMP_LE;
               REAL_POW_MUL] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (\y. (u:real^M->real^K) y - u x)` MP_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_SUB THEN ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[wan_lloc] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[COMPACT_INTERVAL; SUBSET_UNIV]);;

let WAN_MOLL_UNIFORM = prove
 (`!(u:real^M->real^K) c.
     u continuous_on (:real^M) /\ compact c
     ==> !eps. &0 < eps
               ==> ?d. &0 < d /\
                       !e x. &0 < e /\ e < d /\ x IN c
                             ==> norm(wan_moll e u x - u x) <= eps`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `cc = {x + y:real^M | x IN c /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact(cc:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^M->real^K) uniformly_continuous_on cc` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`e:real`; `x:real^M`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (u:real^M->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (\y. (u:real^M->real^K) y - u x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_SUB THEN ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\y. lift(eps * wan_mke e (x - y))) has_integral lift eps) (:real^M)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`e:real`; `x:real^M`] WAN_MKE_INTEGRAL_AT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `eps:real` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_MOLL_SUB] THEN
  MP_TAC(ISPECL [`\y. wan_mke e (x - y) % ((u:real^M->real^K) y - u x)`;
                 `\y:real^M. lift(eps * wan_mke e (x - y))`; `(:real^M)`]
                INTEGRAL_NORM_BOUND_INTEGRAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MP_TAC(ISPECL [`wan_mke e:real^M->real`; `\y. (u:real^M->real^K) y - u x`;
                     `x:real^M`] WAN_KCONV_INTEGRABLE) THEN
      ASM_SIMP_TAC[WAN_MKE_TEST];
      ASM_MESON_TAC[integrable_on];
      X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN REWRITE_TAC[NORM_MUL; LIFT_DROP] THEN
      ASM_SIMP_TAC[WAN_MKE_POS; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      ASM_CASES_TAC `norm(x - y:real^M) < e` THENL
       [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[WAN_MKE_POS] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        REWRITE_TAC[GSYM dist] THEN USE_THEN "uc" MATCH_MP_TAC THEN
        REWRITE_TAC[dist] THEN EXPAND_TAC "cc" THEN
        REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN REPEAT CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`x:real^M`; `vec 0:real^M`] THEN
          ASM_REWRITE_TAC[NORM_0; REAL_POS; VECTOR_ADD_RID];
          MAP_EVERY EXISTS_TAC [`x:real^M`; `y - x:real^M`] THEN
          ASM_REWRITE_TAC[VECTOR_ARITH `x + y - x:real^M = y`] THEN
          ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
          ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `wan_mke e (x - y:real^M) = &0` (fun th -> REWRITE_TAC[th]) THENL
         [MATCH_MP_TAC WAN_MKE_ZERO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[LIFT_DROP]);;

(* ========================================================================= *)
(* Localisation.  Products with test functions on an open set,               *)
(* extended by zero, have weak partials on the whole space.                  *)
(* ========================================================================= *)

let WAN_LLOC_EXTEND = prove
 (`!(f:real^M->real^K) s.
     f absolutely_integrable_on s
     ==> wan_lloc (:real^M) (\x. if x IN s then f x else vec 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `(:real^M)` THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV; LEBESGUE_MEASURABLE_COMPACT]);;

let WAN_TEST_PRODUCT_UNIV = prove
 (`!(s:real^M->bool) phi zeta.
     wan_test (:real^M) phi /\ wan_test s zeta
     ==> wan_test s (\x. phi x * zeta x) /\
         !i x. wan_dpart i (\x. phi x * zeta x) x =
               wan_dpart i phi x * zeta x + phi x * wan_dpart i zeta x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `phi:real^M->real`; `zeta:real^M->real`]
                WAN_TEST_MUL_SMOOTH) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_UNIV; wan_test]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV; ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `wan_test (:real^M) (\x. phi x * zeta x)` THEN
  UNDISCH_TAC `wan_test s (zeta:real^M->real)` THEN
  REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kz:real^M->bool` STRIP_ASSUME_TAC)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `kz:real^M->bool` THEN
  ASM_SIMP_TAC[REAL_MUL_RZERO]);;

let WAN_WPD_ZERO_EXTENSION = prove
 (`!(s:real^M->bool) i (u:real^M->real^K) v zeta.
     open s /\ wan_wpd s i u v /\ wan_test s zeta
     ==> wan_wpd (:real^M) i (\x. if x IN s then zeta x % u x else vec 0)
                 (\x. if x IN s then wan_dpart i zeta x % u x + zeta x % v x
                      else vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `wan_wpd s i (u:real^M->real^K) v` THEN REWRITE_TAC[wan_wpd] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ibp"))) THEN
  MP_TAC(REWRITE_RULE[wan_test] (ASSUME `wan_test s (zeta:real^M->real)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kz:real^M->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `zeta:real^M->real`; `u:real^M->real^K`]
                WAN_TEST_PAIRING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i:num`)) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `zeta:real^M->real`; `v:real^M->real^K`]
                WAN_TEST_PAIRING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_EXTEND THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_LLOC_EXTEND THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `phi:real^M->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `phi:real^M->real`; `zeta:real^M->real`]
                WAN_TEST_PRODUCT_UNIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "ibp" (fun th -> MP_TAC(MP (SPEC `\x:real^M. phi x * zeta x` th)
                     (ASSUME `wan_test s (\x:real^M. phi x * zeta x)`))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COND_RAND; VECTOR_MUL_RZERO; INTEGRAL_RESTRICT_UNIV] THEN
  SUBGOAL_THEN
   `(\x. lift((phi:real^M->real) x)) continuous_on (:real^M) /\
    (\x. lift(wan_dpart i phi x)) continuous_on (:real^M) /\
    (\x. lift((zeta:real^M->real) x)) continuous_on (:real^M) /\
    (\x. lift(wan_dpart i zeta x)) continuous_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^M)`; `phi:real^M->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `zeta:real^M->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x IN kz) ==> wan_dpart i (zeta:real^M->real) x = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
    EXISTS_TAC `kz:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (wan_dpart i phi x * zeta x) % (u:real^M->real^K) x) integrable_on s /\
    (\x. (phi x * wan_dpart i zeta x) % (u:real^M->real^K) x) integrable_on s /\
    (\x. (phi x * zeta x) % (v:real^M->real^K) x) integrable_on s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_LLOC_PAIRING THEN EXISTS_TAC `kz:real^M->bool` THEN
    ASM_SIMP_TAC[LIFT_CMUL; CONTINUOUS_ON_MUL; o_DEF; REAL_MUL_RZERO];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_ADD_RDISTRIB; INTEGRAL_ADD; GSYM VECTOR_MUL_ASSOC;
               VECTOR_ADD_LDISTRIB] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `(\x. (phi x * wan_dpart i zeta x) % (u:real^M->real^K) x +
         (phi x * zeta x) % (v:real^M->real^K) x) integrable_on s`
  ASSUME_TAC THENL [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* L^2 estimates.  A weighted Cauchy-Schwarz inequality and a               *)
(* Schur-type bound for integral operators whose kernel is dominated by a   *)
(* bounded integrable convolution kernel (used for mollifiers and for the   *)
(* Friedrichs commutators).                                                  *)
(* ========================================================================= *)

let WAN_QUAD_DISCRIMINANT = prove
 (`!a b c. &0 <= a /\ (!t. &0 <= a * t pow 2 - &2 * b * t + c) ==> b pow 2 <= a * c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a = &0` THENL
   [ASM_CASES_TAC `b = &0` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `(c + &1) / (&2 * b)`) THEN
      SUBGOAL_THEN `a * ((c + &1) / (&2 * b)) pow 2 - &2 * b * ((c + &1) / (&2 * b)) + c =
                    --(&1)`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(b = &0)` THEN CONV_TAC REAL_FIELD;
        REAL_ARITH_TAC]];
    FIRST_X_ASSUM(MP_TAC o SPEC `b / a`) THEN
    SUBGOAL_THEN `a * (b / a) pow 2 - &2 * b * (b / a) + c = (a * c - b pow 2) / a`
    SUBST1_TAC THENL [UNDISCH_TAC `~(a = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN REAL_ARITH_TAC]);;

let WAN_NONNEG_ABS_INTEGRABLE = prove
 (`!(g:real^M->real) s.
     (!x. x IN s ==> &0 <= g x) /\ (\x. lift(g x)) integrable_on s
     ==> (\x. lift(g x)) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LIFT_COMPONENT]);;

let WAN_WEIGHTED_CS = prove
 (`!(w:real^M->real) (g:real^M->real).
     (!y. &0 <= w y) /\
     (\y. lift(w y)) integrable_on (:real^M) /\
     (\y. lift(w y * g y)) integrable_on (:real^M) /\
     (\y. lift(w y * g y pow 2)) integrable_on (:real^M)
     ==> drop(integral (:real^M) (\y. lift(w y * g y))) pow 2 <=
         drop(integral (:real^M) (\y. lift(w y))) *
         drop(integral (:real^M) (\y. lift(w y * g y pow 2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_QUAD_DISCRIMINANT THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN
  SUBGOAL_THEN
   `(\y. lift((w:real^M->real) y * g y pow 2) - (&2 * t) % lift(w y * g y))
      integrable_on (:real^M) /\
    (\y. t pow 2 % lift((w:real^M->real) y)) integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_SIMP_TAC[INTEGRABLE_CMUL];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (:real^M) (\y. lift(w y))) * t pow 2 -
    &2 * drop(integral (:real^M) (\y. lift((w:real^M->real) y * g y))) * t +
    drop(integral (:real^M) (\y. lift(w y * g y pow 2))) =
    drop(integral (:real^M)
           (\y. (lift(w y * g y pow 2) - (&2 * t) % lift(w y * g y)) +
                t pow 2 % lift(w y)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_ADD] THEN ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRABLE_CMUL] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_ADD; DROP_SUB; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_CMUL; LIFT_DROP] THEN
  SUBGOAL_THEN `&0 <= (w:real^M->real) y * (g y - t) pow 2` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> &0 <= a ==> &0 <= b`) THEN CONV_TAC REAL_RING);;

let WAN_KERNEL_SHIFT = prove
 (`!(k0:real^M->real^N) i x.
     (k0 has_integral i) (:real^M) ==> ((\y. k0(x - y)) has_integral i) (:real^M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\z. (k0:real^M->real^N)(--z)) has_integral i) (:real^M)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HAS_INTEGRAL_REFLECT_GEN; REFLECT_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^M. (k0:real^M->real^N)(--z)`; `i:real^N`; `(:real^M)`;
                 `--x:real^M`] HAS_INTEGRAL_TRANSLATION) THEN
  ASM_REWRITE_TAC[TRANSLATION_UNIV; VECTOR_ARITH `--(--x + y):real^M = x - y`]);;

let WAN_SHIFT_FACTS = prove
 (`!(k0:real^M->real) (f:real^M->real^N) B x.
     (\z. lift(k0 z)) integrable_on (:real^M) /\ (!z. &0 <= k0 z /\ k0 z <= B) /\
     f IN lspace (:real^M) (&2)
     ==> ((\y. lift(k0(x - y))) has_integral integral (:real^M) (\z. lift(k0 z)))
           (:real^M) /\
         (\y. lift(k0(x - y) * norm(f y) pow 2)) integrable_on (:real^M) /\
         (\y. lift(k0(x - y) * norm(f y))) integrable_on (:real^M)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) measurable_on (:real^M) /\
                (\x. lift(norm(f x) pow 2)) integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^M->real^N) IN lspace (:real^M) (&2)` THEN
    SIMP_TAC[lspace; IN_ELIM_THM; RPOW_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. lift(k0(x - y))) has_integral
     integral (:real^M) (\z. lift((k0:real^M->real) z))) (:real^M)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^M. lift((k0:real^M->real) z)`;
                   `integral (:real^M) (\z. lift((k0:real^M->real) z))`; `x:real^M`]
                  WAN_KERNEL_SHIFT) THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift(k0(x - y) * norm((f:real^M->real^N) y) pow 2)) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`\a:real^1 b:real^1. drop a % b`; `\z:real^M. lift((k0:real^M->real) z)`;
                   `\y:real^M. lift(norm((f:real^M->real^N) y) pow 2)`; `x:real^M`]
                  ABSOLUTELY_INTEGRABLE_CONVOLUTION_LINF_L1) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; GSYM LIFT_CMUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[INTEGRABLE_IMP_MEASURABLE];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV; NORM_LIFT] THEN
      EXISTS_TAC `B + &1` THEN
      SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
       [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `z:real^M` THEN
      MP_TAC(SPEC `z:real^M` (ASSUME `!z:real^M. &0 <= k0 z /\ k0 z <= B`)) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC WAN_NONNEG_ABS_INTEGRABLE THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\y:real^M. inv(&2) % (lift(k0(x - y)) +
                                   lift(k0(x - y) * norm((f:real^M->real^N) y) pow 2))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC MEASURABLE_ON_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN ASM_MESON_TAC[integrable_on];
      MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    ASM_MESON_TAC[integrable_on];
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; DROP_CMUL; DROP_ADD; LIFT_DROP; REAL_ABS_MUL; REAL_ABS_NORM] THEN
    SUBGOAL_THEN `&0 <= (k0:real^M->real)(x - y)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`] THEN
    MP_TAC(SPECL [`(k0:real^M->real)(x - y)`; `(norm((f:real^M->real^N) y) - &1) pow 2`]
                 REAL_LE_MUL) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN CONV_TAC REAL_ARITH]);;

let WAN_KERNEL_L2_BOUND = prove
 (`!(K:real^M->real^M->real) (k0:real^M->real) (f:real^M->real^N) A B.
     (\z. lift(k0 z)) integrable_on (:real^M) /\ (!z. &0 <= k0 z /\ k0 z <= B) /\
     drop(integral (:real^M) (\z. lift(k0 z))) <= A /\
     (!x y. abs(K x y) <= k0(x - y)) /\
     (!x. (\y. lift(K x y)) measurable_on (:real^M)) /\
     f IN lspace (:real^M) (&2) /\
     (\x. integral (:real^M) (\y. K x y % f y)) measurable_on (:real^M)
     ==> (!x. (\y. K x y % f y) integrable_on (:real^M)) /\
         (\x. integral (:real^M) (\y. K x y % f y)) IN lspace (:real^M) (&2) /\
         drop(integral (:real^M)
                (\x. lift(norm(integral (:real^M) (\y. K x y % f y)) pow 2)))
         <= A pow 2 * drop(integral (:real^M) (\x. lift(norm(f x) pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) measurable_on (:real^M) /\
                (\x. lift(norm(f x) pow 2)) integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^M->real^N) IN lspace (:real^M) (&2)` THEN
    SIMP_TAC[lspace; IN_ELIM_THM; RPOW_POW];
    ALL_TAC] THEN
  ABBREV_TAC `W0 = drop(integral (:real^M) (\z. lift((k0:real^M->real) z)))` THEN
  SUBGOAL_THEN `&0 <= W0` ASSUME_TAC THENL
   [EXPAND_TAC "W0" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= drop(integral (:real^M) (\x. lift(norm((f:real^M->real^N) x) pow 2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. ((\y. lift(k0(x - y))) has_integral lift W0) (:real^M) /\
        (\y. lift(k0(x - y) * norm((f:real^M->real^N) y) pow 2)) integrable_on (:real^M) /\
        (\y. lift(k0(x - y) * norm(f y))) integrable_on (:real^M)`
  (LABEL_TAC "sh") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`k0:real^M->real`; `f:real^M->real^N`; `B:real`; `x:real^M`]
                  WAN_SHIFT_FACTS) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "W0" THEN REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. (\y. (K:real^M->real^M->real) x y % (f:real^M->real^N) y) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\y:real^M. lift(k0(x - y) * norm((f:real^M->real^N) y))` THEN
    ASM_SIMP_TAC[MEASURABLE_ON_MUL; IN_UNIV; LIFT_DROP; NORM_MUL] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `W2 = \x. drop(integral (:real^M)
                    (\y. lift(k0(x - y) * norm((f:real^M->real^N) y) pow 2)))` THEN
  SUBGOAL_THEN `!x. &0 <= (W2:real^M->real) x` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "W2" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[LIFT_DROP; REAL_LE_MUL; REAL_LE_POW_2] THEN
    USE_THEN "sh" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. norm(integral (:real^M) (\y. (K:real^M->real^M->real) x y % (f:real^M->real^N) y)) pow 2 <=
        A * (W2:real^M->real) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN
    USE_THEN "sh" (STRIP_ASSUME_TAC o SPEC `x:real^M`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (:real^M)
                       (\y. lift(k0(x - y) * norm((f:real^M->real^N) y)))) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_REWRITE_TAC[IN_UNIV; LIFT_DROP; NORM_MUL] THEN GEN_TAC THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `W0 * (W2:real^M->real) x` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "W2" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `W0 = drop(integral (:real^M) (\y. lift(k0(x - y))))` SUBST1_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[LIFT_DROP];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`\y:real^M. (k0:real^M->real)(x - y)`;
                     `\y:real^M. norm((f:real^M->real^N) y)`] WAN_WEIGHTED_CS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[integrable_on];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((W2:real^M->real) x)) integrable_on (:real^M) /\
    drop(integral (:real^M) (\x. lift((W2:real^M->real) x))) =
    W0 * drop(integral (:real^M) (\x. lift(norm((f:real^M->real^N) x) pow 2)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W2" THEN EXPAND_TAC "W0" THEN REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`\a:real^1 b:real^1. drop a % b`; `\z:real^M. lift((k0:real^M->real) z)`;
                   `\y:real^M. lift(norm((f:real^M->real^N) y) pow 2)`]
                  DOUBLE_INTEGRABLE_CONVOLUTION) THEN
    MP_TAC(ISPECL [`\a:real^1 b:real^1. drop a % b`; `\z:real^M. lift((k0:real^M->real) z)`;
                   `\y:real^M. lift(norm((f:real^M->real^N) y) pow 2)`]
                  DOUBLE_INTEGRAL_CONVOLUTION) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; GSYM LIFT_CMUL] THEN
    SUBGOAL_THEN
     `(\z:real^M. lift((k0:real^M->real) z)) absolutely_integrable_on (:real^M) /\
      (\y:real^M. lift(norm((f:real^M->real^N) y) pow 2)) absolutely_integrable_on (:real^M)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC WAN_NONNEG_ABS_INTEGRABLE THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SIMP_TAC[DROP_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(integral (:real^M) (\y. (K:real^M->real^M->real) x y % (f:real^M->real^N) y)) pow 2))
      integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x:real^M. A % lift((W2:real^M->real) x)` THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; IN_UNIV; NORM_LIFT; DROP_CMUL; LIFT_DROP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN
      MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^M) (\x:real^M. A % lift((W2:real^M->real) x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; DROP_CMUL; LIFT_DROP];
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
    ONCE_REWRITE_TAC[REAL_RING `(A:real) pow 2 * x = A * (A * x)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

let WAN_L2_LLOC = prove
 (`!(u:real^M->real^K). u IN lspace (:real^M) (&2) ==> wan_lloc (:real^M) u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^M->real^K) IN lspace k (&1)` MP_TAC THENL
   [MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC `&2` THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_UNIV];
    REWRITE_TAC[LSPACE_1; IN_ELIM_THM]]);;

let WAN_MOLL_EQ = prove
 (`!e (u:real^M->real^K).
     wan_moll e u = (\x. integral (:real^M) (\y. wan_mke e (x - y) % u y))`,
  REWRITE_TAC[FUN_EQ_THM; wan_moll; wan_kconv]);;

let WAN_MOLL_SMOOTH = prove
 (`!e (u:real^M->real^K).
     &0 < e /\ wan_lloc (:real^M) u ==> smooth_map_on (:real^M) (wan_moll e u)`,
  SIMP_TAC[wan_moll; WAN_KCONV_SMOOTH; WAN_MKE_TEST]);;

let WAN_MOLL_L2 = prove
 (`!e (u:real^M->real^K).
     &0 < e /\ u IN lspace (:real^M) (&2)
     ==> wan_moll e u IN lspace (:real^M) (&2) /\
         drop(integral (:real^M) (\x. lift(norm(wan_moll e u x) pow 2))) <=
         drop(integral (:real^M) (\x. lift(norm(u x) pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:M`,`:M`] WAN_MKE_BOUND) THEN
  MP_TAC(SPEC `e:real` (INST_TYPE [`:M`,`:M`] WAN_MKE_PROPS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(wan_moll e (u:real^M->real^K)) measurable_on (:real^M)` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC WAN_MOLL_SMOOTH THEN
    ASM_SIMP_TAC[WAN_L2_LLOC];
    ALL_TAC] THEN
  REWRITE_TAC[WAN_MOLL_EQ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x y:real^M. wan_mke e (x - y)`; `wan_mke e:real^M->real`;
                 `u:real^M->real^K`; `&1`; `B * inv(e) pow dimindex(:M)`]
                WAN_KERNEL_L2_BOUND) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[integrable_on];
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
      REWRITE_TAC[LIFT_DROP; REAL_LE_REFL];
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x <= x`];
      GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
      ASM_MESON_TAC[WAN_MKE_INTEGRAL_AT; integrable_on]];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* The Friedrichs commutator estimate.  For a Lipschitz                     *)
(* multiplier a, the commutator of a with the derivative of the mollifier,  *)
(* f |-> (d_i rho_e) conv (a f) - a ((d_i rho_e) conv f), is bounded on L^2 *)
(* uniformly in e (the kernel (d_i rho_e)(x - y) (a y - a x) is dominated   *)
(* by L |z| |d_i rho_e(z)|, whose integral does not depend on e).           *)
(* ========================================================================= *)

let WAN_MKE_DPART = prove
 (`!e i (z:real^M).
     &0 < e
     ==> wan_dpart i (wan_mke e) z =
         inv(e) pow (dimindex(:M) + 1) * wan_dpart i wan_mk (inv e % z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart] THEN
  SUBGOAL_THEN
   `(\y. lift(wan_mke e (y:real^M))) =
    (\y. inv e pow dimindex(:M) % ((\w. lift(wan_mk w)) o (\y. inv e % y)) y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_mke; LIFT_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w:real^M. lift(wan_mk w)) has_derivative
     frechet_derivative (\w. lift(wan_mk w)) (at (inv e % z))) (at (inv e % z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
                   SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `(:real^M)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV; WAN_MK_PROPS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\w:real^M. lift(wan_mk w)) (at (inv e % z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_MESON_TAC[differentiable];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. inv e pow dimindex(:M) % ((\w. lift(wan_mk w)) o (\y. inv e % y)) y) has_derivative
     (\h. inv e pow dimindex(:M) %
          (frechet_derivative (\w:real^M. lift(wan_mk w)) (at (inv e % z)) o
           (\h. inv e % h)) h)) (at z)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL; DROP_CMUL] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_ASSOC]);;

let WAN_MK_DPART_TEST = prove
 (`!i. wan_test (:real^M) (wan_dpart i wan_mk)`,
  GEN_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_TEST THEN
  REWRITE_TAC[wan_test; WAN_MK_PROPS; SUBSET_UNIV] THEN
  EXISTS_TAC `cball(vec 0:real^M,&1)` THEN
  SIMP_TAC[COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE; REAL_LT_IMP_LE; WAN_MK_PROPS]);;

let WAN_MK_WEIGHTED_L1 = prove
 (`!i. ?D. &0 <= D /\
           !e. &0 < e
               ==> ((\z:real^M. lift(norm z * abs(wan_dpart i (wan_mke e) z)))
                    has_integral lift D) (:real^M)`,
  GEN_TAC THEN
  ABBREV_TAC `h = \w:real^M. norm w * abs(wan_dpart i wan_mk w)` THEN
  SUBGOAL_THEN `(\w. lift((h:real^M->real) w)) integrable_on (:real^M)` ASSUME_TAC THENL
   [MP_TAC(SPEC `i:num` (INST_TYPE [`:M`,`:M`] WAN_MK_DPART_TEST)) THEN
    REWRITE_TAC[wan_test] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `c:real^M->bool` THEN
    EXPAND_TAC "h" THEN ASM_SIMP_TAC[REAL_ABS_NUM; REAL_MUL_RZERO; LIFT_NUM] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; CONTINUOUS_ON_LIFT_NORM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  EXISTS_TAC `drop(integral (:real^M) (\w. lift((h:real^M->real) w)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    EXPAND_TAC "h" THEN SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z:real^M. lift(norm z * abs(wan_dpart i (wan_mke e) z))) =
    (\z. inv e pow dimindex(:M) % lift((h:real^M->real)(inv e % z + vec 0)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; VECTOR_ADD_RID] THEN X_GEN_TAC `z:real^M` THEN
    AP_TERM_TAC THEN EXPAND_TAC "h" THEN ASM_SIMP_TAC[WAN_MKE_DPART] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`; REAL_POW_ADD; REAL_POW_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w:real^M. lift((h:real^M->real) w)`;
                 `integral (:real^M) (\w. lift((h:real^M->real) w))`; `(:real^M)`;
                 `inv e`; `vec 0:real^M`] HAS_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; REAL_INV_EQ_0; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_NEG_0; VECTOR_ADD_RID; REAL_INV_INV] THEN
  SUBGOAL_THEN `IMAGE (\x:real^M. e % x) (:real^M) = (:real^M)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^M` THEN
    EXISTS_TAC `inv e % y:real^M` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv e pow dimindex(:M)` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[VECTOR_ADD_RID] THEN
  SUBGOAL_THEN `inv e pow dimindex(:M) * inv(abs(inv e) pow dimindex(:M)) = &1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < e ==> abs e = e`] THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN
    ASM_SIMP_TAC[REAL_POW_NZ; REAL_INV_EQ_0; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_LID; LIFT_DROP]);;

let WAN_FRIEDRICHS_IDENTITY = prove
 (`!e i (a:real^M->real) (f:real^M->real^K) x.
     &0 < e /\ (\x. lift(a x)) continuous_on (:real^M) /\ wan_lloc (:real^M) f
     ==> wan_kconv (wan_dpart i (wan_mke e)) (\y. a y % f y) x -
         a x % wan_kconv (wan_dpart i (wan_mke e)) f x =
         integral (:real^M) (\y. (wan_dpart i (wan_mke e) (x - y) * (a y - a x)) % f y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_test (:real^M) (wan_dpart i (wan_mke e))` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_TEST_DPART_TEST THEN ASM_SIMP_TAC[WAN_MKE_TEST]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (\y. (a:real^M->real) y % (f:real^M->real^K) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[wan_kconv] THEN
  SUBGOAL_THEN
   `(\y. wan_dpart i (wan_mke e) (x - y) % (a:real^M->real) y % (f:real^M->real^K) y)
      integrable_on (:real^M) /\
    (\y. wan_dpart i (wan_mke e) (x - y) % (f:real^M->real^K) y) integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
     [MP_TAC(ISPECL [`wan_dpart i (wan_mke e):real^M->real`;
                     `\y. (a:real^M->real) y % (f:real^M->real^K) y`; `x:real^M`]
                    WAN_KCONV_INTEGRABLE);
      MP_TAC(ISPECL [`wan_dpart i (wan_mke e):real^M->real`; `f:real^M->real^K`;
                     `x:real^M`] WAN_KCONV_INTEGRABLE)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a:real^M->real) x % integral (:real^M)
       (\y. wan_dpart i (wan_mke e) (x - y) % (f:real^M->real^K) y) =
    integral (:real^M) (\y. a x % (wan_dpart i (wan_mke e) (x - y) % f y))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_SUB; INTEGRABLE_CMUL] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC);;

let WAN_FRIEDRICHS = prove
 (`!i. ?D. &0 <= D /\
           !e (a:real^M->real) L (f:real^M->real^K).
             &0 < e /\ (\x. lift(a x)) continuous_on (:real^M) /\ &0 <= L /\
             (!x y. abs(a x - a y) <= L * norm(x - y)) /\
             f IN lspace (:real^M) (&2)
             ==> (\x. wan_kconv (wan_dpart i (wan_mke e)) (\y. a y % f y) x -
                      a x % wan_kconv (wan_dpart i (wan_mke e)) f x)
                   IN lspace (:real^M) (&2) /\
                 drop(integral (:real^M)
                        (\x. lift(norm(wan_kconv (wan_dpart i (wan_mke e))
                                                 (\y. a y % f y) x -
                                       a x % wan_kconv (wan_dpart i (wan_mke e)) f x)
                                  pow 2)))
                 <= (L * D) pow 2 * drop(integral (:real^M) (\x. lift(norm(f x) pow 2)))`,
  GEN_TAC THEN
  X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC
    (SPEC `i:num` (INST_TYPE [`:M`,`:M`] WAN_MK_WEIGHTED_L1)) THEN
  EXISTS_TAC `D:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (f:real^M->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_L2_LLOC]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_test (:real^M) (wan_dpart i (wan_mke e))` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_TEST_DPART_TEST THEN ASM_SIMP_TAC[WAN_MKE_TEST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. wan_kconv (wan_dpart i (wan_mke e)) (\y. (a:real^M->real) y % (f:real^M->real^K) y) x -
         a x % wan_kconv (wan_dpart i (wan_mke e)) f x) measurable_on (:real^M)`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC WAN_KCONV_SMOOTH THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC WAN_KCONV_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. wan_kconv (wan_dpart i (wan_mke e)) (\y. (a:real^M->real) y % (f:real^M->real^K) y) x -
         a x % wan_kconv (wan_dpart i (wan_mke e)) f x) =
    (\x. integral (:real^M) (\y. (wan_dpart i (wan_mke e) (x - y) * (a y - a x)) % f y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC WAN_FRIEDRICHS_IDENTITY THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!z:real^M. ~(norm z <= e) ==> wan_dpart i (wan_mke e) z = &0` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN EXISTS_TAC `cball(vec 0:real^M,e)` THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[WAN_MKE_PROPS];
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WAN_MKE_ZERO THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_dpart i (wan_mke e):real^M->real`; `cball(vec 0:real^M,e)`]
                WAN_SMOOTH_SUPPORT_BOUNDS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0] THEN CONJ_TAC THENL
     [UNDISCH_TAC `wan_test (:real^M) (wan_dpart i (wan_mke e))` THEN SIMP_TAC[wan_test];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:real` o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 <= G` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(wan_dpart i (wan_mke e) (vec 0:real^M))` THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x y:real^M. wan_dpart i (wan_mke e) (x - y) * ((a:real^M->real) y - a x)`;
                 `\z:real^M. L * (norm z * abs(wan_dpart i (wan_mke e) z))`;
                 `f:real^M->real^K`; `L * D`; `L * (e * G)`] WAN_KERNEL_L2_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(MP (SPEC `e:real` (ASSUME
      `!e. &0 < e
           ==> ((\z:real^M. lift(norm z * abs(wan_dpart i (wan_mke e) z))) has_integral
                lift D) (:real^M)`)) (ASSUME `&0 < e`)) THEN
    DISCH_THEN(MP_TAC o SPEC `L:real` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[integrable_on];
      GEN_TAC THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_ABS_POS];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `norm(z:real^M) <= e` THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS];
          ASM_SIMP_TAC[REAL_ABS_NUM; REAL_MUL_RZERO] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
      REWRITE_TAC[LIFT_DROP; REAL_LE_REFL];
      MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `L * (n * d) = d * (L * n)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^M` THEN MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN
        SUBGOAL_THEN `(\y:real^M. lift(wan_dpart i (wan_mke e) (x - y))) =
                      (\z. lift(wan_dpart i (wan_mke e) z)) o (\y. x - y)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN
        MP_TAC(ISPECL [`(:real^M)`; `wan_dpart i (wan_mke e):real^M->real`; `i:num`]
                      WAN_TEST_CONTINUOUS) THEN ASM_SIMP_TAC[ETA_AX];
        REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]]];
    ASM_SIMP_TAC[WAN_FRIEDRICHS_IDENTITY]]);;

(* ========================================================================= *)
(* The mollification wan_moll e in the forms used downstream.                *)
(* ========================================================================= *)

let WAN_MOLL_PARTIAL = prove
 (`!e (u:real^M->real^K) i x.
     &0 < e /\ wan_lloc (:real^M) u
     ==> partial_derivative i (wan_moll e u) x =
         wan_kconv (wan_dpart i (wan_mke e)) u x`,
  SIMP_TAC[wan_moll; WAN_KCONV_PARTIAL; WAN_MKE_TEST]);;

let WAN_MOLL_WPD = prove
 (`!e (u:real^M->real^K) v i x.
     &0 < e /\ wan_wpd (:real^M) i u v
     ==> partial_derivative i (wan_moll e u) x = wan_moll e v x`,
  SIMP_TAC[wan_moll; WAN_KCONV_WPD; WAN_MKE_TEST]);;

let WAN_MOLL_TRANSLATE = prove
 (`!e (u:real^M->real^K) c x.
     wan_moll e (\y. u(y + c)) x = wan_moll e u (x + c)`,
  REWRITE_TAC[wan_moll; WAN_KCONV_TRANSLATE]);;

let WAN_MOLL_SUPPORT = prove
 (`!e (u:real^M->real^K) t.
     &0 < e /\ (!y. ~(y IN t) ==> u y = vec 0)
     ==> !x. ~(x IN {a + b | a IN t /\ b IN ball(vec 0,e)}) ==> wan_moll e u x = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wan_moll] THEN
  MATCH_MP_TAC WAN_KCONV_SUPPORT THEN ASM_SIMP_TAC[WAN_MKE_ZERO]);;

(* ========================================================================= *)
(* Convergence in L^2.  For a compactly supported map in L^2,               *)
(* the integral of |wan_moll e u - u|^2 tends to 0 with e (approximation by  *)
(* continuous compactly supported maps, uniform convergence for those, and  *)
(* the L^2 contraction).                                                     *)
(* ========================================================================= *)

let WAN_CC_MOLL_CONV = prove
 (`!(h:real^M->real^K) k eps.
     h continuous_on (:real^M) /\ compact k /\ (!x. ~(x IN k) ==> h x = vec 0) /\
     &0 < eps
     ==> ?d. &0 < d /\
             !e. &0 < e /\ e < d
                 ==> drop(integral (:real^M) (\x. lift(norm(wan_moll e h x - h x) pow 2)))
                     < eps`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `kk = {a + b:real^M | a IN k /\ b IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact(kk:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  ABBREV_TAC `m = measure(kk:real^M->bool)` THEN
  SUBGOAL_THEN `&0 <= m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC MEASURE_POS_LE THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT];
    ALL_TAC] THEN
  ABBREV_TAC `eta = sqrt(eps / (m + &1))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta pow 2 * m < eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `&0 < eps / (m + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_ARITH `a / b * m = (a * m) / b`] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= m ==> &0 < m + &1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^M->real^K`; `kk:real^M->bool`] WAN_MOLL_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "un"))) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (h:real^M->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x IN kk) ==> wan_moll e (h:real^M->real^K) x - h x = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((x:real^M) IN k) /\
                  ~(x IN {a + b:real^M | a IN k /\ b IN ball(vec 0,e)})`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real^M) IN kk)` THEN EXPAND_TAC "kk" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0; IN_BALL_0] THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN CONJ_TAC THENL
       [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `vec 0:real^M`]) THEN
        ASM_REWRITE_TAC[NORM_0; REAL_POS; VECTOR_ADD_RID];
        MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`e:real`; `h:real^M->real^K`; `k:real^M->bool`] WAN_MOLL_SUPPORT) THEN
    ASM_SIMP_TAC[VECTOR_SUB_RZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `eta pow 2 * m` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^M)
                 (\x. if x IN kk then lift(eta pow 2) else vec 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `kk:real^M->bool` THEN
      ASM_SIMP_TAC[NORM_0; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC WAN_MOLL_SMOOTH THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
      ASM_SIMP_TAC[INTEGRABLE_ON_CONST; MEASURABLE_COMPACT];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[LIFT_DROP; DROP_VEC; NORM_0; REAL_POW_ZERO; ARITH_EQ; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      USE_THEN "un" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN
    ASM_SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_COMPACT; DROP_CMUL; LIFT_DROP] THEN
    REAL_ARITH_TAC]);;

let WAN_CC_APPROX = prove
 (`!(u:real^M->real^K) c eps.
     compact c /\ (!x. ~(x IN c) ==> u x = vec 0) /\ u IN lspace (:real^M) (&2) /\
     &0 < eps
     ==> ?h k. h continuous_on (:real^M) /\ compact k /\
               (!x. ~(x IN k) ==> h x = vec 0) /\
               drop(integral (:real^M) (\x. lift(norm(u x - h x) pow 2))) < eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^M->bool`; `vec 0:real^M`] BOUNDED_SUBSET_BALL) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = ball(vec 0:real^M,R + &1)` THEN
  SUBGOAL_THEN `measurable(s:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[MEASURABLE_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^M->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
    EXPAND_TAC "s" THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^M->real^K`; `s:real^M->bool`; `&2`; `sqrt eps`]
                LSPACE_APPROXIMATE_CONTINUOUS) THEN
  ASM_SIMP_TAC[SQRT_POS_LT] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^K` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `chi = \x:real^M. smooth_bump R (R + &1) x` THEN
  SUBGOAL_THEN
   `(\x. lift((chi:real^M->real) x)) continuous_on (:real^M) /\
    (!x. &0 <= chi x /\ chi x <= &1) /\
    (!x. norm x <= R ==> chi x = &1) /\ (!x. R + &1 <= norm x ==> chi x = &0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "chi" THEN REWRITE_TAC[SMOOTH_BUMP_BOUNDS] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^M. chi x % (g:real^M->real^K) x`; `cball(vec 0:real^M,R + &1)`] THEN
  REWRITE_TAC[COMPACT_CBALL] THEN
  SUBGOAL_THEN `(\x:real^M. (chi:real^M->real) x % (g:real^M->real^K) x) continuous_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^M. ~(x IN cball(vec 0,R + &1)) ==> chi x % (g:real^M->real^K) x = vec 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(chi:real^M->real) x = &0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. norm((u:real^M->real^K) x - chi x % g x) <= (if x IN s then norm(u x - g x) else &0)`
  (LABEL_TAC "pb") THENL
   [X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN c` THENL
     [SUBGOAL_THEN `(x:real^M) IN s /\ (chi:real^M->real) x = &1` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `c SUBSET ball(vec 0:real^M,R)` THEN EXPAND_TAC "s" THEN
        REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_LE_REFL]];
      ASM_SIMP_TAC[VECTOR_SUB_LZERO; NORM_NEG; NORM_MUL] THEN COND_CASES_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= x /\ x <= &1 ==> abs x <= &1`];
        SUBGOAL_THEN `(chi:real^M->real) x = &0` (fun th -> REWRITE_TAC[th]) THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `~((x:real^M) IN s)` THEN
          EXPAND_TAC "s" THEN REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LZERO; REAL_LE_REFL]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^M. (chi:real^M->real) x % (g:real^M->real^K) x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `cball(vec 0:real^M,R + &1)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; COMPACT_CBALL; SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `drop(integral s (\x. lift(norm((u:real^M->real^K) x - g x) pow 2)))` THEN
  SUBGOAL_THEN `(\x. (u:real^M->real^K) x - g x) IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^M)`; `&2`;
                     `\x:real^M. (u:real^M->real^K) x - chi x % g x`]
                    LSPACE_IMP_INTEGRABLE) THEN
      ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; RPOW_POW];
      REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
      MP_TAC(ISPECL [`s:real^M->bool`; `&2`; `\x:real^M. (u:real^M->real^K) x - g x`]
                    LSPACE_IMP_INTEGRABLE) THEN
      ASM_SIMP_TAC[RPOW_POW];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "pb" (MP_TAC o SPEC `x:real^M`) THEN
      COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_VEC] THEN DISCH_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
        SUBGOAL_THEN `norm((u:real^M->real^K) x - chi x % g x) = &0` SUBST1_TAC THENL
         [MP_TAC(ISPEC `(u:real^M->real^K) x - chi x % g x` NORM_POS_LE) THEN
          ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]]];
    MP_TAC(ISPECL [`s:real^M->bool`; `&2`; `\x:real^M. (u:real^M->real^K) x - g x`]
                  LNORM_RPOW) THEN
    ASM_REWRITE_TAC[RPOW_POW] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `eps = sqrt eps pow 2` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_SIMP_TAC[LNORM_POS_LE; ARITH_EQ]]);;

let WAN_THREE_SQUARES = prove
 (`!a b c:real^N. norm(a + b - c) pow 2 <=
                  &3 * (norm a pow 2 + norm b pow 2 + norm c pow 2)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(norm(a:real^N) + norm(b:real^N) + norm(c:real^N)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONV_TAC NORM_ARITH;
    MP_TAC(SPEC `norm(a:real^N) - norm(b:real^N)` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `norm(b:real^N) - norm(c:real^N)` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `norm(a:real^N) - norm(c:real^N)` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC]);;

let WAN_MOLL_L2_CONV = prove
 (`!(u:real^M->real^K) c.
     compact c /\ (!x. ~(x IN c) ==> u x = vec 0) /\ u IN lspace (:real^M) (&2)
     ==> !eps. &0 < eps
               ==> ?d. &0 < d /\
                       !e. &0 < e /\ e < d
                           ==> drop(integral (:real^M)
                                      (\x. lift(norm(wan_moll e u x - u x) pow 2)))
                               < eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^M->real^K`; `c:real^M->bool`; `eps / &12`] WAN_CC_APPROX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^K`
    (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`h:real^M->real^K`; `k:real^M->bool`; `eps / &6`] WAN_CC_MOLL_CONV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hc")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  USE_THEN "hc" (fun th -> MP_TAC(MP (SPEC `e:real` th)
                     (CONJ (ASSUME `&0 < e`) (ASSUME `e < d`)))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^M->real^K) IN lspace (:real^M) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (u:real^M->real^K) x - h x) IN lspace (:real^M) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real`; `\x. (u:real^M->real^K) x - h x`] WAN_MOLL_L2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real`; `u:real^M->real^K`] WAN_MOLL_L2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real`; `h:real^M->real^K`] WAN_MOLL_L2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. wan_moll e (\x. (u:real^M->real^K) x - h x) x =
                    wan_moll e u x - wan_moll e h x`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[wan_moll; wan_kconv; VECTOR_SUB_LDISTRIB] THEN
    MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST; WAN_L2_LLOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^M->real^K. f IN lspace (:real^M) (&2)
                       ==> (\x. lift(norm(f x) pow 2)) integrable_on (:real^M)`
  (LABEL_TAC "sq") THENL
   [GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE) THEN
    REWRITE_TAC[RPOW_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(wan_moll e (\x. (u:real^M->real^K) x - h x) x) pow 2))
      integrable_on (:real^M) /\
    (\x. lift(norm(wan_moll e (h:real^M->real^K) x - h x) pow 2)) integrable_on (:real^M) /\
    (\x. lift(norm((u:real^M->real^K) x - h x) pow 2)) integrable_on (:real^M) /\
    (\x. lift(norm(wan_moll e (u:real^M->real^K) x - u x) pow 2)) integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "sq" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(wan_moll e (h:real^M->real^K) x - h x) pow 2) +
         lift(norm((u:real^M->real^K) x - h x) pow 2)) integrable_on (:real^M)`
  ASSUME_TAC THENL [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(wan_moll e (\x. (u:real^M->real^K) x - h x) x) pow 2) +
         lift(norm(wan_moll e h x - h x) pow 2) +
         lift(norm(u x - h x) pow 2)) integrable_on (:real^M)`
  ASSUME_TAC THENL [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC
   `&3 * (drop(integral (:real^M)
                 (\x. lift(norm(wan_moll e (\x. (u:real^M->real^K) x - h x) x) pow 2))) +
          drop(integral (:real^M) (\x. lift(norm(wan_moll e h x - h x) pow 2))) +
          drop(integral (:real^M) (\x. lift(norm(u x - h x) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral (:real^M)
             (\x. &3 % (lift(norm(wan_moll e (\x. (u:real^M->real^K) x - h x) x) pow 2) +
                        lift(norm(wan_moll e h x - h x) pow 2) +
                        lift(norm(u x - h x) pow 2))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[DROP_CMUL; DROP_ADD; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`wan_moll e (u:real^M->real^K) x - wan_moll e h x`;
                     `wan_moll e (h:real^M->real^K) x - h x`;
                     `(u:real^M->real^K) x - h x`] WAN_THREE_SQUARES) THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_CMUL; INTEGRAL_ADD; DROP_CMUL; DROP_ADD; REAL_LE_REFL]];
    ASM_REAL_ARITH_TAC]);;

