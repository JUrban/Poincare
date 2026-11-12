(* ========================================================================= *)
(* pc_wan_lipx: tools for locally Lipschitz weak solutions, used in Part 2B  *)
(* (MT Lemmas 9.21-9.31): the fundamental lemma for continuous functions     *)
(* (= 0 and >= 0 forms), the approximation of nonnegative Lipschitz test     *)
(* functions by smooth ones (mollification; the result W-B), and the weak    *)
(* convergence of a.e. derivatives of uniformly locally Lipschitz, locally   *)
(* uniformly convergent sequences (the result W-A).                          *)
(* ========================================================================= *)

needs "src/pc_wan_moll.ml";;

prioritize_real();;
type_invention_error := true;;

let WAN_TEST_MUL_CONT_INTEGRABLE = prove
 (`!(s:real^M->bool) f phi.
     open s /\ (\x. lift(f x)) continuous_on s /\ wan_test s phi
     ==> (\x. lift(f x * phi x)) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `phi:real^M->real`; `\x. lift((f:real^M->real) x)`]
                WAN_TEST_PAIRING) THEN
  ASM_SIMP_TAC[WAN_CONTINUOUS_ON_LLOC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL] THEN GEN_TAC THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC REAL_MUL_SYM);;

let WAN_CONT_NEG_BALL = prove
 (`!(s:real^M->bool) (f:real^M->real) x0.
     open s /\ (\x. lift(f x)) continuous_on s /\ x0 IN s /\ f x0 < &0
     ==> ?r. &0 < r /\ ball(x0,r) SUBSET s /\ !x. x IN ball(x0,r) ==> f x < f x0 / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift((f:real^M->real) x)`; `s:real^M->bool`]
                CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x0:real^M`) THEN
  ASM_REWRITE_TAC[continuous_at; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `--((f:real^M->real) x0) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `x0:real^M` (REWRITE_RULE[OPEN_CONTAINS_BALL]
    (ASSUME `open(s:real^M->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^M,d2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (is_forall o concl)) THEN
    ASM_MESON_TAC[DIST_SYM; REAL_ARITH `abs(a - b) < --b / &2 ==> a < b / &2`]]);;

let WAN_FUNDAMENTAL_CONT_POS = prove
 (`!(s:real^M->bool) f.
     open s /\ (\x. lift(f x)) continuous_on s /\
     (!phi. wan_test s phi /\ (!x. &0 <= phi x)
            ==> &0 <= drop(integral s (\x. lift(f x * phi x))))
     ==> !x. x IN s ==> &0 <= f x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))) THEN
  X_GEN_TAC `x0:real^M` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real`; `x0:real^M`] WAN_CONT_NEG_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ball(x0:real^M,r)`; `x0:real^M`] WAN_TEST_BUMP) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^M->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. ~(x IN ball(x0:real^M,r)) ==> (phi:real^M->real) x = &0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `wan_test (ball(x0:real^M,r)) phi` THEN REWRITE_TAC[wan_test] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_test s (phi:real^M->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_TEST_SUBSET THEN EXISTS_TAC `ball(x0:real^M,r)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ d <= r /\
        !x. x IN ball(x0:real^M,d) ==> &1 / &2 < (phi:real^M->real) x`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. lift((phi:real^M->real) x)) continuous_on (:real^M)` MP_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      UNDISCH_TAC `wan_test (ball(x0:real^M,r)) phi` THEN SIMP_TAC[wan_test];
      ALL_TAC] THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `x0:real^M`) THEN
    REWRITE_TAC[continuous_at; DIST_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d1 r` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (is_forall o concl)) THEN
    ASM_MESON_TAC[DIST_SYM; REAL_ARITH `abs(a - &1) < &1 / &2 ==> &1 / &2 < a`];
    ALL_TAC] THEN
  REMOVE_THEN "H" (MP_TAC o SPEC `phi:real^M->real`) THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `drop(integral s (\x. if x IN ball(x0:real^M,d)
                                   then lift((f:real^M->real) x0 / &4) else vec 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC WAN_TEST_MUL_CONT_INTEGRABLE THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `ball(x0:real^M,d) SUBSET s` (fun th -> SIMP_TAC[INTEGRABLE_RESTRICT; th])
      THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^M,r)` THEN
        ASM_SIMP_TAC[SUBSET_BALL];
        REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL]];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^M) IN ball(x0,d)` THEN ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC] THENL
       [SUBGOAL_THEN `(x:real^M) IN ball(x0,r)` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`x0:real^M`; `d:real`; `r:real`] SUBSET_BALL) THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(f:real^M->real) x < f x0 / &2 /\ &1 / &2 < (phi:real^M->real) x`
        STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        MP_TAC(SPECL [`--((f:real^M->real) x)`; `(phi:real^M->real) x - &1 / &2`]
                     REAL_LT_MUL) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ASM_CASES_TAC `(x:real^M) IN ball(x0,r)` THENL
         [SUBGOAL_THEN `(f:real^M->real) x < &0` ASSUME_TAC THENL
           [MATCH_MP_TAC(REAL_ARITH `!b. a < b / &2 /\ b < &0 ==> a < &0`) THEN
            EXISTS_TAC `(f:real^M->real) x0` THEN ASM_SIMP_TAC[];
            ALL_TAC] THEN
          MP_TAC(SPECL [`--((f:real^M->real) x)`; `(phi:real^M->real) x`] REAL_LE_MUL) THEN
          ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]]];
    SUBGOAL_THEN `ball(x0:real^M,d) SUBSET s` (fun th -> SIMP_TAC[INTEGRAL_RESTRICT; th])
    THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^M,r)` THEN
      ASM_SIMP_TAC[SUBSET_BALL];
      ALL_TAC] THEN
    SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < m * --c ==> m * c < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[MEASURE_BALL_POS] THEN
    ASM_REAL_ARITH_TAC]);;

let WAN_FUNDAMENTAL_CONT = prove
 (`!(s:real^M->bool) f.
     open s /\ (\x. lift(f x)) continuous_on s /\
     (!phi. wan_test s phi ==> integral s (\x. lift(f x * phi x)) = vec 0)
     ==> !x. x IN s ==> f x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real`] WAN_FUNDAMENTAL_CONT_POS) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. --((f:real^M->real) x)`]
                WAN_FUNDAMENTAL_CONT_POS) THEN
  ASM_SIMP_TAC[DROP_VEC; REAL_LE_REFL; LIFT_NEG; CONTINUOUS_ON_NEG] THEN
  REWRITE_TAC[REAL_MUL_LNEG; LIFT_NEG] THEN
  SUBGOAL_THEN `!phi. wan_test s phi
                      ==> integral s (\x. --lift((f:real^M->real) x * phi x)) = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. lift((f:real^M->real) x * phi x)`; `s:real^M->bool`] INTEGRAL_NEG) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; WAN_TEST_MUL_CONT_INTEGRABLE;
                 VECTOR_NEG_0];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DROP_VEC; REAL_LE_REFL] THEN
  MESON_TAC[REAL_ARITH `&0 <= --a /\ &0 <= a ==> a = &0`]);;

(* ========================================================================= *)
(* Helpers.  Lipschitz bounds for compactly supported                      *)
(* locally Lipschitz maps, sup and Lipschitz bounds and positivity of      *)
(* mollifications, L^1 smallness from L^2 smallness on a set of finite     *)
(* measure, L^1 convergence of mollifications, directional derivatives as  *)
(* sums of partials.                                                         *)
(* ========================================================================= *)

let WAN_LOCLIP_SUPPORT_LIPSCHITZ = prove
 (`!(s:real^M->bool) (psi:real^M->real) k.
     open s /\ wan_loclip s psi /\ compact k /\ k SUBSET s /\
     (!x. ~(x IN k) ==> psi x = &0)
     ==> ?L. &0 <= L /\ !x y. abs(psi x - psi y) <= L * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `kk = {x + y:real^M | x IN k /\ y IN cball(vec 0,d)}` THEN
  SUBGOAL_THEN `(k:real^M->bool) SUBSET kk` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^M. x IN k /\ ~(y IN kk) ==> d < norm(x - y)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((y:real^M) IN kk)` THEN EXPAND_TAC "kk" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:real^M`; `y - x:real^M`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0; VECTOR_ARITH `x + y - x:real^N = y`] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `kk:real^M->bool` (REWRITE_RULE[wan_loclip]
    (ASSUME `wan_loclip s (psi:real^M->real)`))) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `L1:real`) THEN
  SUBGOAL_THEN `?B. !x. abs((psi:real^M->real) x) <= B` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. lift((psi:real^M->real) x)`; `k:real^M->bool`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B:real` THEN X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(x:real^M) IN k` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `max (abs L1) (abs B / d)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 <= max a b`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^M. x IN k /\ ~(y IN kk)
                 ==> abs(psi x - psi y) <= max (abs L1) (abs B / d) * norm(x - y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(psi:real^M->real) y = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs B / d * norm(x - y:real^M)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `d < norm(x - y:real^M)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `abs B / d * n = (abs B * n) / d`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs B * d` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * d` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN
          SUBGOAL_THEN `abs((psi:real^M->real) x) <= B` MP_TAC THENL
           [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[REAL_LE_REFL] THEN
          MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN
  ASM_CASES_TAC `(x:real^M) IN kk /\ (y:real^M) IN kk` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L1 * norm(x - y:real^M)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `~((x:real^M) IN k) /\ ~((y:real^M) IN k)` THENL
   [ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 <= max a b`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((x:real^M) IN k /\ ~(y IN kk)) \/ (y IN k /\ ~(x IN kk))`
  STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[];
    ASM_SIMP_TAC[];
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[]]);;

let WAN_MOLL_NORM_BOUND = prove
 (`!e (w:real^M->real^K) M x.
     &0 < e /\ wan_lloc (:real^M) w /\ (!y. norm(w y) <= M)
     ==> norm(wan_moll e w x) <= M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_moll; wan_kconv] THEN
  MP_TAC(ISPECL [`e:real`; `x:real^M`] WAN_MKE_INTEGRAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^M) (\y. M % lift(wan_mke e (x - y:real^M))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN REWRITE_TAC[integrable_on] THEN
      EXISTS_TAC `lift(&1)` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_MUL; DROP_CMUL; LIFT_DROP] THEN
      SUBGOAL_THEN `&0 <= wan_mke e (x - y:real^M)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[WAN_MKE_POS]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[]];
    MP_TAC(ISPECL [`\y. lift(wan_mke e (x - y:real^M))`; `M:real`; `(:real^M)`]
                  INTEGRAL_CMUL) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[integrable_on] THEN EXISTS_TAC `lift(&1)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC]);;

let WAN_MOLL_LIP = prove
 (`!e (psi:real^M->real) L.
     &0 < e /\ (!x y. abs(psi x - psi y) <= L * norm(x - y))
     ==> !x y. abs(drop(wan_moll e (\z. lift(psi z)) x) -
                   drop(wan_moll e (\z. lift(psi z)) y)) <= L * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!c. (\z. lift((psi:real^M->real)(z + c))) continuous_on (:real^M)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN EXISTS_TAC `L:real` THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a + c:real^M`; `b + c:real^M`] o
      check (fun th -> is_forall(concl th) &&
                       length(fst(strip_forall(concl th))) = 2)) THEN
    REWRITE_TAC[VECTOR_ARITH `(x + c) - (y + c):real^N = x - y`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((psi:real^M->real) z)) continuous_on (:real^M)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^M`) THEN REWRITE_TAC[VECTOR_ADD_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real`; `\z. lift((psi:real^M->real) z)`; `y - x:real^M`; `x:real^M`]
                WAN_MOLL_TRANSLATE) THEN
  REWRITE_TAC[VECTOR_ARITH `x + y - x:real^N = y`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_1] THEN
  SUBGOAL_THEN
   `wan_moll e (\z. lift((psi:real^M->real) z)) x -
    wan_moll e (\z. lift(psi(z + (y - x)))) x =
    wan_moll e (\z. lift(psi z) - lift(psi(z + (y - x)))) x`
  SUBST1_TAC THENL
   [REWRITE_TAC[wan_moll; wan_kconv; VECTOR_SUB_LDISTRIB] THEN
    MP_TAC(ISPECL [`\z. wan_mke e (x - z) % lift((psi:real^M->real) z)`;
                   `\z. wan_mke e (x - z) % lift((psi:real^M->real) (z + (y - x)))`;
                   `(:real^M)`] INTEGRAL_SUB) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
       [MP_TAC(ISPECL [`wan_mke e:real^M->real`; `\z. lift((psi:real^M->real) z)`;
                       `x:real^M`] WAN_KCONV_INTEGRABLE);
        MP_TAC(ISPECL [`wan_mke e:real^M->real`;
                       `\z. lift((psi:real^M->real) (z + (y - x)))`;
                       `x:real^M`] WAN_KCONV_INTEGRABLE)] THEN
      ASM_SIMP_TAC[WAN_MKE_TEST; WAN_CONTINUOUS_LLOC];
      REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_MOLL_NORM_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^M` THEN REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^M`; `z + (y - x):real^M`] o
      check (fun th -> is_forall(concl th) &&
                       length(fst(strip_forall(concl th))) = 2)) THEN
    REWRITE_TAC[VECTOR_ARITH `z - (z + (y - x)):real^N = x - y`]]);;

let WAN_MOLL_NONNEG = prove
 (`!e (psi:real^M->real) x.
     &0 < e /\ (\z. lift(psi z)) continuous_on (:real^M) /\ (!z. &0 <= psi z)
     ==> &0 <= drop(wan_moll e (\z. lift(psi z)) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_moll; wan_kconv] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`wan_mke e:real^M->real`; `\z. lift((psi:real^M->real) z)`;
                   `x:real^M`] WAN_KCONV_INTEGRABLE) THEN
    ASM_SIMP_TAC[WAN_MKE_TEST; WAN_CONTINUOUS_LLOC];
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[WAN_MKE_POS]]);;

let WAN_L1_SMALL_FROM_L2 = prove
 (`!(h:real^M->real^K) c t.
     measurable c /\ (!x. ~(x IN c) ==> h x = vec 0) /\
     h IN lspace (:real^M) (&2) /\ &0 < t
     ==> (\x. lift(norm(h x))) integrable_on (:real^M) /\
         drop(integral (:real^M) (\x. lift(norm(h x)))) <=
         t * drop(integral (:real^M) (\x. lift(norm(h x) pow 2))) + measure c / t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(norm((h:real^M->real^K) x) pow 2)) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `g = \x:real^M. t % lift(norm((h:real^M->real^K) x) pow 2) +
                   (if x IN c then lift(inv t) else vec 0)` THEN
  SUBGOAL_THEN `(g:real^M->real^1) integrable_on (:real^M)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_ON_CONST] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. norm(lift(norm((h:real^M->real^K) x))) <= drop((g:real^M->real^1) x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    ASM_CASES_TAC `(x:real^M) IN c` THEN ASM_SIMP_TAC[DROP_VEC; LIFT_DROP] THENL
     [ABBREV_TAC `a = norm((h:real^M->real^K) x)` THEN
      SUBGOAL_THEN `&0 <= a` ASSUME_TAC THENL
       [EXPAND_TAC "a" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
      ASM_CASES_TAC `&1 <= t * a` THENL
       [MATCH_MP_TAC(REAL_ARITH `a <= t * a pow 2 /\ &0 <= i ==> a <= t * a pow 2 + i`) THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
        SUBGOAL_THEN `t * a pow 2 = (t * a) * a` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 <= t * a pow 2 /\ a <= i ==> a <= t * a pow 2 + i`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
          ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM real_div; REAL_ARITH `inv t = &1 / t`] THEN
          ASM_REAL_ARITH_TAC]];
      REWRITE_TAC[NORM_0; REAL_ARITH `&0 pow 2 = &0`; REAL_MUL_RZERO; REAL_ADD_LID;
                  REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(norm((h:real^M->real^K) x))) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `g:real^M->real^1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_ON_NORM THEN
    UNDISCH_TAC `(h:real^M->real^K) IN lspace (:real^M) (&2)` THEN
    SIMP_TAC[lspace; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^M) (g:real^M->real^1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MP_TAC(SPEC `x:real^M` (ASSUME
      `!x. norm(lift(norm((h:real^M->real^K) x))) <= drop((g:real^M->real^1) x)`)) THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM; LIFT_DROP];
    EXPAND_TAC "g" THEN
    SUBGOAL_THEN
     `integral (:real^M)
        (\x. t % lift(norm((h:real^M->real^K) x) pow 2) +
             (if x IN c then lift(inv t) else vec 0)) =
      t % integral (:real^M) (\x. lift(norm(h x) pow 2)) +
      integral (:real^M) (\x. if x IN c then lift(inv t) else vec 0)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`\x. t % lift(norm((h:real^M->real^K) x) pow 2)`;
                     `\x:real^M. if x IN c then lift(inv t) else vec 0`;
                     `(:real^M)`] INTEGRAL_ADD) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_ON_CONST] THEN
          ASM_REWRITE_TAC[]];
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MP_TAC(ISPECL [`\x. lift(norm((h:real^M->real^K) x) pow 2)`; `t:real`;
                       `(:real^M)`] INTEGRAL_CMUL) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_RESTRICT_UNIV; INTEGRAL_CONST_GEN; DROP_ADD; DROP_CMUL;
                 LIFT_DROP] THEN
    REWRITE_TAC[real_div; REAL_LE_REFL]]);;

let WAN_MOLL_L1_CONV = prove
 (`!(g:real^M->real^K) c.
     compact c /\ (!x. ~(x IN c) ==> g x = vec 0) /\ g IN lspace (:real^M) (&2)
     ==> !eps. &0 < eps
               ==> ?d. &0 < d /\
                       !e. &0 < e /\ e < d
                           ==> (\x. lift(norm(wan_moll e g x - g x))) integrable_on
                               (:real^M) /\
                               drop(integral (:real^M)
                                      (\x. lift(norm(wan_moll e g x - g x)))) < eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  ABBREV_TAC `c1 = {x + y:real^M | x IN c /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact(c1:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN MATCH_MP_TAC COMPACT_SUMS THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  ABBREV_TAC `t = &2 * (measure(c1:real^M->bool) + &1) / eps` THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= m ==> &0 < m + &1`) THEN
    ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^M->real^K`; `c:real^M->bool`] WAN_MOLL_L2_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `eps / (&2 * t)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. wan_moll e (g:real^M->real^K) x - g x`; `c1:real^M->bool`; `t:real`]
                WAN_L1_SMALL_FROM_L2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((x:real^M) IN c)` ASSUME_TAC THENL
       [UNDISCH_TAC `~((x:real^M) IN c1)` THEN EXPAND_TAC "c1" THEN
        REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN DISCH_TAC THEN
        MAP_EVERY EXISTS_TAC [`x:real^M`; `vec 0:real^M`] THEN
        ASM_REWRITE_TAC[CENTRE_IN_CBALL; REAL_POS; VECTOR_ADD_RID];
        ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_SUB_RZERO] THEN
      MP_TAC(ISPECL [`e:real`; `g:real^M->real^K`; `c:real^M->bool`] WAN_MOLL_SUPPORT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `~((x:real^M) IN c1)` THEN EXPAND_TAC "c1" THEN
      REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`a:real^M`; `b:real^M`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(b:real^M) IN ball(vec 0,e)` THEN
      REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[WAN_MOLL_L2; REAL_POS] THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_MOLL_L2]];
    ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `t * drop(integral (:real^M)
                        (\x. lift(norm(wan_moll e (g:real^M->real^K) x - g x) pow 2))) +
              measure(c1:real^M->bool) / t` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `t * drop(integral (:real^M)
              (\x. lift(norm(wan_moll e (g:real^M->real^K) x - g x) pow 2))) < eps / &2 /\
    measure(c1:real^M->bool) / t < eps / &2`
  MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `drop(integral (:real^M)
            (\x. lift(norm(wan_moll e (g:real^M->real^K) x - g x) pow 2))) < eps / (&2 * t)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`drop(integral (:real^M)
                    (\x. lift(norm(wan_moll e (g:real^M->real^K) x - g x) pow 2)))`;
                  `eps:real`; `&2 * t`] REAL_LT_RDIV_EQ) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> &0 < &2 * t`] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `eps / &2 * t = measure(c1:real^M->bool) + &1` SUBST1_TAC THENL
     [EXPAND_TAC "t" THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
      REAL_ARITH_TAC]]);;

let WAN_FRECHET_DIR_SUM = prove
 (`!(f:real^M->real^1) x v.
     f differentiable (at x)
     ==> drop(frechet_derivative f (at x) v) =
         sum(1..dimindex(:M)) (\i. v$i * drop(frechet_derivative f (at x) (basis i)))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; DROP_VSUM; DROP_CMUL]);;

(* ========================================================================= *)
(* Nonnegative Lipschitz test functions with compact                       *)
(* support are approximated by test functions (mollification), with       *)
(* uniform convergence and L^1 convergence of directional derivatives       *)
(* (the result W-B).                                                         *)
(* ========================================================================= *)

let WAN_LIP_GLOBAL_FACTS = prove
 (`!(psi:real^M->real) L k.
     &0 <= L /\ (!x y. abs(psi x - psi y) <= L * norm(x - y)) /\ compact k /\
     (!x. ~(x IN k) ==> psi x = &0)
     ==> negligible {x | ~((\y. lift(psi y)) differentiable at x)} /\
         (!i. wan_wpd (:real^M) i (\x. lift(psi x)) (\x. lift(wan_dpart i psi x))) /\
         (!i x. ~(x IN k) ==> wan_dpart i psi x = &0) /\
         (!i. (\x. lift(wan_dpart i psi x)) IN lspace (:real^M) (&2)) /\
         (!v x. (\y. lift(psi y)) differentiable at x
                ==> drop(frechet_derivative (\y. lift(psi y)) (at x) v) =
                    sum(1..dimindex(:M)) (\i. v$i * wan_dpart i psi x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `negligible {x | ~((\y. lift((psi:real^M->real) y)) differentiable at x)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RADEMACHER_UNIV THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. wan_wpd (:real^M) i (\x. lift((psi:real^M->real) x)) (\x. lift(wan_dpart i psi x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_LIP_WPD THEN REWRITE_TAC[OPEN_UNIV; wan_loclip] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i x. ~(x IN k) ==> wan_dpart i (psi:real^M->real) x = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `open((:real^M) DIFF k)` MP_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_UNIV; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `((\y. lift((psi:real^M->real) y)) has_derivative (\h. vec 0)) (at x)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`\y:real^M. vec 0:real^1`; `r:real`] THEN
      ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN X_GEN_TAC `y:real^M` THEN
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `ball(x:real^M,r) SUBSET (:real^M) DIFF k` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
      DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[wan_dpart] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[DROP_VEC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `(\x. lift(wan_dpart i (psi:real^M->real) x))
                  absolutely_integrable_on (:real^M)` ASSUME_TAC THENL
     [MP_TAC(SPEC `i:num` (ASSUME
        `!i. wan_wpd (:real^M) i (\x. lift((psi:real^M->real) x))
                     (\x. lift(wan_dpart i psi x))`)) THEN
      REWRITE_TAC[wan_wpd; wan_lloc] THEN
      DISCH_THEN(MP_TAC o SPEC `k:real^M->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; IN_UNIV] THEN X_GEN_TAC `x:real^M` THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[LIFT_NUM];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o
      GEN_REWRITE_RULE I [ABSOLUTELY_INTEGRABLE_MEASURABLE]) THEN
    REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC
     [`\x. lift(L * norm(lift(wan_dpart i (psi:real^M->real) x)))`;
      `{x | ~((\y. lift((psi:real^M->real) y)) differentiable at x)}`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN
      MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
      DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_POW; REAL_ABS_ABS] THEN
      SUBGOAL_THEN `abs(wan_dpart i (psi:real^M->real) x) <= L` ASSUME_TAC THENL
       [REWRITE_TAC[wan_dpart] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * norm(basis i:real^M)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC WAN_LIP_DERIV_BOUND THEN EXISTS_TAC `&1` THEN
          ASM_REWRITE_TAC[REAL_LT_01];
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
          ASM_CASES_TAC `1 <= i /\ i <= dimindex(:M)` THENL
           [ASM_SIMP_TAC[NORM_BASIS; REAL_LE_REFL];
            SUBGOAL_THEN `basis i:real^M = vec 0` SUBST1_TAC THENL
             [ASM_REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG]; REWRITE_TAC[NORM_0; REAL_POS]]]];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\y. lift((psi:real^M->real) y)`; `x:real^M`; `v:real^M`]
                  WAN_FRECHET_DIR_SUM) THEN
    ASM_REWRITE_TAC[wan_dpart]]);;

let WAN_MOLL_DIR_DERIV = prove
 (`!(psi:real^M->real) L e v x.
     &0 <= L /\ (!x y. abs(psi x - psi y) <= L * norm(x - y)) /\ &0 < e
     ==> drop(frechet_derivative (wan_moll e (\y. lift(psi y))) (at x) v) =
         sum(1..dimindex(:M))
            (\i. v$i * drop(wan_moll e (\y. lift(wan_dpart i psi y)) x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (\y. lift((psi:real^M->real) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_moll e (\y. lift((psi:real^M->real) y))`; `x:real^M`; `v:real^M`]
                WAN_FRECHET_DIR_SUM) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^M)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; WAN_MOLL_SMOOTH];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`e:real`; `\y. lift((psi:real^M->real) y)`;
                 `\y. lift(wan_dpart i (psi:real^M->real) y)`; `i:num`; `x:real^M`]
                WAN_MOLL_WPD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_LIP_WPD THEN
    REWRITE_TAC[OPEN_UNIV; wan_loclip] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[partial_derivative]]);;

let WAN_MOLL_SEQ_L1 = prove
 (`!(g:real^M->real^K) c (ee:num->real).
     compact c /\ (!x. ~(x IN c) ==> g x = vec 0) /\ g IN lspace (:real^M) (&2) /\
     (!n. &0 < ee n /\ ee n <= inv(&n + &1))
     ==> (!n. (\x. lift(norm(wan_moll (ee n) g x - g x))) integrable_on (:real^M)) /\
         ((\n. lift(drop(integral (:real^M) (\x. lift(norm(wan_moll (ee n) g x - g x))))))
          --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c1 = {x + y:real^M | x IN c /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact(c1:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n x. ~(x IN c1)
          ==> wan_moll ((ee:num->real) n) (g:real^M->real^K) x - g x = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~((x:real^M) IN c)` ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real^M) IN c1)` THEN EXPAND_TAC "c1" THEN
      REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real^M`; `vec 0:real^M`] THEN
      ASM_REWRITE_TAC[CENTRE_IN_CBALL; REAL_POS; VECTOR_ADD_RID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_SUB_RZERO] THEN
    MP_TAC(ISPECL [`(ee:num->real) n`; `g:real^M->real^K`; `c:real^M->bool`]
                  WAN_MOLL_SUPPORT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~((x:real^M) IN c1)` THEN EXPAND_TAC "c1" THEN
    REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`a:real^M`; `b:real^M`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b:real^M) IN ball(vec 0,(ee:num->real) n)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN
    MP_TAC(SPEC `n:num` (ASSUME `!n. &0 < (ee:num->real) n /\ ee n <= inv(&n + &1)`)) THEN
    MP_TAC(SPEC `&n + &1` REAL_INV_LE_1) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_LE_ADDL; REAL_POS]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. lift(norm(wan_moll ((ee:num->real) n) (g:real^M->real^K) x - g x)))
        integrable_on (:real^M)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`\x. wan_moll ((ee:num->real) n) (g:real^M->real^K) x - g x`;
                   `c1:real^M->bool`; `&1`] WAN_L1_SMALL_FROM_L2) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT; REAL_LT_01] THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[WAN_MOLL_L2; REAL_POS] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_MOLL_L2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; NORM_LIFT] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^M->real^K`; `c:real^M->bool`] WAN_MOLL_L1_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `del:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(ee:num->real) n < del` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    UNDISCH_TAC `N:num <= n` THEN UNDISCH_TAC `~(N = 0)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `N:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < e ==> abs x < e`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE];
    FIRST_X_ASSUM(MP_TAC o SPEC `(ee:num->real) n` o
      check (fun th -> is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
    ASM_SIMP_TAC[]]);;

let WAN_LIP_TEST_APPROX = prove
 (`!(s:real^M->bool) (psi:real^M->real) k.
     open s /\ wan_loclip s psi /\ compact k /\ k SUBSET s /\
     (!x. ~(x IN k) ==> psi x = &0) /\ (!x. &0 <= psi x)
     ==> ?k' L (phi:num->real^M->real).
           compact k' /\ k' SUBSET s /\
           (!n. wan_test s (phi n) /\ (!x. &0 <= phi n x) /\
                (!x. ~(x IN k') ==> phi n x = &0) /\
                (!x y. abs(phi n x - phi n y) <= L * norm(x - y))) /\
           (!e. &0 < e ==> ?N. !n x. N <= n ==> abs(phi n x - psi x) < e) /\
           (!v. ((\n. integral (:real^M)
                        (\x. lift(abs(drop(frechet_derivative (\y. lift(phi n y)) (at x) v) -
                                      drop(frechet_derivative (\y. lift(psi y)) (at x) v)))))
                 --> vec 0) sequentially)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `psi:real^M->real`; `k:real^M->bool`]
                WAN_LOCLIP_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`psi:real^M->real`; `L:real`; `k:real^M->bool`] WAN_LIP_GLOBAL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift((psi:real^M->real) y)) continuous_on (:real^M)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `kk = {x + y:real^M | x IN k /\ y IN cball(vec 0,d)}` THEN
  SUBGOAL_THEN `(k:real^M->bool) SUBSET kk` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `d:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M0:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `ee = \n. inv(&(n + M0) + &1)` THEN
  SUBGOAL_THEN `!n. &0 < (ee:num->real) n /\ ee n < d /\ ee n <= inv(&n + &1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "ee" THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&M0)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      UNDISCH_TAC `~(M0 = 0)` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_EQ] THEN
      MP_TAC(SPEC `M0:num` REAL_POS) THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      MP_TAC(SPEC `M0:num` REAL_POS) THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n x. ~(x IN kk)
          ==> wan_moll ((ee:num->real) n) (\y. lift((psi:real^M->real) y)) x = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(ee:num->real) n`; `\y. lift((psi:real^M->real) y)`; `k:real^M->bool`]
                  WAN_MOLL_SUPPORT) THEN
    ASM_SIMP_TAC[LIFT_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~((x:real^M) IN kk)` THEN EXPAND_TAC "kk" THEN
    REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:real^M`; `b:real^M`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b:real^M) IN ball(vec 0,(ee:num->real) n)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN
    MP_TAC(SPEC `n:num` (ASSUME
      `!n. &0 < (ee:num->real) n /\ ee n < d /\ ee n <= inv(&n + &1)`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. lift(drop(wan_moll ((ee:num->real) n) (\y. lift((psi:real^M->real) y)) x))) =
        wan_moll (ee n) (\y. lift(psi y))`
  ASSUME_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`kk:real^M->bool`; `L:real`;
    `\n x. drop(wan_moll ((ee:num->real) n) (\y. lift((psi:real^M->real) y)) x)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[wan_test] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC];
        EXISTS_TAC `kk:real^M->bool` THEN ASM_SIMP_TAC[DROP_VEC]];
      X_GEN_TAC `x:real^M` THEN MATCH_MP_TAC WAN_MOLL_NONNEG THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[DROP_VEC];
      MATCH_MP_TAC WAN_MOLL_LIP THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\y. lift((psi:real^M->real) y)`; `kk:real^M->bool`]
                  WAN_MOLL_UNIFORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `eps / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `del:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ee:num->real) n < del` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      UNDISCH_TAC `N:num <= n` THEN UNDISCH_TAC `~(N = 0)` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
      MP_TAC(SPEC `N:num` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^M) IN kk` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`(ee:num->real) n`; `x:real^M`] o
        check (fun th -> is_forall(concl th) &&
                         length(fst(strip_forall(concl th))) = 2 &&
                         can (find_term ((=) `del:real`)) (concl th))) THEN
      ASM_SIMP_TAC[] THEN
      REWRITE_TAC[NORM_1; DROP_SUB; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~((x:real^M) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^M` THEN
  ABBREV_TAC `nd = {x:real^M | ~((\y. lift((psi:real^M->real) y)) differentiable at x)}` THEN
  SUBGOAL_THEN
   `!i. (!n. (\x. lift(norm(wan_moll ((ee:num->real) n)
                                    (\y. lift(wan_dpart i (psi:real^M->real) y)) x -
                            lift(wan_dpart i psi x)))) integrable_on (:real^M)) /\
        ((\n. lift(drop(integral (:real^M)
                         (\x. lift(norm(wan_moll (ee n) (\y. lift(wan_dpart i psi y)) x -
                                        lift(wan_dpart i psi x)))))))
         --> vec 0) sequentially`
  (LABEL_TAC "conv") THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_MOLL_SEQ_L1 THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_SIMP_TAC[LIFT_NUM; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. sum(1..dimindex(:M))
          (\i. abs((v:real^M)$i) *
               drop(integral (:real^M)
                      (\x. lift(norm(wan_moll ((ee:num->real) n)
                                       (\y. lift(wan_dpart i (psi:real^M->real) y)) x -
                                     lift(wan_dpart i psi x))))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    ABBREV_TAC
     `G = \x:real^M. lift(norm(vsum(1..dimindex(:M))
                    (\i. (v:real^M)$i %
                         (wan_moll ((ee:num->real) n)
                            (\y. lift(wan_dpart i (psi:real^M->real) y)) x -
                          lift(wan_dpart i psi x)))))` THEN
    ABBREV_TAC
     `H = \x:real^M. vsum(1..dimindex(:M))
                    (\i. abs((v:real^M)$i) %
                         lift(norm(wan_moll ((ee:num->real) n)
                                     (\y. lift(wan_dpart i (psi:real^M->real) y)) x -
                                   lift(wan_dpart i psi x))))` THEN
    SUBGOAL_THEN `(H:real^M->real^1) integrable_on (:real^M)` ASSUME_TAC THENL
     [EXPAND_TAC "H" THEN MATCH_MP_TAC INTEGRABLE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN USE_THEN "conv" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `!x. norm((G:real^M->real^1) x) <= drop((H:real^M->real^1) x)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^M` THEN MAP_EVERY EXPAND_TAC ["G"; "H"] THEN
      REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM; DROP_VSUM; o_DEF; DROP_CMUL; LIFT_DROP] THEN
      MP_TAC(ISPECL
       [`\i. (v:real^M)$i %
             (wan_moll ((ee:num->real) n)
                (\y. lift(wan_dpart i (psi:real^M->real) y)) x -
              lift(wan_dpart i psi x))`; `1..dimindex(:M)`] VSUM_NORM) THEN
      REWRITE_TAC[FINITE_NUMSEG; NORM_MUL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(G:real^M->real^1) integrable_on (:real^M)` ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
      EXISTS_TAC `H:real^M->real^1` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN
      MATCH_MP_TAC MEASURABLE_ON_NORM THEN MATCH_MP_TAC MEASURABLE_ON_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MEASURABLE_ON_CMUL THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC WAN_MOLL_SMOOTH THEN
        ASM_SIMP_TAC[WAN_L2_LLOC];
        FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
          can (find_term ((=) `lspace:(real^M->bool)->real->(real^M->real^1)->bool`))
              (concl th))) THEN
        SIMP_TAC[lspace; IN_ELIM_THM]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `integral (:real^M)
        (\x. lift(abs(drop(frechet_derivative
                           (wan_moll ((ee:num->real) n) (\y. lift((psi:real^M->real) y)))
                           (at x) v) -
                     drop(frechet_derivative (\y. lift(psi y)) (at x) v)))) =
      integral (:real^M) (G:real^M->real^1)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `nd:real^M->bool` THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN X_GEN_TAC `x:real^M` THEN
      EXPAND_TAC "nd" THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      EXPAND_TAC "G" THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`psi:real^M->real`; `L:real`; `(ee:num->real) n`; `v:real^M`;
                     `x:real^M`] WAN_MOLL_DIR_DERIV) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[NORM_1; DROP_VSUM; o_DEF; DROP_CMUL; DROP_SUB; LIFT_DROP] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (:real^M) (H:real^M->real^1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "H" THEN
      SUBGOAL_THEN
       `integral (:real^M)
          (\x. vsum(1..dimindex(:M))
                 (\i. abs((v:real^M)$i) %
                      lift(norm(wan_moll ((ee:num->real) n)
                                  (\y. lift(wan_dpart i (psi:real^M->real) y)) x -
                                lift(wan_dpart i psi x))))) =
        vsum(1..dimindex(:M))
          (\i. integral (:real^M)
                 (\x. abs(v$i) %
                      lift(norm(wan_moll (ee n) (\y. lift(wan_dpart i psi y)) x -
                                lift(wan_dpart i psi x)))))`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL
         [`\i x. abs((v:real^M)$i) %
                 lift(norm(wan_moll ((ee:num->real) n)
                             (\y. lift(wan_dpart i (psi:real^M->real) y)) x -
                           lift(wan_dpart i psi x)))`;
          `(:real^M)`; `1..dimindex(:M)`] INTEGRAL_VSUM) THEN
        REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
         [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
          USE_THEN "conv" (fun th -> REWRITE_TAC[th]);
          REWRITE_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[DROP_VSUM; o_DEF] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL
       [`\x. lift(norm(wan_moll ((ee:num->real) n)
                           (\y. lift(wan_dpart i (psi:real^M->real) y)) x -
                         lift(wan_dpart i psi x)))`;
        `abs((v:real^M)$i)`; `(:real^M)`] INTEGRAL_CMUL) THEN
      ANTS_TAC THENL [USE_THEN "conv" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_CMUL]];
    REWRITE_TAC[LIFT_SUM; o_DEF; LIFT_CMUL] THEN
    SUBGOAL_THEN `vec 0:real^1 = vsum(1..dimindex(:M)) (\i. abs((v:real^M)$i) % vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_MUL_RZERO; VSUM_0]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_CMUL THEN
    USE_THEN "conv" (fun th -> REWRITE_TAC[th])]);;

(* ========================================================================= *)
(* Weak convergence of a.e. derivatives of uniformly                        *)
(* Lipschitz, locally uniformly convergent sequences against bounded        *)
(* measurable compactly supported weights (the result W-A). First the global *)
(* Lipschitz case (WAN_LIP_IBP_UNIV for mollified weights, L^1 approximation *)
(* of the weight), then the local case by Kirszbraun extensions.             *)
(* ========================================================================= *)

let WAN_LIP_DERIV_MEASURABLE = prove
 (`!(u:real^M->real) L v.
     (!x y. abs(u x - u y) <= L * norm(x - y))
     ==> (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v))) measurable_on
         (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
  MAP_EVERY EXISTS_TAC
   [`\n x. (&n + &1) % (lift((u:real^M->real)(x + inv(&n + &1) % v)) - lift(u x))`;
    `{x:real^M | ~((\y. lift((u:real^M->real) y)) differentiable at x)}`] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN EXISTS_TAC `L:real` THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a + inv(&n + &1) % v:real^M`;
                                    `b + inv(&n + &1) % v:real^M`]) THEN
      REWRITE_TAC[VECTOR_ARITH `(x + c) - (y + c):real^N = x - y`];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC RADEMACHER_UNIV THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`\y. lift((u:real^M->real) y)`;
                   `frechet_derivative (\y. lift((u:real^M->real) y)) (at x)`;
                   `x:real^M`; `v:real^M`] WAN_DIFF_QUOT_LIMIT) THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let WAN_BOUNDED_MEASURABLE_FACTS = prove
 (`!(X:real^M->real) B k.
     compact k /\ (!x. ~(x IN k) ==> X x = &0) /\
     (\x. lift(X x)) measurable_on (:real^M) /\ (!x. abs(X x) <= B)
     ==> (\x. lift(X x)) absolutely_integrable_on (:real^M) /\
         wan_lloc (:real^M) (\x. lift(X x)) /\
         (\x. lift(X x)) IN lspace (:real^M) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. measurable c ==> (\x:real^M. if x IN c then lift B else vec 0) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_ON_CONST] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((X:real^M->real) x)) absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\x:real^M. if x IN k then lift B else vec 0` THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_LIFT; LIFT_DROP; DROP_VEC; REAL_ABS_NUM;
                                     REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^M)` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x:real^M. if x IN k then lift(B pow 2) else vec 0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN
    MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_ON_CONST] THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_LIFT; LIFT_DROP; DROP_VEC; REAL_ABS_NUM;
                                   REAL_ABS_POW; REAL_ABS_ABS; LIFT_NUM; NORM_0;
                                   REAL_POW_2; REAL_MUL_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let WAN_LIP_DERIV_TIMES_BOUNDED = prove
 (`!(u:real^M->real) L (X:real^M->real) B k v.
     &0 <= L /\ (!x y. abs(u x - u y) <= L * norm(x - y)) /\
     compact k /\ (!x. ~(x IN k) ==> X x = &0) /\
     (\x. lift(X x)) measurable_on (:real^M) /\ (!x. abs(X x) <= B)
     ==> (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * X x))
           integrable_on (:real^M) /\
         norm(integral (:real^M)
                (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * X x)))
         <= L * norm v * drop(integral (:real^M) (\x. lift(abs(X x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^M->real`; `B:real`; `k:real^M->bool`]
                WAN_BOUNDED_MEASURABLE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(abs((X:real^M->real) x))) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. lift((X:real^M->real) x)`; `(:real^M)`]
                  ABSOLUTELY_INTEGRABLE_MEASURABLE) THEN
    ASM_REWRITE_TAC[NORM_LIFT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `nd = {x:real^M | ~((\y. lift((u:real^M->real) y)) differentiable at x)}` THEN
  SUBGOAL_THEN `negligible(nd:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "nd" THEN MATCH_MP_TAC RADEMACHER_UNIV THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. ~(x IN nd)
        ==> abs(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v))
            <= L * norm(v:real^M)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN EXPAND_TAC "nd" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_TAC THEN MATCH_MP_TAC WAN_LIP_DERIV_BOUND THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v) * X x))
    integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC
     [`\x. lift(L * norm(v:real^M) * abs((X:real^M->real) x))`; `nd:real^M->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC MEASURABLE_ON_MUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC WAN_LIP_DERIV_MEASURABLE THEN
        EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[LIFT_CMUL] THEN REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_MUL; REAL_ABS_ABS] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\x. lift(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v) * X x)`;
    `\x. lift(L * norm(v:real^M) * abs((X:real^M->real) x))`; `(:real^M)`;
    `nd:real^M->bool`] INTEGRAL_NORM_BOUND_INTEGRAL_AE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_MUL; REAL_ABS_ABS] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[LIFT_CMUL] THEN
  SUBGOAL_THEN
   `integral (:real^M) (\x. L % (norm(v:real^M) % lift(abs((X:real^M->real) x)))) =
    L % (norm v % integral (:real^M) (\x. lift(abs(X x))))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\x. norm(v:real^M) % lift(abs((X:real^M->real) x))`; `L:real`;
                   `(:real^M)`] INTEGRAL_CMUL) THEN
    ANTS_TAC THENL [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\x. lift(abs((X:real^M->real) x))`; `norm(v:real^M)`;
                   `(:real^M)`] INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[DROP_CMUL; REAL_MUL_ASSOC]]);;

let WAN_FRECHET_ZERO_OUTSIDE = prove
 (`!(f:real^M->real^N) k x.
     closed k /\ (!y. ~(y IN k) ==> f y = vec 0) /\ ~(x IN k)
     ==> frechet_derivative f (at x) = (\h. vec 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open((:real^M) DIFF k)` MP_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\y:real^M. vec 0:real^N`; `r:real`] THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN X_GEN_TAC `y:real^M` THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `ball(x:real^M,r) SUBSET (:real^M) DIFF k` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Differences of two Lipschitz directional derivatives against a bounded    *)
(* measurable weight with compact support.                                   *)
(* ------------------------------------------------------------------------- *)

let WAN_LIP_DIFF_TIMES_BOUNDED = prove
 (`!(u:real^M->real) w L (Y:real^M->real) B k v.
     &0 <= L /\ (!x y. abs(u x - u y) <= L * norm(x - y)) /\
     (!x y. abs(w x - w y) <= L * norm(x - y)) /\
     compact k /\ (!x. ~(x IN k) ==> Y x = &0) /\
     (\x. lift(Y x)) measurable_on (:real^M) /\ (!x. abs(Y x) <= B)
     ==> (\x. lift((drop(frechet_derivative (\y. lift(u y)) (at x) v) -
                    drop(frechet_derivative (\y. lift(w y)) (at x) v)) * Y x))
           integrable_on (:real^M) /\
         integral (:real^M)
           (\x. lift((drop(frechet_derivative (\y. lift(u y)) (at x) v) -
                      drop(frechet_derivative (\y. lift(w y)) (at x) v)) * Y x)) =
         integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * Y x)) -
         integral (:real^M) (\x. lift(drop(frechet_derivative (\y. lift(w y)) (at x) v) * Y x)) /\
         norm(integral (:real^M)
           (\x. lift((drop(frechet_derivative (\y. lift(u y)) (at x) v) -
                      drop(frechet_derivative (\y. lift(w y)) (at x) v)) * Y x)))
         <= &2 * L * norm v * drop(integral (:real^M) (\x. lift(abs(Y x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^M->real`; `L:real`; `Y:real^M->real`; `B:real`; `k:real^M->bool`;
                 `v:real^M`] WAN_LIP_DERIV_TIMES_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^M->real`; `L:real`; `Y:real^M->real`; `B:real`; `k:real^M->bool`;
                 `v:real^M`] WAN_LIP_DERIV_TIMES_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift((drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v) -
               drop(frechet_derivative (\y. lift((w:real^M->real) y)) (at x) v)) *
              (Y:real^M->real) x)) =
    (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * Y x) -
         lift(drop(frechet_derivative (\y. lift(w y)) (at x) v) * Y x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_SUB; REAL_SUB_RDISTRIB]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v) *
                           (Y:real^M->real) x)`;
                 `\x. lift(drop(frechet_derivative (\y. lift((w:real^M->real) y)) (at x) v) *
                           (Y:real^M->real) x)`;
                 `(:real^M)`] INTEGRAL_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^1) <= c /\ norm(b:real^1) <= c ==> norm(a - b) <= &2 * c`) THEN
    ASM_REWRITE_TAC[]]);;

let WAN_INTEGRAL_MUL_SPLIT = prove
 (`!(dd:real^M->real) Y Z.
     (\x. lift(dd x * Y x)) integrable_on (:real^M) /\
     (\x. lift(dd x * Z x)) integrable_on (:real^M)
     ==> integral (:real^M) (\x. lift(dd x * (Y x + Z x))) =
         integral (:real^M) (\x. lift(dd x * Y x)) +
         integral (:real^M) (\x. lift(dd x * Z x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB; LIFT_ADD] THEN
  MP_TAC(ISPECL [`\x. lift((dd:real^M->real) x * (Y:real^M->real) x)`;
                 `\x. lift((dd:real^M->real) x * (Z:real^M->real) x)`;
                 `(:real^M)`] INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Against a smooth compactly supported weight, uniform convergence of       *)
(* Lipschitz functions gives convergence of the weighted directional         *)
(* derivatives (integration by parts moves the derivative to the weight).    *)
(* ------------------------------------------------------------------------- *)

let WAN_LIP_DERIV_SMOOTH_WEIGHT_CONV = prove
 (`!(u:num->real^M->real) u0 (phi:real^M->real) ce L v.
     (!n x y. abs(u n x - u n y) <= L * norm(x - y)) /\
     (!x y. abs(u0 x - u0 y) <= L * norm(x - y)) /\
     smooth_map_on (:real^M) (\x. lift(phi x)) /\
     compact ce /\ (!x. ~(x IN ce) ==> phi x = &0) /\
     (!e. &0 < e ==> ?N. !n x. N <= n /\ x IN ce ==> abs(u n x - u0 x) < e)
     ==> ((\n. integral (:real^M)
                 (\x. lift(drop(frechet_derivative (\y. lift(u n y)) (at x) v) * phi x)) -
               integral (:real^M)
                 (\x. lift(drop(frechet_derivative (\y. lift(u0 y)) (at x) v) * phi x)))
          --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif")))))) THEN
  ABBREV_TAC `dphi = \x. drop(frechet_derivative (\y. lift((phi:real^M->real) y)) (at x) v)` THEN
  SUBGOAL_THEN `!x. drop(frechet_derivative (\y. lift((phi:real^M->real) y)) (at x) v) = dphi x`
  ASSUME_TAC THENL [EXPAND_TAC "dphi" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((dphi:real^M->real) x)) continuous_on (:real^M)` ASSUME_TAC THENL
   [EXPAND_TAC "dphi" THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x IN ce) ==> (dphi:real^M->real) x = &0` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN EXPAND_TAC "dphi" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\y. lift((phi:real^M->real) y)`; `ce:real^M->bool`; `x:real^M`]
                  WAN_FRECHET_ZERO_OUTSIDE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; LIFT_NUM]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; DROP_VEC]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^M->real. (!x y. abs(w x - w y) <= L * norm(x - y))
       ==> (\x. lift(w x * dphi x)) integrable_on (:real^M) /\
           integral (:real^M)
             (\x. lift(drop(frechet_derivative (\y. lift(w y)) (at x) v) * phi x)) =
           --(integral (:real^M) (\x. lift(w x * dphi x)))`
  (LABEL_TAC "ibp") THENL
   [X_GEN_TAC `w:real^M->real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w:real^M->real`; `L:real`; `phi:real^M->real`; `ce:real^M->bool`;
                   `v:real^M`] WAN_LIP_IBP_UNIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[VECTOR_NEG_NEG]] THEN
    MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `ce:real^M->bool` THEN
    ASM_SIMP_TAC[REAL_MUL_RZERO; LIFT_NUM] THEN
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. integral (:real^M)
          (\x. lift(drop(frechet_derivative (\y. lift((u:num->real^M->real) n y)) (at x) v) *
                    phi x)) -
        integral (:real^M)
          (\x. lift(drop(frechet_derivative (\y. lift((u0:real^M->real) y)) (at x) v) *
                    phi x)) =
        integral (:real^M) (\x. lift((u0 x - u n x) * dphi x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "ibp" (fun th ->
      MP_TAC(MATCH_MP th (SPEC `n:num` (ASSUME
        `!n x y. abs((u:num->real^M->real) n x - u n y) <= L * norm(x - y)`))) THEN
      MP_TAC(MATCH_MP th (ASSUME
        `!x y. abs((u0:real^M->real) x - u0 y) <= L * norm(x - y)`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    SUBGOAL_THEN
     `(\x. lift(((u0:real^M->real) x - (u:num->real^M->real) n x) * dphi x)) =
      (\x. lift(u0 x * dphi x) - lift(u n x * dphi x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_SUB; REAL_SUB_RDISTRIB]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. lift((u0:real^M->real) x * dphi x)`;
                   `\x. lift((u:num->real^M->real) n x * dphi x)`; `(:real^M)`]
                  INTEGRAL_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\x. lift(abs((dphi:real^M->real) x))) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `ce:real^M->bool` THEN
    ASM_SIMP_TAC[REAL_ABS_0; LIFT_NUM] THEN
    SUBGOAL_THEN `(\x. lift(abs((dphi:real^M->real) x))) = (\x. lift(norm(lift(dphi x))))`
    SUBST1_TAC THENL [REWRITE_TAC[NORM_LIFT]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `A = drop(integral (:real^M) (\x. lift(abs((dphi:real^M->real) x))))` THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps / (A + &1) /\ eps / (A + &1) * A < eps` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < eps / (A + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `eps / (A + &1) * A = eps - eps / (A + &1)` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD
       `~(A + &1 = &0) ==> eps / (A + &1) * A = eps - eps / (A + &1)`) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "unif" (MP_TAC o SPEC `eps / (A + &1)`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `drop(integral (:real^M)
                 (\x. lift(eps / (A + &1) * abs((dphi:real^M->real) x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REWRITE_TAC[IN_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `ce:real^M->bool` THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; LIFT_NUM] THEN
      MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[LIFT_SUB] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN EXISTS_TAC `L:real` THEN
      ASM_REWRITE_TAC[IN_UNIV];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_MUL] THEN
      ASM_CASES_TAC `(x:real^M) IN ce` THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_ABS_0; REAL_MUL_RZERO; REAL_LE_REFL]]];
    REWRITE_TAC[LIFT_CMUL] THEN
    MP_TAC(ISPECL [`\x. lift(abs((dphi:real^M->real) x))`; `eps / (A + &1)`; `(:real^M)`]
                  INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[DROP_CMUL]]);;

let WAN_LIP_DERIV_WEAK_CONV_GLOBAL = prove
 (`!(u:num->real^M->real) u0 (X:real^M->real) B k kk L v d.
     &0 <= L /\ (!n x y. abs(u n x - u n y) <= L * norm(x - y)) /\
     (!x y. abs(u0 x - u0 y) <= L * norm(x - y)) /\
     compact k /\ (!x. ~(x IN k) ==> X x = &0) /\
     (\x. lift(X x)) measurable_on (:real^M) /\ (!x. abs(X x) <= B) /\
     &0 < d /\ {x + y | x IN k /\ y IN cball(vec 0,d)} SUBSET kk /\
     (!e. &0 < e ==> ?N. !n x. N <= n /\ x IN kk ==> abs(u n x - u0 x) < e)
     ==> ((\n. integral (:real^M)
                 (\x. lift((drop(frechet_derivative (\y. lift(u n y)) (at x) v) -
                            drop(frechet_derivative (\y. lift(u0 y)) (at x) v)) * X x)))
          --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif")))))))))) THEN
  MP_TAC(ISPECL [`X:real^M->real`; `B:real`; `k:real^M->bool`]
                WAN_BOUNDED_MEASURABLE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  ABBREV_TAC `Lv = L * norm(v:real^M)` THEN
  SUBGOAL_THEN `&0 <= Lv` ASSUME_TAC THENL
   [EXPAND_TAC "Lv" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((X:real^M->real) x)`; `k:real^M->bool`] WAN_MOLL_L1_CONV) THEN
  ASM_SIMP_TAC[LIFT_NUM] THEN DISCH_THEN(MP_TAC o SPEC `eps / (&4 * (Lv + &1))`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min (del / &2) d` THEN
  SUBGOAL_THEN `&0 < e /\ e < del /\ e <= d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ce = {x + y:real^M | x IN k /\ y IN cball(vec 0,e)}` THEN
  SUBGOAL_THEN `compact(ce:real^M->bool) /\ ce SUBSET kk /\ k SUBSET ce`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "ce" THEN MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `{x + y:real^M | x IN k /\ y IN cball(vec 0,d)}` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "ce" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^M` THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^M` (X_CHOOSE_THEN `b:real^M` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`a:real^M`; `b:real^M`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(b:real^M) IN cball(vec 0,e)` THEN
      REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "ce" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`z:real^M`; `vec 0:real^M`] THEN
      ASM_REWRITE_TAC[CENTRE_IN_CBALL; VECTOR_ADD_RID] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `phi = \x. drop(wan_moll e (\z. lift((X:real^M->real) z)) x)` THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^M) (\x. lift((phi:real^M->real) x)) /\
    (!x. ~(x IN ce) ==> phi x = &0) /\ (!x. abs(phi x) <= abs B) /\
    (\x. lift(abs((X:real^M->real) x - phi x))) integrable_on (:real^M) /\
    drop(integral (:real^M) (\x. lift(abs(X x - phi x)))) < eps / (&4 * (Lv + &1))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. lift((phi:real^M->real) x)) = wan_moll e (\z. lift((X:real^M->real) z))`
    ASSUME_TAC THENL
     [EXPAND_TAC "phi" THEN REWRITE_TAC[FUN_EQ_THM; LIFT_DROP]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`e:real`; `\z. lift((X:real^M->real) z)`; `k:real^M->bool`]
                    WAN_MOLL_SUPPORT) THEN
      ASM_SIMP_TAC[LIFT_NUM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[DROP_VEC]] THEN
      UNDISCH_TAC `~((x:real^M) IN ce)` THEN EXPAND_TAC "ce" THEN
      REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`a:real^M`; `b:real^M`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(b:real^M) IN ball(vec 0,e)` THEN
      REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:real^M` THEN EXPAND_TAC "phi" THEN REWRITE_TAC[GSYM NORM_1] THEN
      MATCH_MP_TAC WAN_MOLL_NORM_BOUND THEN ASM_REWRITE_TAC[NORM_LIFT] THEN
      GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs x <= b ==> abs x <= abs b`) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
        can (find_term ((=) `del:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN EXPAND_TAC "phi" THEN
      REWRITE_TAC[NORM_1; DROP_SUB; LIFT_DROP] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_ABS_SUB;
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
        can (find_term ((=) `del:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> a < c ==> b < c`) THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN EXPAND_TAC "phi" THEN
      REWRITE_TAC[NORM_1; DROP_SUB; LIFT_DROP] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_ABS_SUB];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:num->real^M->real`; `u0:real^M->real`; `phi:real^M->real`;
                 `ce:real^M->bool`; `L:real`; `v:real^M`]
                WAN_LIP_DERIV_SMOOTH_WEIGHT_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e1:real` THEN DISCH_TAC THEN
    REMOVE_THEN "unif" (MP_TAC o SPEC `e1:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN DISCH_THEN(MP_TAC o SPEC `eps / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(u:num->real^M->real) n`; `u0:real^M->real`; `L:real`; `phi:real^M->real`;
                 `abs B`; `ce:real^M->bool`; `v:real^M`] WAN_LIP_DIFF_TIMES_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`(u:num->real^M->real) n`; `u0:real^M->real`; `L:real`;
                 `\x. (X:real^M->real) x - phi x`; `B + abs B`; `ce:real^M->bool`; `v:real^M`]
                WAN_LIP_DIFF_TIMES_BOUNDED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((x:real^M) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_SUB_REFL];
      REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      X_GEN_TAC `x:real^M` THEN
      MATCH_MP_TAC(REAL_ARITH `abs a <= b /\ abs c <= d ==> abs(a - c) <= b + d`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`\x. drop(frechet_derivative (\y. lift((u:num->real^M->real) n y)) (at x) v) -
         drop(frechet_derivative (\y. lift((u0:real^M->real) y)) (at x) v)`;
    `\x. (X:real^M->real) x - phi x`; `phi:real^M->real`] WAN_INTEGRAL_MUL_SPLIT) THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&2 * L * norm(v:real^M) *
    drop(integral (:real^M) (\x. lift(abs((X:real^M->real) x - phi x)))) < eps / &2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 <= drop(integral (:real^M) (\x. lift(abs((X:real^M->real) x - phi x))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_ABS_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `drop(integral (:real^M) (\x. lift(abs((X:real^M->real) x - phi x)))) *
      (&4 * (Lv + &1)) < eps`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= Lv ==> &0 < &4 * (Lv + &1)`];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&2 * L * norm(v:real^M) *
      drop(integral (:real^M) (\x. lift(abs((X:real^M->real) x - phi x)))) =
      &2 * Lv * drop(integral (:real^M) (\x. lift(abs(X x - phi x))))`
    SUBST1_TAC THENL [EXPAND_TAC "Lv" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a:real^1 b c. norm a <= c /\ norm b < eps / &2 /\ c < eps / &2
                   ==> norm(a + b) < eps`) THEN
  EXISTS_TAC
   `&2 * L * norm(v:real^M) *
    drop(integral (:real^M) (\x. lift(abs((X:real^M->real) x - phi x))))` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* W-A: the local form.  Uniformly locally Lipschitz u_n converging locally  *)
(* uniformly to u0 on an open set s: the directional derivatives converge    *)
(* weakly against bounded measurable weights with compact support in s.     *)
(* Proof: extend u_n and u0 from a compact neighbourhood kk of the support   *)
(* by Kirszbraun with a common constant, apply the global form, and note     *)
(* that the derivatives agree on the open set uu between the support and kk. *)
(* ------------------------------------------------------------------------- *)

let WAN_LIP_DERIV_WEAK_CONV = prove
 (`!(s:real^M->bool) (u:num->real^M->real) (u0:real^M->real) (X:real^M->real) k v.
     open s /\
     (!k'. compact k' /\ k' SUBSET s
           ==> ?L. !n x y. x IN k' /\ y IN k' ==> abs(u n x - u n y) <= L * norm(x - y)) /\
     (!k' e. compact k' /\ k' SUBSET s /\ &0 < e
             ==> ?N. !n x. N <= n /\ x IN k' ==> abs(u n x - u0 x) < e) /\
     compact k /\ k SUBSET s /\ (!x. ~(x IN k) ==> X x = &0) /\
     (\x. lift(X x)) measurable_on (:real^M) /\ (?B. !x. abs(X x) <= B)
     ==> ((\n. integral (:real^M)
                 (\x. lift((drop(frechet_derivative (\y. lift(u n y)) (at x) v) -
                            drop(frechet_derivative (\y. lift(u0 y)) (at x) v)) * X x)))
          --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lip")
   (CONJUNCTS_THEN2 (LABEL_TAC "conv") STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` MP_TAC) THEN
  ABBREV_TAC `kk = {x + y:real^M | x IN k /\ y IN cball(vec 0,d)}` THEN
  ABBREV_TAC `uu = {x + y:real^M | x IN k /\ y IN ball(vec 0,d)}` THEN
  STRIP_TAC THEN
  REMOVE_THEN "lip" (MP_TAC o SPEC `kk:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `L0:real`) THEN
  ABBREV_TAC `L = abs L0` THEN
  SUBGOAL_THEN
   `&0 <= L /\
    !n x y. x IN kk /\ y IN kk
            ==> abs((u:num->real^M->real) n x - u n y) <= L * norm(x - y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_ABS_POS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L0 * norm(x - y:real^M)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n x. N <= n /\ x IN kk ==> abs((u:num->real^M->real) n x - u0 x) < e`
  (LABEL_TAC "ukk") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "conv" (MP_TAC o SPECL [`kk:real^M->bool`; `e:real`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN kk /\ y IN kk ==> abs((u0:real^M->real) x - u0 y) <= L * norm(x - y)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `e3 = (abs((u0:real^M->real) x - u0 y) - L * norm(x - y:real^M)) / &3` THEN
    SUBGOAL_THEN `&0 < e3` ASSUME_TAC THENL [EXPAND_TAC "e3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ukk" (fun th -> X_CHOOSE_TAC `N:num` (MATCH_MP th (ASSUME `&0 < e3`))) THEN
    SUBGOAL_THEN
     `abs((u:num->real^M->real) N x - u0 x) < e3 /\ abs(u N y - u0 y) < e3`
    MP_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((u:num->real^M->real) N x - u N y) <= L * norm(x - y:real^M)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?G. !n. (!x y. norm((G:num->real^M->real^1) n x - G n y) <= L * norm(x - y)) /\
            (!x. x IN kk ==> G n x = lift((u:num->real^M->real) n x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC KIRSZBRAUN THEN ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g0. (!x y. norm((g0:real^M->real^1) x - g0 y) <= L * norm(x - y)) /\
         (!x. x IN kk ==> g0 x = lift((u0:real^M->real) x))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC KIRSZBRAUN THEN ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n x. drop((G:num->real^M->real^1) n x)`; `\x. drop((g0:real^M->real^1) x)`;
                 `X:real^M->real`; `B:real`; `k:real^M->bool`; `kk:real^M->bool`; `L:real`;
                 `v:real^M`; `d:real`] WAN_LIP_DERIV_WEAK_CONV_GLOBAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_1; SUBSET_REFL] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "ukk" (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
  ASM_CASES_TAC `(x:real^M) IN k` THENL
   [SUBGOAL_THEN `(x:real^M) IN uu` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `frechet_derivative (\y. lift(drop((G:num->real^M->real^1) n y))) (at x) =
      frechet_derivative (\y. lift((u:num->real^M->real) n y)) (at x)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `uu:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^M) IN kk` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[LIFT_DROP];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `frechet_derivative (\y. lift(drop((g0:real^M->real^1) y))) (at x) =
      frechet_derivative (\y. lift((u0:real^M->real) y)) (at x)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `uu:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^M) IN kk` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[LIFT_DROP];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_MUL_RZERO]]);;

