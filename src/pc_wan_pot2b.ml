(* ========================================================================= *)
(* pc_wan_pot2b: from weak solutions to smooth mollifications and back:      *)
(*   - mollifications of a very weak solution of Lap u = f solve             *)
(*     Lap u_e = f_e classically, with the sup and Hoelder bounds kept;      *)
(*   - uniform jet expansions pass to a.e. limits (the limit function        *)
(*     and the limit jets).                                                  *)
(* ========================================================================= *)

needs "src/pc_wan_pot2a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Mollified very weak solutions.                                            *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_MOLL_EQ = prove
 (`!(s:real^N->bool) (u:real^N->real) (f:real^N->real) (Ue:real^N->real^1) Fe e x.
     open s /\
     (!phi. wan_test s phi
            ==> integral s (\x. lift(u x * llap (\y:real^N. mat 1) phi x)) =
                integral s (\x. lift(f x * phi x))) /\
     wan_lloc (:real^N) Ue /\ wan_lloc (:real^N) Fe /\ &0 < e /\ cball(x,e) SUBSET s /\
     (!y. y IN cball(x,e) ==> Ue y = lift(u y) /\ Fe y = lift(f y))
     ==> llap (\y:real^N. mat 1) (\z. drop(wan_moll e Ue z)) x = drop(wan_moll e Fe x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_moll] THEN
  MP_TAC(ISPECL [`wan_mke e:real^N->real`; `Ue:real^N->real^1`; `x:real^N`] WANL_KCONV_LLAP) THEN
  ASM_SIMP_TAC[WAN_MKE_TEST] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `L = \z:real^N. sum(1..dimindex(:N)) (\i. wan_dpart i (wan_dpart i (wan_mke e)) z)` THEN
  SUBGOAL_THEN `!y:real^N. ~(y IN cball(x,e)) ==> L(x - y) = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "L" THEN MATCH_MP_TAC WANL_MKE_LAP_ZERO THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN
    UNDISCH_TAC `~((y:real^N) IN cball(x,e))` THEN REWRITE_TAC[IN_CBALL; dist];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. ~(y IN cball(x,e)) ==> wan_mke e (x - y) = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_MKE_ZERO THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y:real^N) IN cball(x,e))` THEN REWRITE_TAC[IN_CBALL; dist] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. sum(1..dimindex(:N)) (\i. wan_dpart i (wan_dpart i (wan_mke e)) (x - y)) =
               L(x - y)`
  (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\y:real^N. wan_mke e (x - y)` o check (fun th ->
    is_forall(concl th) && can (find_term (fun u -> u = `wan_test (s:real^N->bool)`)) (concl th))) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`wan_mke e:real^N->real`; `x:real^N`] WAN_TEST_UNIV_REFLECT) THEN
    ASM_SIMP_TAC[WAN_MKE_TEST; wan_test] THEN STRIP_TAC THEN
    EXISTS_TAC `cball(x:real^N,e)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_mke e:real^N->real`; `x:real^N`] WANL_LLAP_REFLECT) THEN
  ASM_SIMP_TAC[WAN_MKE_TEST] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `integral s (\y:real^N. lift(u y * L(x - y))) =
    integral (cball(x,e)) (\y. lift(u y * L(x - y))) /\
    integral s (\y:real^N. lift(f y * wan_mke e (x - y))) =
    integral (cball(x,e)) (\y. lift(f y * wan_mke e (x - y)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `cball(x:real^N,e)` THEN ASM_SIMP_TAC[SUBSET_REFL; REAL_MUL_RZERO; LIFT_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[wan_kconv] THEN
  SUBGOAL_THEN
   `integral (:real^N) (\y. L(x - y) % (Ue:real^N->real^1) y) =
    integral (cball(x,e)) (\y. L(x - y) % Ue y) /\
    integral (:real^N) (\y. wan_mke e (x - y) % (Fe:real^N->real^1) y) =
    integral (cball(x,e)) (\y. wan_mke e (x - y) % Fe y)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `cball(x:real^N,e)` THEN
    ASM_SIMP_TAC[SUBSET_REFL; SUBSET_UNIV; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (cball(x,e)) (\y. L(x - y) % (Ue:real^N->real^1) y) =
    integral (cball(x,e)) (\y:real^N. lift(u y * L(x - y))) /\
    integral (cball(x,e)) (\y. wan_mke e (x - y) % (Fe:real^N->real^1) y) =
    integral (cball(x,e)) (\y:real^N. lift(f y * wan_mke e (x - y)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let wanl_pt_zx = new_definition
 `wanl_pt_zx (s:real^N->bool) (g:real^N->real) = \y. if y IN s then lift(g y) else vec 0`;;

let wanl_pt_me = new_definition
 `wanl_pt_me e (s:real^N->bool) (g:real^N->real) (x:real^N) =
    drop(wan_moll e (wanl_pt_zx s g) x)`;;

let WANL_PT_ZX_LLOC = prove
 (`!(s:real^N->bool) (g:real^N->real) M.
     lebesgue_measurable s /\ (\x. lift(g x)) measurable_on s /\
     (!x. x IN s ==> abs(g x) <= M)
     ==> wan_lloc (:real^N) (wanl_pt_zx s g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_lloc; wanl_pt_zx; SUBSET_UNIV] THEN
  X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^N. lift(abs M)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[MEASURABLE_ON_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN MATCH_MP_TAC MEASURABLE_COMPACT THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRABLE_ON_CONST] THEN DISJ2_TAC THEN
    MATCH_MP_TAC MEASURABLE_COMPACT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    COND_CASES_TAC THEN REWRITE_TAC[NORM_LIFT; NORM_0; REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= m ==> x <= abs m`) THEN ASM_SIMP_TAC[]]);;

let WANL_PT_KINT_BOUND = prove
 (`!e (G:real^N->real^1) x M.
     &0 < e /\ (\y. wan_mke e (x - y) % G y) integrable_on (:real^N) /\
     (!y. y IN cball(x,e) ==> norm(G y) <= M)
     ==> norm(integral (:real^N) (\y. wan_mke e (x - y) % G y)) <= M`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^N) (\y. M % lift(wan_mke e (x - y))))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN REWRITE_TAC[integrable_on] THEN
      EXISTS_TAC `lift(&1)` THEN ASM_SIMP_TAC[WAN_MKE_INTEGRAL_AT];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_MUL; DROP_CMUL; LIFT_DROP] THEN
    MP_TAC(INST_TYPE [`:N`,`:M`] (SPEC `e:real` WAN_MKE_PROPS)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    ASM_CASES_TAC `(y:real^N) IN cball(x,e)` THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `wan_mke e (x - y:real^N) = &0` SUBST1_TAC THENL
       [MATCH_MP_TAC WAN_MKE_ZERO THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~((y:real^N) IN cball(x,e))` THEN REWRITE_TAC[IN_CBALL; dist] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL]]];
    MP_TAC(ISPECL [`e:real`; `x:real^N`] WAN_MKE_INTEGRAL_AT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `integral (:real^N) (\y. M % lift(wan_mke e (x - y))) = M % lift(&1)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[DROP_CMUL; LIFT_DROP; REAL_MUL_RID; REAL_LE_REFL]]]);;

let WANL_PT_CONST_LLOC = prove
 (`!c:real^1. wan_lloc (:real^N) (\y:real^N. c)`,
  REWRITE_TAC[wan_lloc; SUBSET_UNIV; ABSOLUTELY_INTEGRABLE_ON_CONST] THEN
  MESON_TAC[MEASURABLE_COMPACT]);;

let WANL_PT_ME_SMOOTH = prove
 (`!e (s:real^N->bool) g M.
     &0 < e /\ lebesgue_measurable s /\ (\x. lift(g x)) measurable_on s /\
     (!x. x IN s ==> abs(g x) <= M)
     ==> smooth_map_on (:real^N) (\x. lift(wanl_pt_me e s g x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wanl_pt_me; LIFT_DROP; ETA_AX] THEN
  MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WANL_PT_ZX_LLOC THEN ASM_MESON_TAC[]);;

let WANL_PT_ME_BOUND = prove
 (`!e (s:real^N->bool) g M x.
     &0 < e /\ lebesgue_measurable s /\ (\x. lift(g x)) measurable_on s /\ &0 <= M /\
     (!x. x IN s ==> abs(g x) <= M)
     ==> abs(wanl_pt_me e s g x) <= M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^N) (wanl_pt_zx s g)` ASSUME_TAC THENL
   [MATCH_MP_TAC WANL_PT_ZX_LLOC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[wanl_pt_me; WAN_MOLL_EQ; GSYM NORM_1] THEN
  MATCH_MP_TAC WANL_PT_KINT_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[wanl_pt_zx] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_LIFT; NORM_0]]);;

let WANL_PT_ME_CLOSE = prove
 (`!e (s:real^N->bool) g M x D.
     &0 < e /\ lebesgue_measurable s /\ (\x. lift(g x)) measurable_on s /\
     (!x. x IN s ==> abs(g x) <= M) /\ cball(x,e) SUBSET s /\
     (!y. y IN cball(x,e) ==> abs(g y - g x) <= D)
     ==> abs(wanl_pt_me e s g x - g x) <= D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^N) (wanl_pt_zx s g)` ASSUME_TAC THENL
   [MATCH_MP_TAC WANL_PT_ZX_LLOC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN REWRITE_TAC[CENTRE_IN_CBALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `g(x:real^N) = drop(wanl_pt_zx s g x)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[wanl_pt_zx; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[wanl_pt_me; GSYM DROP_SUB; GSYM NORM_1] THEN
  ASM_SIMP_TAC[WAN_MOLL_SUB] THEN MATCH_MP_TAC WANL_PT_KINT_BOUND THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
     [MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST];
      MP_TAC(ISPECL [`wan_mke e:real^N->real`; `\y:real^N. wanl_pt_zx s g (x:real^N)`;
                     `x:real^N`] WAN_KCONV_INTEGRABLE) THEN
      ASM_SIMP_TAC[WAN_MKE_TEST; WANL_PT_CONST_LLOC]];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[wanl_pt_zx; GSYM LIFT_SUB; NORM_LIFT] THEN ASM_SIMP_TAC[]]);;

let WANL_PT_ME_HOLDER = prove
 (`!e (s:real^N->bool) g M x x' D.
     &0 < e /\ lebesgue_measurable s /\ (\x. lift(g x)) measurable_on s /\
     (!x. x IN s ==> abs(g x) <= M) /\ cball(x,e) SUBSET s /\ cball(x',e) SUBSET s /\
     (!z. norm z <= e ==> abs(g(x - z) - g(x' - z)) <= D)
     ==> abs(wanl_pt_me e s g x - wanl_pt_me e s g x') <= D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^N) (wanl_pt_zx s g)` ASSUME_TAC THENL
   [MATCH_MP_TAC WANL_PT_ZX_LLOC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u = wanl_pt_zx (s:real^N->bool) g` THEN
  ABBREV_TAC `a:real^N = x' - x` THEN
  SUBGOAL_THEN
   `(\y. wan_mke e (x' - y) % (u:real^N->real^1) y) integrable_on (:real^N) /\
    (\y. wan_mke e (x - y) % (u:real^N->real^1) y) integrable_on (:real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. wan_mke e (x' - (a + y)) % (u:real^N->real^1) (a + y)) integrable_on (:real^N) /\
    integral (:real^N) (\y. wan_mke e (x' - (a + y)) % u (a + y)) =
    integral (:real^N) (\y. wan_mke e (x' - y) % u y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[integrable_on] THEN
      EXISTS_TAC `integral (:real^N) (\y. wan_mke e (x' - y) % (u:real^N->real^1) y)` THEN
      MP_TAC(ISPECL [`\z:real^N. wan_mke e (x' - z) % (u:real^N->real^1) z`;
                     `integral (:real^N) (\y. wan_mke e (x' - y) % (u:real^N->real^1) y)`;
                     `(:real^N)`; `a:real^N`] HAS_INTEGRAL_TRANSLATION) THEN
      REWRITE_TAC[TRANSLATION_UNIV] THEN ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
      MP_TAC(ISPECL [`\z:real^N. wan_mke e (x' - z) % (u:real^N->real^1) z`;
                     `(:real^N)`; `a:real^N`] INTEGRAL_TRANSLATION) THEN
      REWRITE_TAC[TRANSLATION_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. x' - (a + y) = x - y` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [EXPAND_TAC "a" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[wanl_pt_me; WAN_MOLL_EQ; GSYM DROP_SUB; GSYM NORM_1] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_SUB; GSYM VECTOR_SUB_LDISTRIB] THEN
  MATCH_MP_TAC WANL_PT_KINT_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN s /\ a + y IN s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (fun th -> concl th = `cball(x:real^N,e) SUBSET s`)) THEN
      ASM_REWRITE_TAC[IN_CBALL; dist];
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (fun th -> concl th = `cball(x':real^N,e) SUBSET s`)) THEN
      REWRITE_TAC[IN_CBALL; dist] THEN EXPAND_TAC "a" THEN
      UNDISCH_TAC `norm(x - y:real^N) <= e` THEN
      REWRITE_TAC[VECTOR_ARITH `x' - ((x' - x) + y):real^N = x - y`]];
    ALL_TAC] THEN
  EXPAND_TAC "u" THEN REWRITE_TAC[wanl_pt_zx] THEN
  ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
  MP_TAC(SPEC `x - y:real^N`
    (ASSUME `!z:real^N. norm z <= e ==> abs(g(x - z) - g(x' - z)) <= D`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `x - (x - y):real^N = y`] THEN
  EXPAND_TAC "a" THEN
  REWRITE_TAC[VECTOR_ARITH `x' - (x - y):real^N = (x' - x) + y`]);;

let WANL_PT_ME_LAP = prove
 (`!e (s:real^N->bool) u f Mu Mf x.
     open s /\ &0 < e /\ lebesgue_measurable s /\
     (\x. lift(u x)) measurable_on s /\ (\x. lift(f x)) measurable_on s /\
     (!x. x IN s ==> abs(u x) <= Mu) /\ (!x. x IN s ==> abs(f x) <= Mf) /\
     (!phi. wan_test s phi
            ==> integral s (\x. lift(u x * llap (\y:real^N. mat 1) phi x)) =
                integral s (\x. lift(f x * phi x))) /\
     cball(x,e) SUBSET s
     ==> llap (\y:real^N. mat 1) (wanl_pt_me e s u) x = wanl_pt_me e s f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wanl_pt_me e (s:real^N->bool) u = (\z. drop(wan_moll e (wanl_pt_zx s u) z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; wanl_pt_me]; ALL_TAC] THEN
  REWRITE_TAC[wanl_pt_me] THEN MATCH_MP_TAC WANL_PT_MOLL_EQ THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->real`; `f:real^N->real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WANL_PT_ZX_LLOC THEN ASM_MESON_TAC[];
    MATCH_MP_TAC WANL_PT_ZX_LLOC THEN ASM_MESON_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN s` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[wanl_pt_zx]]);;

let WANL_PT_ME_AE = prove
 (`!(s:real^N->bool) g M.
     lebesgue_measurable s /\ (\x. lift(g x)) measurable_on s /\
     (!x. x IN s ==> abs(g x) <= M)
     ==> ?t. negligible t /\
             !x eps. x IN s /\ ~(x IN t) /\ &0 < eps
                     ==> ?d. &0 < d /\
                             !e. &0 < e /\ e < d ==> abs(wanl_pt_me e s g x - g x) < eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `wanl_pt_zx (s:real^N->bool) g` WAN_MOLL_AE_CONV) THEN ANTS_TAC THENL
   [MATCH_MP_TAC WANL_PT_ZX_LLOC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `eps:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `eps:real`]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[wanl_pt_me; wanl_pt_zx; NORM_1; DROP_SUB; LIFT_DROP]);;

let WANL_PT_TEST_MUL_INTEGRABLE = prove
 (`!(s:real^N->bool) (u:real^N->real) psi.
     wan_lloc s (\x. lift(u x)) /\ wan_test s psi
     ==> (\x. lift(psi x * u x)) integrable_on s /\
         (\x. psi x % lift(u x)) integrable_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((psi:real^N->real) x * u x)) integrable_on s` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_test (s:real^N->bool) psi` THEN REWRITE_TAC[wan_test] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(u x)`; `\x:real^N. lift(psi x)`;
                   `k:real^N->bool`] WAN_LLOC_DOT_CONT_SUPPORT) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LIFT_EQ; LIFT_NUM] THEN
    REWRITE_TAC[DOT_1; GSYM drop; LIFT_DROP] THEN REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM LIFT_CMUL]);;

let WANL_PT_VERY_WEAK = prove
 (`!(s:real^2->bool) (u:real^2->real) (f:real^2->real).
     open s /\ wan_w12 s (\x. lift(u x)) /\
     (!phi. wan_test s phi
            ==> vsum(1..2)
                  (\i. integral s (\x. wan_dpart i phi x % wan_wd s i (\y. lift(u y)) x)) =
                --(integral s (\x. lift(f x * phi x))))
     ==> !phi. wan_test s phi
               ==> integral s (\x. lift(u x * llap (\y:real^2. mat 1) phi x)) =
                   integral s (\x. lift(f x * phi x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc s (\x:real^2. lift(u x))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC; WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `phi:real^2->real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (VECTOR_ARITH `(a:real^1) = --b ==> b = --a`)) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> integral s (\x. wan_dpart i phi x % wan_wd s i (\y. lift(u y)) x) =
            --(integral s (\x. wan_dpart i (wan_dpart i phi) x % lift((u:real^2->real) x)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `\x:real^2. lift(u x)`] WAN_WD_WORKS) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN REWRITE_TAC[wan_wpd] THEN
    DISCH_THEN(MP_TAC o SPEC `wan_dpart i (phi:real^2->real)` o CONJUNCT2 o CONJUNCT2 o
               CONJUNCT2) THEN
    ASM_SIMP_TAC[WAN_TEST_DPART_OPEN] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_NEG_NEG];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_2] THEN ASM_SIMP_TAC[ARITH] THEN
  SUBGOAL_THEN
   `(\x. lift((u:real^2->real) x * llap (\y:real^2. mat 1) phi x)) =
    (\x. wan_dpart 1 (wan_dpart 1 phi) x % lift(u x) +
         wan_dpart 2 (wan_dpart 2 phi) x % lift(u x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
    MP_TAC(ISPECL [`phi:real^2->real`; `x:real^2`] WANL_LLAP_DPART) THEN ANTS_TAC THENL
     [UNDISCH_TAC `wan_test (s:real^2->bool) phi` THEN SIMP_TAC[wan_test]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIMINDEX_2; SUM_2] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (\x. wan_dpart i (wan_dpart i (phi:real^2->real)) x % lift((u:real^2->real) x))
        integrable_on s`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real`;
                   `wan_dpart i (wan_dpart i (phi:real^2->real))`]
           WANL_PT_TEST_MUL_INTEGRABLE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[WAN_TEST_DPART_OPEN]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD] THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Limits of uniform jet expansions.  Sequences that are equi-Lipschitz at  *)
(* small scales and converge a.e. converge everywhere; the jet coefficients *)
(* are Cauchy by first and second differences; the expansions pass to the  *)
(* limit.                                                                   *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_DENSE = prove
 (`!(s:real^N->bool) t x d.
     open s /\ negligible t /\ x IN s /\ &0 < d
     ==> ?y. y IN s /\ ~(y IN t) /\ dist(x,y) < d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(ball(x:real^N,d) INTER s SUBSET t)` MP_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `negligible(ball(x:real^N,d) INTER s)` MP_TAC THENL
     [ASM_MESON_TAC[NEGLIGIBLE_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> F`) THEN MATCH_MP_TAC OPEN_NOT_NEGLIGIBLE THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; NOT_FORALL_THM; NOT_IMP] THEN MESON_TAC[]]);;

let WANL_PT_REAL_CAUCHY = prove
 (`!(a:num->real).
     (!e. &0 < e ==> ?N. !m n. N <= m /\ N <= n ==> abs(a m - a n) < e)
     ==> ?l. ((\m. lift(a m)) --> l) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVERGENT_EQ_CAUCHY; cauchy; GE; DIST_LIFT] THEN
  ASM_REWRITE_TAC[]);;

let WANL_PT_LIMIT_EVERYWHERE = prove
 (`!(s:real^N->bool) t (v:num->real^N->real) Lip rho0.
     open s /\ negligible t /\ &0 < rho0 /\ &0 <= Lip /\
     (!x. x IN s /\ ~(x IN t) ==> ?l. ((\m. lift(v m x)) --> l) sequentially) /\
     (!m x y. x IN s /\ y IN s /\ dist(x,y) <= rho0 ==> abs(v m x - v m y) <= Lip * dist(x,y))
     ==> !x. x IN s ==> ?l. ((\m. lift(v m x)) --> l) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_PT_REAL_CAUCHY THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `x:real^N`;
                 `min rho0 (e / (&3 * (Lip + &1)))`] WANL_PT_DENSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
    can (find_term (fun u -> u = `negligible`)) (concl th) = false &&
    is_forall(concl th) && can (find_term is_exists) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `l:real^1`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
  REWRITE_TAC[cauchy; GE; DIST_LIFT] THEN DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dist(x:real^N,y) <= rho0 /\ Lip * dist(x,y) <= e / &3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Lip + &1) * (e / (&3 * (Lip + &1)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[DIST_POS_LE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(Lip + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((v:num->real^N->real) m x - v m y) <= Lip * dist(x,y) /\
    abs(v n x - v n y) <= Lip * dist(x,y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(ASSUME `!m x y. x IN s /\ y IN s /\ dist(x,y) <= rho0
                     ==> abs((v:num->real^N->real) m x - v m y) <= Lip * dist(x,y)`) THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let WANL_PT_RPOW_SPLIT = prove
 (`!d rho0 sg. &0 <= d /\ d <= rho0 /\ &1 <= sg
               ==> d rpow sg <= d * rho0 rpow (sg - &1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = &0` THENL
   [ASM_SIMP_TAC[RPOW_ZERO; REAL_ARITH `&1 <= sg ==> ~(sg = &0)`; REAL_MUL_LZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d rpow sg = d * d rpow (sg - &1)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `sg = &1 + (sg - &1)`] THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC);;

let WANL_PT_DIR_EST = prove
 (`!(v:real^2->real) c1 (P:complex->real) K rho0 sg x0 e tau.
     (!w. P(--w) = P w) /\ norm(e:complex) = &1 /\ &0 < tau /\ tau <= rho0 /\
     (!x. norm(x - x0) <= rho0
          ==> abs(v x - v x0 - Re(c1 * (x - x0)) - P(x - x0)) <= K * norm(x - x0) rpow sg)
     ==> abs(tau * Re(c1 * e) - (v(x0 + tau % e) - v(x0 - tau % e)) / &2) <= K * tau rpow sg`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x0 + tau % e:complex` th) THEN
                          MP_TAC(SPEC `x0 - tau % e:complex` th)) THEN
  REWRITE_TAC[VECTOR_ARITH `(x0 + t % e) - x0:real^2 = t % e`;
              VECTOR_ARITH `(x0 - t % e) - x0:real^2 = --(t % e)`; NORM_NEG; NORM_MUL] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`; REAL_MUL_RID] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RNEG; RE_NEG] THEN
  REWRITE_TAC[COMPLEX_RING `c1 * Cx tau * e = Cx tau * (c1 * e)`; RE_MUL_CX] THEN
  ABBREV_TAC `R = Re(c1 * e)` THEN
  ABBREV_TAC `Q = (P:complex->real)(Cx tau * e)` THEN
  ABBREV_TAC `Tb = K * tau rpow sg` THEN REAL_ARITH_TAC);;

let WANL_PT_TAU_CHOICE = prove
 (`!rho0 d K sg ep.
     &0 < rho0 /\ &0 < d /\ &0 <= K /\ &1 < sg /\ &0 < ep
     ==> ?tau. &0 < tau /\ tau <= rho0 /\ tau < d /\ K * tau rpow (sg - &1) <= ep / &8`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `eta = ep / (&8 * (K + &1))` THEN
  SUBGOAL_THEN `&0 < eta /\ K * eta <= ep / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `K * ep / (&8 * (K + &1)) = (ep / &8) * (K / (K + &1))` SUBST1_TAC THENL
       [SUBGOAL_THEN `~(K + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= K ==> &0 < K + &1`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (min rho0 (d / &2)) (eta rpow inv(sg - &1))` THEN
  SUBGOAL_THEN `&0 < eta rpow inv(sg - &1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * eta` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(eta rpow inv(sg - &1)) rpow (sg - &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_MIN] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `inv(sg - &1) * (sg - &1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]]]);;

let WANL_PT_DIR_CAUCHY = prove
 (`!(s:real^2->bool) (v:num->real^2->real) (c1:num->complex) (P:num->complex->real)
    K rho0 sg x0 e tau ep.
     (!x. x IN s ==> ?l. ((\m. lift(v m x)) --> l) sequentially) /\
     (!m w. P m (--w) = P m w) /\ norm(e:complex) = &1 /\
     &0 < tau /\ tau <= rho0 /\ &0 < ep /\ K * tau rpow (sg - &1) <= ep / &8 /\
     x0 + tau % e IN s /\ x0 - tau % e IN s /\
     (!m x. norm(x - x0) <= rho0
            ==> abs(v m x - v m x0 - Re(c1 m * (x - x0)) - P m (x - x0))
                <= K * norm(x - x0) rpow sg)
     ==> ?N. !m n. N <= m /\ N <= n ==> abs(Re((c1 m - c1 n) * e)) < ep / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?l. ((\m. lift((v:num->real^2->real) m (x0 + tau % e) - v m (x0 - tau % e))) --> l)
        sequentially`
  (X_CHOOSE_TAC `l:real^1`) THENL
   [MP_TAC(SPEC `x0 + tau % e:real^2`
     (ASSUME `!x:real^2. x IN s ==> ?l. ((\m. lift((v:num->real^2->real) m x)) --> l)
                                        sequentially`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `l1:real^1`)] THEN
    MP_TAC(SPEC `x0 - tau % e:real^2`
     (ASSUME `!x:real^2. x IN s ==> ?l. ((\m. lift((v:num->real^2->real) m x)) --> l)
                                        sequentially`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `l2:real^1`)] THEN
    EXISTS_TAC `l1 - l2:real^1` THEN REWRITE_TAC[LIFT_SUB] THEN
    MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
  REWRITE_TAC[cauchy; GE; DIST_LIFT] THEN DISCH_THEN(MP_TAC o SPEC `ep * tau / &4`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(v:num->real^2->real) m`; `(c1:num->complex) m`; `(P:num->complex->real) m`;
                 `K:real`; `rho0:real`; `sg:real`; `x0:real^2`; `e:complex`; `tau:real`]
         WANL_PT_DIR_EST) THEN
  MP_TAC(ISPECL [`(v:num->real^2->real) n`; `(c1:num->complex) n`; `(P:num->complex->real) n`;
                 `K:real`; `rho0:real`; `sg:real`; `x0:real^2`; `e:complex`; `tau:real`]
         WANL_PT_DIR_EST) THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `tau rpow sg = tau * tau rpow (sg - &1)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `sg = &1 + (sg - &1)`] THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau * abs(Re(((c1:num->complex) m - c1 n) * e)) < tau * (ep / &2)` MP_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_RDISTRIB; RE_SUB] THEN
    ABBREV_TAC `Rm = Re((c1:num->complex) m * e)` THEN
    ABBREV_TAC `Rn = Re((c1:num->complex) n * e)` THEN
    ABBREV_TAC `Dm = (v:num->real^2->real) m (x0 + tau % e) - v m (x0 - tau % e)` THEN
    ABBREV_TAC `Dn = (v:num->real^2->real) n (x0 + tau % e) - v n (x0 - tau % e)` THEN
    SUBGOAL_THEN `K * tau rpow sg <= tau * (ep / &8)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `K * tau * t = tau * (K * t)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_LDISTRIB] THEN
    UNDISCH_TAC `abs(Dm - Dn) < ep * tau / &4` THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ]]);;

let WANL_PT_C1_CAUCHY = prove
 (`!(s:real^2->bool) (v:num->real^2->real) (c1:num->complex) (P:num->complex->real)
    K rho0 sg x0.
     open s /\ &0 < rho0 /\ &0 <= K /\ &1 < sg /\ x0 IN s /\
     (!x. x IN s ==> ?l. ((\m. lift(v m x)) --> l) sequentially) /\
     (!m w. P m (--w) = P m w) /\
     (!m x. norm(x - x0) <= rho0
            ==> abs(v m x - v m x0 - Re(c1 m * (x - x0)) - P m (x - x0))
                <= K * norm(x - x0) rpow sg)
     ==> ?l. (c1 --> l) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVERGENT_EQ_CAUCHY; cauchy; GE; dist] THEN
  X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x0:real^2` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`rho0:real`; `d:real`; `K:real`; `sg:real`; `ep:real`] WANL_PT_TAU_CHOICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!e:complex. norm e = &1 ==> x0 + tau % e IN s /\ x0 - tau % e IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
      check (fun th -> concl th = `ball(x0:real^2,d) SUBSET s`)) THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `x0 - (x0 + t % e):real^N = --(t % e)`;
                VECTOR_ARITH `x0 - (x0 - t % e):real^N = t % e`; NORM_NEG; NORM_MUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:num->real^2->real`; `c1:num->complex`;
                 `P:num->complex->real`; `K:real`; `rho0:real`; `sg:real`; `x0:real^2`;
                 `Cx(&1)`; `tau:real`; `ep:real`] WANL_PT_DIR_CAUCHY) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:num->real^2->real`; `c1:num->complex`;
                 `P:num->complex->real`; `K:real`; `rho0:real`; `sg:real`; `x0:real^2`;
                 `ii`; `tau:real`; `ep:real`] WANL_PT_DIR_CAUCHY) THEN
  ASM_SIMP_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_II; REAL_ABS_NUM] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(Re((c1:num->complex) m - c1 n)) + abs(Im(c1 m - c1 n))` THEN
  REWRITE_TAC[COMPLEX_NORM_LE_RE_IM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_MUL_RID; RE_MUL_II; REAL_ABS_NEG]) THEN
  ASM_REAL_ARITH_TAC);;

let WANL_PT_OMEGA = prove
 (`norm(cexp(ii * Cx(pi / &4))) = &1 /\ cexp(ii * Cx(pi / &4)) pow 2 = ii`,
  REWRITE_TAC[NORM_CEXP_II; COMPLEX_POW_2; GSYM CEXP_ADD] THEN
  REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; GSYM CX_ADD] THEN
  REWRITE_TAC[REAL_ARITH `pi / &4 + pi / &4 = pi / &2`; CEXP_EULER] THEN
  REWRITE_TAC[GSYM CX_COS; GSYM CX_SIN; COS_PI2; SIN_PI2] THEN
  CONV_TAC COMPLEX_RING);;

let WANL_PT_DIR2_EST = prove
 (`!(v:real^2->real) c1 c2 q K rho0 sg x0 e tau.
     norm(e:complex) = &1 /\ &0 < tau /\ tau <= rho0 /\
     (!x. norm(x - x0) <= rho0
          ==> abs(v x - v x0 - Re(c1 * (x - x0)) -
                  (Re(c2 * (x - x0) pow 2) + q * norm(x - x0) pow 2))
              <= K * norm(x - x0) rpow sg)
     ==> abs(tau pow 2 * (Re(c2 * e pow 2) + q) -
             (v(x0 + tau % e) + v(x0 - tau % e) - &2 * v x0) / &2) <= K * tau rpow sg`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x0 + tau % e:complex` th) THEN
                          MP_TAC(SPEC `x0 - tau % e:complex` th)) THEN
  REWRITE_TAC[VECTOR_ARITH `(x0 + t % e) - x0:real^2 = t % e`;
              VECTOR_ARITH `(x0 - t % e) - x0:real^2 = --(t % e)`; NORM_NEG; NORM_MUL] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`; REAL_MUL_RID] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RNEG; RE_NEG; COMPLEX_POW_NEG; ARITH] THEN
  REWRITE_TAC[COMPLEX_RING `c1 * Cx tau * e = Cx tau * (c1 * e)`; RE_MUL_CX] THEN
  REWRITE_TAC[COMPLEX_POW_MUL; GSYM CX_POW] THEN
  REWRITE_TAC[COMPLEX_RING `c2 * Cx t * e = Cx t * (c2 * e)`; RE_MUL_CX] THEN
  ABBREV_TAC `R1 = Re(c1 * e)` THEN ABBREV_TAC `R2 = Re(c2 * e pow 2)` THEN
  ABBREV_TAC `Tb = K * tau rpow sg` THEN REAL_ARITH_TAC);;

let WANL_PT_DIR2_CAUCHY = prove
 (`!(s:real^2->bool) (v:num->real^2->real) (c1:num->complex) (c2:num->complex) (q:num->real)
    K rho0 sg x0 e tau ep.
     (!x. x IN s ==> ?l. ((\m. lift(v m x)) --> l) sequentially) /\
     norm(e:complex) = &1 /\ &0 < tau /\ tau <= rho0 /\ &0 < ep /\
     K * tau rpow (sg - &2) <= ep / &8 /\
     x0 IN s /\ x0 + tau % e IN s /\ x0 - tau % e IN s /\
     (!m x. norm(x - x0) <= rho0
            ==> abs(v m x - v m x0 - Re(c1 m * (x - x0)) -
                    (Re(c2 m * (x - x0) pow 2) + q m * norm(x - x0) pow 2))
                <= K * norm(x - x0) rpow sg)
     ==> ?N. !m n. N <= m /\ N <= n
                   ==> abs((Re(c2 m * e pow 2) + q m) - (Re(c2 n * e pow 2) + q n)) < ep / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?l. ((\m. lift((v:num->real^2->real) m (x0 + tau % e) + v m (x0 - tau % e) -
                   &2 * v m x0)) --> l) sequentially`
  (X_CHOOSE_TAC `l:real^1`) THENL
   [MP_TAC(SPEC `x0 + tau % e:real^2`
     (ASSUME `!x:real^2. x IN s ==> ?l. ((\m. lift((v:num->real^2->real) m x)) --> l)
                                        sequentially`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `l1:real^1`)] THEN
    MP_TAC(SPEC `x0 - tau % e:real^2`
     (ASSUME `!x:real^2. x IN s ==> ?l. ((\m. lift((v:num->real^2->real) m x)) --> l)
                                        sequentially`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `l2:real^1`)] THEN
    MP_TAC(SPEC `x0:real^2`
     (ASSUME `!x:real^2. x IN s ==> ?l. ((\m. lift((v:num->real^2->real) m x)) --> l)
                                        sequentially`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `l3:real^1`)] THEN
    EXISTS_TAC `l1 + (l2 - &2 % l3):real^1` THEN
    REWRITE_TAC[LIFT_SUB; LIFT_ADD; LIFT_CMUL] THEN
    MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
  REWRITE_TAC[cauchy; GE; DIST_LIFT] THEN DISCH_THEN(MP_TAC o SPEC `ep * tau pow 2 / &2`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(v:num->real^2->real) m`; `(c1:num->complex) m`; `(c2:num->complex) m`;
                 `(q:num->real) m`; `K:real`; `rho0:real`; `sg:real`; `x0:real^2`; `e:complex`;
                 `tau:real`] WANL_PT_DIR2_EST) THEN
  MP_TAC(ISPECL [`(v:num->real^2->real) n`; `(c1:num->complex) n`; `(c2:num->complex) n`;
                 `(q:num->real) n`; `K:real`; `rho0:real`; `sg:real`; `x0:real^2`; `e:complex`;
                 `tau:real`] WANL_PT_DIR2_EST) THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `tau rpow sg = tau pow 2 * tau rpow (sg - &2)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `sg = &2 + (sg - &2)`] THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `K * tau rpow sg <= tau pow 2 * (ep / &8)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `K * t2 * t = t2 * (K * t)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `tau pow 2 * abs((Re((c2:num->complex) m * e pow 2) + (q:num->real) m) -
                    (Re(c2 n * e pow 2) + q n)) < tau pow 2 * (ep / &2)`
  MP_TAC THENL
   [ABBREV_TAC `Am = Re((c2:num->complex) m * e pow 2) + (q:num->real) m` THEN
    ABBREV_TAC `An = Re((c2:num->complex) n * e pow 2) + (q:num->real) n` THEN
    ABBREV_TAC `Sm = (v:num->real^2->real) m (x0 + tau % e) + v m (x0 - tau % e) - &2 * v m x0` THEN
    ABBREV_TAC `Sn = (v:num->real^2->real) n (x0 + tau % e) + v n (x0 - tau % e) - &2 * v n x0` THEN
    ABBREV_TAC `t2 = tau pow 2` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(t2) = t2` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs(Sm - Sn) < ep * t2 / &2` THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ]]);;

let WANL_PT_C2_CAUCHY = prove
 (`!(s:real^2->bool) (v:num->real^2->real) (c1:num->complex) (c2:num->complex) (q:num->real)
    K rho0 sg x0.
     open s /\ &0 < rho0 /\ &0 <= K /\ &2 < sg /\ x0 IN s /\
     (!x. x IN s ==> ?l. ((\m. lift(v m x)) --> l) sequentially) /\
     (?l. ((\m. lift(q m)) --> l) sequentially) /\
     (!m x. norm(x - x0) <= rho0
            ==> abs(v m x - v m x0 - Re(c1 m * (x - x0)) -
                    (Re(c2 m * (x - x0) pow 2) + q m * norm(x - x0) pow 2))
                <= K * norm(x - x0) rpow sg)
     ==> ?l. (c2 --> l) sequentially`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONVERGENT_EQ_CAUCHY; cauchy; GE; dist] THEN
  X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x0:real^2` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`rho0:real`; `d:real`; `K:real`; `sg - &1`; `ep / &2`] WANL_PT_TAU_CHOICE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(sg - &1) - &1 = sg - &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!e:complex. norm e = &1 ==> x0 + tau % e IN s /\ x0 - tau % e IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
      check (fun th -> concl th = `ball(x0:real^2,d) SUBSET s`)) THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `x0 - (x0 + t % e):real^N = --(t % e)`;
                VECTOR_ARITH `x0 - (x0 - t % e):real^N = t % e`; NORM_NEG; NORM_MUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:num->real^2->real`; `c1:num->complex`; `c2:num->complex`;
                 `q:num->real`; `K:real`; `rho0:real`; `sg:real`; `x0:real^2`;
                 `Cx(&1)`; `tau:real`; `ep / &2`] WANL_PT_DIR2_CAUCHY) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:num->real^2->real`; `c1:num->complex`; `c2:num->complex`;
                 `q:num->real`; `K:real`; `rho0:real`; `sg:real`; `x0:real^2`;
                 `cexp(ii * Cx(pi / &4))`; `tau:real`; `ep / &2`] WANL_PT_DIR2_CAUCHY) THEN
  ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; WANL_PT_OMEGA; REAL_ARITH `&0 < e ==> &0 < e / &2`] THEN
  REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_MUL_RID; RE_MUL_II] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
  REWRITE_TAC[cauchy; GE; DIST_LIFT] THEN DISCH_THEN(MP_TAC o SPEC `ep / &8`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N3:num`)] THEN
  EXISTS_TAC `N1 + N2 + N3:num` THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
  REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(Re((c2:num->complex) m - c2 n)) + abs(Im(c2 m - c2 n))` THEN
  REWRITE_TAC[COMPLEX_NORM_LE_RE_IM; RE_SUB; IM_SUB] THEN ASM_REAL_ARITH_TAC);;

let WANL_PT_JET_PASS = prove
 (`!(v:num->real^2->real) w (c1:num->complex) c1l (c2:num->complex) c2l (q:num->real) ql
    K sg x0 x.
     ((\m. lift(v m x)) --> lift(w x)) sequentially /\
     ((\m. lift(v m x0)) --> lift(w x0)) sequentially /\
     (c1 --> c1l) sequentially /\ (c2 --> c2l) sequentially /\
     ((\m. lift(q m)) --> lift ql) sequentially /\
     (!m. abs(v m x - v m x0 - Re(c1 m * (x - x0)) -
              (Re(c2 m * (x - x0) pow 2) + q m * norm(x - x0) pow 2))
          <= K * norm(x - x0) rpow sg)
     ==> abs(w x - w x0 - Re(c1l * (x - x0)) -
             (Re(c2l * (x - x0) pow 2) + ql * norm(x - x0) pow 2))
         <= K * norm(x - x0) rpow sg`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sequentially`;
     `\m. lift((v:num->real^2->real) m x - v m x0 - Re((c1:num->complex) m * (x - x0)) -
               (Re((c2:num->complex) m * (x - x0) pow 2) + (q:num->real) m * norm(x - x0) pow 2))`;
     `lift((w:real^2->real) x - w x0 - Re(c1l * (x - x0)) -
           (Re(c2l * (x - x0) pow 2) + ql * norm(x - x0) pow 2))`;
     `K * norm(x - x0:real^2) rpow sg`] LIM_NORM_UBOUND) THEN
  REWRITE_TAC[NORM_LIFT; TRIVIAL_LIMIT_SEQUENTIALLY] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[EVENTUALLY_TRUE] THEN
  REWRITE_TAC[LIFT_SUB; LIFT_ADD] THEN
  REPEAT(MATCH_MP_TAC LIM_SUB THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC LIM_ADD THEN CONJ_TAC) THENL
   [MP_TAC(ISPECL [`sequentially`; `\c:complex. lift(Re(c * (x - x0)))`; `c1:num->complex`;
                   `c1l:complex`] LIM_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; COMPLEX_ADD_RDISTRIB; RE_ADD; LIFT_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; LIFT_CMUL];
    MP_TAC(ISPECL [`sequentially`; `\c:complex. lift(Re(c * (x - x0) pow 2))`;
                   `c2:num->complex`; `c2l:complex`] LIM_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; COMPLEX_ADD_RDISTRIB; RE_ADD; LIFT_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; LIFT_CMUL];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[]]);;

let WANL_PT_LIM_EXISTS = prove
 (`!(f:num->real^N). (?l. (f --> l) sequentially)
                     ==> (f --> lim sequentially f) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lim sequentially (f:num->real^N) = l` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC TENDSTO_LIM THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]);;

let WANL_PT_JET_LIMIT_CORE = prove
 (`!(s:real^2->bool) t (v:num->real^2->real) (u:real^2->real) (c1:num->real^2->complex)
    (c2:num->real^2->complex) (q:num->real^2->real) K G rho0 sg.
     open s /\ negligible t /\ &0 < rho0 /\ &0 <= K /\ &0 <= G /\ &1 < sg /\
     (!x. x IN s /\ ~(x IN t) ==> ((\m. lift(v m x)) --> lift(u x)) sequentially) /\
     (!m x0. x0 IN s ==> norm(c1 m x0) <= G /\ norm(c2 m x0) <= G /\ abs(q m x0) <= G) /\
     (!m x0 x. x0 IN s /\ norm(x - x0) <= rho0
               ==> abs(v m x - v m x0 - Re(c1 m x0 * (x - x0)) -
                       (Re(c2 m x0 * (x - x0) pow 2) + q m x0 * norm(x - x0) pow 2))
                   <= K * norm(x - x0) rpow sg) /\
     ((!x. x IN s ==> ?l. ((\m. lift(v m x)) --> l) sequentially)
      ==> !x0. x0 IN s ==> ?l. ((\m. c2 m x0) --> l) sequentially) /\
     (!x0. x0 IN s ==> ?l. ((\m. lift(q m x0)) --> l) sequentially)
     ==> ?w a1 a2 aq.
           (!x. x IN s ==> ((\m. lift(v m x)) --> lift(w x)) sequentially) /\
           (!x. x IN s /\ ~(x IN t) ==> w x = u x) /\
           (!x0. x0 IN s ==> ((\m. c1 m x0) --> a1 x0) sequentially /\
                             ((\m. c2 m x0) --> a2 x0) sequentially /\
                             ((\m. lift(q m x0)) --> lift(aq x0)) sequentially) /\
           (!x0. x0 IN s ==> norm(a1 x0) <= G /\ norm(a2 x0) <= G /\ abs(aq x0) <= G) /\
           (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
                   ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                           (Re(a2 x0 * (x - x0) pow 2) + aq x0 * norm(x - x0) pow 2))
                       <= K * norm(x - x0) rpow sg)`,
  REPEAT STRIP_TAC THEN
  (* uniform Lipschitz bound at small scales *)
  SUBGOAL_THEN
   `!m x y. x IN s /\ y IN s /\ dist(x,y) <= rho0
            ==> abs((v:num->real^2->real) m x - v m y) <=
                (G + &2 * G * rho0 + K * rho0 rpow (sg - &1)) * dist(x,y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `y:real^2`; `x:real^2`] o check (fun th ->
      can (find_term (fun t -> t = `rpow`)) (concl th) && is_forall(concl th))) THEN
    SUBGOAL_THEN `norm(x - y:real^2) = dist(x,y)` SUBST1_TAC THENL
     [REWRITE_TAC[dist]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `y:real^2`] o check (fun th ->
      can (find_term (fun t -> t = `norm:complex->real`)) (concl th) &&
      not(can (find_term (fun t -> t = `rpow`)) (concl th)) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `dd = dist(x:real^2,y)` THEN
    SUBGOAL_THEN `&0 <= dd` ASSUME_TAC THENL [EXPAND_TAC "dd" THEN REWRITE_TAC[DIST_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(Re((c1:num->real^2->complex) m y * (x - y))) <= G * dd /\
      abs(Re((c2:num->real^2->complex) m y * (x - y) pow 2)) <= G * rho0 * dd /\
      abs((q:num->real^2->real) m y * dd pow 2) <= G * rho0 * dd /\
      K * dd rpow sg <= K * rho0 rpow (sg - &1) * dd`
    MP_TAC THENL
     [SUBGOAL_THEN `norm(x - y:real^2) = dd` ASSUME_TAC THENL
       [EXPAND_TAC "dd" THEN REWRITE_TAC[dist]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm((c1:num->real^2->complex) m y * (x - y))` THEN
        REWRITE_TAC[COMPLEX_NORM_GE_RE_IM; COMPLEX_NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm((c2:num->real^2->complex) m y * (x - y) pow 2)` THEN
        REWRITE_TAC[COMPLEX_NORM_GE_RE_IM; COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
        ASM_REWRITE_TAC[REAL_POW_2] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
        REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[REAL_ARITH `K * r * d = K * (d * r)`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC WANL_PT_RPOW_SPLIT THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= G + &2 * G * rho0 + K * rho0 rpow (sg - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_LT_IMP_LE; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`; `v:num->real^2->real`;
                 `G + &2 * G * rho0 + K * rho0 rpow (sg - &1)`; `rho0:real`]
         WANL_PT_LIMIT_EVERYWHERE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `lift((u:real^2->real) x)` THEN
    ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `!x0. x0 IN s ==> ?l. ((\m. (c2:num->real^2->complex) m x0) --> l) sequentially`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x0. x0 IN s ==> ?l. ((\m. (c1:num->real^2->complex) m x0) --> l) sequentially`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_PT_C1_CAUCHY THEN
    MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `v:num->real^2->real`;
      `\m w. Re((c2:num->real^2->complex) m x0 * w pow 2) + (q:num->real^2->real) m x0 * norm w pow 2`;
      `K:real`; `rho0:real`; `sg:real`; `x0:real^2`] THEN
    ASM_SIMP_TAC[COMPLEX_POW_NEG; ARITH; NORM_NEG];
    ALL_TAC] THEN
  EXISTS_TAC `\x. drop(lim sequentially (\m. lift((v:num->real^2->real) m x)))` THEN
  EXISTS_TAC `\x0. lim sequentially (\m. (c1:num->real^2->complex) m x0)` THEN
  EXISTS_TAC `\x0. lim sequentially (\m. (c2:num->real^2->complex) m x0)` THEN
  EXISTS_TAC `\x0. drop(lim sequentially (\m. lift((q:num->real^2->real) m x0)))` THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN
   `(!x. x IN s ==> ((\m. lift((v:num->real^2->real) m x)) -->
                     lim sequentially (\m. lift(v m x))) sequentially) /\
    (!x0. x0 IN s ==> ((\m. (c1:num->real^2->complex) m x0) -->
                       lim sequentially (\m. c1 m x0)) sequentially /\
                      ((\m. (c2:num->real^2->complex) m x0) -->
                       lim sequentially (\m. c2 m x0)) sequentially /\
                      ((\m. lift((q:num->real^2->real) m x0)) -->
                       lim sequentially (\m. lift(q m x0))) sequentially)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_PT_LIM_EXISTS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MESON[LIFT_DROP] `lift a = lift b ==> a = b`) THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\m. lift((v:num->real^2->real) m x)` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY];
    X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
      EXISTS_TAC `\m. (c1:num->real^2->complex) m x0` THEN
      ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE];
      MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
      EXISTS_TAC `\m. (c2:num->real^2->complex) m x0` THEN
      ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE];
      REWRITE_TAC[GSYM NORM_1] THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
      EXISTS_TAC `\m. lift((q:num->real^2->real) m x0)` THEN
      ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE; NORM_LIFT]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_PT_JET_PASS THEN
    MAP_EVERY EXISTS_TAC [`v:num->real^2->real`; `\m. (c1:num->real^2->complex) m x0`;
                          `\m. (c2:num->real^2->complex) m x0`;
                          `\m. (q:num->real^2->real) m x0`] THEN
    ASM_SIMP_TAC[LIFT_DROP; ETA_AX]]);;

let WANL_PT_JET1_LIMIT = prove
 (`!(s:real^2->bool) t (v:num->real^2->real) (u:real^2->real) (c1:num->real^2->complex)
    K G rho0 sg.
     open s /\ negligible t /\ &0 < rho0 /\ &0 <= K /\ &0 <= G /\ &1 < sg /\
     (!x. x IN s /\ ~(x IN t) ==> ((\m. lift(v m x)) --> lift(u x)) sequentially) /\
     (!m x0. x0 IN s ==> norm(c1 m x0) <= G) /\
     (!m x0 x. x0 IN s /\ norm(x - x0) <= rho0
               ==> abs(v m x - v m x0 - Re(c1 m x0 * (x - x0))) <= K * norm(x - x0) rpow sg)
     ==> ?w a1. (!x. x IN s ==> ((\m. lift(v m x)) --> lift(w x)) sequentially) /\
                (!x. x IN s /\ ~(x IN t) ==> w x = u x) /\
                (!x0. x0 IN s ==> norm(a1 x0) <= G) /\
                (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
                        ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)))
                            <= K * norm(x - x0) rpow sg)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`; `v:num->real^2->real`; `u:real^2->real`;
                 `c1:num->real^2->complex`; `\m:num x0:real^2. Cx(&0)`;
                 `\m:num x0:real^2. &0`; `K:real`; `G:real`; `rho0:real`; `sg:real`]
         WANL_PT_JET_LIMIT_CORE) THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; RE_CX; REAL_MUL_LZERO; REAL_ADD_RID; REAL_SUB_RZERO;
              COMPLEX_NORM_CX; REAL_ABS_NUM; LIFT_NUM] THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRY(EXISTS_TAC `Cx(&0)` THEN REWRITE_TAC[LIM_CONST] THEN NO_TAC) THEN
    EXISTS_TAC `vec 0:real^1` THEN REWRITE_TAC[LIM_CONST];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` (X_CHOOSE_THEN `a1:real^2->complex`
    (X_CHOOSE_THEN `a2:real^2->complex` (X_CHOOSE_THEN `aq:real^2->real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `!x0. x0 IN s ==> (a2:real^2->complex) x0 = Cx(&0) /\ (aq:real^2->real) x0 = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x0:real^2` o check (fun th ->
      can (find_term (fun t -> t = `a2:real^2->complex`)) (concl th) &&
      can (find_term (fun t -> t = `(-->):(num->complex)->complex->(num)net->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `\m:num. Cx(&0)` THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIM_CONST];
      MATCH_MP_TAC(MESON[LIFT_DROP] `lift a = lift b ==> a = b`) THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `\m:num. lift(&0)` THEN
      ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIM_CONST; LIFT_NUM]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`w:real^2->real`; `a1:real^2->complex`] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x0:real^2`; `x:real^2`] o check (fun th ->
    can (find_term (fun t -> t = `rpow`)) (concl th) &&
    can (find_term (fun t -> t = `w:real^2->real`)) (concl th))) THEN
  ASM_SIMP_TAC[COMPLEX_MUL_LZERO; RE_CX; REAL_MUL_LZERO; REAL_ADD_RID; REAL_SUB_RZERO]);;

let WANL_PT_JET2_LIMIT = prove
 (`!(s:real^2->bool) t (v:num->real^2->real) (u:real^2->real) (c1:num->real^2->complex)
    (c2:num->real^2->complex) (q:num->real^2->real) ql K G rho0 sg.
     open s /\ negligible t /\ &0 < rho0 /\ &0 <= K /\ &0 <= G /\ &2 < sg /\
     (!x. x IN s /\ ~(x IN t) ==> ((\m. lift(v m x)) --> lift(u x)) sequentially) /\
     (!m x0. x0 IN s ==> norm(c1 m x0) <= G /\ norm(c2 m x0) <= G /\ abs(q m x0) <= G) /\
     (!x0. x0 IN s ==> ((\m. lift(q m x0)) --> lift(ql x0)) sequentially) /\
     (!m x0 x. x0 IN s /\ norm(x - x0) <= rho0
               ==> abs(v m x - v m x0 - Re(c1 m x0 * (x - x0)) -
                       (Re(c2 m x0 * (x - x0) pow 2) + q m x0 * norm(x - x0) pow 2))
                   <= K * norm(x - x0) rpow sg)
     ==> ?w a1 a2. (!x. x IN s ==> ((\m. lift(v m x)) --> lift(w x)) sequentially) /\
                   (!x. x IN s /\ ~(x IN t) ==> w x = u x) /\
                   (!x0. x0 IN s ==> norm(a1 x0) <= G /\ norm(a2 x0) <= G) /\
                   (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
                           ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                                   (Re(a2 x0 * (x - x0) pow 2) + ql x0 * norm(x - x0) pow 2))
                               <= K * norm(x - x0) rpow sg)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`; `v:num->real^2->real`; `u:real^2->real`;
                 `c1:num->real^2->complex`; `c2:num->real^2->complex`; `q:num->real^2->real`;
                 `K:real`; `G:real`; `rho0:real`; `sg:real`] WANL_PT_JET_LIMIT_CORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
      MATCH_MP_TAC WANL_PT_C2_CAUCHY THEN
      MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `v:num->real^2->real`;
                            `\m. (c1:num->real^2->complex) m x0`;
                            `\m. (q:num->real^2->real) m x0`; `K:real`; `rho0:real`;
                            `sg:real`; `x0:real^2`] THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `lift((ql:real^2->real) x0)` THEN ASM_SIMP_TAC[];
      X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN EXISTS_TAC `lift((ql:real^2->real) x0)` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` (X_CHOOSE_THEN `a1:real^2->complex`
    (X_CHOOSE_THEN `a2:real^2->complex` (X_CHOOSE_THEN `aq:real^2->real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `!x0. x0 IN s ==> (aq:real^2->real) x0 = ql x0` ASSUME_TAC THENL
   [X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(MESON[LIFT_DROP] `lift a = lift b ==> a = b`) THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\m. lift((q:num->real^2->real) m x0)` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`w:real^2->real`; `a1:real^2->complex`; `a2:real^2->complex`] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x0:real^2`; `x:real^2`] o check (fun th ->
    can (find_term (fun t -> t = `rpow`)) (concl th) &&
    can (find_term (fun t -> t = `w:real^2->real`)) (concl th))) THEN
  ASM_SIMP_TAC[]);;

