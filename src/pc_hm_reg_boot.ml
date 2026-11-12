(* ========================================================================= *)
(* Unit pc_hm_reg_boot (a unit of the harmonic map regularity chain of       *)
(* pc_hm_regularity): estimates for smooth harmonic maps into a cm_target    *)
(* from small energy.  Schoen's maximum-point argument with the planar       *)
(* sub-mean value inequality (WAN_SUBMEAN_2D) turns the Bochner inequality   *)
(* Lap e >= -C e^2 of pc_hm_reg_cov into an interior bound of the energy     *)
(* density by the energy; the higher derivatives follow by the same weighted *)
(* maximum trick with the log-potential estimate WAN_LOGPOT_C1A_QUANT.       *)
(* ========================================================================= *)

needs "src/pc_hm_reg_cov.ml";;
needs "src/pc_wan_pot2c.ml";;
needs "src/pc_pde_rdt_coef.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The flat Laplacian llap (mat 1) is cml_lap for smooth functions; the      *)
(* Laplacian of |y - x0|^2 is 4.                                             *)
(* ========================================================================= *)

let HMR_LLAP_CML = prove
 (`!s (h:real^2->real) x.
     open s /\ smooth_map_on s (\x. lift(h x)) /\ x IN s
     ==> llap (\y. mat 1) h x = cml_lap h x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real`; `x:real^2`] LLAP_FLAT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2; cml_lap; cml_d; partial_derivative; LIFT_DROP; ETA_AX]);;

let HMR_SQ_SMOOTH = prove
 (`!x0:real^2. smooth_map_on (:real^2) (\y. lift(norm(y - x0) pow 2))`,
  GEN_TAC THEN REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let HMR_D_COORD = prove
 (`!i k (x:real^2). 1 <= k /\ k <= 2 ==> cml_d i (\z:real^2. z$k) x = if i = k then &1 else &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d] THEN
  SUBGOAL_THEN `linear (\z:real^2. lift(z$k))` ASSUME_TAC THENL
   [REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_LINEAR; LIFT_DROP] THEN
  ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2] THEN MESON_TAC[]);;

let HMR_LAP_SQ = prove
 (`!x0 x:real^2. cml_lap (\y. norm(y - x0) pow 2) x = &4`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> !z. cml_d i (\y:real^2. norm(y - x0) pow 2) z = &2 * (z$i - x0$i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
    MP_TAC(ISPECL [`(:real^2)`; `\y:real^2. y - x0`; `z:real^2`; `i:num`] HMR_D_SQ) THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `partial_derivative i (\y:real^2. y - x0) z = basis i` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`i:num`; `\y:real^2. y`; `\y:real^2. x0:real^2`; `z:real^2`]
                    PARTIAL_DERIVATIVE_SUB) THEN
      REWRITE_TAC[DIFFERENTIABLE_CONST; DIFFERENTIABLE_ID; PARTIAL_DERIVATIVE_ID;
                  PARTIAL_DERIVATIVE_CONST; VECTOR_SUB_RZERO; ETA_AX];
      ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_2; VECTOR_SUB_COMPONENT]];
    ALL_TAC] THEN
  REWRITE_TAC[cml_lap] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> cml_d i (cml_d i (\y:real^2. norm(y - x0) pow 2)) x = &2`
  (fun th -> SIMP_TAC[th; ARITH] THEN REAL_ARITH_TAC) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cml_d i (\y:real^2. norm(y - x0) pow 2) = (\z. &2 * (z$i - x0$i))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `&2`; `\z:real^2. z$i - (x0:real^2)$i`; `x:real^2`; `i:num`]
                CML_D_CMUL) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CML_SM_SUB THEN SIMP_TAC[OPEN_UNIV; CML_SM_COORD; CML_SM_CONST];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `\z:real^2. z$i`; `\z:real^2. (x0:real^2)$i`; `x:real^2`; `i:num`]
                CML_D_SUB) THEN
  SIMP_TAC[OPEN_UNIV; IN_UNIV; CML_SM_COORD; CML_SM_CONST] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[HMR_D_COORD; CML_D_CONST] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Schoen's argument.  For a smooth h >= 0 with Lap h >= -A h^2 near         *)
(* cball(a,rho) and A int_{B(a,rho)} h small:                                *)
(*   (rho - |x - a|)^2 h(x) <= 6 int_{B(a,rho)} h    on cball(a,rho).        *)
(* (Maximum point x0 of (rho - |x - a|)^2 h, then the sub-mean value         *)
(* inequality for h + 4 A h(x0)^2 |y - x0|^2 on a disc around x0.)           *)
(* ========================================================================= *)

let HMR_SUBMEAN_STEP = prove
 (`!A s (h:real^2->real) x0 sigma0 sigma e0 B.
     &0 <= A /\ open s /\ ball(x0,sigma0) SUBSET s /\ smooth_map_on s (\x. lift(h x)) /\
     (!x. x IN s ==> &0 <= h x) /\ (!x. x IN s ==> --(A * h x pow 2) <= cml_lap h x) /\
     (!y. y IN ball(x0,sigma0) ==> h y <= &4 * e0) /\ h x0 = e0 /\
     &0 < sigma /\ sigma < sigma0 /\
     ball(x0,sigma) SUBSET B /\ (\x. lift(h x)) integrable_on B /\ (!x. x IN B ==> &0 <= h x)
     ==> pi * sigma pow 2 * e0 <=
         drop(integral B (\x. lift(h x))) + &4 * A * pi * e0 pow 2 * sigma pow 4`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `dd = &4 * A * e0 pow 2` THEN
  SUBGOAL_THEN `&0 <= dd` ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `w = \y:real^2. &1 * (h:real^2->real) y + dd * norm(y - x0) pow 2` THEN
  SUBGOAL_THEN `open(ball(x0:real^2,sigma0))` ASSUME_TAC THENL [REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(x0:real^2,sigma0)) (\x. lift((h:real^2->real) x))`
  ASSUME_TAC THENL [ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(x0:real^2,sigma0)) (\y. lift(norm(y - x0) pow 2))`
  ASSUME_TAC THENL [MESON_TAC[SMOOTH_MAP_ON_SUBSET; SUBSET_UNIV; HMR_SQ_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(x0:real^2,sigma0)) (\y. lift((w:real^2->real) y))`
  ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC CML_SM_ADD THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC CML_SM_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(x0:real^2,sigma0) ==> &0 <= llap (\z. mat 1) w y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN EXPAND_TAC "w" THEN
    MP_TAC(ISPECL [`ball(x0:real^2,sigma0)`; `h:real^2->real`; `\y:real^2. norm(y - x0) pow 2`;
                   `&1`; `dd:real`; `y:real^2`] WANL_LLAP_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`ball(x0:real^2,sigma0)`; `h:real^2->real`; `y:real^2`] HMR_LLAP_CML) THEN
    MP_TAC(ISPECL [`ball(x0:real^2,sigma0)`; `\y:real^2. norm(y - x0) pow 2`; `y:real^2`]
                  HMR_LLAP_CML) THEN
    ASM_REWRITE_TAC[HMR_LAP_SQ] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    SUBGOAL_THEN `(y:real^2) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^2->real) y pow 2 <= (&4 * e0) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `A * (h:real^2->real) y pow 2 <= A * (&4 * e0) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `cml_lap`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "dd" THEN UNDISCH_TAC
     `A * (h:real^2->real) y pow 2 <= A * (&4 * e0) pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ball(x0:real^2,sigma0)`; `w:real^2->real`; `x0:real^2`; `sigma:real`]
               (REWRITE_RULE[WAN_SUBMEAN_2D_STATEMENT] WAN_SUBMEAN_2D)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN `(w:real^2->real) x0 = e0` SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(x0:real^2,sigma) SUBSET ball(x0,sigma0)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((h:real^2->real) x)) integrable_on ball(x0,sigma) /\
                (\x. lift(norm(x - x0:real^2) pow 2)) integrable_on ball(x0,sigma)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
      `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(x0:real^2,sigma0)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (ball(x0,sigma)) (\x. lift((w:real^2->real) x))) =
    drop(integral (ball(x0,sigma)) (\x. lift((h:real^2->real) x))) +
    dd * drop(integral (ball(x0,sigma)) (\x. lift(norm(x - x0:real^2) pow 2)))`
  SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[REAL_MUL_LID; LIFT_ADD; LIFT_CMUL] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRABLE_CMUL; DROP_ADD; DROP_CMUL;
                 REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (ball(x0,sigma)) (\x. lift((h:real^2->real) x))) <=
                drop(integral B (\x. lift(h x)))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_SIMP_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (ball(x0,sigma)) (\x. lift(norm(x - x0:real^2) pow 2))) <=
                sigma pow 2 * (pi * sigma pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(x0:real^2,sigma)) (\y. lift(sigma pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST; LIFT_DROP] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
      `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST];
        X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_MESON_TAC[dist; REAL_LT_IMP_LE]];
      SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
      ASM_SIMP_TAC[AREA_BALL; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < pi * sigma pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[PI_POS; REAL_POW_LT]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `pi * sigma pow 2 * e0 <=
                drop(integral (ball(x0,sigma)) (\x. lift((h:real^2->real) x))) +
                dd * drop(integral (ball(x0,sigma)) (\x. lift(norm(x - x0:real^2) pow 2)))`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `inv`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o
      CONJ (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < pi * sigma pow 2`))) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dd * drop(integral (ball(x0,sigma)) (\x. lift(norm(x - x0:real^2) pow 2))) <=
                dd * (sigma pow 2 * (pi * sigma pow 2))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "dd" THEN UNDISCH_TAC
   `drop(integral (ball(x0,sigma)) (\x. lift((h:real^2->real) x))) <=
    drop(integral B (\x. lift(h x)))` THEN
  REWRITE_TAC[REAL_POW_2; REAL_ARITH `x pow 4 = (x * x) * (x * x)`] THEN REAL_ARITH_TAC);;

let HMR_WEIGHT_CONT = prove
 (`!a rho n s. (\x:real^2. lift((rho - norm(x - a)) pow n)) continuous_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

let HMR_PI_GT_3 = prove
 (`&3 < pi`,
  MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let HMR_SCHOEN = prove
 (`!A s (h:real^2->real) a rho.
     &0 <= A /\ open s /\ &0 < rho /\ cball(a,rho) SUBSET s /\
     smooth_map_on s (\x. lift(h x)) /\ (!x. x IN s ==> &0 <= h x) /\
     (!x. x IN s ==> --(A * h x pow 2) <= cml_lap h x) /\
     A * drop(integral (ball(a,rho)) (\x. lift(h x))) < &3 * pi / &64
     ==> !x. x IN cball(a,rho)
             ==> (rho - norm(x - a)) pow 2 * h x <=
                 &6 * drop(integral (ball(a,rho)) (\x. lift(h x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `I0 = drop(integral (ball(a,rho)) (\x. lift((h:real^2->real) x)))` THEN
  SUBGOAL_THEN `(\x. lift((h:real^2->real) x)) continuous_on cball(a,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((h:real^2->real) x)) integrable_on ball(a,rho)` ASSUME_TAC THENL
   [ASM_MESON_TAC[WANL_CONT_CBALL_INTEGRABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,rho) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,rho)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= I0` ASSUME_TAC THENL
   [EXPAND_TAC "I0" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^2. (rho - norm(x - a)) pow 2 * (h:real^2->real) x`;
                 `cball(a:real^2,rho)`] CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL; CBALL_EQ_EMPTY; o_DEF] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF; HMR_WEIGHT_CONT];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(rho - norm(x0 - a:real^2)) pow 2 * (h:real^2->real) x0 <= &6 * I0`
  (fun th -> ASM_MESON_TAC[th; REAL_LE_TRANS]) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e0 = (h:real^2->real) x0` THEN
  ABBREV_TAC `sigma0 = (rho - norm(x0 - a:real^2)) / &2` THEN
  SUBGOAL_THEN `(x0:real^2) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e0` ASSUME_TAC THENL [EXPAND_TAC "e0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(x0 - a:real^2) <= rho` ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^2) IN cball(a,rho)` THEN REWRITE_TAC[IN_CBALL; dist] THEN
    MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e0 /\ &0 < sigma0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (rho - norm(x0 - a:real^2)) pow 2 * e0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "sigma0" THEN
    ASM_CASES_TAC `rho - norm(x0 - a:real^2) = &0` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
      ASM_CASES_TAC `e0 = &0` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL] THEN
      DISCH_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho - norm(x0 - a:real^2) = &2 * sigma0` ASSUME_TAC THENL
   [EXPAND_TAC "sigma0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(x0:real^2,sigma0) SUBSET ball(a,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; dist] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MP_TAC(NORM_ARITH `norm(a - y:real^2) <= norm(x0 - a) + norm(x0 - y)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(x0:real^2,sigma0) ==> (h:real^2->real) y <= &4 * e0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN cball(a,rho) /\ (y:real^2) IN s` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `rho:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sigma0 <= rho - norm(y - a:real^2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^2) IN ball(x0,sigma0)` THEN REWRITE_TAC[IN_BALL; dist] THEN
      MP_TAC(NORM_ARITH `norm(y - a:real^2) <= norm(x0 - a) + norm(x0 - y)`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sigma0 pow 2 * (h:real^2->real) y <= (&2 * sigma0) pow 2 * e0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(rho - norm(y - a:real^2)) pow 2 * (h:real^2->real) y` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `(&2 * s) * (&2 * s) * e = (s * s) * (&4 * e)`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `sigma0 * sigma0` THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `A * e0 * sigma0 pow 2 <= inv(&16)` THENL
   [MP_TAC(ISPECL [`A:real`; `s:real^2->bool`; `h:real^2->real`; `x0:real^2`; `sigma0:real`;
                   `sigma0 / &2`; `e0:real`; `ball(a:real^2,rho)`] HMR_SUBMEAN_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^2,sigma0)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `P = pi * e0 * sigma0 pow 2` THEN
    SUBGOAL_THEN `pi * (sigma0 / &2) pow 2 * e0 = P / &4 /\
                  &4 * A * pi * e0 pow 2 * (sigma0 / &2) pow 4 = (P * (A * e0 * sigma0 pow 2)) / &4 /\
                  pi * ((&2 * sigma0) pow 2 * e0) = &4 * P`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN REPEAT CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[PI_POS; REAL_LT_MUL; REAL_POW_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `P * (A * e0 * sigma0 pow 2) <= P * inv(&16)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&3 * ((&2 * sigma0) pow 2 * e0) <= pi * ((&2 * sigma0) pow 2 * e0)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; HMR_PI_GT_3; REAL_LE_MUL; REAL_LE_POW_2];
      ALL_TAC] THEN
    UNDISCH_TAC `&6 * I0 < (rho - norm(x0 - a:real^2)) pow 2 * e0` THEN
    UNDISCH_TAC `&3 * ((&2 * sigma0) pow 2 * e0) <= pi * ((&2 * sigma0) pow 2 * e0)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `P / &4 <= I0 + (P * (A * e0 * sigma0 pow 2)) / &4` THEN
    UNDISCH_TAC `P * (A * e0 * sigma0 pow 2) <= P * inv(&16)` THEN
    UNDISCH_TAC `&0 < P` THEN UNDISCH_TAC `&0 <= I0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL
   [ASM_CASES_TAC `A = &0` THENL
     [UNDISCH_TAC `~(A * e0 * sigma0 pow 2 <= inv (&16))` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `sig = sqrt(inv(&16 * A * e0))` THEN
  SUBGOAL_THEN `&0 < &16 * A * e0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sig /\ sig pow 2 = inv(&16 * A * e0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV_EQ; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `sig < sigma0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!x y. &0 < y /\ ~(y <= x) ==> x < y`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sigma0 pow 2 <= sig pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(A * e0 * sigma0 pow 2 <= inv (&16))` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `A * e0 * sigma0 pow 2 <= (A * e0) * inv(&16 * A * e0)` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
    UNDISCH_TAC `&0 < &16 * A * e0` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real`; `s:real^2->bool`; `h:real^2->real`; `x0:real^2`; `sigma0:real`;
                 `sig:real`; `e0:real`; `ball(a:real^2,rho)`] HMR_SUBMEAN_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^2,sigma0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `A * (pi * sig pow 2 * e0) = pi / &16 /\
                A * (&4 * A * pi * e0 pow 2 * sig pow 4) = pi / &64`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x pow 4 = (x pow 2) pow 2`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN UNDISCH_TAC `&0 < A` THEN UNDISCH_TAC `&0 < e0` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < A`))) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB;
              ASSUME `A * (pi * sig pow 2 * e0) = pi / &16`;
              ASSUME `A * (&4 * A * pi * e0 pow 2 * sig pow 4) = pi / &64`;
              ASSUME `drop(integral (ball(a,rho)) (\x. lift((h:real^2->real) x))) = I0`] THEN
  UNDISCH_TAC `A * I0 < &3 * pi / &64` THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* First-derivative epsilon-regularity.                                      *)
(* The Euclidean energy density e = hmr_e u of a smooth W^{1,2} map is       *)
(* integrable with lam int e <= wan_gdir; with the Bochner inequality and    *)
(* Schoen's argument on cball(a, 3r/4):                                      *)
(*   r^2 e(x) <= C wan_gdir (ball(a,r)) G u   on ball(a, r/2)                *)
(* for small G-energy.                                                       *)
(* ========================================================================= *)

let HMR_E_SMOOTH = prove
 (`!s (u:real^2->real^K). open s /\ smooth_map_on s u ==> smooth_map_on s (\x. lift(hmr_e u x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_e] THEN MATCH_MP_TAC CML_SM_ADD THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX]);;

let HMR_E_POS = prove
 (`!(u:real^2->real^K) x. &0 <= hmr_e u x`,
  REWRITE_TAC[hmr_e] THEN MESON_TAC[DOT_POS_LE; REAL_LE_ADD]);;

let HMR_GDIR_LOWER = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?lam. &0 < lam /\
               !s (u:real^2->real^K).
                  open s /\ smooth_map_on s u /\ wan_w12 s u
                  ==> (\x. lift(hmr_e u x)) integrable_on s /\
                      lam * drop(integral s (\x. lift(hmr_e u x))) <= wan_gdir s G u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam0:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 s (u:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(partial_derivative i (u:real^2->real^K) x dot partial_derivative i u x))
            integrable_on s /\
            (\x. lift(partial_derivative i u x dot ((G:real^K->real^K^K)(u x) **
                                                    partial_derivative i u x)))
            integrable_on s`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\x. partial_derivative i (u:real^2->real^K) x) IN lspace s (&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC HMC_PD_LSPACE THEN ASM_REWRITE_TAC[DIMINDEX_2]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(\x. partial_derivative i (u:real^2->real^K) x) IN lspace s (&2)` THEN
      REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW; NORM_POW_2] THEN SIMP_TAC[];
      MATCH_MP_TAC HMC_QUAD_INTEGRABLE THEN EXISTS_TAC `Lam0:real` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
        SUBGOAL_THEN `(vectorize:real^K^K->real^(K,K)finite_prod) o
                      (\x. (G:real^K->real^K^K)((u:real^2->real^K) x)) =
                      ((vectorize:real^K^K->real^(K,K)finite_prod) o G) o u` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_ABS_REFL; REAL_ARITH `&0 <= x ==> abs x = x`]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[hmr_e; LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `u:real^2->real^K`] HMC_GDIR_CLASSICAL) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; SUM_2] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[hmr_e; LIFT_ADD] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; DROP_ADD; REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_REWRITE_TAC[]);;

let HMR_EPS_E = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?e C. &0 < e /\ &0 < C /\
               !(a:real^2) r (u:real^2->real^K).
                  &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
                  wan_gdir (ball(a,r)) G u <= e
                  ==> !x. x IN ball(a,r / &2)
                          ==> r pow 2 * hmr_e u x <= C * wan_gdir (ball(a,r)) G u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC o MATCH_MP HMR_BOCHNER) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lam:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GL")) o
    MATCH_MP HMR_GDIR_LOWER) THEN
  MAP_EVERY EXISTS_TAC [`lam * pi / (&64 * (A + &1))`; `&96 / lam`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; PI_POS; REAL_ARITH `&0 <= A ==> &0 < &64 * (A + &1)`];
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real^K`] THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `ball(a:real^2,&3 * r / &4) SUBSET ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "GL" (MP_TAC o ISPECL [`ball(a:real^2,r)`; `u:real^2->real^K`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL]; STRIP_TAC] THEN
  ABBREV_TAC `E = wan_gdir (ball(a,r)) (G:real^K->real^K^K) (u:real^2->real^K)` THEN
  SUBGOAL_THEN `(\x. lift(hmr_e (u:real^2->real^K) x)) integrable_on ball(a,&3 * r / &4)`
  ASSUME_TAC THENL
   [USE_THEN "GL" (MP_TAC o ISPECL [`ball(a:real^2,&3 * r / &4)`; `u:real^2->real^K`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET];
        MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
        ASM_REWRITE_TAC[OPEN_BALL]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (ball(a,&3 * r / &4)) (\x. lift(hmr_e (u:real^2->real^K) x))) <=
                drop(integral (ball(a,r)) (\x. lift(hmr_e u x)))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP; HMR_E_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (ball(a,r)) (\x. lift(hmr_e (u:real^2->real^K) x))) <=
                pi / (&64 * (A + &1))` ASSUME_TAC THENL
   [SUBGOAL_THEN `lam * drop(integral (ball(a,r)) (\x. lift(hmr_e (u:real^2->real^K) x))) <=
                  lam * pi / (&64 * (A + &1))` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS]; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real`; `ball(a:real^2,r)`; `hmr_e (u:real^2->real^K)`; `a:real^2`;
                 `&3 * r / &4`] HMR_SCHOEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; HMR_E_POS] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HMR_E_SMOOTH THEN ASM_REWRITE_TAC[OPEN_BALL];
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `A * pi / (&64 * (A + &1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN `A * pi / (&64 * (A + &1)) = (A / (A + &1)) * pi / &64` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 <= A` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(prove(`!p q. &0 < p /\ q < &1 ==> q * p / &64 < &3 * p / &64`,
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_DIV; REAL_ARITH `&0 < &64`] THEN
      ASM_REAL_ARITH_TAC)) THEN
    REWRITE_TAC[PI_POS] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= A ==> &0 < A + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN ball(a,r / &2)` THEN REWRITE_TAC[IN_BALL; IN_CBALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r / &4 <= &3 * r / &4 - norm(x - a:real^2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN ball(a,r / &2)` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL [`a:real^2`; `x:real^2`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(r / &4) pow 2 * hmr_e (u:real^2->real^K) x <=
                (&3 * r / &4 - norm(x - a:real^2)) pow 2 * hmr_e u x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[HMR_E_POS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(r / &4) pow 2 * hmr_e (u:real^2->real^K) x <=
                &6 * drop(integral (ball(a,r)) (\x. lift(hmr_e u x)))` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(r / &4) pow 2 * hmr_e (u:real^2->real^K) x <=
       (&3 * r / &4 - norm(x - a:real^2)) pow 2 * hmr_e u x`;
      `(&3 * r / &4 - norm(x - a:real^2)) pow 2 * hmr_e (u:real^2->real^K) x <=
       &6 * drop(integral (ball(a,&3 * r / &4)) (\x. lift(hmr_e u x)))`;
      `drop(integral (ball(a,&3 * r / &4)) (\x. lift(hmr_e (u:real^2->real^K) x))) <=
       drop(integral (ball(a,r)) (\x. lift(hmr_e u x)))`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (ball(a,r)) (\x. lift(hmr_e (u:real^2->real^K) x))) <= E / lam`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 * hmr_e (u:real^2->real^K) x = &16 * ((r / &4) pow 2 * hmr_e u x)`
  SUBST1_TAC THENL [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&96 / lam * E = &96 * (E / lam)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The log-potential estimate for smooth functions.  A map smooth on an open *)
(* set containing cball(c,rho) is in W^{1,2} of the ball with the classical  *)
(* partials as weak partials; a smooth scalar function solves                *)
(* Lap w = cml_lap w weakly there; hence WAN_LOGPOT_C1A_QUANT bounds         *)
(* rho |d_i w(c)| by C (M rho^2 + U).                                        *)
(* ========================================================================= *)

let HMR_LSPACE_CBALL = prove
 (`!s (g:real^2->real^N) c rho.
     open s /\ cball(c,rho) SUBSET s /\ g continuous_on s
     ==> g IN lspace (ball(c,rho)) (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_BOUNDED_MEASURABLE_SIMPLE THEN
  REWRITE_TAC[MEASURABLE_BALL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `ball(c:real^2,rho) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(c:real^2,rho)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `IMAGE (g:real^2->real^N) (cball(c,rho))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL]]);;

let HMR_W12_SMOOTH_BALL = prove
 (`!s (h:real^2->real^N) c rho.
     open s /\ cball(c,rho) SUBSET s /\ smooth_map_on s h
     ==> wan_w12 (ball(c,rho)) h /\
         !i. 1 <= i /\ i <= 2
             ==> wan_wpd (ball(c,rho)) i h (\x. partial_derivative i h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(c:real^2,rho) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(c:real^2,rho)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[WAN_W12_C1_STATEMENT]
    (ISPECL [`(:2)`; `(:N)`] WAN_W12_C1)) THEN
  DISCH_THEN(MP_TAC o SPECL [`ball(c:real^2,rho)`; `h:real^2->real^N`]) THEN
  REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `smooth_map_on (ball(c:real^2,rho)) (h:real^2->real^N)` MP_TAC THENL
       [ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET]; SIMP_TAC[smooth_map_on]];
      MATCH_MP_TAC HMR_LSPACE_CBALL THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC HMR_LSPACE_CBALL THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]];
    SIMP_TAC[]]);;

let HMR_WEAK_LAP_BALL = prove
 (`!s (w:real^2->real) c rho.
     open s /\ cball(c,rho) SUBSET s /\ smooth_map_on s (\x. lift(w x))
     ==> !phi. wan_test (ball(c,rho)) phi
               ==> vsum(1..2)
                     (\i. integral (ball(c,rho))
                            (\x. wan_dpart i phi x %
                                 wan_wd (ball(c,rho)) i (\y. lift(w y)) x)) =
                   --(integral (ball(c,rho)) (\x. lift(cml_lap w x * phi x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `phi:real^2->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ball(c:real^2,rho) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(c:real^2,rho)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `\y. lift((w:real^2->real) y)`; `c:real^2`; `rho:real`]
    HMR_W12_SMOOTH_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> integral (ball(c,rho))
              (\x. wan_dpart i phi x % wan_wd (ball(c,rho)) i (\y. lift((w:real^2->real) y)) x) =
            --(integral (ball(c,rho)) (\x. lift(phi x * cml_d i (cml_d i w) x)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(c:real^2,rho)`; `i:num`; `\y. lift((w:real^2->real) y)`;
                   `\x. partial_derivative i (\y. lift((w:real^2->real) y)) x`]
      WAN_WD_UNIQUE) THEN
    ASM_SIMP_TAC[OPEN_BALL; DIMINDEX_2] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `integral (ball(c,rho))
        (\x. wan_dpart i phi x % wan_wd (ball(c,rho)) i (\y. lift((w:real^2->real) y)) x) =
      integral (ball(c,rho))
        (\x. wan_dpart i phi x % partial_derivative i (\y. lift((w:real^2->real) y)) x)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC `{x | x IN ball(c,rho) /\
                       ~(wan_wd (ball(c,rho)) i (\y. lift((w:real^2->real) y)) x =
                         partial_derivative i (\y. lift(w y)) x)}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `partial_derivative i (\y. lift((w:real^2->real) y))`;
                   `c:real^2`; `rho:real`] HMR_W12_SMOOTH_BALL) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[wan_wpd] THEN
    DISCH_THEN(MP_TAC o SPEC `phi:real^2->real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
    REWRITE_TAC[cml_d; LIFT_DROP; ETA_AX; LIFT_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_2] THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC o CONJUNCT2 o
    GEN_REWRITE_RULE I [wan_test]) THEN
  SUBGOAL_THEN
   `!i. (\x. lift(phi x * cml_d i (cml_d i (w:real^2->real)) x)) integrable_on ball(c,rho)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC HMR_SUPP_ABSINT THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CML_SM_MUL THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[wan_test];
        REPEAT(MATCH_MP_TAC CML_D_SMOOTH THEN REWRITE_TAC[OPEN_BALL]) THEN
        ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET]];
      REWRITE_TAC[IN_DIFF] THEN ASM_SIMP_TAC[REAL_MUL_LZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `--a + --b:real^N = --(a + b)`] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_ADD] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM LIFT_ADD; cml_lap] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let HMR_LOGPOT_SMOOTH = prove
 (`?C. &0 < C /\
       !s (w:real^2->real) c rho M U.
          open s /\ &0 < rho /\ cball(c,rho) SUBSET s /\ smooth_map_on s (\x. lift(w x)) /\
          (!x. x IN ball(c,rho) ==> abs(cml_lap w x) <= M) /\
          (!x. x IN ball(c,rho) ==> abs(w x) <= U)
          ==> !i. 1 <= i /\ i <= 2 ==> rho * abs(cml_d i w c) <= C * (M * rho pow 2 + U)`,
  MP_TAC(REWRITE_RULE[WAN_LOGPOT_C1A_QUANT_STATEMENT] WAN_LOGPOT_C1A_QUANT) THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lp"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(c:real^2,rho) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(c:real^2,rho)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  USE_THEN "lp" (MP_TAC o SPECL [`c:real^2`; `rho:real`; `w:real^2->real`;
                                 `cml_lap (w:real^2->real)`; `M:real`; `U:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^2->bool`; `\y. lift((w:real^2->real) y)`; `c:real^2`;
                     `rho:real`] HMR_W12_SMOOTH_BALL) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[cml_lap] THEN
      MATCH_MP_TAC CML_SM_ADD THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC CML_D_SMOOTH THEN REWRITE_TAC[OPEN_BALL]) THEN
      ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET];
      MATCH_MP_TAC HMR_WEAK_LAP_BALL THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2->real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gb") (K ALL_TAC))))) THEN
  SUBGOAL_THEN `!x. x IN ball(c,rho / &2) ==> lift((v:real^2->real) x) = lift(w x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONT_AE_EQ_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(c:real^2,rho)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[LIFT_EQ] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] NEGLIGIBLE_SUBSET)) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cml_d i (w:real^2->real) c = cml_d i v c` SUBST1_TAC THENL
   [MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `ball(c:real^2,rho / &2)` THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[LIFT_EQ]];
    ALL_TAC] THEN
  USE_THEN "gb" (MP_TAC o SPEC `c:real^2`) THEN
  REWRITE_TAC[CENTRE_IN_BALL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MP_TAC(ISPECL [`wan_grad (v:real^2->real) c`; `i:num`] COMPONENT_LE_NORM) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN
  SIMP_TAC[wan_grad; LAMBDA_BETA; DIMINDEX_2; ASSUME `1 <= i`; ASSUME `i <= 2`] THEN
  REWRITE_TAC[wan_dpart; cml_d; partial_derivative]);;

(* ========================================================================= *)
(* The jet bound of the right-hand side                                      *)
(* hmr_fq S G u = sum_i Bq(u)(d_i u, d_i u) of the harmonic map system.      *)
(* Writing Bq(u)(X, X) = sum_(a,b) X_a X_b Bq(u)(e_a, e_b), the Leibniz rule *)
(* with split orders (RDT_LEIBNIZ_JET) puts at most one factor of top order  *)
(* on X = d_i u, and the tame composition bound (RDT_COMPOSE_JETN) controls  *)
(* Bq(u)(e_a, e_b); so the m-jet of hmr_fq is linear in the m-jets of the    *)
(* d_i u once their (m-1)-jets are bounded.                                  *)
(* ========================================================================= *)

let hmr_fq = new_definition
 `hmr_fq S (G:real^K->real^K^K) (u:real^2->real^K) (y:real^2) =
    vsum(1..2) (\i. hmr_bq S G (u y) (partial_derivative i u y) (partial_derivative i u y))`;;

(* Products of two jets of total order at most m: one factor has order below *)
(* m, or the other has order 0.                                               *)

let HMR_JET_PAIR = prove
 (`!m A (X:real^2->real^P) z p q.
     1 <= m /\ pde_jetn (m - 1) X z <= A /\ p + q <= m
     ==> pde_jetn p X z * pde_jetn q X z <= A * pde_jetn m X z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k <= m - 1 ==> pde_jetn k (X:real^2->real^P) z <= A` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (m - 1) (X:real^2->real^P) z` THEN ASM_SIMP_TAC[PDE_JETN_MONO];
    ALL_TAC] THEN
  ASM_CASES_TAC `p <= m - 1` THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[PDE_JETN_POS] THEN
    MATCH_MP_TAC PDE_JETN_MONO THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(p:num) = m /\ (q:num) = 0` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[PDE_JETN_POS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* The m-jet of a product of two components of X, linear in the m-jet of X. *)

let HMR_FSC_JET = prove
 (`!m A U (X:real^2->real^K) z a b.
     1 <= m /\ &0 <= A /\ open U /\ smooth_map_on U X /\ z IN U /\
     1 <= a /\ a <= dimindex(:K) /\ 1 <= b /\ b <= dimindex(:K) /\
     pde_jetn (m - 1) X z <= A
     ==> pde_jetn m (\y. lift(X y$a * X y$b)) z <=
         &(CARD(pde_index_lists m (:2))) * (&2 pow m * &(m + 1) * A * pde_jetn m X z)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [pde_jetn] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x y:real^1. lift(drop x * drop y)`; `&1`]
    (INST_TYPE [`:2`,`:N`] RDT_LEIBNIZ_JET)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BILINEAR_LIFT_MUL; REAL_POS; NORM_LIFT; REAL_ABS_MUL; REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o ISPECL [`l:num list`; `U:real^2->bool`; `\y. lift((X:real^2->real^K) y$a)`;
                              `\y. lift((X:real^2->real^K) y$b)`; `z:real^2`]) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; LIFT_DROP; REAL_MUL_LID] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN
   `sum(0..LENGTH(l:num list))
        (\k. pde_jetn k (\y. lift((X:real^2->real^K) y$a)) z *
             pde_jetn (LENGTH l - k) (\y. lift(X y$b)) z) <=
    &(m + 1) * (A * pde_jetn m X z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..LENGTH(l:num list)) (\k. A * pde_jetn m (X:real^2->real^K) z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_jetn k (X:real^2->real^K) z * pde_jetn (LENGTH(l:num list) - k) X z` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[PDE_JETN_POS] THEN
        CONJ_TAC THEN MATCH_MP_TAC P2CT_JETN_LIFT_COMPONENT THEN
        EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HMR_JET_PAIR THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 pow m * (&(m + 1) * (A * pde_jetn m (X:real^2->real^K) z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PDE_JETN_POS]];
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]]);;

(* The jet bound of hmr_fq. *)

let HMR_FQ_JET = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !m A. 1 <= m /\ &0 <= A
               ==> ?C. &0 <= C /\
                       !U (u:real^2->real^K) z.
                          open U /\ smooth_map_on U u /\ (!y. y IN U ==> u y IN S) /\
                          z IN U /\
                          sum(1..2) (\i. pde_jetn (m - 1) (partial_derivative i u) z) <= A
                          ==> pde_jetn m (hmr_fq S G u) z <=
                              C * sum(1..2) (\i. pde_jetn m (partial_derivative i u) z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_BQ_FAMILY) THEN
  SUBGOAL_THEN `?R. &0 <= R /\ !p:real^K. p IN S ==> norm p <= R` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `NL = &(CARD(pde_index_lists m (:2)))` THEN
  SUBGOAL_THEN `&0 <= NL` ASSUME_TAC THENL [EXPAND_TAC "NL" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. ?Cab. &0 <= Cab /\
                !U' (Kf:real^2->real^K) y.
                   open U' /\ smooth_map_on U' Kf /\ IMAGE Kf U' SUBSET cm_tube S d /\
                   y IN U' /\ Kf y IN S /\ pde_jetn (m DIV 2 + 1) Kf y <= R + NL * A
                   ==> pde_jetn m (\z. hmr_bq S G (Kf z) (basis a) (basis b)) y <=
                       Cab * (&1 + pde_jetn m Kf y)`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`m:num`; `\p. hmr_bq S (G:real^K->real^K^K) p (basis a) (basis b)`;
                   `cm_tube (S:real^K->bool) d`; `S:real^K->bool`; `R + NL * A`]
      (INST_TYPE [`:K`,`:M`; `:K`,`:P`; `:2`,`:N`] RDT_COMPOSE_JETN)) THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL] THEN
    DISCH_THEN(X_CHOOSE_THEN `Cab:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Cab:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `CC:num->num->real` (LABEL_TAC "cc"))] THEN
  SUBGOAL_THEN `!a b. &0 <= (CC:num->num->real) a b` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN USE_THEN "cc" (MP_TAC o SPECL [`a:num`; `b:num`]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `B1 = NL * &2 pow m * &(m + 1) * A` THEN
  SUBGOAL_THEN `&0 <= B1` ASSUME_TAC THENL
   [EXPAND_TAC "B1" THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `CS = sum(1..dimindex(:K)) (\a. sum(1..dimindex(:K)) (\b. (CC:num->num->real) a b))` THEN
  SUBGOAL_THEN `&0 <= CS` ASSUME_TAC THENL
   [EXPAND_TAC "CS" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + R + NL * A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `NL * &2 pow m * B1 * (&1 + R + NL * A) * CS` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^2->bool`; `u:real^2->real^K`; `z:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (u:real^2->real^K) U SUBSET cm_tube S d` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. smooth_map_on U (partial_derivative i (u:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> pde_jetn (m - 1) (partial_derivative i (u:real^2->real^K)) z <= A`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\i. pde_jetn (m - 1) (partial_derivative i (u:real^2->real^K)) z`; `A:real`;
                   `1..2`] SUM_POS_BOUND) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; PDE_JETN_POS; IN_NUMSEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the jet of u itself *)
  SUBGOAL_THEN `pde_jetn m (u:real^2->real^K) z <= R + NL * A` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m - 1`; `u:real^2->real^K`; `z:real^2`] P2CT_JETN_SUC_BOUND) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= m ==> SUC(m - 1) = m`; DIMINDEX_2] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= R /\ b <= c ==> x <= a + b ==> x <= R + c`) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "NL" THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  (* the coefficient jets *)
  SUBGOAL_THEN
   `!a b. pde_jetn m (\y. hmr_bq S G ((u:real^2->real^K) y) (basis a) (basis b)) z <=
          CC a b * (&1 + R + NL * A)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(CC:num->num->real) a b * (&1 + pde_jetn m (u:real^2->real^K) z)` THEN
    CONJ_TAC THENL
     [USE_THEN "cc" (MP_TAC o SPECL [`a:num`; `b:num`]) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `U:real^2->bool` THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn m (u:real^2->real^K) z` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN
      UNDISCH_TAC `1 <= m` THEN MP_TAC(SPECL [`m:num`; `2`] DIVISION) THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the expansion of hmr_fq *)
  SUBGOAL_THEN
   `!y. y IN U
        ==> hmr_fq S G (u:real^2->real^K) y =
            vsum(1..2) (\i. vsum(1..dimindex(:K)) (\a. vsum(1..dimindex(:K)) (\b.
              drop(lift(partial_derivative i u y$a * partial_derivative i u y$b)) %
              hmr_bq S G (u y) (basis a) (basis b))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_fq; LIFT_DROP] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CT_BILINEAR_BASIS_EXPAND THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `U:real^2->bool`; `hmr_fq S G (u:real^2->real^K)`;
    `\y. vsum(1..2) (\i. vsum(1..dimindex(:K)) (\a. vsum(1..dimindex(:K)) (\b.
           drop(lift(partial_derivative i (u:real^2->real^K) y$a * partial_derivative i u y$b)) %
           hmr_bq S G (u y) (basis a) (basis b))))`; `z:real^2`] P2CT_JETN_LOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  (* smoothness of the summands *)
  SUBGOAL_THEN
   `!i a b. smooth_map_on U (\y. lift(partial_derivative i (u:real^2->real^K) y$a *
                                      partial_derivative i u y$b))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `\y. lift(partial_derivative i (u:real^2->real^K) y$a)`;
                   `\y. lift(partial_derivative i (u:real^2->real^K) y$b)`]
      SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. smooth_map_on U (\y. hmr_bq S G ((u:real^2->real^K) y) (basis a) (basis b))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `(\y. hmr_bq S G ((u:real^2->real^K) y) (basis a) (basis b)) =
                  (\p. hmr_bq S (G:real^K->real^K^K) p (basis a) (basis b)) o u`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i a b. smooth_map_on U
              (\y. drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                             partial_derivative i u y$b)) %
                   hmr_bq S G (u y) (basis a) (basis b))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i a. smooth_map_on U
            (\y. vsum(1..dimindex(:K)) (\b.
               drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                         partial_derivative i u y$b)) %
               hmr_bq S G (u y) (basis a) (basis b)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^2->bool`;
      `\b y. drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                       partial_derivative i u y$b)) %
             hmr_bq S G (u y) (basis a) (basis b)`; `1..dimindex(:K)`]
      SMOOTH_MAP_ON_VSUM_OPEN) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. smooth_map_on U
          (\y. vsum(1..dimindex(:K)) (\a. vsum(1..dimindex(:K)) (\b.
             drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                       partial_derivative i u y$b)) %
             hmr_bq S G (u y) (basis a) (basis b))))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^2->bool`;
      `\a y. vsum(1..dimindex(:K)) (\b.
               drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                         partial_derivative i u y$b)) %
               hmr_bq S G (u y) (basis a) (basis b))`; `1..dimindex(:K)`]
      SMOOTH_MAP_ON_VSUM_OPEN) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  (* the bound of one summand *)
  SUBGOAL_THEN
   `!i a b. 1 <= i /\ i <= 2 /\ 1 <= a /\ a <= dimindex(:K) /\ 1 <= b /\ b <= dimindex(:K)
            ==> pde_jetn m
                  (\y. drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                                 partial_derivative i u y$b)) %
                       hmr_bq S G (u y) (basis a) (basis b)) z <=
                NL * &2 pow m * &1 * (B1 * pde_jetn m (partial_derivative i u) z) *
                (CC a b * (&1 + R + NL * A))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`; `U:real^2->bool`;
      `\y. lift(partial_derivative i (u:real^2->real^K) y$a * partial_derivative i u y$b)`;
      `\y. hmr_bq S G ((u:real^2->real^K) y) (basis a) (basis b)`; `z:real^2`]
      P2CT_JETN_DROP_MUL) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    EXPAND_TAC "NL" THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[PDE_JETN_POS] THEN
    MP_TAC(ISPECL [`m:num`; `A:real`; `U:real^2->bool`;
                   `partial_derivative i (u:real^2->real^K)`; `z:real^2`; `a:num`; `b:num`]
      HMR_FSC_JET) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "B1" THEN EXPAND_TAC "NL" THEN REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  (* summing up *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..2) (\i. pde_jetn m
      (\y. vsum(1..dimindex(:K)) (\a. vsum(1..dimindex(:K)) (\b.
             drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                       partial_derivative i u y$b)) %
             hmr_bq S G (u y) (basis a) (basis b)))) z)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `U:real^2->bool`; `1..2`;
      `\i y. vsum(1..dimindex(:K)) (\a. vsum(1..dimindex(:K)) (\b.
               drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                         partial_derivative i u y$b)) %
               hmr_bq S G (u y) (basis a) (basis b)))`; `z:real^2`] P2CT_JETN_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:K)) (\a. pde_jetn m
      (\y. vsum(1..dimindex(:K)) (\b.
             drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                       partial_derivative i u y$b)) %
             hmr_bq S G (u y) (basis a) (basis b))) z)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `U:real^2->bool`; `1..dimindex(:K)`;
      `\a y. vsum(1..dimindex(:K)) (\b.
               drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                         partial_derivative i u y$b)) %
               hmr_bq S G (u y) (basis a) (basis b))`; `z:real^2`] P2CT_JETN_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:K)) (\a. sum(1..dimindex(:K)) (\b. pde_jetn m
      (\y. drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                     partial_derivative i u y$b)) %
           hmr_bq S G (u y) (basis a) (basis b)) z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:num`; `U:real^2->bool`; `1..dimindex(:K)`;
      `\b y. drop(lift(partial_derivative i (u:real^2->real^K) y$a *
                       partial_derivative i u y$b)) %
             hmr_bq S G (u y) (basis a) (basis b)`; `z:real^2`] P2CT_JETN_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:K)) (\a. sum(1..dimindex(:K)) (\b.
      NL * &2 pow m * &1 * (B1 * pde_jetn m (partial_derivative i (u:real^2->real^K)) z) *
      (CC a b * (&1 + R + NL * A))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "CS" THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The scaled jet bound.  For the dilated map v(w) = u(r w + z) the jets at  *)
(* w = 0 are the r-weighted jets of u at z, and                              *)
(* hmr_fq S G v = r^2 hmr_fq S G u (r w + z); so HMR_FQ_JET at v gives the   *)
(* bound of the r-weighted m-jet of hmr_fq S G u by the r-weighted           *)
(* derivative jet hmr_dj m r u z.                                            *)
(* ========================================================================= *)

let hmr_dj = new_definition
 `hmr_dj m r (u:real^2->real^K) (z:real^2) =
    sum(1..2) (\i. sum (pde_index_lists m (:2))
                     (\l. r pow (LENGTH l + 1) *
                          norm(iterated_partial l (partial_derivative i u) z)))`;;

let HMR_DJ_POS = prove
 (`!m r (u:real^2->real^K) z. &0 <= r ==> &0 <= hmr_dj m r u z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_dj] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; NORM_POS_LE]);;

(* Iterated partials of a dilation on an open set. *)

let HMR_ITLIST_CONST_MUL = prove
 (`!(r:real) l. ITLIST (\i:num s. r * s) l (&1) = r pow (LENGTH l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; LENGTH; real_pow]);;

let HMR_ITP_SCALE = prove
 (`!U (f:real^2->real^N) r z l.
     open U /\ smooth_map_on U f /\ ALL (\i. 1 <= i /\ i <= 2) l
     ==> !w. r % w + z IN U
             ==> iterated_partial l (\w. f(r % w + z)) w =
                 r pow (LENGTH l) % iterated_partial l f (r % w + z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `\w:real^2. r % w + z`; `U:real^2->bool`;
                 `\i:num. r:real`; `\i:num. i`; `l:num list`]
    PDE_ITERATED_PARTIAL_COMPOSE) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; MAP_ID; HMR_ITLIST_CONST_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_ADD THEN REWRITE_TAC[DIFFERENTIABLE_CONST] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN REWRITE_TAC[DIFFERENTIABLE_ID];
    MAP_EVERY X_GEN_TAC [`w:real^2`; `i:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x:real^2. x`; `r:real`; `z:real^2`; `i:num`; `w:real^2`]
      PDM_PARTIAL_AFFINE) THEN
    REWRITE_TAC[DIFFERENTIABLE_ID; PARTIAL_DERIVATIVE_ID]]);;

(* Smoothness of hmr_fq. *)

let HMR_FQ_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d U (u:real^2->real^K).
     cm_target S G d /\ open U /\ smooth_map_on U u /\ (!y. y IN U ==> u y IN S)
     ==> smooth_map_on U (hmr_fq S G u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_BQ_FAMILY) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\y. vsum(1..2) (\i. vsum(1..dimindex(:K)) (\a. vsum(1..dimindex(:K)) (\b.
          drop(lift(partial_derivative i (u:real^2->real^K) y$a * partial_derivative i u y$b)) %
          hmr_bq S G (u y) (basis a) (basis b))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_fq; LIFT_DROP] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CT_BILINEAR_BASIS_EXPAND THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (u:real^2->real^K) U SUBSET cm_tube S d` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. smooth_map_on U (partial_derivative i (u:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^2->bool`; `\y. lift(partial_derivative i (u:real^2->real^K) y$a)`;
                   `\y. lift(partial_derivative i (u:real^2->real^K) y$b)`]
      SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; LIFT_DROP; ETA_AX];
    SUBGOAL_THEN `(\y. hmr_bq S G ((u:real^2->real^K) y) (basis a) (basis b)) =
                  (\p. hmr_bq S (G:real^K->real^K^K) p (basis a) (basis b)) o u`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
    ASM_REWRITE_TAC[]]);;

(* The scaled jet bound. *)

let HMR_FQ_JET_SCALED = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !m A. 1 <= m /\ &0 <= A
               ==> ?C. &0 <= C /\
                       !U (u:real^2->real^K) z r.
                          open U /\ smooth_map_on U u /\ (!y. y IN U ==> u y IN S) /\
                          z IN U /\ &0 < r /\ hmr_dj (m - 1) r u z <= A
                          ==> sum (pde_index_lists m (:2))
                                (\l. r pow (LENGTH l + 2) *
                                     norm(iterated_partial l (hmr_fq S G u) z))
                              <= C * hmr_dj m r u z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`m:num`; `A:real`] o MATCH_MP HMR_FQ_JET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fj"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`U:real^2->bool`; `u:real^2->real^K`; `z:real^2`; `r:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `U' = {w:real^2 | r % w + z IN U}` THEN
  SUBGOAL_THEN `open (U':real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U'" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_CONST] THEN MATCH_MP_TAC CONTINUOUS_CMUL THEN
    REWRITE_TAC[CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. w IN U' ==> r % w + z IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U'" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^2) IN U'` ASSUME_TAC THENL
   [EXPAND_TAC "U'" THEN ASM_REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_RZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U' (\w. (u:real^2->real^K)(r % w + z))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\w. (u:real^2->real^K)(r % w + z)) = u o (\w. r % w + z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. ALL (\i. 1 <= i /\ i <= 2) l
                    ==> !w. w IN U'
                            ==> iterated_partial l (\w. (u:real^2->real^K)(r % w + z)) w =
                                r pow (LENGTH l) % iterated_partial l u (r % w + z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `u:real^2->real^K`; `r:real`; `z:real^2`; `l:num list`]
      HMR_ITP_SCALE) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the derivative jets of the dilation *)
  SUBGOAL_THEN
   `!k. sum(1..2) (\i. pde_jetn k
          (partial_derivative i (\w. (u:real^2->real^K)(r % w + z))) (vec 0)) =
        hmr_dj k r u z`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[hmr_dj; pde_jetn] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM; DIMINDEX_2] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!f:real^2->real^K. iterated_partial l (partial_derivative i f) =
                         iterated_partial (APPEND l [i]) f`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `APPEND (l:num list) [i]`) THEN
    ASM_REWRITE_TAC[ALL_APPEND; ALL] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_POW; LENGTH_APPEND; LENGTH] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; ARITH_RULE `n + SUC 0 = n + 1`];
    ALL_TAC] THEN
  (* the right-hand side of the dilation *)
  SUBGOAL_THEN
   `!w. w IN U'
        ==> hmr_fq S G (\w. (u:real^2->real^K)(r % w + z)) w =
            (r pow 2) % hmr_fq S G u (r % w + z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_fq] THEN
    SUBGOAL_THEN
     `!i. 1 <= i /\ i <= 2
          ==> partial_derivative i (\w. (u:real^2->real^K)(r % w + z)) w =
              r % partial_derivative i u (r % w + z)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `[i:num]`) THEN
      ASM_REWRITE_TAC[ALL; iterated_partial; LENGTH] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^2`) THEN ASM_REWRITE_TAC[ETA_AX] THEN
      REWRITE_TAC[REAL_POW_1; ARITH_RULE `SUC 0 = 1`];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM VSUM_LMUL] THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_BQ_FAMILY) THEN
    SUBGOAL_THEN `bilinear (hmr_bq S (G:real^K->real^K^K) ((u:real^2->real^K)(r % w + z)))`
    ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[BILINEAR_LMUL; BILINEAR_RMUL; VECTOR_MUL_ASSOC; REAL_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (hmr_fq S G (u:real^2->real^K))` ASSUME_TAC THENL
   [MATCH_MP_TAC HMR_FQ_SMOOTH THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_jetn m (hmr_fq S G (\w. (u:real^2->real^K)(r % w + z))) (vec 0) =
    sum (pde_index_lists m (:2))
        (\l. r pow (LENGTH l + 2) * norm(iterated_partial l (hmr_fq S G u) z))`
  (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM; DIMINDEX_2] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:num list`; `U':real^2->bool`;
                   `hmr_fq S G (\w. (u:real^2->real^K)(r % w + z))`;
                   `\w. (r pow 2) % hmr_fq S G (u:real^2->real^K) (r % w + z)`;
                   `vec 0:real^2`] TEXT_ITERATED_PARTIAL_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`l:num list`; `\x:real^K. (r pow 2) % x`;
                   `\w. hmr_fq S G (u:real^2->real^K) (r % w + z)`; `U':real^2->bool`;
                   `vec 0:real^2`] PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
        SUBGOAL_THEN `(\w. hmr_fq S G (u:real^2->real^K) (r % w + z)) =
                      hmr_fq S G u o (\w. r % w + z)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^2->bool` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `hmr_fq S G (u:real^2->real^K)`; `r:real`; `z:real^2`;
                   `l:num list`] HMR_ITP_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_POW; REAL_ABS_MUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_POW_ADD; REAL_MUL_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hmr_dj m r (u:real^2->real^K) z =
    sum(1..2) (\i. pde_jetn m (partial_derivative i (\w. u(r % w + z))) (vec 0))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "fj" (MP_TAC o SPECL [`U':real^2->bool`; `\w. (u:real^2->real^K)(r % w + z)`;
                                 `vec 0:real^2`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* Tools for the weighted maximum argument: monotonicity, continuity and     *)
(* splitting of the weighted derivative jet hmr_dj, and the Laplacian of a   *)
(* component of a derivative of u, which is a component of a derivative of   *)
(* hmr_vlap u.                                                               *)
(* ========================================================================= *)

let HMR_DJ_MONO = prove
 (`!m r1 r2 (u:real^2->real^K) z.
     &0 <= r1 /\ r1 <= r2 ==> hmr_dj m r1 u z <= hmr_dj m r2 u z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_dj] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]);;

(* A single term of hmr_dj. *)

let HMR_DJ_TERM = prove
 (`!m r (u:real^2->real^K) z i l.
     &0 <= r /\ 1 <= i /\ i <= 2 /\ LENGTH l <= m /\ ALL (\j. 1 <= j /\ j <= 2) l
     ==> r pow (LENGTH l + 1) * norm(iterated_partial l (partial_derivative i u) z)
         <= hmr_dj m r u z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_dj] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists m (:2))
                (\l. r pow (LENGTH l + 1) *
                     norm(iterated_partial l (partial_derivative i (u:real^2->real^K)) z))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\l. r pow (LENGTH l + 1) *
                        norm(iterated_partial l (partial_derivative i (u:real^2->real^K)) z)`;
                   `sum (pde_index_lists m (:2))
                      (\l. r pow (LENGTH l + 1) *
                           norm(iterated_partial l (partial_derivative i (u:real^2->real^K)) z))`;
                   `pde_index_lists m (:2)`] SUM_POS_BOUND) THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE; REAL_LE_REFL] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; NORM_POS_LE];
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM; DIMINDEX_2]];
    MP_TAC(ISPECL [`\i. sum (pde_index_lists m (:2))
                          (\l. r pow (LENGTH l + 1) *
                               norm(iterated_partial l (partial_derivative i (u:real^2->real^K)) z))`;
                   `sum(1..2) (\i. sum (pde_index_lists m (:2))
                          (\l. r pow (LENGTH l + 1) *
                               norm(iterated_partial l (partial_derivative i (u:real^2->real^K)) z)))`;
                   `1..2`] SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; IN_NUMSEG] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; NORM_POS_LE];
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]]]);;

(* Splitting off the top order. *)

let HMR_DJ_SPLIT = prove
 (`!n r (u:real^2->real^K) z T0.
     &0 <= r /\ &0 <= T0 /\
     (!i l. 1 <= i /\ i <= 2 /\ LENGTH l = n + 1 /\ ALL (\j. 1 <= j /\ j <= 2) l
            ==> r pow (n + 2) * norm(iterated_partial l (partial_derivative i u) z) <= T0)
     ==> hmr_dj (n + 1) r u z <=
         hmr_dj n r u z + &2 * &(CARD(pde_index_lists (n + 1) (:2))) * T0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_dj] THEN
  SUBGOAL_THEN `&2 * &(CARD(pde_index_lists (n + 1) (:2))) * T0 =
                sum(1..2) (\i. &(CARD(pde_index_lists (n + 1) (:2))) * T0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_CONST_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `pde_index_lists n (:2) =
    {l | l IN pde_index_lists (n + 1) (:2) /\ LENGTH(l:num list) <= n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; pde_index_lists; IN_ELIM_THM] THEN X_GEN_TAC `l:num list` THEN
    MP_TAC(ARITH_RULE `LENGTH(l:num list) <= n ==> LENGTH l <= n + 1`) THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists (n + 1) (:2))
        (\l. (if LENGTH l <= n
              then r pow (LENGTH l + 1) *
                   norm(iterated_partial l (partial_derivative i (u:real^2->real^K)) z)
              else &0) + T0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM; DIMINDEX_2] THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH(l:num list) = n + 1` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`; REAL_ADD_LID] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SIMP_TAC[SUM_ADD; PDE_INDEX_LISTS_FINITE; SUM_CONST; REAL_LE_REFL]]);;

(* Continuity of the weighted jet along the ball. *)

let HMR_DJ_CONT = prove
 (`!s (u:real^2->real^K) m x0 R.
     open s /\ smooth_map_on s u
     ==> (\y. lift(hmr_dj m (R - norm(y - x0)) u y)) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_dj; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF; HMR_WEIGHT_CONT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

(* Components and partial derivatives. *)

let HMR_D_COMPONENT = prove
 (`!s (g:real^2->real^K) j k z.
     open s /\ smooth_map_on s g /\ z IN s /\ 1 <= k /\ k <= dimindex(:K)
     ==> cml_d j (\x. g x$k) z = (partial_derivative j g z)$k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d; partial_derivative] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CML_FRECHET_COMPONENT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
  ASM_REWRITE_TAC[]);;

let HMR_LAP_COMPONENT = prove
 (`!s (g:real^2->real^K) k z.
     open s /\ smooth_map_on s g /\ z IN s /\ 1 <= k /\ k <= dimindex(:K)
     ==> cml_lap (\x. g x$k) z = (hmr_vlap g z)$k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. cml_d j (cml_d j (\x. (g:real^2->real^K) x$k)) z =
        (partial_derivative j (partial_derivative j g) z)$k`
  (fun th -> REWRITE_TAC[th; cml_lap; hmr_vlap; VSUM_2; VECTOR_ADD_COMPONENT]) THEN
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `cml_d j (\x. (partial_derivative j (g:real^2->real^K) x)$k) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HMR_D_COMPONENT THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HMR_D_COMPONENT THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]]);;

(* The Laplacian commutes with iterated partials. *)

let HMR_VLAP_ITP = prove
 (`!s (u:real^2->real^K) l y.
     open s /\ smooth_map_on s u /\ ALL (\j. 1 <= j /\ j <= 2) l /\ y IN s
     ==> hmr_vlap (iterated_partial l u) y = iterated_partial l (hmr_vlap u) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hmr_vlap (u:real^2->real^K) =
                (\x. vsum(1..2) (\j. partial_derivative j (partial_derivative j u) x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; hmr_vlap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`; `s:real^2->bool`;
                 `\j. partial_derivative j (partial_derivative j (u:real^2->real^K))`; `1..2`]
    PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[hmr_vlap] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative j (iterated_partial l (partial_derivative j (u:real^2->real^K))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `j:num`]
      TEXT_PARTIAL_COMMUTE_ITERATED) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:real^2->bool`; `partial_derivative j (u:real^2->real^K)`; `j:num`]
      TEXT_PARTIAL_COMMUTE_ITERATED) THEN
    ASM_SIMP_TAC[DIMINDEX_2; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]]);;

(* The Laplacian of a component of a derivative of the first derivatives. *)

let HMR_LAP_TERM = prove
 (`!s (u:real^2->real^K) l i k y.
     open s /\ smooth_map_on s u /\ ALL (\j. 1 <= j /\ j <= 2) l /\ 1 <= i /\ i <= 2 /\
     1 <= k /\ k <= dimindex(:K) /\ y IN s
     ==> cml_lap (\x. iterated_partial l (partial_derivative i u) x$k) y =
         (iterated_partial (APPEND l [i]) (hmr_vlap u) y)$k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `iterated_partial l (partial_derivative i (u:real^2->real^K)) =
                iterated_partial (APPEND l [i]) u` SUBST1_TAC THENL
   [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `iterated_partial (APPEND l [i]) (u:real^2->real^K)`;
                 `k:num`; `y:real^2`] HMR_LAP_COMPONENT) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC HMR_VLAP_ITP THEN
  EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[ALL_APPEND; ALL]);;

(* ========================================================================= *)
(* The bound of one top-order term.  A derivative of order n + 2 of u at y   *)
(* is a first partial of a component w of a derivative of order n + 1; on    *)
(* ball(y, th r) the Laplacian of w is a component of a derivative of hmr_fq *)
(* (HMR_LAP_TERM, the PDE), bounded by the scaled jet bound, and w itself by *)
(* the weighted jet of order n; the log-potential estimate then bounds       *)
(* r^(n+2) |D^l d_i u (y)| by K1 (th Q + A / th).                            *)
(* ========================================================================= *)

let HMR_TOP_ALG = prove
 (`!r th CL C Q A X n.
     &0 < r /\ &0 < th /\ &0 <= CL /\
     (th * r) * abs X <=
     CL * (((C * Q) / r pow ((n + 1) + 2)) * (th * r) pow 2 + A / r pow (n + 1))
     ==> r pow (n + 2) * abs X <= CL * (C * th * Q + A / th)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r pow n` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `r pow (n + 2) * abs X = (r pow (n + 1) / th) * ((th * r) * abs X)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD] THEN UNDISCH_TAC `&0 < th` THEN UNDISCH_TAC `&0 < r` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CL * (C * th * Q + A / th) =
    (r pow (n + 1) / th) *
    (CL * (((C * Q) / r pow ((n + 1) + 2)) * (th * r) pow 2 + A / r pow (n + 1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD] THEN UNDISCH_TAC `&0 < r pow n` THEN
    UNDISCH_TAC `&0 < th` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LT]);;

let HMR_TOP_TERM = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !n A0. &0 <= A0
                ==> ?K1. &0 <= K1 /\
                         !s (u:real^2->real^K) y r th Q A.
                            open s /\ smooth_map_on s u /\ (!x. x IN s ==> u x IN S) /\
                            (!x. x IN s ==> hmr_vlap u x = hmr_fq S G u x) /\
                            &0 < r /\ &0 < th /\ cball(y,th * r) SUBSET s /\
                            &0 <= A /\ A <= A0 /\
                            (!x. x IN ball(y,th * r)
                                 ==> hmr_dj n r u x <= A /\ hmr_dj (n + 1) r u x <= Q)
                            ==> !i l. 1 <= i /\ i <= 2 /\ LENGTH l = n + 1 /\
                                      ALL (\j. 1 <= j /\ j <= 2) l
                                      ==> r pow (n + 2) *
                                          norm(iterated_partial l (partial_derivative i u) y)
                                          <= K1 * (th * Q + A / th)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n + 1`; `A0:real`] o MATCH_MP HMR_FQ_JET_SCALED) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= n + 1 /\ (n + 1) - 1 = n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fj"))) THEN
  X_CHOOSE_THEN `CL:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lp")) HMR_LOGPOT_SMOOTH THEN
  EXISTS_TAC `&(dimindex(:K)) * CL * (Cf + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `y:real^2`; `r:real`;
                       `th:real`; `Q:real`; `A:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `l:num list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(y:real^2,th * r) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y:real^2,th * r)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^2) IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hmr_dj (n + 1) r (u:real^2->real^K) y` THEN
    ASM_SIMP_TAC[HMR_DJ_POS; REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "hmr_dj")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_LT_MUL];
    ALL_TAC] THEN
  (* the list splits as CONS j l' *)
  SUBGOAL_THEN `?j l'. l = CONS j (l':num list)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `l:num list` list_CASES) THEN STRIP_TAC THENL
     [UNDISCH_TAC `LENGTH(l:num list) = n + 1` THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `LENGTH(l:num list) = n + 1` THEN
  UNDISCH_TAC `ALL (\j. 1 <= j /\ j <= 2) (l:num list)` THEN
  ASM_REWRITE_TAC[LENGTH; ALL; ARITH_RULE `SUC m = n + 1 <=> m = n`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[iterated_partial] THEN
  ABBREV_TAC `g = iterated_partial l' (partial_derivative i (u:real^2->real^K))` THEN
  SUBGOAL_THEN `smooth_map_on s (g:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL;
                                     SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  (* componentwise *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:K))
                (\k. r pow (n + 2) * abs(cml_d j (\x. (g:real^2->real^K) x$k) y))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:K)) (\k. abs((partial_derivative j (g:real^2->real^K) y)$k))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC HMR_D_COMPONENT THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&(dimindex(:K)) * CL * (Cf + &1)) * (th * Q + A / th) =
                sum(1..dimindex(:K)) (\k. CL * (Cf + &1) * (th * Q + A / th))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - 1 = n`; REAL_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  (* the log-potential estimate for the component *)
  USE_THEN "lp" (MP_TAC o SPECL [`s:real^2->bool`; `\x. (g:real^2->real^K) x$k`; `y:real^2`;
                                 `th * r`; `(Cf * Q) / r pow ((n + 1) + 2)`;
                                 `A / r pow (n + 1)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; SMOOTH_MAP_ON_LIFT_COMPONENT] THEN CONJ_TAC THENL
     [(* the Laplacian *)
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "hmr_dj")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      EXPAND_TAC "g" THEN
      MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `l':num list`; `i:num`; `k:num`;
                     `x:real^2`] HMR_LAP_TERM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `iterated_partial (APPEND l' [i]) (hmr_vlap (u:real^2->real^K)) x =
                    iterated_partial (APPEND l' [i]) (hmr_fq S G u) x`
      SUBST1_TAC THENL
       [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `s:real^2->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(iterated_partial (APPEND l' [i]) (hmr_fq S G (u:real^2->real^K)) x)` THEN
      REWRITE_TAC[COMPONENT_LE_NORM] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Cf * hmr_dj (n + 1) r (u:real^2->real^K) x` THEN CONJ_TAC THENL
       [ALL_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum (pde_index_lists (n + 1) (:2))
                    (\l. r pow (LENGTH l + 2) *
                         norm(iterated_partial l (hmr_fq S G (u:real^2->real^K)) x))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        USE_THEN "fj" MATCH_MP_TAC THEN EXISTS_TAC `s:real^2->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A:real` THEN
        ASM_REWRITE_TAC[]] THEN
      MP_TAC(ISPECL [`\l. r pow (LENGTH l + 2) *
                          norm(iterated_partial l (hmr_fq S G (u:real^2->real^K)) x)`;
                     `sum (pde_index_lists (n + 1) (:2))
                        (\l. r pow (LENGTH l + 2) *
                             norm(iterated_partial l (hmr_fq S G (u:real^2->real^K)) x))`;
                     `pde_index_lists (n + 1) (:2)`] SUM_POS_BOUND) THEN
      REWRITE_TAC[PDE_INDEX_LISTS_FINITE; REAL_LE_REFL] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; NORM_POS_LE;
                                           REAL_LT_IMP_LE];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `APPEND l' [i:num]`) THEN
      ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM; DIMINDEX_2; LENGTH_APPEND; LENGTH;
                      ALL_APPEND; ALL] THEN
      REWRITE_TAC[ARITH_RULE `n + SUC 0 <= n + 1 /\ (n + SUC 0) + 2 = (n + 1) + 2`] THEN
      REAL_ARITH_TAC;
      (* the function *)
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "hmr_dj")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      EXPAND_TAC "g" THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(iterated_partial l' (partial_derivative i (u:real^2->real^K)) x)` THEN
      REWRITE_TAC[COMPONENT_LE_NORM] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hmr_dj n r (u:real^2->real^K) x` THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MP_TAC(ISPECL [`n:num`; `r:real`; `u:real^2->real^K`; `x:real^2`; `i:num`;
                     `l':num list`] HMR_DJ_TERM) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; LE_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:real`; `th:real`; `CL:real`; `Cf:real`; `Q:real`; `A:real`;
                 `cml_d j (\x. (g:real^2->real^K) x$k) y`; `n:num`] HMR_TOP_ALG) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `&0 <= Cf * (A / th) /\ &0 <= th * Q` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The weighted maximum argument for one order.  On B = ball(x0,R) with      *)
(* delta(y) = R - |y - x0|, a bound A on hmr_dj n delta u gives the bound    *)
(* K2 A on hmr_dj (n + 1) delta u: at a maximum point y0 of                  *)
(* hmr_dj (n + 1) delta u on the closed ball the top terms are bounded by    *)
(* HMR_TOP_TERM at scale r = delta(y0)/2 with a small ratio th, and the top  *)
(* part is absorbed.                                                         *)
(* ========================================================================= *)

let HMR_DJ_ZERO = prove
 (`!m (u:real^2->real^K) z. hmr_dj m (&0) u z = &0`,
  REWRITE_TAC[hmr_dj; REAL_POW_ZERO; ADD_EQ_0; ARITH_EQ; REAL_MUL_LZERO; SUM_0]);;

let HMR_ABSORB_ALG = prove
 (`!Q A c th.
     &0 <= Q /\ &0 <= A /\ &0 <= c /\ &0 < th /\ c * th <= &1 / &2 /\
     Q <= A + c * (th * Q + A / th)
     ==> Q <= &2 * (&1 + c / th) * A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c * th) * Q <= (&1 / &2) * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `Q <= A + c * (th * Q + A / th)` THEN UNDISCH_TAC `(c * th) * Q <= (&1 / &2) * Q` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let HMR_ABSORB = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> !n A0. &0 <= A0
                ==> ?K2. &0 <= K2 /\
                         !s (u:real^2->real^K) x0 R A.
                            open s /\ smooth_map_on s u /\ (!x. x IN s ==> u x IN S) /\
                            (!x. x IN s ==> hmr_vlap u x = hmr_fq S G u x) /\
                            &0 < R /\ cball(x0,R) SUBSET s /\ &0 <= A /\ A <= A0 /\
                            (!y. y IN ball(x0,R) ==> hmr_dj n (R - norm(y - x0)) u y <= A)
                            ==> !y. y IN ball(x0,R)
                                    ==> hmr_dj (n + 1) (R - norm(y - x0)) u y <= K2 * A`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `A0:real`] o MATCH_MP HMR_TOP_TERM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "top"))) THEN
  ABBREV_TAC `c = (&2 * &(CARD(pde_index_lists (n + 1) (:2)))) * &2 pow (n + 2) * K1` THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE] THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `th = inv(&2 * c + &2)` THEN
  SUBGOAL_THEN `&0 < th /\ th <= &1 /\ c * th <= &1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN
    SUBGOAL_THEN `&0 < &2 * c + &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LT_INV_EQ; ASSUME `&0 < &2 * c + &2`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; ASSUME `&0 < &2 * c + &2`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + c / th` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `&2 * (&1 + c / th)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`; `x0:real^2`; `R:real`; `A:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ball(x0:real^2,R) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^2,R)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  (* the maximum point *)
  MP_TAC(ISPECL [`\y:real^2. hmr_dj (n + 1) (R - norm(y - x0)) (u:real^2->real^K) y`;
                 `cball(x0:real^2,R)`] CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL; CBALL_EQ_EMPTY; o_DEF] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[HMR_DJ_CONT];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^2` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `Q = hmr_dj (n + 1) (R - norm(y0 - x0)) (u:real^2->real^K) y0` THEN
  SUBGOAL_THEN `Q <= &2 * (&1 + c / th) * A`
  (fun th -> X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
             MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q:real` THEN
             REWRITE_TAC[th; GSYM REAL_MUL_ASSOC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
             ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]) THEN
  SUBGOAL_THEN `norm(y0 - x0:real^2) <= R` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^2) IN cball(x0,R)` THEN REWRITE_TAC[IN_CBALL; dist] THEN
    MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(y0 - x0:real^2) = R` THENL
   [SUBGOAL_THEN `Q = &0` SUBST1_TAC THENL
     [EXPAND_TAC "Q" THEN
      REWRITE_TAC[ASSUME `norm(y0 - x0:real^2) = R`; REAL_SUB_REFL; HMR_DJ_ZERO];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `dl = R - norm(y0 - x0:real^2)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^2) IN ball(x0,R)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = dl / &2` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC HMR_DJ_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* points near y0 are well inside *)
  SUBGOAL_THEN `!x:real^2. x IN ball(y0,th * r) ==> x IN ball(x0,R) /\ r <= R - norm(x - x0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_BALL; dist] THEN DISCH_TAC THEN
    SUBGOAL_THEN `th * r <= r` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`x - x0:real^2`; `y0 - x0:real^2`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`x0:real^2`; `x:real^2`] NORM_SUB) THEN
    MP_TAC(ISPECL [`y0:real^2`; `x:real^2`] NORM_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH `(x - x0) - (y0 - x0):real^2 = x - y0`] THEN
    UNDISCH_TAC `R - norm(y0 - x0:real^2) = dl` THEN UNDISCH_TAC `dl / &2 = r` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(y0:real^2,th * r) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^2,R)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL; dist] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `th * r <= r` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`x0 - x:real^2`; `x0 - y0:real^2`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`x0:real^2`; `y0:real^2`] NORM_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH `(x0 - x) - (x0 - y0):real^2 = y0 - x`] THEN
    UNDISCH_TAC `R - norm(y0 - x0:real^2) = dl` THEN UNDISCH_TAC `dl / &2 = r` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the top-order bound at y0 *)
  USE_THEN "top" (MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`; `y0:real^2`; `r:real`;
                                  `th:real`; `Q:real`; `A:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
      can (find_term (fun t -> t = `ball(y0:real^2,th * r)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `hmr_dj n (R - norm(x - x0)) (u:real^2->real^K) x` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC HMR_DJ_MONO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `hmr_dj (n + 1) (R - norm(x - x0)) (u:real^2->real^K) x` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HMR_DJ_MONO THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]]];
    DISCH_TAC] THEN
  (* splitting at y0 with weight dl *)
  MP_TAC(ISPECL [`n:num`; `dl:real`; `u:real^2->real^K`; `y0:real^2`;
                 `&2 pow (n + 2) * K1 * (th * Q + A / th)`] HMR_DJ_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `l:num list`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `dl = &2 * r` SUBST1_TAC THENL [EXPAND_TAC "r" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `l:num list`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hmr_dj n dl (u:real^2->real^K) y0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hmr_dj (n + 1) dl (u:real^2->real^K) y0 = Q` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HMR_ABSORB_ALG THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `Q <= hmr_dj n dl (u:real^2->real^K) y0 +
                    &2 * &(CARD (pde_index_lists (n + 1) (:2))) *
                    &2 pow (n + 2) * K1 * (th * Q + A / th)` THEN
  UNDISCH_TAC `hmr_dj n dl (u:real^2->real^K) y0 <= A` THEN
  EXPAND_TAC "c" THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC);;

