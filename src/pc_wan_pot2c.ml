(* ========================================================================= *)
(* pc_wan_pot2c: first-order regularity from jets, and the statement         *)
(* WAN_LOGPOT_C1A_QUANT:                                                     *)
(*   - first-order jets give differentiability and a Hoelder gradient;       *)
(*   - mollified first-order jets, the limit, WAN_LOGPOT_C1A_QUANT.          *)
(* ========================================================================= *)

needs "src/pc_wan_pot2b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* First-order jets.                                                         *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_JET_DERIV1 = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:complex) K rho0 sg x0.
     open s /\ x0 IN s /\ &0 < rho0 /\ &0 <= K /\ &1 < sg /\
     (!x. x IN s /\ norm(x - x0) <= rho0
          ==> abs(w x - w x0 - Re(a1 * (x - x0))) <= K * norm(x - x0) rpow sg)
     ==> ((\x. lift(w x)) has_derivative (\h. lift(Re(a1 * h)))) (at x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_derivative_at] THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; COMPLEX_ADD_LDISTRIB; RE_ADD; LIFT_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[COMPLEX_RING `a * Cx c * x = Cx c * (a * x)`; RE_MUL_CX; LIFT_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_AT; DIST_0] THEN X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x0:real^2` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `eta = ep / (K + &1)` THEN
  SUBGOAL_THEN `&0 < eta /\ K * eta < ep` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `K * ep / (K + &1) = (K * ep) / (K + &1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= K ==> &0 < K + &1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (min d1 rho0) (eta rpow inv(sg - &1))` THEN
  SUBGOAL_THEN `&0 < eta rpow inv(sg - &1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN REWRITE_TAC[REAL_LT_MIN; dist] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^2) IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
    can (find_term (fun t -> t = `rpow`)) (concl th))) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  REWRITE_TAC[NORM_MUL; NORM_LIFT; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ABBREV_TAC `dy = norm(y - x0:real^2)` THEN
  SUBGOAL_THEN `dy rpow sg = dy * dy rpow (sg - &1)` SUBST_ALL_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `sg = &1 + (sg - &1)`] THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `dy rpow (sg - &1) < eta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(eta rpow inv(sg - &1)) rpow (sg - &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LT2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `inv(sg - &1) * (sg - &1) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_SUB; NORM_LIFT] THEN
  SUBGOAL_THEN
   `abs((w:real^2->real) y - (w x0 + Re(a1 * (y - x0)))) <= K * dy * dy rpow (sg - &1)`
  MP_TAC THENL [UNDISCH_TAC `abs((w:real^2->real) y - w x0 - Re(a1 * (y - x0))) <=
                             K * dy * dy rpow (sg - &1)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `E = abs((w:real^2->real) y - (w x0 + Re(a1 * (y - x0))))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `E <= dy * (K * eta)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * dy * dy rpow (sg - &1)` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `K * d * r = d * (K * r)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dy` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dy * (K * eta)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dy * (K * eta) < dy * ep` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let WANL_PT_JET_HOLDER1 = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:real^2->complex) K rho0 sg x0 x1.
     (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
             ==> abs(w x - w x0 - Re(a1 x0 * (x - x0))) <= K * norm(x - x0) rpow sg) /\
     x0 IN s /\ x1 IN s /\ &0 <= K /\ &1 < sg /\ &2 * norm(x1 - x0) <= rho0 /\
     (!e. norm e = &1 ==> x1 + norm(x1 - x0) % e IN s /\ x1 - norm(x1 - x0) % e IN s)
     ==> norm(a1 x0 - a1 x1) <= &2 * K * (&2 rpow sg + &1) * norm(x1 - x0) rpow (sg - &1)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `d = norm(x1 - x0:real^2)` THEN
  ASM_CASES_TAC `d = &0` THENL
   [UNDISCH_TAC `norm(x1 - x0:real^2) = d` THEN ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_POS; REAL_LE_REFL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
    MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[NORM_POS_LT] THEN
    UNDISCH_TAC `~(d = &0)` THEN EXPAND_TAC "d" THEN REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  ABBREV_TAC `R = d rpow (sg - &1)` THEN ABBREV_TAC `S2 = &2 rpow sg` THEN
  SUBGOAL_THEN `d rpow sg = d * R /\ (&2 * d) rpow sg = S2 * (d * R)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "R" THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `sg = &1 + (sg - &1)`] THEN
      ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
      DISCH_TAC THEN EXPAND_TAC "S2" THEN ASM_REWRITE_TAC[RPOW_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= R /\ &0 <= S2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["R"; "S2"] THEN CONJ_TAC THEN MATCH_MP_TAC RPOW_POS_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. norm(e:complex) = &1
        ==> abs(Re(((a1:real^2->complex) x0 - a1 x1) * e)) <= K * (S2 + &1) * R`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:complex` o check (fun th ->
      can (find_term (fun t -> t = `(%):real->real^2->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(d % e:real^2) = d` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `norm((x1 + d % e) - x0:real^2) <= &2 * d /\ norm((x1 - d % e) - x0:real^2) <= &2 * d`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(x1 + d % e) - x0:real^N = (x1 - x0) + d % e`;
                  VECTOR_ARITH `(x1 - d % e) - x0:real^N = (x1 - x0) + --(d % e)`] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `norm(x1 - x0:real^2) + norm(d % e:real^2)`;
        EXISTS_TAC `norm(x1 - x0:real^2) + norm(--(d % e):real^2)`] THEN
      REWRITE_TAC[NORM_TRIANGLE; NORM_NEG] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ norm(x - x0:real^2) <= &2 * d
          ==> abs((w:real^2->real) x - w x0 - Re((a1:real^2->complex) x0 * (x - x0)))
              <= K * (S2 * (d * R))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `K * norm(x - x0:real^2) rpow sg` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          can (find_term (fun t -> t = `S2:real`)) (concl th) && is_eq(concl th))) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC RPOW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ norm(x - x1:real^2) = d
          ==> abs((w:real^2->real) x - w x1 - Re((a1:real^2->complex) x1 * (x - x1)))
              <= K * (d * R)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x1:real^2`; `x:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `rho0:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(SPEC `x1 + d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x0:real^2) <= &2 * d
                  ==> abs((w:real^2->real) x - w x0 - Re((a1:real^2->complex) x0 * (x - x0)))
                      <= K * (S2 * (d * R))`)) THEN
    MP_TAC(SPEC `x1 - d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x0:real^2) <= &2 * d
                  ==> abs((w:real^2->real) x - w x0 - Re((a1:real^2->complex) x0 * (x - x0)))
                      <= K * (S2 * (d * R))`)) THEN
    MP_TAC(SPEC `x1 + d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x1:real^2) = d
                  ==> abs((w:real^2->real) x - w x1 - Re((a1:real^2->complex) x1 * (x - x1)))
                      <= K * (d * R)`)) THEN
    MP_TAC(SPEC `x1 - d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x1:real^2) = d
                  ==> abs((w:real^2->real) x - w x1 - Re((a1:real^2->complex) x1 * (x - x1)))
                      <= K * (d * R)`)) THEN
    REPEAT(ANTS_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(x1 + d % e) - x1:real^N = d % e`;
                  VECTOR_ARITH `(x1 - d % e) - x1:real^N = --(d % e)`; NORM_NEG] THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_ARITH `(x1 + d % e) - x1:real^N = d % e`;
                VECTOR_ARITH `(x1 - d % e) - x1:real^N = --(d % e)`;
                VECTOR_ARITH `(x1 + d % e) - x0:real^N = (x1 - x0) + d % e`;
                VECTOR_ARITH `(x1 - d % e) - x0:real^N = (x1 - x0) - d % e`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_ADD_LDISTRIB; COMPLEX_SUB_LDISTRIB; COMPLEX_MUL_RNEG;
                RE_ADD; RE_SUB; RE_NEG; COMPLEX_CMUL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_RING `a * Cx d * e = Cx d * (a * e)`; RE_MUL_CX]) THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB; RE_SUB] THEN
    ABBREV_TAC `P0 = Re((a1:real^2->complex) x0 * e)` THEN
    ABBREV_TAC `P1 = Re((a1:real^2->complex) x1 * e)` THEN
    ABBREV_TAC `Q0 = Re((a1:real^2->complex) x0 * (x1 - x0))` THEN
    SUBGOAL_THEN `abs(d * P0 - d * P1) <= d * (K * (S2 + &1) * R)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LE_LMUL_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(Re((a1:real^2->complex) x0 - a1 x1)) + abs(Im(a1 x0 - a1 x1))` THEN
  REWRITE_TAC[COMPLEX_NORM_LE_RE_IM] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `Cx(&1)` th) THEN MP_TAC(SPEC `ii` th)) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_II; REAL_ABS_NUM; COMPLEX_MUL_RID; RE_MUL_II;
              REAL_ABS_NEG] THEN
  REAL_ARITH_TAC);;

let WANL_PT_GRAD_CNJ = prove
 (`!(w:real^2->real) c x.
     ((\y. lift(w y)) has_derivative (\h. lift(Re(c * h)))) (at x)
     ==> wan_grad w x = cnj c`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_SIMP_TAC[wan_grad; wan_dpart; CART_EQ; LAMBDA_BETA; DIMINDEX_2; FORALL_2] THEN
  REWRITE_TAC[LIFT_DROP; COMPLEX_BASIS; COMPLEX_MUL_RID; RE_MUL_II] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_CNJ; IM_CNJ]);;

let WANL_PT_HOLDER_CONT = prove
 (`!(s:real^2->bool) (g:real^2->complex) H al.
     &0 < al /\
     (!x. x IN s ==> ?d. &0 < d /\
                         !y. y IN s /\ norm(y - x) < d ==> norm(g y - g x) <= H * norm(y - x) rpow al)
     ==> g continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_on] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `eta = ep / (abs H + &1)` THEN
  SUBGOAL_THEN `&0 < eta /\ abs H * eta < ep` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs H * ep / (abs H + &1) = (abs H * ep) / (abs H + &1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < abs H + &1`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min d (eta rpow inv al)` THEN
  SUBGOAL_THEN `&0 < eta rpow inv al` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  UNDISCH_TAC `dist(y:real^2,x) < d` THEN UNDISCH_TAC `dist(y:real^2,x) < eta rpow inv al` THEN
  REWRITE_TAC[dist] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(y - x:real^2) rpow al < eta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(eta rpow inv al) rpow al` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs H * norm(y - x:real^2) rpow al` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_ABS_LE; REAL_LE_RMUL; RPOW_POS_LE; NORM_POS_LE;
                                REAL_LE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs H * eta` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* WAN_LOGPOT_C1A_QUANT: mollify, expand to first order (N = 1), pass to    *)
(* the limit, read off the C^(1,al) bounds.                                 *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_LOG_CONST = prove
 (`!al r U M.
     &0 < al /\ al < &1 /\ &0 < r /\ &0 <= U /\ &0 <= M
     ==> (U / (r / &8) rpow (&1 + al) + M * (r / &8) rpow (&1 - al)) * r rpow (&1 + al)
         <= &64 * (U + M * r pow 2) /\
         (U / (r / &8) rpow (&1 + al) + M * (r / &8) rpow (&1 - al)) * (r / &8) rpow al * r
         <= &64 * (U + M * r pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r rpow (&1 + al) /\ &0 < r rpow (&1 - al) /\ &0 < r rpow al /\
                &0 < &8 rpow (&1 + al) /\ &1 <= &8 rpow (&1 - al) /\ &8 rpow (&1 + al) <= &64 /\
                &1 <= &8 rpow al`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT; REAL_ARITH `&0 < &8`] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LE_1 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&8 rpow &2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[RPOW_POW] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC RPOW_LE_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r rpow (&1 + al) * r rpow (&1 - al) = r pow 2 /\
                r rpow al * r = r rpow (&1 + al)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(&1 + al) + (&1 - al) = &2`; RPOW_POW];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_POW_1] THEN
      ASM_SIMP_TAC[GSYM RPOW_POW; GSYM RPOW_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[RPOW_DIV] THEN
  ABBREV_TAC `A1 = r rpow (&1 + al)` THEN ABBREV_TAC `A2 = r rpow (&1 - al)` THEN
  ABBREV_TAC `A3 = r rpow al` THEN ABBREV_TAC `E1 = &8 rpow (&1 + al)` THEN
  ABBREV_TAC `E2 = &8 rpow (&1 - al)` THEN ABBREV_TAC `E3 = &8 rpow al` THEN
  SUBGOAL_THEN `~(A1 = &0) /\ ~(E1 = &0) /\ ~(E2 = &0) /\ ~(E3 = &0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(U / (A1 / E1) + M * A2 / E2) * A1 = U * E1 + (M * r pow 2) * inv E2`
  SUBST1_TAC THENL
   [UNDISCH_TAC `A1 * A2 = r pow 2` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`~(A1 = &0)`; `~(E1 = &0)`; `~(E2 = &0)`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(U / (A1 / E1) + M * A2 / E2) * A3 / E3 * r = (U * E1 + (M * r pow 2) * inv E2) * inv E3`
  SUBST1_TAC THENL
   [UNDISCH_TAC `A3 * r = A1` THEN UNDISCH_TAC `A1 * A2 = r pow 2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC [`~(A1 = &0)`; `~(E1 = &0)`; `~(E2 = &0)`; `~(E3 = &0)`;
                           `A3 * r = A1`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv E2 <= &1 /\ inv E3 <= &1 /\ &0 <= inv E2 /\ &0 <= inv E3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_LE_1) THEN
    TRY(MATCH_MP_TAC REAL_LE_INV) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M * r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `U * E1 + (M * r pow 2) * inv E2 <= &64 * (U + M * r pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `U * E1 <= U * &64 /\ (M * r pow 2) * inv E2 <= (M * r pow 2) * &1`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(U * E1 + (M * r pow 2) * inv E2) * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_MUL_RID]]);;

let WANL_PT_RHO_FACTOR = prove
 (`!rho rho0 al. &0 < rho /\ rho <= rho0 /\ al < &1
                 ==> &1 <= rho0 rpow (&1 - al) * rho rpow (&1 + al - &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 + al - &2 = --(&1 - al)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[RPOW_NEG; GSYM real_div] THEN
  SUBGOAL_THEN `&0 < rho rpow (&1 - al)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
  MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC);;

let WANL_PT_LOG_JETS = prove
 (`!al. &0 < al /\ al < &1
        ==> ?C1. &0 < C1 /\
             !(a:real^2) r (u:real^2->real) (f:real^2->real) U M e x0.
                &0 < r /\ &0 < e /\ e < r / &8 /\ &0 <= U /\ &0 <= M /\
                (\x. lift(u x)) measurable_on ball(a,r) /\
                (\x. lift(f x)) measurable_on ball(a,r) /\
                (!x. x IN ball(a,r) ==> abs(u x) <= U) /\
                (!x. x IN ball(a,r) ==> abs(f x) <= M) /\
                (!phi. wan_test (ball(a,r)) phi
                       ==> integral (ball(a,r)) (\x. lift(u x * llap (\y:real^2. mat 1) phi x)) =
                           integral (ball(a,r)) (\x. lift(f x * phi x))) /\
                x0 IN ball(a,&3 / &4 * r)
                ==> ?c. norm c <= C1 * (U + M * r pow 2) / r /\
                        !x. norm(x - x0) <= r / &8
                            ==> abs(wanl_pt_me e (ball(a,r)) u x -
                                    wanl_pt_me e (ball(a,r)) u x0 - Re(c * (x - x0)))
                                <= (C1 * (U + M * r pow 2) / r rpow (&1 + al)) *
                                   norm(x - x0) rpow (&1 + al)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `al:real`] WANL_PT_EXPAND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ex"))) THEN
  EXISTS_TAC `&64 * C0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lebesgue_measurable(ball(a:real^2,r))` ASSUME_TAC THENL
   [REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]; ALL_TAC] THEN
  ABBREV_TAC `v = wanl_pt_me e (ball(a:real^2,r)) u` THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\x. lift((v:real^2->real) x))` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC WANL_PT_ME_SMOOTH THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. abs((v:real^2->real) x) <= U` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "v" THEN MATCH_MP_TAC WANL_PT_ME_BOUND THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(a:real^2,&7 / &8 * r)
        ==> abs(llap (\y:real^2. mat 1) (v:real^2->real) x) <= M`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "v" THEN
    MP_TAC(ISPECL [`e:real`; `ball(a:real^2,r)`; `u:real^2->real`; `f:real^2->real`;
                   `U:real`; `M:real`; `x:real^2`] WANL_PT_ME_LAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_BALL] THEN
      UNDISCH_TAC `(x:real^2) IN ball(a,&7 / &8 * r)` THEN
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN DISCH_TAC THEN X_GEN_TAC `y:real^2` THEN
      MP_TAC(ISPECL [`a:real^2`; `x:real^2`; `y:real^2`] DIST_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC WANL_PT_ME_BOUND THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `rho0 = r / &8` THEN
  SUBGOAL_THEN `&0 < rho0` ASSUME_TAC THENL [EXPAND_TAC "rho0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ex" (MP_TAC o SPECL [`ball(a:real^2,&7 / &8 * r)`; `v:real^2->real`; `&0`;
                                 `x0:real^2`; `rho0:real`; `M * rho0 rpow (&1 - al)`; `U:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; REAL_SUB_RZERO; real_div; REAL_MUL_LZERO] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(x0:real^2) IN ball(a,&3 / &4 * r)` THEN
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN DISCH_TAC THEN X_GEN_TAC `y:real^2` THEN
      MP_TAC(ISPECL [`a:real^2`; `x0:real^2`; `y:real^2`] DIST_TRIANGLE) THEN
      EXPAND_TAC "rho0" THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE];
      MAP_EVERY X_GEN_TAC [`rho:real`; `x:real^2`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(x0:real^2) IN ball(a,&3 / &4 * r)` THEN
        UNDISCH_TAC `(x:real^2) IN ball(x0,rho)` THEN REWRITE_TAC[IN_BALL] THEN
        REPEAT DISCH_TAC THEN MP_TAC(ISPECL [`a:real^2`; `x0:real^2`; `x:real^2`] DIST_TRIANGLE) THEN
        EXPAND_TAC "rho0" THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WANL_PT_RHO_FACTOR THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cf:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(cf:num->complex) 1` THEN
  MP_TAC(SPECL [`al:real`; `r:real`; `U:real`; `M:real`] WANL_PT_LOG_CONST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S0 = U / rho0 rpow (&1 + al) + M * rho0 rpow (&1 - al)` THEN
  SUBGOAL_THEN `&0 <= S0` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r rpow (&1 + al)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th ->
      can (find_term (fun t -> t = `cf:num->complex`)) (concl th) && is_forall(concl th) &&
      not(can (find_term (fun t -> t = `wanl_pt_hp`)) (concl th)))) THEN
    REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    SUBGOAL_THEN `rho0 rpow (&1 + al - &1) = rho0 rpow al` SUBST1_TAC THENL
     [AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * ((&64 * (U + M * r pow 2)) / r)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_RDIV_EQ] THEN ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `x:real^2` th) THEN MP_TAC(SPEC `x0:real^2` th)) o
    check (fun th -> can (find_term (fun t -> t = `wanl_pt_hp`)) (concl th))) THEN
  REWRITE_TAC[IN_CBALL; DIST_REFL; VECTOR_SUB_REFL; NORM_0] THEN
  ASM_SIMP_TAC[RPOW_ZERO; REAL_ARITH `&0 < al ==> ~(&1 + al = &0)`; REAL_MUL_RZERO;
               REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wanl_pt_hp] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; ARITH; VSUM_TRIV_NUMSEG] THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_MUL_RID; VECTOR_SUB_REFL; RE_ADD] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO; RE_CX; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LZERO; real_div] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `S0 <= (&64 * (U + M * r pow 2)) / r rpow (&1 + al)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  ABBREV_TAC `D = norm(x - x0:real^2) rpow (&1 + al)` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `C0 * S0 * D <= ((&64 * C0) * (U + M * r pow 2) * inv(r rpow (&1 + al))) * D`
  MP_TAC THENL
   [SUBGOAL_THEN
     `((&64 * C0) * (U + M * r pow 2) * inv(r rpow (&1 + al))) * D =
      C0 * ((&64 * (U + M * r pow 2)) / r rpow (&1 + al)) * D`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let WANL_PT_LOG_LIMIT = prove
 (`!al. &0 < al /\ al < &1
        ==> ?C1. &0 < C1 /\
             !(a:real^2) r (u:real^2->real) (f:real^2->real) U M.
                &0 < r /\ &0 <= U /\ &0 <= M /\
                (\x. lift(u x)) measurable_on ball(a,r) /\
                (\x. lift(f x)) measurable_on ball(a,r) /\
                (!x. x IN ball(a,r) ==> abs(u x) <= U) /\
                (!x. x IN ball(a,r) ==> abs(f x) <= M) /\
                (!phi. wan_test (ball(a,r)) phi
                       ==> integral (ball(a,r)) (\x. lift(u x * llap (\y:real^2. mat 1) phi x)) =
                           integral (ball(a,r)) (\x. lift(f x * phi x)))
                ==> ?w a1 t.
                      negligible t /\
                      (!x. x IN ball(a,&3 / &4 * r) /\ ~(x IN t) ==> w x = u x) /\
                      (!x. x IN ball(a,&3 / &4 * r) ==> abs(w x) <= U) /\
                      (!x0. x0 IN ball(a,&3 / &4 * r)
                            ==> norm(a1 x0) <= C1 * (U + M * r pow 2) / r) /\
                      (!x0 x. x0 IN ball(a,&3 / &4 * r) /\ x IN ball(a,&3 / &4 * r) /\
                              norm(x - x0) <= r / &8
                              ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)))
                                  <= (C1 * (U + M * r pow 2) / r rpow (&1 + al)) *
                                     norm(x - x0) rpow (&1 + al))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `al:real` WANL_PT_LOG_JETS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "jets"))) THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `em = \m. r / (&8 * (&m + &2))` THEN
  SUBGOAL_THEN `!m. &0 < (em:num->real) m /\ em m < r / &8` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "em" THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = C1 * (U + M * r pow 2) / r rpow (&1 + al)` THEN
  ABBREV_TAC `Gc = C1 * (U + M * r pow 2) / r` THEN
  SUBGOAL_THEN
   `?c1:num->real^2->complex.
      !m x0. x0 IN ball(a,&3 / &4 * r)
             ==> norm(c1 m x0) <= Gc /\
                 !x. norm(x - x0) <= r / &8
                     ==> abs(wanl_pt_me (em m) (ball(a,r)) u x -
                             wanl_pt_me (em m) (ball(a,r)) u x0 - Re(c1 m x0 * (x - x0)))
                         <= Kc * norm(x - x0) rpow (&1 + al)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `x0:real^2` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["Gc"; "Kc"] THEN USE_THEN "jets" MATCH_MP_TAC THEN
    EXISTS_TAC `f:real^2->real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `u:real^2->real`; `U:real`] WANL_PT_ME_AE) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(a:real^2,&3 / &4 * r) SUBSET ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,&3 / &4 * r)`; `t:real^2->bool`;
                 `\m x. wanl_pt_me ((em:num->real) m) (ball(a:real^2,r)) u x`;
                 `u:real^2->real`; `c1:num->real^2->complex`; `Kc:real`; `Gc:real`;
                 `r / &8`; `&1 + al`] WANL_PT_JET1_LIMIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXPAND_TAC "Kc" THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
      EXPAND_TAC "Gc" THEN REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LE_ADD; REAL_LE_MUL; REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
      X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `ep:real`] o check (fun th ->
        can (find_term (fun t -> t = `t:real^2->bool`)) (concl th) && is_forall(concl th))) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `r / (&8 * d)` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "em" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &8 * (&n + &2)` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      UNDISCH_TAC `r / (&8 * d) <= &N` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &8`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `d * &N <= d * &n` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE];
        ASM_REAL_ARITH_TAC];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` (X_CHOOSE_THEN `a1:real^2->complex`
    (STRIP_ASSUME_TAC o BETA_RULE))) THEN
  MAP_EVERY EXISTS_TAC [`w:real^2->real`; `a1:real^2->complex`; `t:real^2->bool`] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM NORM_LIFT] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\m. lift(wanl_pt_me ((em:num->real) m) (ball(a:real^2,r)) u x)` THEN
  ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN GEN_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
  MATCH_MP_TAC WANL_PT_ME_BOUND THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]);;

let WAN_LOGPOT_C1A_QUANT = prove
 (`WAN_LOGPOT_C1A_QUANT_STATEMENT`,
  REWRITE_TAC[WAN_LOGPOT_C1A_QUANT_STATEMENT] THEN X_GEN_TAC `al:real` THEN STRIP_TAC THEN
  MP_TAC(SPEC `al:real` WANL_PT_LOG_LIMIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lim"))) THEN
  EXISTS_TAC `&32 * C1 + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real`; `f:real^2->real`;
                       `M:real`; `U:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= U /\ &0 <= M` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `abs((u:real^2->real) a)`; EXISTS_TAC `abs((f:real^2->real) a)`] THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((u:real^2->real) x)) measurable_on ball(a,r)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x:real^2. lift(u x)`] WAN_W12_IMP_LSPACE) THEN
    ASM_REWRITE_TAC[lspace; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `u:real^2->real`; `f:real^2->real`] WANL_PT_VERY_WEAK) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
  USE_THEN "lim" (MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real`; `f:real^2->real`;
                                  `U:real`; `M:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` (X_CHOOSE_THEN `a1:real^2->complex`
    (X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `K = C1 * (U + M * r pow 2) / r rpow (&1 + al)` THEN
  ABBREV_TAC `G = C1 * (U + M * r pow 2) / r` THEN
  ABBREV_TAC `s = ball(a:real^2,&3 / &4 * r)` THEN
  SUBGOAL_THEN `&0 <= K /\ &0 <= G` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "G"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; REAL_LE_ADD; REAL_LE_MUL; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,r / &2) SUBSET s /\ open(s:real^2->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* derivative and gradient *)
  SUBGOAL_THEN
   `!x0. x0 IN s
         ==> ((\x. lift((w:real^2->real) x)) has_derivative
              (\h. lift(Re((a1:real^2->complex) x0 * h)))) (at x0) /\
             wan_grad w x0 = cnj(a1 x0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC WANL_PT_JET_DERIV1 THEN
      MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `K:real`; `r / &8`; `&1 + al`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_ACCEPT_TAC WANL_PT_GRAD_CNJ];
    ALL_TAC] THEN
  (* local Hoelder bound for a1 *)
  SUBGOAL_THEN
   `!x y. x IN ball(a:real^2,r / &2) /\ y IN ball(a,r / &2) /\ norm(x - y) <= r / &16
          ==> norm((a1:real^2->complex) y - a1 x) <=
              &2 * K * (&2 rpow (&1 + al) + &1) * norm(x - y) rpow al`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `w:real^2->real`; `a1:real^2->complex`; `K:real`;
                   `r / &8`; `&1 + al`; `y:real^2`; `x:real^2`] WANL_PT_JET_HOLDER1) THEN
    REWRITE_TAC[REAL_ARITH `(&1 + al) - &1 = al`] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      ASM_MESON_TAC[SUBSET];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `e:complex` THEN DISCH_TAC THEN EXPAND_TAC "s" THEN
      REWRITE_TAC[IN_BALL; dist] THEN
      UNDISCH_TAC `(x:real^2) IN ball(a,r / &2)` THEN REWRITE_TAC[IN_BALL; dist] THEN
      DISCH_TAC THEN ABBREV_TAC `dd = norm(x - y:real^2)` THEN
      SUBGOAL_THEN `norm(dd % (e:complex)) <= r / &16` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN EXPAND_TAC "dd" THEN
        REWRITE_TAC[REAL_ABS_NORM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH `a - (x + d):real^N = (a - x) + --d`;
                  VECTOR_ARITH `a - (x - d):real^N = (a - x) + d`] THEN
      MP_TAC(ISPECL [`a - x:real^2`; `--(dd % (e:complex))`] NORM_TRIANGLE) THEN
      MP_TAC(ISPECL [`a - x:real^2`; `dd % (e:complex)`] NORM_TRIANGLE) THEN
      REWRITE_TAC[NORM_NEG] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `w:real^2->real` THEN REPEAT CONJ_TAC THENL
   [(* C^1 *)
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
    EXISTS_TAC `\x0:real^2 h:real^2. lift(Re((a1:real^2->complex) x0 * h))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `h:real^2` THEN
    SUBGOAL_THEN `(a1:real^2->complex) continuous_on ball(a,r / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC WANL_PT_HOLDER_CONT THEN
      EXISTS_TAC `&2 * K * (&2 rpow (&1 + al) + &1)` THEN EXISTS_TAC `al:real` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      EXISTS_TAC `r / &16` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`x:real^2`; `y:real^2`]
        (ASSUME `!x y. x IN ball(a:real^2,r / &2) /\ y IN ball(a,r / &2) /\
                       norm(x - y) <= r / &16
                       ==> norm((a1:real^2->complex) y - a1 x) <=
                           &2 * K * (&2 rpow (&1 + al) + &1) * norm(x - y) rpow al`)) THEN
      SUBGOAL_THEN `norm(x - y:real^2) = norm(y - x)` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_ACCEPT_TAC NORM_SUB; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_ASSOC]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a1:real^2->complex`; `\z:complex. lift(Re(z * h))`;
                   `ball(a:real^2,r / &2)`] LINEAR_CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; COMPLEX_ADD_RDISTRIB; RE_ADD; LIFT_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; LIFT_CMUL];
    (* negligible exceptional set *)
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `t:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM(ASSUME `(u:real^2->real) x = w x`) ] THEN
    ASM_MESON_TAC[SUBSET];
    (* sup bounds *)
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN s` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= M * r pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `U:real` THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `&0 <= &32 * C1 * (M * r pow 2 + U)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[COMPLEX_NORM_CNJ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `r * G` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        EXPAND_TAC "G" THEN
        SUBGOAL_THEN `r * C1 * (U + M * r pow 2) / r = C1 * (U + M * r pow 2)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= C1 * (U + M * r pow 2)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]];
    (* Hoelder bound for the gradient *)
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN s /\ y IN s` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CNJ_SUB; COMPLEX_NORM_CNJ] THEN
    SUBGOAL_THEN `norm((a1:real^2->complex) x - a1 y) = norm(a1 y - a1 x)` SUBST1_TAC THENL
     [MATCH_ACCEPT_TAC NORM_SUB; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r rpow (&1 + al) /\ &0 <= norm(x - y:real^2) rpow al`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RPOW_POS_LT; RPOW_POS_LE; NORM_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= C1 * (U + M * r pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_ADD; REAL_LE_MUL;
                                                 REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= M * r pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_CASES_TAC `norm(x - y:real^2) <= r / &16` THENL
     [MP_TAC(SPECL [`x:real^2`; `y:real^2`]
        (ASSUME `!x y. x IN ball(a:real^2,r / &2) /\ y IN ball(a,r / &2) /\
                       norm(x - y) <= r / &16
                       ==> norm((a1:real^2->complex) y - a1 x) <=
                           &2 * K * (&2 rpow (&1 + al) + &1) * norm(x - y) rpow al`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&2 rpow (&1 + al) <= &4` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 rpow &2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[RPOW_POW] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `r rpow (&1 + al) * (&2 * K * (&2 rpow (&1 + al) + &1) * norm(x - y:real^2) rpow al)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `r rpow (&1 + al) * K = C1 * (U + M * r pow 2)` ASSUME_TAC THENL
       [EXPAND_TAC "K" THEN UNDISCH_TAC `&0 < r rpow (&1 + al)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      ABBREV_TAC `Dxy = norm(x - y:real^2) rpow al` THEN
      ABBREV_TAC `T2 = &2 rpow (&1 + al)` THEN
      SUBGOAL_THEN `r rpow (&1 + al) * (&2 * K * (T2 + &1) * Dxy) =
                    (&2 * (T2 + &1)) * (C1 * (U + M * r pow 2)) * Dxy` SUBST1_TAC THENL
       [UNDISCH_TAC `r rpow (&1 + al) * K = C1 * (U + M * r pow 2)` THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(&2 * (T2 + &1)) * (C1 * (U + M * r pow 2)) <= &10 * (C1 * (U + M * r pow 2))`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 <= M * r pow 2` MP_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `r / &16 < norm(x - y:real^2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm((a1:real^2->complex) y - a1 x) <= &2 * G` ASSUME_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH `!a b:complex g. norm(a) <= g /\ norm(b) <= g
                                              ==> norm(a - b) <= &2 * g`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `r rpow al <= &16 * norm(x - y:real^2) rpow al` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&16 rpow al * (r / &16) rpow al` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM RPOW_MUL] THEN
        SUBGOAL_THEN `&16 * r / &16 = r` SUBST1_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]];
        MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&16 rpow &1` THEN CONJ_TAC THENL
           [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
            REWRITE_TAC[RPOW_POW] THEN REAL_ARITH_TAC];
          MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `r rpow (&1 + al) = r rpow al * r` ASSUME_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `&1 + al = al + &1`] THEN
      ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r rpow (&1 + al) * (&2 * G)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `r rpow (&1 + al) * (&2 * G) = &2 * C1 * (U + M * r pow 2) * r rpow al`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * C1 * (U + M * r pow 2) * (&16 * norm(x - y:real^2) rpow al)` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `Dxy = norm(x - y:real^2) rpow al` THEN
    SUBGOAL_THEN
     `(&32 * C1 + &1) * (M * r pow 2 + U) * Dxy =
      &32 * (C1 * (U + M * r pow 2)) * Dxy + (M * r pow 2 + U) * Dxy`
    ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (M * r pow 2 + U) * Dxy` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

