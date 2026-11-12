(* ========================================================================= *)
(* pc_wan_lap2c: Campanato's characterisation of Hoelder continuity,         *)
(* WAN_CAMPANATO, in every dimension.                                        *)
(*   - means over balls; comparison of means on nested balls;                *)
(*   - the dyadic limit w and its distance to the means;                     *)
(*   - the Hoelder bound, Lebesgue points, WAN_CAMPANATO.                    *)
(* ========================================================================= *)

needs "src/pc_wan_p4defs.ml";;
needs "src/pc_wan_weak.ml";;
needs "src/pc_wan_lap2a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Means over balls and their comparison on nested balls.                   *)
(* ========================================================================= *)

let wanl_cp_mean = new_definition
 `wanl_cp_mean (u:real^N->real^K) x rho =
    inv(measure(ball(x,rho))) % integral (ball(x,rho)) u`;;

let wanl_cp_var = new_definition
 `wanl_cp_var (u:real^N->real^K) x rho =
    drop(integral (ball(x,rho)) (\y. lift(norm(u y - wanl_cp_mean u x rho) pow 2)))`;;

let WANL_CP_MEASURE_BALL = prove
 (`!(x:real^N) rho. &0 <= rho
        ==> measure(ball(x,rho)) = measure(ball(vec 0:real^N,&1)) * rho pow dimindex(:N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `rho:real`; `&1`] MEASURE_BALL_SCALING) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `vec 0:real^N`; `&1`] WANL_MEASURE_BALL_TRANSLATE) THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let WANL_CP_LSPACE_SUB = prove
 (`!(u:real^N->real^K) a r x rho c.
        u IN lspace (ball(a,r)) (&2) /\ ball(x,rho) SUBSET ball(a,r)
        ==> (\y. u y - c) IN lspace (ball(x,rho)) (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN
  SIMP_TAC[LSPACE_CONST; MEASURABLE_BALL; ETA_AX] THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^N,r)` THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]);;

(* |mean_B' (u) - c|^2 <= (1/|B'|) int_B' |u - c|^2.                         *)

let WANL_CP_MEAN_DEV = prove
 (`!(u:real^N->real^K) a r x rho c.
        &0 < rho /\ u IN lspace (ball(a,r)) (&2) /\ ball(x,rho) SUBSET ball(a,r)
        ==> norm(wanl_cp_mean u x rho - c) pow 2 <=
            inv(measure(ball(x,rho))) *
            drop(integral (ball(x,rho)) (\y. lift(norm(u y - c) pow 2)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = measure(ball(x:real^N,rho))` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REWRITE_TAC[MEASURE_BALL_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `a:real^N`; `r:real`; `x:real^N`; `rho:real`; `c:real^K`]
         WANL_CP_LSPACE_SUB) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y. (u:real^N->real^K) y - c`; `ball(x:real^N,rho)`; `&2`] HOELDER_BOUND) THEN
  ASM_REWRITE_TAC[MEASURABLE_BALL; RPOW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N->real^K) integrable_on ball(x,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    SUBGOAL_THEN `(u:real^N->real^K) = (\y. (u y - c) + c)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_ON_CONST; MEASURABLE_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `wanl_cp_mean (u:real^N->real^K) x rho - c =
                inv m % integral (ball(x,rho)) (\y. u y - c)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[wanl_cp_mean] THEN
    ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRABLE_ON_CONST; MEASURABLE_BALL; INTEGRAL_CONST_GEN] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < m ==> abs m = m`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv m pow 2 * m * norm(integral (ball(x:real^N,rho))
                                     (\y. lift(norm((u:real^N->real^K) y - c) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_1] THEN
  SUBGOAL_THEN `&0 <= drop(integral (ball(x:real^N,rho))
                     (\y. lift(norm((u:real^N->real^K) y - c) pow 2)))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    MP_TAC(ISPECL [`ball(x:real^N,rho)`; `&2`; `\y. (u:real^N->real^K) y - c`]
           LSPACE_IMP_INTEGRABLE) THEN
    ASM_REWRITE_TAC[RPOW_POW];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD);;

let WANL_CP_SQ_INTEGRABLE = prove
 (`!(u:real^N->real^K) a r x rho c.
        u IN lspace (ball(a,r)) (&2) /\ ball(x,rho) SUBSET ball(a,r)
        ==> (\y. lift(norm(u y - c) pow 2)) integrable_on ball(x,rho)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `a:real^N`; `r:real`; `x:real^N`; `rho:real`; `c:real^K`]
         WANL_CP_LSPACE_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE) THEN
  REWRITE_TAC[RPOW_POW]);;

(* Means on nested balls: |mean_B' - mean_B|^2 <= var_B / |B'|.             *)

let WANL_CP_NESTED = prove
 (`!(u:real^N->real^K) a r x rho x' rho'.
        &0 < rho' /\ u IN lspace (ball(a,r)) (&2) /\
        ball(x',rho') SUBSET ball(x,rho) /\ ball(x,rho) SUBSET ball(a,r)
        ==> norm(wanl_cp_mean u x' rho' - wanl_cp_mean u x rho) pow 2 <=
            inv(measure(ball(x',rho'))) * wanl_cp_var u x rho`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(measure(ball(x':real^N,rho'))) *
              drop(integral (ball(x',rho'))
                (\y. lift(norm((u:real^N->real^K) y - wanl_cp_mean u x rho) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WANL_CP_MEAN_DEV THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_LE_INV_EQ; MEASURE_POS_LE; MEASURABLE_BALL]; ALL_TAC] THEN
  REWRITE_TAC[wanl_cp_var] THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN CONJ_TAC THEN
  MATCH_MP_TAC WANL_CP_SQ_INTEGRABLE THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let WANL_CP_STEP_ARITH = prove
 (`!D V om rp P Q Kc c.
        &0 < om /\ &0 < rp /\ &0 <= Kc /\ &0 <= Q /\ &0 <= c /\
        D pow 2 <= inv(om * rp) * V /\ V <= Kc pow 2 * P * Q pow 2 /\ P <= c * rp
        ==> D <= sqrt(c / om) * Kc * Q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  SUBGOAL_THEN `&0 <= c / om` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(c / om)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(om * rp) * V` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(om * rp) * (Kc pow 2 * (c * rp) * Q pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kc pow 2 * P * Q pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `k * p * q:real = (k * q) * p`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < om` THEN UNDISCH_TAC `&0 < rp` THEN
    CONV_TAC REAL_FIELD]);;

(* One step of the comparison of means, for radii within a factor 2.        *)

let WANL_CP_STEP = prove
 (`!(u:real^N->real^K) a r Kc al x rho x' rho'.
        &0 < rho' /\ rho <= &2 * rho' /\ &0 <= Kc /\
        u IN lspace (ball(a,r)) (&2) /\
        ball(x',rho') SUBSET ball(x,rho) /\ ball(x,rho) SUBSET ball(a,r) /\
        wanl_cp_var u x rho <= Kc pow 2 * rho rpow (&(dimindex(:N)) + &2 * al)
        ==> norm(wanl_cp_mean u x' rho' - wanl_cp_mean u x rho) <=
            sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1))) * Kc * rho rpow al`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rho' <= rho` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(x':real^N,rho') SUBSET ball(x,rho)` THEN
    REWRITE_TAC[SUBSET_BALLS] THEN
    MP_TAC(ISPECL [`x':real^N`; `x:real^N`] DIST_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC WANL_CP_STEP_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`wanl_cp_var (u:real^N->real^K) x rho`; `rho' pow dimindex(:N)`;
    `rho pow dimindex(:N)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MEASURE_BALL_POS] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`x':real^N`; `rho':real`] WANL_CP_MEASURE_BALL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC WANL_CP_NESTED THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Kc pow 2 * rho rpow (&(dimindex(:N)) + &2 * al)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_POW] THEN
    REWRITE_TAC[REAL_ARITH `&2 * al = al + al`] THEN
    ASM_SIMP_TAC[RPOW_ADD] THEN REWRITE_TAC[REAL_POW_2];
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC]);;

let WANL_CP_B0_POS = prove
 (`&0 < sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1)))`,
  MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
  REWRITE_TAC[MEASURE_BALL_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let WANL_CP_Q_BOUNDS = prove
 (`!al. &0 < al ==> &0 < inv(&2 rpow al) /\ inv(&2 rpow al) < &1`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC RPOW_POS_LT THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LT_1 THEN MATCH_MP_TAC RPOW_LT_1 THEN ASM_REAL_ARITH_TAC]);;

let WANL_CP_C1_POS = prove
 (`!al. &0 < al
        ==> &0 < sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1))) /
                 (&1 - inv(&2 rpow al))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[WANL_CP_B0_POS] THEN
  MP_TAC(SPEC `al:real` WANL_CP_Q_BOUNDS) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Comparison of means of one centre over all radii, and the                *)
(* limit of the means as the radius tends to 0.  With q = 2^(-al),          *)
(* B0 = sqrt(2^N / |B(0,1)|) and C1 = B0 / (1 - q), halving the radius      *)
(* n times costs at most C1 Kc rho^al in total.                             *)
(* ========================================================================= *)

let WANL_CP_CHAIN = prove
 (`!(u:real^N->real^K) a r Kc al x.
        &0 < al /\ &0 <= Kc /\ u IN lspace (ball(a,r)) (&2) /\
        (!x rho. &0 < rho /\ ball(x,rho) SUBSET ball(a,r)
                 ==> wanl_cp_var u x rho <= Kc pow 2 * rho rpow (&(dimindex(:N)) + &2 * al))
        ==> !n rho rho'. &0 < rho' /\ rho' <= rho /\ rho <= &2 pow n * rho' /\
                         ball(x,rho) SUBSET ball(a,r)
                         ==> norm(wanl_cp_mean u x rho' - wanl_cp_mean u x rho) <=
                             sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1))) /
                             (&1 - inv(&2 rpow al)) * Kc * rho rpow al`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "camp")))) THEN
  MP_TAC(SPEC `al:real` WANL_CP_Q_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:N`,`:N`] WANL_CP_B0_POS) THEN DISCH_TAC THEN
  ABBREV_TAC `B0 = sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1)))` THEN
  ABBREV_TAC `q = inv(&2 rpow al)` THEN
  ABBREV_TAC `C1 = B0 / (&1 - q)` THEN
  SUBGOAL_THEN `B0 <= C1 /\ C1 * q + B0 = C1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= B0 * q ==> B0 * (&1 - q) <= B0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `q < &1` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `!rho. &0 < rho ==> &0 <= C1 * Kc * rho rpow al` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!rho x'' rho''. &0 < rho'' /\ rho <= &2 * rho'' /\
                    ball(x'',rho'') SUBSET ball(x:real^N,rho) /\ ball(x,rho) SUBSET ball(a,r)
                    ==> norm(wanl_cp_mean (u:real^N->real^K) x'' rho'' - wanl_cp_mean u x rho) <=
                        B0 * Kc * rho rpow al`
  (LABEL_TAC "step") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "B0" THEN MATCH_MP_TAC WANL_CP_STEP THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "camp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(x'':real^N,rho'') SUBSET ball(x,rho)` THEN
    REWRITE_TAC[SUBSET_BALLS] THEN
    MP_TAC(ISPECL [`x'':real^N`; `x:real^N`] DIST_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_LID] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `rho':real = rho` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `rho <= &2 * rho'` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B0 * Kc * rho rpow al` THEN CONJ_TAC THENL
     [USE_THEN "step" MATCH_MP_TAC THEN ASM_SIMP_TAC[SUBSET_BALL];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(x:real^N,rho / &2) SUBSET ball(x,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rho / &2`; `rho':real`]) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THENL
     [UNDISCH_TAC `rho <= &2 pow SUC n * rho'` THEN REWRITE_TAC[real_pow] THEN
      REAL_ARITH_TAC;
      ASM SET_TAC[]];
    DISCH_TAC] THEN
  USE_THEN "step" (MP_TAC o SPECL [`rho:real`; `x:real^N`; `rho / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(rho / &2) rpow al = rho rpow al * q` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [EXPAND_TAC "q" THEN REWRITE_TAC[RPOW_DIV; real_div]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C1 * Kc * (rho rpow al * q) + B0 * Kc * rho rpow al` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `!a b c:real^K e1 e2. norm(a - b) <= e1 /\ norm(b - c) <= e2 ==> norm(a - c) <= e1 + e2`) THEN
    EXISTS_TAC `wanl_cp_mean (u:real^N->real^K) x (rho / &2)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `C1 * q + B0 = C1` THEN
    CONV_TAC REAL_RING]);;

let WANL_CP_SAME = prove
 (`!(u:real^N->real^K) a r Kc al x rho rho'.
        &0 < al /\ &0 <= Kc /\ u IN lspace (ball(a,r)) (&2) /\
        (!x rho. &0 < rho /\ ball(x,rho) SUBSET ball(a,r)
                 ==> wanl_cp_var u x rho <= Kc pow 2 * rho rpow (&(dimindex(:N)) + &2 * al)) /\
        &0 < rho' /\ rho' <= rho /\ ball(x,rho) SUBSET ball(a,r)
        ==> norm(wanl_cp_mean u x rho' - wanl_cp_mean u x rho) <=
            sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1))) /
            (&1 - inv(&2 rpow al)) * Kc * rho rpow al`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&2`; `rho / rho'`] REAL_ARCH_POW) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `n:num`)] THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `a:real^N`; `r:real`; `Kc:real`; `al:real`; `x:real^N`]
         WANL_CP_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rho / rho' < &2 pow n` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  REAL_ARITH_TAC);;

let WANL_RPOW_SMALL = prove
 (`!al e. &0 < al /\ &0 < e ==> ?d. &0 < d /\ !x. &0 <= x /\ x <= d ==> x rpow al <= e`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `e rpow inv al` THEN
  ASM_SIMP_TAC[RPOW_POS_LT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(e rpow inv al) rpow al` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]]);;

(* The limit of the means at x exists and is within C1 Kc rho^al of the     *)
(* mean over B(x,rho), for every rho <= r0 with B(x,r0) inside B(a,r).      *)

let WANL_CP_LIMIT = prove
 (`!(u:real^N->real^K) a r Kc al x r0.
        &0 < al /\ &0 <= Kc /\ u IN lspace (ball(a,r)) (&2) /\
        (!x rho. &0 < rho /\ ball(x,rho) SUBSET ball(a,r)
                 ==> wanl_cp_var u x rho <= Kc pow 2 * rho rpow (&(dimindex(:N)) + &2 * al)) /\
        &0 < r0 /\ ball(x,r0) SUBSET ball(a,r)
        ==> ((\e. wanl_cp_mean u x (drop e)) -->
             lim (at (vec 0) within {t | &0 < drop t}) (\e. wanl_cp_mean u x (drop e)))
            (at (vec 0) within {t | &0 < drop t}) /\
            !rho. &0 < rho /\ rho <= r0
                  ==> norm(lim (at (vec 0) within {t | &0 < drop t})
                               (\e. wanl_cp_mean u x (drop e)) - wanl_cp_mean u x rho) <=
                      sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1))) /
                      (&1 - inv(&2 rpow al)) * Kc * rho rpow al`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `al:real` (INST_TYPE [`:N`,`:N`] WANL_CP_C1_POS)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `C1 = sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1))) /
                   (&1 - inv(&2 rpow al))` THEN
  SUBGOAL_THEN
   `!rho rho'. &0 < rho' /\ rho' <= rho /\ rho <= r0
               ==> norm(wanl_cp_mean (u:real^N->real^K) x rho' - wanl_cp_mean u x rho) <=
                   C1 * Kc * rho rpow al`
  (LABEL_TAC "same") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "C1" THEN MATCH_MP_TAC WANL_CP_SAME THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^N,r0)` THEN
    ASM_SIMP_TAC[SUBSET_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?l. ((\e. wanl_cp_mean (u:real^N->real^K) x (drop e)) --> l)
        (at (vec 0) within {t | &0 < drop t})`
  MP_TAC THENL
   [REWRITE_TAC[CONVERGENT_EQ_CAUCHY_WITHIN] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &2 * C1 * Kc + &1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 * x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e / (&2 * C1 * Kc + &1) /\
                  (&2 * C1 * Kc + &1) * e / (&2 * C1 * Kc + &1) = e` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `&0 < &2 * C1 * Kc + &1` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    ABBREV_TAC `eps = e / (&2 * C1 * Kc + &1)` THEN
    MP_TAC(SPECL [`al:real`; `eps:real`] WANL_RPOW_SMALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d r0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; DIST_0; NORM_1] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `t':real^1`] THEN STRIP_TAC THEN
    USE_THEN "same" (MP_TAC o SPECL [`min d r0`; `drop t`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "same" (MP_TAC o SPECL [`min d r0`; `drop t'`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `(min d r0) rpow al <= eps` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `C1 * Kc * (min d r0) rpow al <= C1 * Kc * eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!a b m:real^K x e. norm(a - m) <= x /\ norm(b - m) <= x /\ &2 * x < e
                         ==> dist(a,b) < e`) THEN
    MAP_EVERY EXISTS_TAC
     [`wanl_cp_mean (u:real^N->real^K) x (min d r0)`; `C1 * Kc * (min d r0) rpow al`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real^K`) THEN
  SUBGOAL_THEN `lim (at (vec 0) within {t | &0 < drop t})
                    (\e. wanl_cp_mean (u:real^N->real^K) x (drop e)) = l`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TENDSTO_LIM THEN ASM_REWRITE_TAC[WAN_LIMPT_POSITIVE_REALS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `at (vec 0:real^1) within {t | &0 < drop t}` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\e. wanl_cp_mean (u:real^N->real^K) x (drop e) - wanl_cp_mean u x rho` THEN
  REWRITE_TAC[WAN_LIMPT_POSITIVE_REALS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_WITHIN; IN_ELIM_THM; DIST_0; NORM_1] THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  USE_THEN "same" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Lebesgue points (the limit of the means is u a.e.), the                  *)
(* Hoelder bound for the limit (cases |x - y| <= r/4 and |x - y| > r/4),    *)
(* and WAN_CAMPANATO.                                                        *)
(* ========================================================================= *)

let WANL_CP_LEBESGUE = prove
 (`!(u:real^N->real^K) a r.
        u IN lspace (ball(a,r)) (&2)
        ==> ?k. negligible k /\
                !x. x IN ball(a,r) /\ ~(x IN k)
                    ==> ((\e. wanl_cp_mean u x (drop e)) --> u x)
                        (at (vec 0) within {t | &0 < drop t})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `ball(a:real^N,r)`]
         LEBESGUE_DENSITY_THEOREM_INTEGRAL_BALL) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:real^N`; `d:real^N`] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `ball(a:real^N,r)` THEN
    SIMP_TAC[INTER_SUBSET; LEBESGUE_MEASURABLE_INTER; LEBESGUE_MEASURABLE_BALL;
             LEBESGUE_MEASURABLE_INTERVAL] THEN
    REWRITE_TAC[GSYM LSPACE_1] THEN MATCH_MP_TAC LSPACE_MONO THEN
    EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[MEASURABLE_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_WITHIN; IN_ELIM_THM; DIST_0; NORM_1] THEN
  EXISTS_TAC `r - dist(a:real^N,x)` THEN CONJ_TAC THENL
   [UNDISCH_TAC `x IN ball(a:real^N,r)` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN REWRITE_TAC[wanl_cp_mean] THEN
  SUBGOAL_THEN `ball(a:real^N,r) INTER ball(x,drop t) = ball(x,drop t)` SUBST1_TAC THENL
   [REWRITE_TAC[SET_RULE `!s t:real^N->bool. s INTER t = t <=> t SUBSET s`; SUBSET_BALLS] THEN
    DISJ1_TAC THEN MP_TAC(ISPECL [`a:real^N`; `x:real^N`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    REFL_TAC]);;

(* At the points of B(a,r/2) outside a null set, the limit of the means is u. *)

let WANL_CP_AE = prove
 (`!(u:real^N->real^K) a r.
        &0 < r /\ u IN lspace (ball(a,r)) (&2)
        ==> negligible {x | x IN ball(a,r / &2) /\
                            ~(u x = lim (at (vec 0) within {t | &0 < drop t})
                                        (\e. wanl_cp_mean u x (drop e)))}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `a:real^N`; `r:real`] WANL_CP_LEBESGUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  ONCE_REWRITE_TAC[TAUT `p /\ ~q ==> r <=> p /\ ~r ==> q`] THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC TENDSTO_LIM THEN
  REWRITE_TAC[WAN_LIMPT_POSITIVE_REALS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `x IN ball(a:real^N,r / &2)` THEN
  REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC);;

let WANL_RPOW_SCALE_LE = prove
 (`!c x al. &1 <= c /\ &0 <= x /\ &0 <= al /\ al <= &1
            ==> (c * x) rpow al <= c * x rpow al`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RPOW_MUL] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[RPOW_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c rpow &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]]);;

let WANL_CP_MUL_LE = prove
 (`!c k p q. &0 <= c /\ &0 <= k /\ p <= q ==> c * k * p <= c * k * q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* The Hoelder bound for the limit of the means.                            *)

let WANL_CP_HOELDER = prove
 (`!(u:real^N->real^K) a r Kc al x y.
        &0 < al /\ al <= &1 /\ &0 < r /\ &0 <= Kc /\ u IN lspace (ball(a,r)) (&2) /\
        (!x rho. &0 < rho /\ ball(x,rho) SUBSET ball(a,r)
                 ==> wanl_cp_var u x rho <= Kc pow 2 * rho rpow (&(dimindex(:N)) + &2 * al)) /\
        x IN ball(a,r / &2) /\ y IN ball(a,r / &2)
        ==> norm(lim (at (vec 0) within {t | &0 < drop t}) (\e. wanl_cp_mean u x (drop e)) -
                 lim (at (vec 0) within {t | &0 < drop t}) (\e. wanl_cp_mean u y (drop e))) <=
            (&8 * sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1))) /
                  (&1 - inv(&2 rpow al)) +
             &8 * sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1)))) *
            Kc * norm(x - y) rpow al`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:N`,`:N`] WANL_CP_B0_POS) THEN DISCH_TAC THEN
  MP_TAC(SPEC `al:real` (INST_TYPE [`:N`,`:N`] WANL_CP_C1_POS)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z. z IN ball(a:real^N,r / &2) ==> ball(z,r / &2) SUBSET ball(a,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_BALL; SUBSET_BALLS] THEN
    MP_TAC(ISPECL [`a:real^N`; `z:real^N`] DIST_SYM) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^N = y` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x' rho' z rho. &0 < rho' /\ rho <= &2 * rho' /\
                    ball(x',rho') SUBSET ball(z,rho) /\ ball(z,rho) SUBSET ball(a,r)
                    ==> norm(wanl_cp_mean (u:real^N->real^K) x' rho' - wanl_cp_mean u z rho) <=
                        sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1))) *
                        Kc * rho rpow al`
  (LABEL_TAC "step") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_CP_STEP THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(x':real^N,rho') SUBSET ball(z,rho)` THEN
    REWRITE_TAC[SUBSET_BALLS] THEN
    MP_TAC(ISPECL [`x':real^N`; `z:real^N`] DIST_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `a:real^N`; `r:real`; `Kc:real`; `al:real`;
                 `x:real^N`; `r / &2`] WANL_CP_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "lx" o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `a:real^N`; `r:real`; `Kc:real`; `al:real`;
                 `y:real^N`; `r / &2`] WANL_CP_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "ly" o CONJUNCT2)] THEN
  ABBREV_TAC `Lx = lim (at (vec 0) within {t | &0 < drop t})
                       (\e. wanl_cp_mean (u:real^N->real^K) x (drop e))` THEN
  ABBREV_TAC `Ly = lim (at (vec 0) within {t | &0 < drop t})
                       (\e. wanl_cp_mean (u:real^N->real^K) y (drop e))` THEN
  ABBREV_TAC `d = norm(x - y:real^N)` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ABBREV_TAC `B0 = sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1)))` THEN
  ABBREV_TAC `C1 = B0 / (&1 - inv(&2 rpow al))` THEN
  SUBGOAL_THEN `&0 <= d rpow al` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C1 * Kc * d rpow al /\ &0 <= B0 * Kc * d rpow al`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  ASM_CASES_TAC `&2 * d <= r / &2` THENL
   [USE_THEN "lx" (MP_TAC o SPEC `d:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "ly" (MP_TAC o SPEC `&2 * d`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "step" (MP_TAC o SPECL [`x:real^N`; `d:real`; `y:real^N`; `&2 * d`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET_BALLS] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[dist] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^N,r / &2)` THEN
        ASM_SIMP_TAC[SUBSET_BALL]];
      DISCH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C1 * Kc * d rpow al + C1 * Kc * (&2 * d) rpow al +
                B0 * Kc * (&2 * d) rpow al` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `!Lx Ly mx my:real^K e1 e2 e3.
          norm(Lx - mx) <= e1 /\ norm(Ly - my) <= e2 /\ norm(mx - my) <= e3
          ==> norm(Lx - Ly) <= e1 + e2 + e3`) THEN
      MAP_EVERY EXISTS_TAC [`wanl_cp_mean (u:real^N->real^K) x d`;
                            `wanl_cp_mean (u:real^N->real^K) y (&2 * d)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`&2`; `d:real`; `al:real`] WANL_RPOW_SCALE_LE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`C1:real`; `Kc:real`; `(&2 * d) rpow al`; `&2 * d rpow al`]
           WANL_CP_MUL_LE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`B0:real`; `Kc:real`; `(&2 * d) rpow al`; `&2 * d rpow al`]
           WANL_CP_MUL_LE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "lx" (MP_TAC o SPEC `r / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "ly" (MP_TAC o SPEC `r / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "step" (MP_TAC o SPECL [`x:real^N`; `r / &2`; `a:real^N`; `r:real`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "step" (MP_TAC o SPECL [`y:real^N`; `r / &2`; `a:real^N`; `r:real`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(r / &2) rpow al <= &4 * d rpow al /\ r rpow al <= &4 * d rpow al`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `r rpow al <= &4 * d rpow al` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4 * d) rpow al` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC WANL_RPOW_SCALE_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r rpow al` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`C1:real`; `Kc:real`; `(r / &2) rpow al`; `&4 * d rpow al`]
         WANL_CP_MUL_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`B0:real`; `Kc:real`; `r rpow al`; `&4 * d rpow al`] WANL_CP_MUL_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C1 * Kc * (r / &2) rpow al + C1 * Kc * (r / &2) rpow al +
              B0 * Kc * r rpow al + B0 * Kc * r rpow al` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `!Lx Ly mx my ma:real^K e1 e2 e3 e4.
        norm(Lx - mx) <= e1 /\ norm(Ly - my) <= e2 /\ norm(mx - ma) <= e3 /\
        norm(my - ma) <= e4
        ==> norm(Lx - Ly) <= e1 + e2 + e3 + e4`) THEN
    MAP_EVERY EXISTS_TAC [`wanl_cp_mean (u:real^N->real^K) x (r / &2)`;
                          `wanl_cp_mean (u:real^N->real^K) y (r / &2)`;
                          `wanl_cp_mean (u:real^N->real^K) a r`] THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Campanato's characterisation of Hoelder continuity.                      *)
(* ------------------------------------------------------------------------- *)

let WAN_CAMPANATO = prove
 (`!(n:N->bool) (kk:K->bool). WAN_CAMPANATO_STATEMENT n kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WAN_CAMPANATO_STATEMENT] THEN
  X_GEN_TAC `al:real` THEN STRIP_TAC THEN
  EXISTS_TAC `&8 * sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1))) /
                   (&1 - inv(&2 rpow al)) +
              &8 * sqrt(&2 pow dimindex(:N) / measure(ball(vec 0:real^N,&1)))` THEN
  CONJ_TAC THENL
   [MP_TAC(INST_TYPE [`:N`,`:N`] WANL_CP_B0_POS) THEN
    MP_TAC(SPEC `al:real` (INST_TYPE [`:N`,`:N`] WANL_CP_C1_POS)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `r:real`; `u:real^N->real^K`; `Kc:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x rho. &0 < rho /\ ball(x,rho) SUBSET ball(a,r)
            ==> wanl_cp_var (u:real^N->real^K) x rho <=
                Kc pow 2 * rho rpow (&(dimindex(:N)) + &2 * al)`
  ASSUME_TAC THENL
   [REWRITE_TAC[wanl_cp_var; wanl_cp_mean] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  EXISTS_TAC `\x. lim (at (vec 0) within {t | &0 < drop t})
                      (\e. wanl_cp_mean (u:real^N->real^K) x (drop e))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_CP_HOELDER THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WANL_CP_AE THEN ASM_REWRITE_TAC[]]);;

