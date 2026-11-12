(* ========================================================================= *)
(* Unit pc_cmr_cont (a unit of the replacement chain of pc_cm_replacement):  *)
(* continuity of the cap replacement in the map and in the radius (C^0 and   *)
(* Dirichlet), hence of the tightened families of sweepouts and of the       *)
(* homotopies.                                                               *)
(*                                                                           *)
(* L^2 continuity of planar dilations.                                       *)
(* ========================================================================= *)

needs "src/pc_cmr_rep.ml";;
needs "src/pc_cmw_reg.ml";;

prioritize_real();;
type_invention_error := true;;

let CMR_LNORM_BOUND = prove
 (`!(f:real^2->real^K) s M.
     measurable s /\ f measurable_on s /\ &0 <= M /\ (!x. x IN s ==> norm(f x) <= M)
     ==> f IN lspace s (&2) /\ lnorm s (&2) f <= measure s rpow inv(&2) * M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^2. M % basis 1:real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LSPACE_CONST; REAL_LT_IMP_LE; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:K`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
    EXISTS_TAC `\x:real^2. M % basis 1:real^K` THEN
    ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= M ==> abs M = M`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm s (&2) (\x:real^2. M % basis 1:real^K)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:K`,`:P`] LNORM_MONO) THEN EXISTS_TAC `{}:real^2->bool` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY; REAL_POS] THEN
    ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= M ==> abs M = M`];
    ASM_SIMP_TAC[LNORM_CONST; REAL_ARITH `&0 < &2`; NORM_MUL; NORM_BASIS; DIMINDEX_GE_1;
                 LE_REFL; REAL_MUL_RID; REAL_ARITH `&0 <= M ==> abs M = M`; REAL_LE_REFL]]);;

let CMR_AFF_IMAGE_INV = prove
 (`!r (c:real^N) s. ~(r = &0)
     ==> IMAGE (\x. inv r % x + --(inv r % c)) (IMAGE (\x. r % x + c) s) = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  ASM_SIMP_TAC[CMR_AFF_INV; IMAGE_ID]);;

let CMR_CONT_AFF_COMPOSE = prove
 (`!(h:real^2->real^K) m (b:real^2) s.
     h continuous_on (:real^2) ==> (\x. h(m % x + b)) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (h:real^2->real^K)(m % x + b)) = h o (\x. m % x + b)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON; CMR_AFF_SMOOTH];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]]);;

let CMR_DIL_L2_SEQ = prove
 (`!(g:real^2->real^K) (a:real^2) rho (rn:num->real) (cn:num->real^2) r c.
     g IN lspace (:real^2) (&2) /\ &0 < r /\
     (!n. &0 < rn n) /\ (rn ---> r) sequentially /\ (cn --> c) sequentially
     ==> ((\n. lnorm (ball(a,rho)) (&2) (\x. g(rn n % x + cn n) - g(r % x + c))) ---> &0)
         sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `B = norm(a:real^2) + abs rho + &1` THEN
  SUBGOAL_THEN `&0 < B /\ !x:real^2. x IN ball(a,rho) ==> norm x <= B` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `a:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_BALL] THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = &2 * r * B + norm(c:real^2) + &1` THEN
  ABBREV_TAC `K = cball(vec 0:real^2,R0)` THEN
  SUBGOAL_THEN `measurable(K:real^2->bool) /\ compact(K:real^2->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[MEASURABLE_CBALL; COMPACT_CBALL]; ALL_TAC] THEN
  ABBREV_TAC `d = e * r / &8` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^2->real^K`; `K:real^2->bool`; `&2`; `d:real`]
                LSPACE_APPROXIMATE_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; MEASURABLE_IMP_LEBESGUE_MEASURABLE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^K` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m0 = measure(ball(a:real^2,rho)) rpow inv(&2)` THEN
  SUBGOAL_THEN `&0 <= m0` ASSUME_TAC THENL
   [EXPAND_TAC "m0" THEN MATCH_MP_TAC RPOW_POS_LE THEN MATCH_MP_TAC MEASURE_POS_LE THEN
    REWRITE_TAC[MEASURABLE_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = e / (&2 * (m0 + &1))` THEN
  SUBGOAL_THEN `&0 < e1 /\ m0 * e1 < e / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN
    SUBGOAL_THEN `&0 < &2 * (m0 + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `m * (e / d) = (m * e) / d`] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^2->real^K`; `K:real^2->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e1:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?N. !n. N <= n
            ==> r / &2 < rn n /\ rn n < &2 * r /\ dist((cn:num->real^2) n,c) < &1 /\
                abs(rn n - r) * B + dist(cn n,c) < eta`
  (X_CHOOSE_TAC `N:num`) THENL
   [UNDISCH_TAC `(rn ---> r) sequentially` THEN UNDISCH_TAC `((cn:num->real^2) --> c) sequentially` THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY; LIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `min (&1) (eta / &2)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
    DISCH_THEN(MP_TAC o SPEC `min (r / &2) (eta / (&2 * B))`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_TAC `N2:num`)] THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_LT_MIN]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x < a / &2 /\ y < a / &2 ==> x + y < a`) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs((rn:num->real) n - r) < eta / (&2 * B)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < B ==> &0 < &2 * B`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^2. x IN ball(a,rho) ==> (rn:num->real) n % x + (cn:num->real^2) n IN K /\ r % x + c IN K`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(x:real^2) <= B` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `norm((rn:num->real) n % x) <= &2 * r * B /\ norm(r % (x:real^2)) <= &2 * r * B`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `(rn:num->real) n * B`; EXISTS_TAC `r * B`] THEN
      (CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((cn:num->real^2) n) <= norm(c:real^2) + &1` ASSUME_TAC THENL
     [UNDISCH_TAC `dist((cn:num->real^2) n,c) < &1` THEN CONV_TAC NORM_ARITH; ALL_TAC] THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_CBALL_0] THEN
    UNDISCH_TAC `&2 * r * B + norm(c:real^2) + &1 = R0` THEN
    MP_TAC(ISPECL [`(rn:num->real) n % (x:real^2)`; `(cn:num->real^2) n`] NORM_TRIANGLE) THEN
    MP_TAC(ISPECL [`r % (x:real^2)`; `c:real^2`] NORM_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = ball(a:real^2,rho)` THEN
  SUBGOAL_THEN `measurable(s:real^2->bool) /\ lebesgue_measurable(s:real^2->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[MEASURABLE_BALL; LEBESGUE_MEASURABLE_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y. (g:real^2->real^K) y - h y) IN lspace K (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; MEASURABLE_IMP_LEBESGUE_MEASURABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m (b:real^2). &0 < m /\ r / &2 < m /\ (!x. x IN s ==> m % x + b IN K)
        ==> (\x. (g:real^2->real^K)(m % x + b) - h(m % x + b)) IN lspace s (&2) /\
            lnorm s (&2) (\x. g(m % x + b) - h(m % x + b)) < &2 * d / r`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\y. (g:real^2->real^K) y - h y`; `IMAGE (\x:real^2. m % x + b) s`;
                   `m:real`; `b:real^2`] CMR_AFF_LSPACE) THEN
    ASM_SIMP_TAC[CMR_AFF_IMAGE_INV; REAL_LT_IMP_NZ] THEN
    SUBGOAL_THEN `IMAGE (\x:real^2. m % x + b) s SUBSET K /\
                  lebesgue_measurable(IMAGE (\x:real^2. m % x + b) s)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN ASM_SIMP_TAC[MEASURABLE_AFFINITY];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `K:real^2->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d / m` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `lnorm K (&2) (\y. (g:real^2->real^K) y - h y)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC HMD_LNORM_SUBSET THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      UNDISCH_TAC `lnorm K (&2) (\x. (g:real^2->real^K) x - h x) < d` THEN
      REWRITE_TAC[ETA_AX];
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      REWRITE_TAC[real_div; REAL_ARITH `(&2 * d * ir) * m = d * (&2 * m * ir)`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM real_div; REAL_ARITH `&2 * m / r = (&2 * m) / r`] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x:real^2. x IN s ==> (rn:num->real) n % x + (cn:num->real^2) n IN K) /\
                (!x:real^2. x IN s ==> r % x + c IN K) /\ r / &2 < r`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `d:real`)) (concl th)
    then MP_TAC(ISPECL [`(rn:num->real) n`; `(cn:num->real^2) n`] th) THEN
         MP_TAC(ISPECL [`r:real`; `c:real^2`] th) else failwith "no") THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `A = \x. (g:real^2->real^K)((rn:num->real) n % x + (cn:num->real^2) n) -
                     h(rn n % x + cn n)` THEN
  ABBREV_TAC `C = \x. (g:real^2->real^K)(r % x + c) - h(r % x + c)` THEN
  ABBREV_TAC `Bm = \x. (h:real^2->real^K)((rn:num->real) n % x + (cn:num->real^2) n) -
                      h(r % x + c)` THEN
  SUBGOAL_THEN `(Bm:real^2->real^K) IN lspace s (&2) /\ lnorm s (&2) Bm <= m0 * e1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m0" THEN EXPAND_TAC "s" THEN MATCH_MP_TAC CMR_LNORM_BOUND THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; MEASURABLE_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN EXPAND_TAC "Bm" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      CONJ_TAC THEN MATCH_MP_TAC CMR_CONT_AFF_COMPOSE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXPAND_TAC "Bm" THEN
    SUBGOAL_THEN `(x:real^2) IN s` ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM dist] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `eta:real`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `norm(x:real^2) <= B` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs((rn:num->real) n - r) * B + dist((cn:num->real^2) n,c)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `(a % x + b) - (c % x + d):real^N = (a - c) % x + (b - d)`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(((rn:num->real) n - r) % (x:real^2)) + norm((cn:num->real^2) n - c)` THEN
    REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (g:real^2->real^K)((rn:num->real) n % x + (cn:num->real^2) n) - g(r % x + c)) =
    (\x. A x + (\x. (Bm:real^2->real^K) x + --(C x)) x)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "Bm"; "C"] THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. --((C:real^2->real^K) x)) IN lspace s (&2) /\
                lnorm s (&2) (\x. --((C:real^2->real^K) x)) = lnorm s (&2) C`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LSPACE_NEG; LNORM_NEG]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (Bm:real^2->real^K) x + --(C x)) IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (A:real^2->real^K) x + (\x. (Bm:real^2->real^K) x + --(C x)) x)
                IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[REAL_POS] THEN
    UNDISCH_TAC `(\x. (Bm:real^2->real^K) x + --(C x)) IN lspace s (&2)` THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LNORM_POS_LE; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `&2`; `A:real^2->real^K`;
                 `\x. (Bm:real^2->real^K) x + --(C x)`] LNORM_TRIANGLE) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `&2`; `Bm:real^2->real^K`;
                 `\x. --((C:real^2->real^K) x)`] LNORM_TRIANGLE) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN REWRITE_TAC[ETA_AX] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 * d / r = e / &4` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EXPAND_TAC "d" THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Dirichlet continuity of planar dilations of a continuous                  *)
(* map with L^2 weak partials on the plane.                                  *)
(* ========================================================================= *)

let CMR_CONT_W12_OPEN_BOUNDED = prove
 (`!(U:real^2->real^K) s.
     U continuous_on (:real^2) /\ open s /\ bounded s /\
     (!i. 1 <= i /\ i <= 2 ==> ?v. v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i U v)
     ==> wan_w12 s U`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_w12; DIMINDEX_2] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `bounded(IMAGE (U:real^2->real^K) (closure s))` MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
    MATCH_MP_TAC HMC_BOUNDED_LSPACE THEN EXISTS_TAC `M:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ASM_MESON_TAC[SUBSET; CLOSURE_SUBSET]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^2->real^K` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN];
      MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]]]);;

let CMR_DIL_WPD = prove
 (`!(U:real^2->real^K) (v:real^2->real^K) (a:real^2) rho m (b:real^2) i.
     U continuous_on (:real^2) /\
     (!i. 1 <= i /\ i <= 2 ==> ?v. v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i U v) /\
     v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i U v /\
     &0 < m /\ 1 <= i /\ i <= 2
     ==> wan_wpd (ball(a,rho)) i (\x. U(m % x + b))
           (\x. m % wan_wd (IMAGE (\x. m % x + b) (ball(a,rho))) i U (m % x + b)) /\
         negligible {x | x IN ball(a,rho) /\
                         ~(wan_wd (IMAGE (\x. m % x + b) (ball(a,rho))) i U (m % x + b) =
                           v(m % x + b))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `s' = IMAGE (\x:real^2. m % x + b) (ball(a,rho))` THEN
  SUBGOAL_THEN `open(s':real^2->bool) /\ bounded(s':real^2->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_AFFINITY THEN ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_NZ];
      MATCH_MP_TAC BOUNDED_AFFINITY THEN REWRITE_TAC[BOUNDED_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s' (U:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_CONT_W12_OPEN_BOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `U:real^2->real^K`; `m:real`; `b:real^2`] CMR_AFF_W12) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (\x. inv m % x + --(inv m % b)) (s':real^2->bool) = ball(a,rho)`
  SUBST1_TAC THENL
   [EXPAND_TAC "s'" THEN ASM_SIMP_TAC[CMR_AFF_IMAGE_INV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `i:num`; `U:real^2->real^K`; `v:real^2->real^K`]
                WAN_WD_UNIQUE) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN ANTS_TAC THENL
   [MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\y:real^2. ~(wan_wd s' i (U:real^2->real^K) y = v y)`;
                 `s':real^2->bool`; `m:real`; `b:real^2`] CMR_AFF_SET) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `IMAGE (\x. inv m % x + --(inv m % b)) (s':real^2->bool) = ball(a,rho)`
  SUBST1_TAC THENL
   [EXPAND_TAC "s'" THEN ASM_SIMP_TAC[CMR_AFF_IMAGE_INV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CMR_AFF_NEGLIGIBLE THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

(* Dilations of an L^2 map of the plane are L^2 on balls.                  *)

let CMR_DIL_LSPACE = prove
 (`!(v:real^2->real^K) (a:real^2) rho m (b:real^2).
     v IN lspace (:real^2) (&2) /\ &0 < m
     ==> (\x. v(m % x + b)) IN lspace (ball(a,rho)) (&2) /\
         lnorm (ball(a,rho)) (&2) (\x. v(m % x + b)) <= lnorm (:real^2) (&2) v / m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^2->real^K`; `IMAGE (\x:real^2. m % x + b) (ball(a,rho))`;
                 `m:real`; `b:real^2`] CMR_AFF_LSPACE) THEN
  ASM_SIMP_TAC[CMR_AFF_IMAGE_INV; REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `lebesgue_measurable(IMAGE (\x:real^2. m % x + b) (ball(a,rho)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN
    SIMP_TAC[MEASURABLE_AFFINITY; MEASURABLE_BALL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC HMD_LNORM_SUBSET THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; REAL_POS]);;

let CMR_DIL_L2_SCALED = prove
 (`!(v:real^2->real^K) (a:real^2) rho (rn:num->real) (cn:num->real^2) r c.
     v IN lspace (:real^2) (&2) /\ &0 < r /\
     (!n. &0 < rn n) /\ (rn ---> r) sequentially /\ (cn --> c) sequentially
     ==> ((\n. lnorm (ball(a,rho)) (&2) (\x. rn n % v(rn n % x + cn n) - r % v(r % x + c)))
          ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m (b:real^2). &0 < m
        ==> (\x. (v:real^2->real^K)(m % x + b)) IN lspace (ball(a,rho)) (&2) /\
            lnorm (ball(a,rho)) (&2) (\x. v(m % x + b)) <= lnorm (:real^2) (&2) v / m`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CMR_DIL_LSPACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^2->real^K`; `a:real^2`; `rho:real`; `rn:num->real`;
                 `cn:num->real^2`; `r:real`; `c:real^2`] CMR_DIL_L2_SEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. abs(rn n - r) * (&2 * lnorm (:real^2) (&2) (v:real^2->real^K) / r) +
                  r * lnorm (ball(a,rho)) (&2)
                        (\x. v((rn:num->real) n % x + (cn:num->real^2) n) - v(r % x + c))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_NULL_RMUL THEN
      REWRITE_TAC[REALLIM_NULL_ABS; GSYM REALLIM_NULL] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN ASM_REWRITE_TAC[]]] THEN
  UNDISCH_TAC `(rn ---> r) sequentially` THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `r / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(ISPECL [`(rn:num->real) n`; `(cn:num->real^2) n`] th) THEN
                          MP_TAC(ISPECL [`r:real`; `c:real^2`] th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (rn:num->real) n % (v:real^2->real^K)(rn n % x + (cn:num->real^2) n) - r % v(r % x + c)) =
    (\x. (\x. (rn n - r) % v(rn n % x + cn n)) x +
         (\x. r % (v(rn n % x + cn n) - v(r % x + c))) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. ((rn:num->real) n - r) % (v:real^2->real^K)(rn n % x + (cn:num->real^2) n))
      IN lspace (ball(a,rho)) (&2) /\
    (\x. r % (v(rn n % x + cn n) - v(r % x + c))) IN lspace (ball(a,rho)) (&2) /\
    (\x. v(rn n % x + cn n) - v(r % x + c)) IN lspace (ball(a,rho)) (&2)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `b /\ (b ==> c) /\ a ==> a /\ c /\ b`) THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS];
      DISCH_TAC THEN MATCH_MP_TAC LSPACE_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LSPACE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_ABS] THEN
  ASM_SIMP_TAC[LNORM_POS_LE; LSPACE_ADD; REAL_POS; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm (ball(a,rho)) (&2)
                (\x. ((rn:num->real) n - r) % (v:real^2->real^K)(rn n % x + (cn:num->real^2) n)) +
              lnorm (ball(a,rho)) (&2) (\x. r % (v(rn n % x + cn n) - v(r % x + c)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`ball(a:real^2,rho)`; `&2`;
                   `\x. (v:real^2->real^K)((rn:num->real) n % x + (cn:num->real^2) n) -
                        v(r % x + c)`; `r:real`] LNORM_MUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_LE_REFL]] THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `&2`;
                 `\x. (v:real^2->real^K)((rn:num->real) n % x + (cn:num->real^2) n)`;
                 `(rn:num->real) n - r`] LNORM_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lnorm (:real^2) (&2) (v:real^2->real^K) / (rn:num->real) n` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= lnorm (:real^2) (&2) (v:real^2->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LNORM_POS_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `(&2 * l / r) * m = (&2 * l * m) / r`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MP_TAC(SPECL [`lnorm (:real^2) (&2) (v:real^2->real^K)`; `&2 * (rn:num->real) n - r`]
               REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Dilations of a continuous map with global L^2 weak partials are W^(1,2) *)
(* on balls; the Dirichlet integral of the difference of two dilations is   *)
(* the sum of the squared L^2 norms of the differences of the dilated       *)
(* partials, which tends to 0 when the dilations converge.                  *)

let CMR_DIL_W12 = prove
 (`!(U:real^2->real^K) (a:real^2) rho m (b:real^2).
     U continuous_on (:real^2) /\
     (!i. 1 <= i /\ i <= 2 ==> ?v. v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i U v) /\
     &0 < m
     ==> wan_w12 (ball(a,rho)) (\x. U(m % x + b))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s' = IMAGE (\x:real^2. m % x + b) (ball(a,rho))` THEN
  SUBGOAL_THEN `open(s':real^2->bool) /\ bounded(s':real^2->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_AFFINITY THEN ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_NZ];
      MATCH_MP_TAC BOUNDED_AFFINITY THEN REWRITE_TAC[BOUNDED_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s' (U:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_CONT_W12_OPEN_BOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `U:real^2->real^K`; `m:real`; `b:real^2`] CMR_AFF_W12) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (\x. inv m % x + --(inv m % b)) (s':real^2->bool) = ball(a,rho)`
  SUBST1_TAC THENL
   [EXPAND_TAC "s'" THEN ASM_SIMP_TAC[CMR_AFF_IMAGE_INV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  DISCH_THEN(ACCEPT_TAC o CONJUNCT1));;

let CMR_DIL_DIR_TERM = prove
 (`!(U:real^2->real^K) (v:real^2->real^K) (a:real^2) rho m (b:real^2) m' (b':real^2) i.
     U continuous_on (:real^2) /\
     (!i. 1 <= i /\ i <= 2 ==> ?v. v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i U v) /\
     v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i U v /\
     &0 < m /\ &0 < m' /\ 1 <= i /\ i <= 2
     ==> drop(integral (ball(a,rho))
               (\x. lift(norm(wan_wd (ball(a,rho)) i
                               (\x. U(m % x + b) - U(m' % x + b')) x) pow 2))) =
         lnorm (ball(a,rho)) (&2) (\x. m % v(m % x + b) - m' % v(m' % x + b')) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. m % (v:real^2->real^K)(m % x + b) - m' % v(m' % x + b'))
    IN lspace (ball(a,rho)) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN
    CONJ_TAC THEN MATCH_MP_TAC LSPACE_CMUL THEN ASM_SIMP_TAC[CMR_DIL_LSPACE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `wan_w12 (ball(a,rho)) (\x. (U:real^2->real^K)(m % x + b) - U(m' % x + b'))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN CONJ_TAC THEN MATCH_MP_TAC CMR_DIL_W12 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->real^K`; `v:real^2->real^K`; `a:real^2`; `rho:real`;
                 `m':real`; `b':real^2`; `i:num`] CMR_DIL_WPD) THEN
  MP_TAC(ISPECL [`U:real^2->real^K`; `v:real^2->real^K`; `a:real^2`; `rho:real`;
                 `m:real`; `b:real^2`; `i:num`] CMR_DIL_WPD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d1 = wan_wd (IMAGE (\x. m % x + b) (ball(a,rho))) i (U:real^2->real^K)` THEN
  ABBREV_TAC `d2 = wan_wd (IMAGE (\x. m' % x + b') (ball(a,rho))) i (U:real^2->real^K)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `i:num`;
                 `\x. (U:real^2->real^K)(m % x + b)`;
                 `\x. m % (d1:real^2->real^K)(m % x + b)`;
                 `\x. (U:real^2->real^K)(m' % x + b')`;
                 `\x. m' % (d2:real^2->real^K)(m' % x + b')`] WAN_WPD_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `i:num`;
                 `\x. (U:real^2->real^K)(m % x + b) - U(m' % x + b')`;
                 `\x. m % (d1:real^2->real^K)(m % x + b) -
                      m' % (d2:real^2->real^K)(m' % x + b')`] WAN_WD_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN DISCH_TAC THEN
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC
   `{x | x IN ball(a,rho) /\
         ~(wan_wd (ball(a,rho)) i (\x. (U:real^2->real^K)(m % x + b) - U(m' % x + b')) x =
           m % (d1:real^2->real^K)(m % x + b) - m' % (d2:real^2->real^K)(m' % x + b'))} UNION
    {x | x IN ball(a,rho) /\ ~(d1(m % x + b) = (v:real^2->real^K)(m % x + b))} UNION
    {x | x IN ball(a,rho) /\ ~(d2(m' % x + b') = (v:real^2->real^K)(m' % x + b'))}` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_wd (ball(a,rho)) i (\x. (U:real^2->real^K)(m % x + b) - U(m' % x + b')) x =
    m % (d1:real^2->real^K)(m % x + b) - m' % (d2:real^2->real^K)(m' % x + b') /\
    d1(m % x + b) = (v:real^2->real^K)(m % x + b) /\
    d2(m' % x + b') = (v:real^2->real^K)(m' % x + b')`
  (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let CMR_DIL_DIR_SEQ = prove
 (`!(U:real^2->real^K) (a:real^2) rho (rn:num->real) (cn:num->real^2) r c.
     U continuous_on (:real^2) /\
     (!i. 1 <= i /\ i <= 2 ==> ?v. v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i U v) /\
     &0 < r /\ (!n. &0 < rn n) /\ (rn ---> r) sequentially /\ (cn --> c) sequentially
     ==> ((\n. wan_dir (ball(a,rho)) (\x. U(rn n % x + cn n) - U(r % x + c))) ---> &0)
         sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?v1:real^2->real^K. v1 IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) 1 U v1`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?v2:real^2->real^K. v2 IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) 2 U v2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `1 <= 2 /\ 2 <= 2`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_dir (ball(a,rho))
          (\x. (U:real^2->real^K)((rn:num->real) n % x + (cn:num->real^2) n) - U(r % x + c)) =
        lnorm (ball(a,rho)) (&2)
          (\x. rn n % (v1:real^2->real^K)(rn n % x + cn n) - r % v1(r % x + c)) pow 2 +
        lnorm (ball(a,rho)) (&2)
          (\x. rn n % (v2:real^2->real^K)(rn n % x + cn n) - r % v2(r % x + c)) pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[wan_dir; DIMINDEX_2; SUM_2] THEN
    BINOP_TAC THEN MATCH_MP_TAC CMR_DIL_DIR_TERM THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `&0 = &0 pow 2`] THEN
  MATCH_MP_TAC REALLIM_POW THEN MATCH_MP_TAC CMR_DIL_L2_SCALED THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Dirichlet integrals of maps that have L^2 weak partials but               *)
(* need not be L^2 themselves (chart pictures on the whole plane): the      *)
(* chosen partials, the sum formula, monotonicity in the open set, the     *)
(* bounds for sums and differences, vanishing, splitting along a circle,    *)
(* and the sphere-to-chart identity for differences of maps.              *)
(* ========================================================================= *)

let CMR_WD_WORKS_P = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v.
     v IN lspace s (&2) /\ wan_wpd s i u v
     ==> wan_wd s i u IN lspace s (&2) /\ wan_wpd s i u (wan_wd s i u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wan_wd] THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `v:real^N->real^K` THEN ASM_REWRITE_TAC[]);;

let CMR_W12_PARTIALS = prove
 (`!(s:real^N->bool) (u:real^N->real^K).
     wan_w12 s u
     ==> !i. 1 <= i /\ i <= dimindex(:N) ==> ?v. v IN lspace s (&2) /\ wan_wpd s i u v`,
  SIMP_TAC[wan_w12]);;

let CMR_DIR_EQ_P = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> v i IN lspace s (&2) /\ wan_wpd s i u (v i))
     ==> wan_dir s u =
         sum(1..dimindex(:N)) (\i. drop(integral s (\x. lift(norm(v i x) pow 2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN s /\ ~(wan_wd s i (u:real^N->real^K) x = v i x)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_WPD_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `u:real^N->real^K`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`;
                   `(v:num->real^N->real^K) i`] CMR_WD_WORKS_P) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]]);;

let CMR_DIR_POS_P = prove
 (`!(s:real^N->bool) (u:real^N->real^K).
     (!i. 1 <= i /\ i <= dimindex(:N) ==> ?v. v IN lspace s (&2) /\ wan_wpd s i u v)
     ==> &0 <= wan_dir s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->real^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`; `v:real^N->real^K`]
                CMR_WD_WORKS_P) THEN
  ASM_SIMP_TAC[ETA_AX]);;

let CMR_DIR_MONO_P = prove
 (`!(s:real^N->bool) t (u:real^N->real^K).
     open s /\ open t /\ t SUBSET s /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> ?v. v IN lspace s (&2) /\ wan_wpd s i u v)
     ==> wan_dir t u <= wan_dir s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->real^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`; `v:real^N->real^K`]
                CMR_WD_WORKS_P) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g = wan_wd s i (u:real^N->real^K)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^N->real^K) IN lspace t (&2) /\ wan_wpd t i (u:real^N->real^K) g`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
      MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `i:num`; `u:real^N->real^K`; `g:real^N->real^K`]
                CMR_WD_WORKS_P) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `i:num`; `u:real^N->real^K`;
                 `wan_wd t i (u:real^N->real^K)`; `g:real^N->real^K`] WAN_WPD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS `drop(integral t (\x. lift(norm((g:real^N->real^K) x) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN t /\ ~(wan_wd t i (u:real^N->real^K) x = g x)}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; LIFT_DROP; REAL_LE_POW_2]]);;

let CMR_DIR_ADD_LE_P = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> ?g. g IN lspace s (&2) /\ wan_wpd s i u g) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> ?g. g IN lspace s (&2) /\ wan_wpd s i v g)
     ==> (!i. 1 <= i /\ i <= dimindex(:N)
              ==> ?g. g IN lspace s (&2) /\ wan_wpd s i (\x. u x + v x) g) /\
         wan_dir s (\x. u x + v x) <= &2 * wan_dir s u + &2 * wan_dir s v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\x. wan_wd s i (u:real^N->real^K) x + wan_wd s i (v:real^N->real^K) x)
            IN lspace s (&2) /\
            wan_wpd s i (\x. u x + v x)
              (\x. wan_wd s i (u:real^N->real^K) x + wan_wd s i (v:real^N->real^K) x) /\
            wan_wd s i u IN lspace s (&2) /\ wan_wd s i v IN lspace s (&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:real^N->real^K` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `g2:real^N->real^K` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`; `g1:real^N->real^K`]
                  CMR_WD_WORKS_P) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `v:real^N->real^K`; `g2:real^N->real^K`]
                  CMR_WD_WORKS_P) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
      MATCH_MP_TAC WAN_WPD_ADD THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    EXISTS_TAC `\x. wan_wd s i (u:real^N->real^K) x + wan_wd s i (v:real^N->real^K) x` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. (u:real^N->real^K) x + v x`;
                 `\i x. wan_wd s i (u:real^N->real^K) x + wan_wd s i (v:real^N->real^K) x`]
                CMR_DIR_EQ_P) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dir; GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s (\x. &2 % lift(norm(wan_wd s i (u:real^N->real^K) x) pow 2) +
                                   &2 % lift(norm(wan_wd s i (v:real^N->real^K) x) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; INTEGRABLE_CMUL; INTEGRABLE_ADD; ETA_AX] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    MP_TAC(ISPECL [`wan_wd s i (u:real^N->real^K) x`; `wan_wd s i (v:real^N->real^K) x`]
                  WAN_NORM_ADD_SUB_POW2) THEN
    MP_TAC(ISPEC `norm(wan_wd s i (u:real^N->real^K) x - wan_wd s i (v:real^N->real^K) x)`
                 REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRABLE_CMUL; WAN_LSPACE2_SQNORM_INTEGRABLE;
                 DROP_ADD; DROP_CMUL; REAL_LE_REFL; ETA_AX]]);;

let CMR_DIR_SUB_LE_P = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> ?g. g IN lspace s (&2) /\ wan_wpd s i u g) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> ?g. g IN lspace s (&2) /\ wan_wpd s i v g)
     ==> (!i. 1 <= i /\ i <= dimindex(:N)
              ==> ?g. g IN lspace s (&2) /\ wan_wpd s i (\x. u x - v x) g) /\
         wan_dir s (\x. u x - v x) <= &2 * wan_dir s u + &2 * wan_dir s v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\x. wan_wd s i (u:real^N->real^K) x - wan_wd s i (v:real^N->real^K) x)
            IN lspace s (&2) /\
            wan_wpd s i (\x. u x - v x)
              (\x. wan_wd s i (u:real^N->real^K) x - wan_wd s i (v:real^N->real^K) x) /\
            wan_wd s i u IN lspace s (&2) /\ wan_wd s i v IN lspace s (&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:real^N->real^K` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `g2:real^N->real^K` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`; `g1:real^N->real^K`]
                  CMR_WD_WORKS_P) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `v:real^N->real^K`; `g2:real^N->real^K`]
                  CMR_WD_WORKS_P) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
      MATCH_MP_TAC WAN_WPD_SUB THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    EXISTS_TAC `\x. wan_wd s i (u:real^N->real^K) x - wan_wd s i (v:real^N->real^K) x` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. (u:real^N->real^K) x - v x`;
                 `\i x. wan_wd s i (u:real^N->real^K) x - wan_wd s i (v:real^N->real^K) x`]
                CMR_DIR_EQ_P) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dir; GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s (\x. &2 % lift(norm(wan_wd s i (u:real^N->real^K) x) pow 2) +
                                   &2 % lift(norm(wan_wd s i (v:real^N->real^K) x) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; INTEGRABLE_CMUL; INTEGRABLE_ADD; ETA_AX] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    MP_TAC(ISPECL [`wan_wd s i (u:real^N->real^K) x`; `wan_wd s i (v:real^N->real^K) x`]
                  WAN_NORM_ADD_SUB_POW2) THEN
    MP_TAC(ISPEC `norm(wan_wd s i (u:real^N->real^K) x + wan_wd s i (v:real^N->real^K) x)`
                 REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRABLE_CMUL; WAN_LSPACE2_SQNORM_INTEGRABLE;
                 DROP_ADD; DROP_CMUL; REAL_LE_REFL; ETA_AX]]);;

let CMR_DIR_ZERO_ON = prove
 (`!(s:real^N->bool) (u:real^N->real^K).
     open s /\ (!x. x IN s ==> u x = vec 0) ==> wan_dir s u = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `\x:real^N. vec 0:real^K`]
                CMW_DIR_EQ_ON) THEN
  ASM_SIMP_TAC[WAN_DIR_ZERO]);;

let CMR_GCOND_ID = prove
 (`CMR_GCOND (\y:real^K. mat 1) (&1)`,
  REWRITE_TAC[CMR_GCOND; o_DEF; CONTINUOUS_ON_CONST; TRANSP_MAT;
              MATRIX_VECTOR_MUL_LID; NORM_POW_2; REAL_MUL_LID; REAL_LE_REFL; DOT_POS_LE]);;

let CMR_DIR_SPLIT_ID = prove
 (`!(v:real^2->real^K) (c:real^2) r.
     wan_lloc (:real^2) v /\
     (!i. 1 <= i /\ i <= 2 ==> ?g. g IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i v g)
     ==> wan_dir (:real^2) v =
         wan_dir (ball(c,r)) v + wan_dir ((:real^2) DIFF cball(c,r)) v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `v:real^2->real^K`; `&1`; `c:real^2`; `r:real`]
                CMR_GDIR_SPLIT) THEN
  ASM_REWRITE_TAC[CMR_GCOND_ID; WAN_GDIR_ID]);;

let CMR_S2_DIR_CHART = prove
 (`!(u:real^3->real^K) (Q:real^3^3).
     orthogonal_matrix Q /\ wan_s2_w12 u
     ==> wan_dir wan_shell (wan_rext u) = &3 / &2 * wan_dir (:real^2) (\x. u(cm_capmap Q x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `u:real^3->real^K`; `Q:real^3^3`; `&1`]
                CMR_SEN_CHART) THEN
  ASM_REWRITE_TAC[CMR_GCOND_ID; cm_sen; WAN_GDIR_ID] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH `a / &3 = b / &2 ==> a = &3 / &2 * b`) o
             CONJUNCT2) THEN
  REFL_TAC);;

let CMR_REXT_SUB = prove
 (`!(u1:real^3->real^K) u2.
     (\z. wan_rext u1 z - wan_rext u2 z) = wan_rext (\y. u1 y - u2 y)`,
  REWRITE_TAC[FUN_EQ_THM; wan_rext]);;

let CMR_S2_W12_SUB = prove
 (`!(u1:real^3->real^K) u2.
     wan_s2_w12 u1 /\ wan_s2_w12 u2 ==> wan_s2_w12 (\y. u1 y - u2 y)`,
  REWRITE_TAC[wan_s2_w12; GSYM CMR_REXT_SUB] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX]);;

let CMR_S2_DIR_DIFF_CHART = prove
 (`!(u1:real^3->real^K) u2 (Q:real^3^3).
     orthogonal_matrix Q /\ wan_s2_w12 u1 /\ wan_s2_w12 u2
     ==> wan_dir wan_shell (\z. wan_rext u1 z - wan_rext u2 z) =
         &3 / &2 * wan_dir (:real^2) (\x. u1(cm_capmap Q x) - u2(cm_capmap Q x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CMR_REXT_SUB] THEN
  MP_TAC(ISPECL [`\y. (u1:real^3->real^K) y - u2 y`; `Q:real^3^3`] CMR_S2_DIR_CHART) THEN
  ASM_SIMP_TAC[CMR_S2_W12_SUB]);;


(* ========================================================================= *)
(* Zero extensions, the rescaled chart data on the unit disc,                *)
(* the rescaling identity for chart minimizers, and the representation of   *)
(* a one-cap replacement in the chart as  U + zt o psi,  where zt is the    *)
(* zero extension of (minimizer - data) on the unit disc and psi the        *)
(* similarity taking ball(c,r) onto the unit disc.                          *)
(* ========================================================================= *)

let cmr_dat = new_definition
 `cmr_dat (Q:real^3^3) (c:real^2) r (u:real^3->real^K) =
    \x:real^2. u(cm_capmap Q (r % x + c))`;;

let cmr_zt = new_definition
 `cmr_zt S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K) =
    \x:real^2. if x IN ball(vec 0,&1)
               then cmr_minw S G (vec 0) (&1) (cmr_dat Q c r u) x - cmr_dat Q c r u x
               else vec 0`;;

let CMR_LSPACE_ZERO_EXT = prove
 (`!(f:real^N->real^K) s p.
     &0 < p /\ f IN lspace s p
     ==> (\x. if x IN s then f x else vec 0) IN lspace (:real^N) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MEASURABLE_ON_UNIV] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((if x IN s then (f:real^N->real^K) x else vec 0)) rpow p)) =
    (\x. if x IN s then lift(norm(f x) rpow p) else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[NORM_0; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM];
    ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV]]);;

let CMR_ZEXT_PARTIALS = prove
 (`!(b:real^N->bool) (h:real^N->real^K).
     open b /\ wan_w120 b h
     ==> (\x. if x IN b then h x else vec 0) IN lspace (:real^N) (&2) /\
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> (\x. if x IN b then wan_wd b i h x else vec 0) IN lspace (:real^N) (&2) /\
                 wan_wpd (:real^N) i (\x. if x IN b then h x else vec 0)
                   (\x. if x IN b then wan_wd b i h x else vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `h:real^N->real^K`] WAN_W120_ZERO_EXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC CMR_LSPACE_ZERO_EXT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `i:num`; `h:real^N->real^K`] WAN_WD_WORKS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[wan_w120]; SIMP_TAC[]]);;

let CMR_ZEXT_DIR = prove
 (`!(b:real^N->bool) (h:real^N->real^K).
     open b /\ wan_w120 b h
     ==> wan_dir (:real^N) (\x. if x IN b then h x else vec 0) = wan_dir b h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `h:real^N->real^K`] CMR_ZEXT_PARTIALS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\x. if x IN b then (h:real^N->real^K) x else vec 0`;
                 `\i x. if x IN b then wan_wd b i (h:real^N->real^K) x else vec 0`]
                CMR_DIR_EQ_P) THEN
  ASM_SIMP_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dir] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(norm(if x IN b then wan_wd b i (h:real^N->real^K) x else vec 0) pow 2)) =
    (\x. if x IN b then lift(norm(wan_wd b i h x) pow 2) else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN
    REWRITE_TAC[NORM_0; LIFT_NUM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[LIFT_NUM];
    REWRITE_TAC[INTEGRAL_RESTRICT_UNIV]]);;

let CMR_AFF_IN_BALL = prove
 (`!(c:real^2) r x.
     &0 < r
     ==> (inv r % x + --(inv r % c) IN ball(vec 0,&1) <=> x IN ball(c,r)) /\
         (inv r % x + --(inv r % c) IN cball(vec 0,&1) <=> x IN cball(c,r)) /\
         (inv r % x + --(inv r % c) IN sphere(vec 0,&1) <=> x IN sphere(c,r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[IN_BALL_0; IN_CBALL_0; IN_SPHERE_0; IN_BALL; IN_CBALL; IN_SPHERE] THEN
  REWRITE_TAC[VECTOR_ARITH `inv r % (x:real^2) + --(inv r % c) = inv r % (x - c)`] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_LDIV_EQ; REAL_EQ_LDIV_EQ; REAL_MUL_LID] THEN
  REWRITE_TAC[dist] THEN MESON_TAC[NORM_SUB]);;

let CMR_AFF_UNIT_IMAGE = prove
 (`!(c:real^2) r.
     &0 < r ==> IMAGE (\x. inv r % x + --(inv r % c)) (ball(c,r)) = ball(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CMR_AFF_BALLS; VECTOR_ADD_RINV; REAL_DIV_REFL; REAL_LT_IMP_NZ]);;

let CMR_DAT_FACTS = prove
 (`!S (G:real^K->real^K^K) Lam (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\ CMR_GCOND G Lam
     ==> cm_cmap S (ball(vec 0,&1)) (cmr_dat Q c r u) /\
         wan_gdir (ball(vec 0,&1)) G (cmr_dat Q c r u) =
         wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) /\
         cmr_dat Q c r u continuous_on (:real^2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `Q:real^3^3`; `c:real^2`; `r:real`]
                CMR_CHART_CMAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `wan_w12 (ball(c:real^2,r)) (\x. (u:real^3->real^K)(cm_capmap Q x))`
  ASSUME_TAC THENL [ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `ball(c:real^2,r)`;
                   `\x. (u:real^3->real^K)(cm_capmap Q x)`; `r:real`; `c:real^2`]
                  CMR_AFF_CMAP) THEN
    ASM_SIMP_TAC[OPEN_BALL; CMR_AFF_UNIT_IMAGE; cmr_dat];
    MP_TAC(ISPECL [`ball(c:real^2,r)`; `G:real^K->real^K^K`;
                   `\x. (u:real^3->real^K)(cm_capmap Q x)`; `Lam:real`; `r:real`; `c:real^2`]
                  CMR_AFF_GDIR) THEN
    ASM_SIMP_TAC[OPEN_BALL; CMR_AFF_UNIT_IMAGE; cmr_dat];
    REWRITE_TAC[cmr_dat] THEN
    MP_TAC(ISPECL [`u:real^3->real^K`; `Q:real^3^3`] CMR_CHART_CONT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\y. (u:real^3->real^K)(cm_capmap Q y)`; `r:real`; `c:real^2`;
                   `(:real^2)`] CMR_CONT_AFF_COMPOSE) THEN
    ASM_REWRITE_TAC[]]);;

let CMR_MINW_SCALE = prove
 (`!S (G:real^K->real^K^K) e Lam (c:real^2) r (f:real^2->real^K).
     cmw_repex S G e /\ cmw_repcont S G e /\ CMR_GCOND G Lam /\ &0 < r /\
     cm_cmap S (ball(c,r)) f /\ wan_gdir (ball(c,r)) G f <= e
     ==> !x. x IN cball(c,r)
             ==> cmr_minw S G c r f x =
                 cmr_minw S G (vec 0) (&1) (\y. f(r % y + c)) (inv r % x + --(inv r % c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `r:real`;
                 `f:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = cmr_minw S G (c:real^2) r (f:real^2->real^K)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 (ball(c:real^2,r)) (f:real^2->real^K) /\
                wan_w12 (ball(c:real^2,r)) (M:real^2->real^K)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `ball(c:real^2,r)`; `f:real^2->real^K`; `r:real`; `c:real^2`]
                CMR_AFF_CMAP) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `ball(c:real^2,r)`; `M:real^2->real^K`; `r:real`; `c:real^2`]
                CMR_AFF_CMAP) THEN
  MP_TAC(ISPECL [`ball(c:real^2,r)`; `G:real^K->real^K^K`; `f:real^2->real^K`; `Lam:real`;
                 `r:real`; `c:real^2`] CMR_AFF_GDIR) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `ball(c:real^2,r)`; `M:real^2->real^K`;
                 `Lam:real`; `r:real`; `c:real^2`] CMR_AFF_MINIMIZER) THEN
  ASM_SIMP_TAC[OPEN_BALL; CMR_AFF_UNIT_IMAGE] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!x. x IN cball(vec 0,&1)
        ==> (M:real^2->real^K)(r % x + c) =
            cmr_minw S G (vec 0) (&1) (\y. (f:real^2->real^K)(r % y + c)) x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `vec 0:real^2`; `&1`;
                   `\y. (f:real^2->real^K)(r % y + c)`; `\y. (M:real^2->real^K)(r % y + c)`]
                  CMR_MINW_UNIQUE) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN ANTS_TAC THENL
     [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`c:real^2`; `r:real`; `r % y + c:real^2`] CMR_AFF_IN_BALL) THEN
      ASM_SIMP_TAC[CMR_AFF_INV; REAL_LT_IMP_NZ];
      SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv r % z + --(inv r % c):real^2`) THEN
  ASM_SIMP_TAC[CMR_AFF_IN_BALL; CMR_AFF_INV; REAL_LT_IMP_NZ]);;

let CMR_REP1_REPR = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ cmw_repcont S G e /\ CMR_GCOND G Lam /\
     cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\
     wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> !x. cmr_rep1 S G Q c r u (cm_capmap Q x) =
             u(cm_capmap Q x) + cmr_zt S G Q c r u (inv r % x + --(inv r % c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN
  ASM_SIMP_TAC[CMR_REP1_CHART] THEN REWRITE_TAC[cmr_zt] THEN
  ASM_SIMP_TAC[CMR_AFF_IN_BALL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_RID] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `c:real^2`;
                 `r:real`; `\x. (u:real^3->real^K)(cm_capmap Q x)`] CMR_MINW_SCALE) THEN
  ASM_SIMP_TAC[CMR_CHART_CMAP] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[cmr_dat] THEN
  ASM_SIMP_TAC[CMR_AFF_INV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ARITH `(a:real^N) + (b - a) = b`]);;

let CMR_ZT_FACTS = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\
     cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\
     wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> cmr_zt S G Q c r u continuous_on (:real^2) /\
         (!x. ~(x IN ball(vec 0,&1)) ==> cmr_zt S G Q c r u x = vec 0) /\
         wan_w120 (ball(vec 0,&1))
           (\x. cmr_minw S G (vec 0) (&1) (cmr_dat Q c r u) x - cmr_dat Q c r u x) /\
         cmr_zt S G Q c r u IN lspace (:real^2) (&2) /\
         (!i. 1 <= i /\ i <= 2
              ==> ?v. v IN lspace (:real^2) (&2) /\
                      wan_wpd (:real^2) i (cmr_zt S G Q c r u) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `Q:real^3^3`; `c:real^2`;
                 `r:real`; `u:real^3->real^K`] CMR_DAT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = cmr_dat (Q:real^3^3) (c:real^2) r (u:real^3->real^K)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `vec 0:real^2`; `&1`;
                 `V:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  ABBREV_TAC `W = cmr_minw S G (vec 0:real^2) (&1) (V:real^2->real^K)` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `cmr_zt S G (Q:real^3^3) (c:real^2) r (u:real^3->real^K) =
    (\x. if x IN ball(vec 0,&1) then (W:real^2->real^K) x - V x else vec 0)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[cmr_zt]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\x. (W:real^2->real^K) x - V x`]
                CMR_ZEXT_PARTIALS) THEN
  ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^2. x IN ball(vec 0,&1)`; `\x. (W:real^2->real^K) x - V x`;
                   `\x:real^2. vec 0:real^K`; `cball(vec 0:real^2,&1)`;
                   `(:real^2) DIFF ball(vec 0,&1)`] CONTINUOUS_ON_CASES) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `cball(vec 0:real^2,&1) UNION ((:real^2) DIFF ball(vec 0,&1)) = (:real^2)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[CLOSED_CBALL; CONTINUOUS_ON_CONST; GSYM OPEN_CLOSED; OPEN_BALL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [UNDISCH_TAC `cm_cmap S (ball(vec 0:real^2,&1)) (W:real^2->real^K)` THEN
        SIMP_TAC[cm_cmap; CLOSURE_BALL; REAL_LT_01];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      ASM_CASES_TAC `(x:real^2) IN ball(vec 0,&1)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN sphere(vec 0,&1)` (fun th -> ASM_SIMP_TAC[th; VECTOR_SUB_REFL]) THEN
      UNDISCH_TAC `(x:real^2) IN cball(vec 0,&1)` THEN
      UNDISCH_TAC `~((x:real^2) IN ball(vec 0,&1))` THEN
      REWRITE_TAC[IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC];
    SIMP_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    EXISTS_TAC `\x. if x IN ball(vec 0,&1)
                    then wan_wd (ball(vec 0,&1)) i (\x. (W:real^2->real^K) x - V x) x
                    else vec 0` THEN
    ASM_SIMP_TAC[]]);;


(* ========================================================================= *)
(* Convergence of the rescaled data and of the zero-extended                 *)
(* corrections: uniform convergence of the data on discs, Dirichlet         *)
(* convergence of the data on the unit disc, small data energy on           *)
(* shrinking discs, continuity of the rescaled zero extension under a       *)
(* converging radius, and the uniform convergence of the corrections        *)
(* (via clause 2 of CM_REPLACEMENT for positive limit radius, via CMW_C0EST  *)
(* for limit radius 0).                                                      *)
(* ========================================================================= *)

let CMR_DAT_UNIF = prove
 (`!(Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0 (rn:num->real) r0 M.
     orthogonal_matrix Q /\ u0 continuous_on sphere(vec 0,&1) /\
     (!e. &0 < e
          ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u0 y) < e)
                         sequentially) /\
     (rn ---> r0) sequentially
     ==> !e. &0 < e
             ==> eventually
                   (\n. !x. x IN cball(vec 0,M)
                            ==> norm(cmr_dat Q c (rn n) (un n) x - cmr_dat Q c r0 u0 x) < e)
                   sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[cmr_dat] THEN
  MP_TAC(ISPECL [`u0:real^3->real^K`; `Q:real^3^3`] CMR_CHART_CONT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ABBREV_TAC `R0 = (abs r0 + &1) * abs M + norm(c:real^2)` THEN
  MP_TAC(ISPECL [`\x. (u0:real^3->real^K)(cm_capmap Q x)`; `cball(vec 0:real^2,R0)`]
                COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `eventually (\n. abs((rn:num->real) n - r0) < min (&1) (dd / (abs M + &1))) sequentially`
  MP_TAC THENL
   [UNDISCH_TAC `(rn ---> r0) sequentially` THEN REWRITE_TAC[tendsto_real] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_var t && fst(dest_var t) = "un")) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_CBALL_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((rn:num->real) n - r0) * (abs M + &1) < dd` ASSUME_TAC THENL
   [UNDISCH_TAC `abs((rn:num->real) n - r0) < dd / (abs M + &1)` THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs M + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x:real^2) <= abs M` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(((u0:real^3->real^K)(cm_capmap Q ((rn:num->real) n % x + c))) -
         u0(cm_capmap Q (r0 % x + c))) < e / &2`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_CBALL_0; dist] THEN
    REWRITE_TAC[VECTOR_ARITH `(r0 % x + c) - (rn % x + c):real^2 = (r0 - rn) % x`] THEN
    REWRITE_TAC[NORM_MUL] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "R0" THEN
      MATCH_MP_TAC(NORM_ARITH `norm(a:real^2) <= b ==> norm(a + c) <= b + norm c`) THEN
      REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "R0" THEN
      MATCH_MP_TAC(NORM_ARITH `norm(a:real^2) <= b ==> norm(a + c) <= b + norm c`) THEN
      REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `abs((rn:num->real) n - r0) * (abs M + &1)` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((un:num->real^3->real^K) n (cm_capmap Q ((rn:num->real) n % x + c)) -
         u0(cm_capmap Q (rn n % x + c))) < e / &2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`norm((un:num->real^3->real^K) n (cm_capmap Q ((rn:num->real) n % x + c)) -
          u0(cm_capmap Q (rn n % x + c))) < e / &2`;
    `norm(((u0:real^3->real^K)(cm_capmap Q ((rn:num->real) n % x + c))) -
          u0(cm_capmap Q (r0 % x + c))) < e / &2`] THEN
  CONV_TAC NORM_ARITH);;

let CMR_CHART_DIFF_FACTS = prove
 (`!(u1:real^3->real^K) u2 (Q:real^3^3).
     orthogonal_matrix Q /\
     u1 continuous_on sphere(vec 0,&1) /\ wan_s2_w12 u1 /\
     u2 continuous_on sphere(vec 0,&1) /\ wan_s2_w12 u2
     ==> (\x. u1(cm_capmap Q x) - u2(cm_capmap Q x)) continuous_on (:real^2) /\
         wan_lloc (:real^2) (\x. u1(cm_capmap Q x) - u2(cm_capmap Q x)) /\
         (!i. 1 <= i /\ i <= 2
              ==> ?v. v IN lspace (:real^2) (&2) /\
                      wan_wpd (:real^2) i (\x. u1(cm_capmap Q x) - u2(cm_capmap Q x)) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN MATCH_MP_TAC CMR_CHART_CONT THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`\y. (u1:real^3->real^K) y - u2 y`; `Q:real^3^3`] CMR_CHART_W12LOC) THEN
    ASM_SIMP_TAC[CMR_S2_W12_SUB]]);;

let CMR_DAT_DIR_POS = prove
 (`!S (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0 (rn:num->real) r0.
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (!n. &0 < rn n) /\ &0 < r0 /\ (rn ---> r0) sequentially
     ==> ((\n. wan_dir (ball(vec 0,&1))
                 (\x. cmr_dat Q c (rn n) (un n) x - cmr_dat Q c r0 u0 x)) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_smap; FORALL_AND_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (u0:real^3->real^K)(cm_capmap Q x)) continuous_on (:real^2) /\
    (!i. 1 <= i /\ i <= 2
         ==> ?v. v IN lspace (:real^2) (&2) /\
                 wan_wpd (:real^2) i (\x. (u0:real^3->real^K)(cm_capmap Q x)) v)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CMR_CHART_CONT THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`u0:real^3->real^K`; `Q:real^3^3`] CMR_CHART_W12LOC) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. (un:num->real^3->real^K) n (cm_capmap Q x) - u0(cm_capmap Q x))
          continuous_on (:real^2) /\
        wan_lloc (:real^2) (\x. un n (cm_capmap Q x) - u0(cm_capmap Q x)) /\
        (!i. 1 <= i /\ i <= 2
             ==> ?v. v IN lspace (:real^2) (&2) /\
                     wan_wpd (:real^2) i
                       (\x. un n (cm_capmap Q x) - u0(cm_capmap Q x)) v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CMR_CHART_DIFF_FACTS THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (u0:real^3->real^K)(cm_capmap Q x)`; `vec 0:real^2`; `&1`;
                 `rn:num->real`; `\n:num. (c:real^2)`; `r0:real`; `c:real^2`]
                CMR_DIL_DIR_SEQ) THEN
  ASM_REWRITE_TAC[LIM_CONST] THEN DISCH_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. &4 / &3 * wan_dir wan_shell
                              (\z. wan_rext ((un:num->real^3->real^K) n) z - wan_rext u0 z) +
                  &2 * wan_dir (ball(vec 0,&1))
                         (\x. (u0:real^3->real^K)(cm_capmap Q ((rn:num->real) n % x + c)) -
                              u0(cm_capmap Q (r0 % x + c)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_var t && fst(dest_var t) = "un")) (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_lloc"))
                         (concl th))) THEN
  ABBREV_TAC `D = \x. (un:num->real^3->real^K) n (cm_capmap Q x) - u0(cm_capmap Q x)` THEN
  SUBGOAL_THEN
   `wan_w12 (ball(vec 0:real^2,&1)) (\x. (D:real^2->real^K)((rn:num->real) n % x + c)) /\
    wan_w12 (ball(vec 0:real^2,&1))
      (\x. (u0:real^3->real^K)(cm_capmap Q ((rn:num->real) n % x + c)) -
           u0(cm_capmap Q (r0 % x + c)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CMR_DIL_W12 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUB THEN CONJ_TAC THEN
      MP_TAC(ISPECL [`\x. (u0:real^3->real^K)(cm_capmap Q x)`; `vec 0:real^2`; `&1`]
                    CMR_DIL_W12) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir (ball(vec 0:real^2,&1))
      (\x. cmr_dat Q c ((rn:num->real) n) ((un:num->real^3->real^K) n) x -
           cmr_dat Q c r0 u0 x) =
    wan_dir (ball(vec 0:real^2,&1))
      (\x. (D:real^2->real^K)((rn:num->real) n % x + c) +
           ((u0:real^3->real^K)(cm_capmap Q (rn n % x + c)) - u0(cm_capmap Q (r0 % x + c))))`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; cmr_dat] THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\x. (D:real^2->real^K)((rn:num->real) n % x + c)`;
                 `\x. (u0:real^3->real^K)(cm_capmap Q ((rn:num->real) n % x + c)) -
                      u0(cm_capmap Q (r0 % x + c))`] CMR_DIR_ADD_LE_P) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN MATCH_MP_TAC CMR_W12_PARTIALS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE o CONJUNCT2) THEN
  SUBGOAL_THEN
   `wan_dir (ball(vec 0:real^2,&1)) (\x. (D:real^2->real^K)((rn:num->real) n % x + c)) <=
    &2 / &3 * wan_dir wan_shell (\z. wan_rext ((un:num->real^3->real^K) n) z - wan_rext u0 z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(c:real^2,(rn:num->real) n)`; `D:real^2->real^K`; `(rn:num->real) n`;
                   `c:real^2`] CMR_AFF_DIR) THEN
    ASM_SIMP_TAC[OPEN_BALL; CMR_AFF_UNIT_IMAGE] THEN ANTS_TAC THENL
     [MATCH_MP_TAC CMR_CONT_W12_OPEN_BOUNDED THEN
      ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`un (n:num):real^3->real^K`; `u0:real^3->real^K`; `Q:real^3^3`]
                  CMR_S2_DIR_DIFF_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= &2 / &3 * (&3 / &2 * b)`) THEN
    MATCH_MP_TAC CMR_DIR_MONO_P THEN
    ASM_REWRITE_TAC[OPEN_UNIV; OPEN_BALL; SUBSET_UNIV; DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= wan_dir (ball(vec 0:real^2,&1))
           (\x. (D:real^2->real^K)((rn:num->real) n % x + c) +
                ((u0:real^3->real^K)(cm_capmap Q (rn n % x + c)) -
                 u0(cm_capmap Q (r0 % x + c))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_ADD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMR_SQ_INTEGRAL_SMALL = prove
 (`!(g:real^2->real^K) eps.
     g IN lspace (:real^2) (&2) /\ &0 < eps
     ==> ?d. &0 < d /\
             !a r. &0 <= r /\ r < d
                   ==> drop(integral (ball(a,r)) (\x. lift(norm(g x) pow 2))) < eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift(norm((g:real^2->real^K) x) pow 2)`; `(:real^2)`; `eps:real`]
                ABSOLUTELY_CONTINUOUS_INTEGRAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_EQ_INTEGRABLE_POS; LIFT_DROP; REAL_LE_POW_2;
                 WAN_LSPACE2_SQNORM_INTEGRABLE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (&1) (d1 / &4)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ball(a:real^2,r)`) THEN
  REWRITE_TAC[SUBSET_UNIV; MEASURABLE_BALL; NORM_1] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`] MEASURE_BALL_BOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN
  SUBGOAL_THEN `r * r <= r` MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;

let CMR_DAT_DIR_ZERO = prove
 (`!S (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0 (rn:num->real).
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (rn ---> &0) sequentially
     ==> !eps. &0 < eps
               ==> eventually
                     (\n. &0 < rn n
                          ==> wan_dir (ball(vec 0,&1)) (cmr_dat Q c (rn n) (un n)) < eps)
                     sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_smap; FORALL_AND_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u0:real^3->real^K`; `Q:real^3^3`] CMR_CHART_W12LOC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?v1:real^2->real^K. v1 IN lspace (:real^2) (&2) /\
                        wan_wpd (:real^2) 1 (\x. (u0:real^3->real^K)(cm_capmap Q x)) v1`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?v2:real^2->real^K. v2 IN lspace (:real^2) (&2) /\
                        wan_wpd (:real^2) 2 (\x. (u0:real^3->real^K)(cm_capmap Q x)) v2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ARITH_RULE `1 <= 2 /\ 2 <= 2`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v1:real^2->real^K`; `eps / &8`] CMR_SQ_INTEGRAL_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v2:real^2->real^K`; `eps / &8`] CMR_SQ_INTEGRAL_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `eventually (\n. abs((rn:num->real) n - &0) < min d1 d2) sequentially`
  MP_TAC THENL
   [UNDISCH_TAC `(rn ---> &0) sequentially` THEN REWRITE_TAC[tendsto_real] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_MIN];
    ALL_TAC] THEN
  UNDISCH_TAC
   `((\n. wan_dir wan_shell (\z. wan_rext ((un:num->real^3->real^K) n) z - wan_rext u0 z))
     ---> &0) sequentially` THEN
  REWRITE_TAC[tendsto_real] THEN DISCH_THEN(MP_TAC o SPEC `eps / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[REAL_SUB_RZERO; REAL_LT_MIN] THEN STRIP_TAC THEN
  DISCH_TAC THEN
  ABBREV_TAC `D = \x. (un:num->real^3->real^K) n (cm_capmap Q x) - u0(cm_capmap Q x)` THEN
  MP_TAC(ISPECL [`un (n:num):real^3->real^K`; `u0:real^3->real^K`; `Q:real^3^3`]
                CMR_CHART_DIFF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (u0:real^3->real^K)(cm_capmap Q x)) continuous_on (:real^2) /\
    (\x. (un:num->real^3->real^K) n (cm_capmap Q x)) continuous_on (:real^2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CMR_CHART_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> ?v. v IN lspace (:real^2) (&2) /\
                wan_wpd (:real^2) i (\x. (un:num->real^3->real^K) n (cm_capmap Q x)) v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`un (n:num):real^3->real^K`; `Q:real^3^3`] CMR_CHART_W12LOC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w12 (ball(c:real^2,(rn:num->real) n)) (D:real^2->real^K) /\
    wan_w12 (ball(c:real^2,(rn:num->real) n)) (\x. (u0:real^3->real^K)(cm_capmap Q x)) /\
    wan_w12 (ball(c:real^2,(rn:num->real) n))
      (\x. (un:num->real^3->real^K) n (cm_capmap Q x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CMR_CONT_W12_OPEN_BOUNDED THEN
    ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN EXPAND_TAC "D" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(c:real^2,(rn:num->real) n)`;
                 `\x. (un:num->real^3->real^K) n (cm_capmap Q x)`; `(rn:num->real) n`;
                 `c:real^2`] CMR_AFF_DIR) THEN
  ASM_SIMP_TAC[OPEN_BALL; CMR_AFF_UNIT_IMAGE] THEN
  REWRITE_TAC[GSYM cmr_dat] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `wan_dir (ball(c:real^2,(rn:num->real) n)) (\x. (un:num->real^3->real^K) n (cm_capmap Q x)) =
    wan_dir (ball(c,rn n)) (\x. (D:real^2->real^K) x + u0(cm_capmap Q x))`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN EXPAND_TAC "D" THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(c:real^2,(rn:num->real) n)`; `D:real^2->real^K`;
                 `\x. (u0:real^3->real^K)(cm_capmap Q x)`] CMR_DIR_ADD_LE_P) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN MATCH_MP_TAC CMR_W12_PARTIALS THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o BETA_RULE o CONJUNCT2)] THEN
  SUBGOAL_THEN
   `wan_dir (ball(c:real^2,(rn:num->real) n)) (D:real^2->real^K) <=
    &2 / &3 * wan_dir wan_shell (\z. wan_rext ((un:num->real^3->real^K) n) z - wan_rext u0 z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`un (n:num):real^3->real^K`; `u0:real^3->real^K`; `Q:real^3^3`]
                  CMR_S2_DIR_DIFF_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= &2 / &3 * (&3 / &2 * b)`) THEN
    MATCH_MP_TAC CMR_DIR_MONO_P THEN
    ASM_REWRITE_TAC[OPEN_UNIV; OPEN_BALL; SUBSET_UNIV; DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir (ball(c:real^2,(rn:num->real) n)) (\x. (u0:real^3->real^K)(cm_capmap Q x)) <
    eps / &4`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(c:real^2,(rn:num->real) n)`;
                   `\x. (u0:real^3->real^K)(cm_capmap Q x)`;
                   `\i:num. if i = 1 then (v1:real^2->real^K) else v2`] CMR_DIR_EQ_P) THEN
    REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN
      (CONJ_TAC THENL
        [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
         ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN; OPEN_BALL];
         MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
         ASM_REWRITE_TAC[SUBSET_UNIV]]);
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[SUM_2; ARITH] THEN
    MATCH_MP_TAC(REAL_ARITH `a < e / &8 /\ b < e / &8 ==> a + b < e / &4`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMR_DAT_MINW_FACTS = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\
     cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\
     wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> cm_cmap S (ball(vec 0,&1)) (cmr_dat Q c r u) /\
         wan_gdir (ball(vec 0,&1)) G (cmr_dat Q c r u) <= e /\
         cmr_dat Q c r u continuous_on (:real^2) /\
         cm_minimizer S G (ball(vec 0,&1)) (cmr_minw S G (vec 0) (&1) (cmr_dat Q c r u)) /\
         cm_cmap S (ball(vec 0,&1)) (cmr_minw S G (vec 0) (&1) (cmr_dat Q c r u)) /\
         (!x. x IN sphere(vec 0,&1)
              ==> cmr_minw S G (vec 0) (&1) (cmr_dat Q c r u) x = cmr_dat Q c r u x) /\
         wan_w120 (ball(vec 0,&1))
           (\x. cmr_minw S G (vec 0) (&1) (cmr_dat Q c r u) x - cmr_dat Q c r u x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Lam:real`; `Q:real^3^3`; `c:real^2`;
                 `r:real`; `u:real^3->real^K`] CMR_DAT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `vec 0:real^2`; `&1`;
                 `cmr_dat (Q:real^3^3) (c:real^2) r (u:real^3->real^K)`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[]);;

let CMR_MINW_CONV_POS = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0
    (rn:num->real) r0.
     cmw_repex S G e /\ cmw_repcont S G e /\ CMR_GCOND G Lam /\
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     (!e'. &0 < e'
           ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u0 y) < e')
                          sequentially) /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (!n. &0 < rn n) /\ &0 < r0 /\ (rn ---> r0) sequentially /\
     (!n. wan_gdir (ball(c,rn n)) G (\x. un n (cm_capmap Q x)) <= e) /\
     wan_gdir (ball(c,r0)) G (\x. u0(cm_capmap Q x)) <= e
     ==> (!e'. &0 < e'
               ==> eventually
                     (\n. !x. x IN cball(vec 0,&1)
                              ==> norm(cmr_minw S G (vec 0) (&1) (cmr_dat Q c (rn n) (un n)) x -
                                       cmr_minw S G (vec 0) (&1) (cmr_dat Q c r0 u0) x) < e')
                     sequentially) /\
         ((\n. wan_dir (ball(vec 0,&1))
                 (\x. cmr_minw S G (vec 0) (&1) (cmr_dat Q c (rn n) (un n)) x -
                      cmr_minw S G (vec 0) (&1) (cmr_dat Q c r0 u0) x)) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u0:real^3->real^K) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  UNDISCH_TAC `cmw_repcont S (G:real^K->real^K^K) e` THEN REWRITE_TAC[cmw_repcont] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`vec 0:real^2`; `&1`;
    `\n. cmr_dat (Q:real^3^3) (c:real^2) ((rn:num->real) n) ((un:num->real^3->real^K) n)`;
    `cmr_dat (Q:real^3^3) (c:real^2) r0 (u0:real^3->real^K)`;
    `\n. cmr_minw S (G:real^K->real^K^K) (vec 0) (&1)
           (cmr_dat (Q:real^3^3) (c:real^2) ((rn:num->real) n) ((un:num->real^3->real^K) n))`;
    `cmr_minw S (G:real^K->real^K^K) (vec 0) (&1)
       (cmr_dat (Q:real^3^3) (c:real^2) r0 (u0:real^3->real^K))`]) THEN
  REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r0:real`; `u0:real^3->real^K`] CMR_DAT_MINW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                   `c:real^2`; `(rn:num->real) n`; `(un:num->real^3->real^K) n`]
                  CMR_DAT_MINW_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[tendsto] THEN X_GEN_TAC `e':real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`Q:real^3^3`; `c:real^2`; `un:num->real^3->real^K`; `u0:real^3->real^K`;
                   `rn:num->real`; `r0:real`; `norm(x:real^2)`] CMR_DAT_UNIF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e':real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[dist] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_CBALL_0; REAL_LE_REFL];
    X_GEN_TAC `e':real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`Q:real^3^3`; `c:real^2`; `un:num->real^3->real^K`; `u0:real^3->real^K`;
                   `rn:num->real`; `r0:real`; `&1`] CMR_DAT_UNIF) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC CMR_DAT_DIR_POS THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_REWRITE_TAC[]]);;

let CMR_ZT_UNIF_POS = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0
    (rn:num->real) r0.
     cmw_repex S G e /\ cmw_repcont S G e /\ CMR_GCOND G Lam /\
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     (!e'. &0 < e'
           ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u0 y) < e')
                          sequentially) /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (!n. &0 < rn n) /\ &0 < r0 /\ (rn ---> r0) sequentially /\
     (!n. wan_gdir (ball(c,rn n)) G (\x. un n (cm_capmap Q x)) <= e) /\
     wan_gdir (ball(c,r0)) G (\x. u0(cm_capmap Q x)) <= e
     ==> !e'. &0 < e'
              ==> eventually
                    (\n. !x. norm(cmr_zt S G Q c (rn n) (un n) x - cmr_zt S G Q c r0 u0 x) < e')
                    sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e':real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `un:num->real^3->real^K`; `u0:real^3->real^K`; `rn:num->real`;
                 `r0:real`] CMR_MINW_CONV_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e' / &2` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  MP_TAC(ISPECL [`Q:real^3^3`; `c:real^2`; `un:num->real^3->real^K`; `u0:real^3->real^K`;
                 `rn:num->real`; `r0:real`; `&1`] CMR_DAT_UNIF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e' / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[cmr_zt] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `(x:real^2) IN cball(vec 0,&1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NORM_ARITH;
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0]]);;

let CMR_ZEXT_SHIFT_UNIF = prove
 (`!(h:real^2->real^K) (c:real^2) (rn:num->real) r0.
     h continuous_on (:real^2) /\ (!x. ~(x IN ball(vec 0,&1)) ==> h x = vec 0) /\
     (!n. &0 < rn n) /\ &0 < r0 /\ (rn ---> r0) sequentially
     ==> !e. &0 < e
             ==> eventually
                   (\n. !z. norm(h(inv(rn n) % z + --(inv(rn n) % c)) -
                                 h(inv r0 % z + --(inv r0 % c))) < e)
                   sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `inv r % (z:real^2) + --(inv r % c) = inv r % (z - c)`] THEN
  MP_TAC(ISPECL [`h:real^2->real^K`; `cball(vec 0:real^2,&3)`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `((\n. inv((rn:num->real) n)) ---> inv r0) sequentially` MP_TAC THENL
   [MATCH_MP_TAC REALLIM_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  REWRITE_TAC[tendsto_real] THEN DISCH_THEN(MP_TAC o SPEC `dd / (&2 * r0)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(rn ---> r0) sequentially` THEN REWRITE_TAC[tendsto_real] THEN
  DISCH_THEN(MP_TAC o SPEC `r0 / &3`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN X_GEN_TAC `z:real^2` THEN
  SUBGOAL_THEN `&0 < (rn:num->real) n /\ &2 * r0 / &3 < rn n /\ rn n < &4 * r0 / &3`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(inv((rn:num->real) n) % (z - c:real^2)) = norm(z - c) / rn n /\
    norm(inv r0 % (z - c:real^2)) = norm(z - c) / r0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(z - c:real^2) <= &2 * r0` THENL
   [ONCE_REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_CBALL_0; dist] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `abs(inv((rn:num->real) n) - inv r0) * (&2 * r0)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        UNDISCH_TAC `abs(inv((rn:num->real) n) - inv r0) < dd / (&2 * r0)` THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < r0 ==> &0 < &2 * r0`]]];
    SUBGOAL_THEN
     `~(inv((rn:num->real) n) % (z - c:real^2) IN ball(vec 0,&1)) /\
      ~(inv r0 % (z - c:real^2) IN ball(vec 0,&1))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0]]]);;

let CMR_ZT_UNIF_ZERO = prove
 (`!S (G:real^K->real^K^K) d e Lam (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0
    (rn:num->real).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     CMR_GCOND G Lam /\
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     (!e'. &0 < e'
           ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u0 y) < e')
                          sequentially) /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (rn ---> &0) sequentially /\
     (!n. &0 < rn n ==> wan_gdir (ball(c,rn n)) G (\x. un n (cm_capmap Q x)) <= e)
     ==> !e'. &0 < e'
              ==> eventually (\n. &0 < rn n
                                  ==> !x. norm(cmr_zt S G Q c (rn n) (un n) x) < e')
                             sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e':real` THEN DISCH_TAC THEN
  ABBREV_TAC `q = (u0:real^3->real^K)(cm_capmap Q c)` THEN
  SUBGOAL_THEN `(q:real^K) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_MESON_TAC[cm_smap; CMR_CAPMAP_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `e' / &2`]
                CMW_C0EST) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Q:real^3^3`; `c:real^2`; `un:num->real^3->real^K`; `u0:real^3->real^K`;
                 `rn:num->real`; `&0`; `&1`] CMR_DAT_UNIF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `min delta (e' / &2)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `Q:real^3^3`; `c:real^2`; `un:num->real^3->real^K`;
                 `u0:real^3->real^K`; `rn:num->real`] CMR_DAT_DIR_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `delta:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dz") (LABEL_TAC "un")) THEN DISCH_TAC THEN
  USE_THEN "dz" (MP_TAC o C MP (ASSUME `&0 < (rn:num->real) n`)) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `(rn:num->real) n`; `(un:num->real^3->real^K) n`]
                CMR_DAT_MINW_FACTS) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `V = cmr_dat (Q:real^3^3) (c:real^2) ((rn:num->real) n)
                          ((un:num->real^3->real^K) n)` THEN
  ABBREV_TAC `W = cmr_minw S (G:real^K->real^K^K) (vec 0) (&1) (V:real^2->real^K)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^2. cmr_dat (Q:real^3^3) c (&0) (u0:real^3->real^K) x = q`
  (LABEL_TAC "dq") THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[cmr_dat; VECTOR_MUL_LZERO; VECTOR_ADD_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN cball(vec 0,&1) ==> norm((V:real^2->real^K) x - q) < min delta (e' / &2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "un" (MP_TAC o SPEC `x:real^2`) THEN
    USE_THEN "dq" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:real^2->real^K`; `W:real^2->real^K`; `q:real^K`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "cm_minimizer"))
                         (concl th))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "real_min"))
                           (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[cmr_zt] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `(x:real^2) IN cball(vec 0,&1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> is_var t && fst(dest_var t) = "W")) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "real_min"))
                           (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC NORM_ARITH;
    ASM_REWRITE_TAC[NORM_0]]);;


(* ========================================================================= *)
(* Uniform convergence on S^2 of one-cap replacements when the               *)
(* maps converge uniformly and in energy and the radii converge (positive   *)
(* limit radius with positive radii; limit radius 0).                       *)
(* ========================================================================= *)

let CMR_REP1_POLE = prove
 (`!S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     orthogonal_matrix Q ==> cmr_rep1 S G Q c r u (Q ** basis 3) = u(Q ** basis 3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_rep1] THEN
  SUBGOAL_THEN `~((Q:real^3^3) ** basis 3 IN IMAGE (cm_capmap Q) (ball(c:real^2,r)))`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS]);;

let CMR_SPHERE_CASES = prove
 (`!(Q:real^3^3) y.
     orthogonal_matrix Q /\ y IN sphere(vec 0,&1)
     ==> y = Q ** basis 3 \/ ?z. y = cm_capmap Q z`,
  MESON_TAC[CMR_CAPMAP_FACTS]);;

let CMR_REP1_C0_POS = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0
    (rn:num->real) r0.
     cmw_repex S G e /\ cmw_repcont S G e /\ CMR_GCOND G Lam /\
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     (!e'. &0 < e'
           ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u0 y) < e')
                          sequentially) /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (!n. &0 < rn n) /\ &0 < r0 /\ (rn ---> r0) sequentially /\
     (!n. wan_gdir (ball(c,rn n)) G (\x. un n (cm_capmap Q x)) <= e) /\
     wan_gdir (ball(c,r0)) G (\x. u0(cm_capmap Q x)) <= e
     ==> !e'. &0 < e'
              ==> eventually
                    (\n. !y. y IN sphere(vec 0,&1)
                             ==> norm(cmr_rep1 S G Q c (rn n) (un n) y -
                                      cmr_rep1 S G Q c r0 u0 y) < e')
                    sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e':real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r0:real`; `u0:real^3->real^K`] CMR_ZT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cmr_zt S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r0 (u0:real^3->real^K)`;
                 `c:real^2`; `rn:num->real`; `r0:real`] CMR_ZEXT_SHIFT_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e' / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `un:num->real^3->real^K`; `u0:real^3->real^K`; `rn:num->real`;
                 `r0:real`] CMR_ZT_UNIF_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e' / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e' / &3` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "sphere"))
                         (concl th) &&
                     can (find_term (fun t -> is_var t && fst(dest_var t) = "un")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "u") (CONJUNCTS_THEN2 (LABEL_TAC "z")
    (LABEL_TAC "s"))) THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  USE_THEN "u" (fun th -> LABEL_TAC "uy"
    (MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN sphere(vec 0,&1)`))) THEN
  MP_TAC(ISPECL [`Q:real^3^3`; `y:real^3`] CMR_SPHERE_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[CMR_REP1_POLE] THEN
    USE_THEN "uy" MP_TAC THEN UNDISCH_TAC `&0 < e'` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r0:real`; `u0:real^3->real^K`] CMR_REP1_REPR) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `(rn:num->real) n`; `(un:num->real^3->real^K) n`] CMR_REP1_REPR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "uy" MP_TAC THEN
  USE_THEN "z" (MP_TAC o SPEC `inv((rn:num->real) n) % (z:real^2) + --(inv(rn n) % c)`) THEN
  USE_THEN "s" (MP_TAC o SPEC `z:real^2`) THEN
  CONV_TAC NORM_ARITH);;

let CMR_REP1_C0_ZERO = prove
 (`!S (G:real^K->real^K^K) d e Lam (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0
    (rn:num->real).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     CMR_GCOND G Lam /\
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     (!e'. &0 < e'
           ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u0 y) < e')
                          sequentially) /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (rn ---> &0) sequentially /\
     (!n. &0 < rn n ==> wan_gdir (ball(c,rn n)) G (\x. un n (cm_capmap Q x)) <= e)
     ==> !e'. &0 < e'
              ==> eventually
                    (\n. !y. y IN sphere(vec 0,&1)
                             ==> norm(cmr_rep1 S G Q c (rn n) (un n) y - u0 y) < e')
                    sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e':real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `Lam:real`;
                 `Q:real^3^3`; `c:real^2`; `un:num->real^3->real^K`; `u0:real^3->real^K`;
                 `rn:num->real`] CMR_ZT_UNIF_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e' / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e' / &2` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "sphere"))
                         (concl th) &&
                     can (find_term (fun t -> is_var t && fst(dest_var t) = "un")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "u") (LABEL_TAC "z")) THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  USE_THEN "u" (fun th -> LABEL_TAC "uy"
    (MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN sphere(vec 0,&1)`))) THEN
  ASM_CASES_TAC `&0 < (rn:num->real) n` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CMR_REP1_NONPOS; REAL_ARITH `~(&0 < r) ==> r <= &0`] THEN
    USE_THEN "uy" MP_TAC THEN UNDISCH_TAC `&0 < e'` THEN REAL_ARITH_TAC] THEN
  USE_THEN "z" (MP_TAC o C MP (ASSUME `&0 < (rn:num->real) n`)) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Q:real^3^3`; `y:real^3`] CMR_SPHERE_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[CMR_REP1_POLE] THEN
    USE_THEN "uy" MP_TAC THEN UNDISCH_TAC `&0 < e'` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `(rn:num->real) n`; `(un:num->real^3->real^K) n`] CMR_REP1_REPR) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  USE_THEN "uy" MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv((rn:num->real) n) % (z:real^2) + --(inv(rn n) % c)` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "cmr_zt"))
                         (concl th))) THEN
  CONV_TAC NORM_ARITH);;


(* ========================================================================= *)
(* Dirichlet convergence on S^2 of one-cap replacements.                     *)
(* ========================================================================= *)

let CMR_AFF_UNIV = prove
 (`!r (c:real^N). ~(r = &0) ==> IMAGE (\x. inv r % x + --(inv r % c)) (:real^N) = (:real^N)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMR_AFF_PREIMAGE] THEN SET_TAC[]);;

let CMR_DIL_UNIV_W12 = prove
 (`!(f:real^2->real^K) m (b:real^2).
     wan_w12 (:real^2) f /\ &0 < m
     ==> wan_w12 (:real^2) (\x. f(m % x + b)) /\
         wan_dir (:real^2) (\x. f(m % x + b)) = wan_dir (:real^2) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `f:real^2->real^K`; `m:real`; `b:real^2`] CMR_AFF_W12) THEN
  MP_TAC(ISPECL [`(:real^2)`; `f:real^2->real^K`; `m:real`; `b:real^2`] CMR_AFF_DIR) THEN
  ASM_SIMP_TAC[OPEN_UNIV; CMR_AFF_UNIV; REAL_LT_IMP_NZ]);;

let CMR_ZT_DIFF_DIR = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r1 (u1:real^3->real^K) r2 u2.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ orthogonal_matrix Q /\
     cm_smap S u1 /\ cm_smap S u2 /\ &0 < r1 /\ &0 < r2 /\
     wan_gdir (ball(c,r1)) G (\x. u1(cm_capmap Q x)) <= e /\
     wan_gdir (ball(c,r2)) G (\x. u2(cm_capmap Q x)) <= e
     ==> wan_dir (:real^2) (\x. cmr_zt S G Q c r1 u1 x - cmr_zt S G Q c r2 u2 x) <=
         &2 * wan_dir (ball(vec 0,&1))
                (\x. cmr_minw S G (vec 0) (&1) (cmr_dat Q c r1 u1) x -
                     cmr_minw S G (vec 0) (&1) (cmr_dat Q c r2 u2) x) +
         &2 * wan_dir (ball(vec 0,&1)) (\x. cmr_dat Q c r1 u1 x - cmr_dat Q c r2 u2 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r1:real`; `u1:real^3->real^K`] CMR_DAT_MINW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V1 = cmr_dat (Q:real^3^3) (c:real^2) r1 (u1:real^3->real^K)` THEN
  ABBREV_TAC `W1 = cmr_minw S (G:real^K->real^K^K) (vec 0) (&1) (V1:real^2->real^K)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r2:real`; `u2:real^3->real^K`] CMR_DAT_MINW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V2 = cmr_dat (Q:real^3^3) (c:real^2) r2 (u2:real^3->real^K)` THEN
  ABBREV_TAC `W2 = cmr_minw S (G:real^K->real^K^K) (vec 0) (&1) (V2:real^2->real^K)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. cmr_zt S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r1 (u1:real^3->real^K) x -
         cmr_zt S G Q c r2 u2 x) =
    (\x. if x IN ball(vec 0,&1)
         then (\x. ((W1:real^2->real^K) x - V1 x) - ((W2:real^2->real^K) x - V2 x)) x
         else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cmr_zt] THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[VECTOR_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w120 (ball(vec 0:real^2,&1))
      (\x. ((W1:real^2->real^K) x - V1 x) - ((W2:real^2->real^K) x - V2 x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\x. (W1:real^2->real^K) x - V1 x`;
                   `\x. (W2:real^2->real^K) x - V2 x`] WAN_W120_SUB) THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`;
                 `\x. ((W1:real^2->real^K) x - V1 x) - ((W2:real^2->real^K) x - V2 x)`]
                CMR_ZEXT_DIR) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `wan_dir (ball(vec 0:real^2,&1))
      (\x. ((W1:real^2->real^K) x - V1 x) - ((W2:real^2->real^K) x - V2 x)) =
    wan_dir (ball(vec 0,&1)) (\x. (W1 x - W2 x) - (V1 x - V2 x))`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w12 (ball(vec 0:real^2,&1)) (\x. (W1:real^2->real^K) x - W2 x) /\
    wan_w12 (ball(vec 0:real^2,&1)) (\x. (V1:real^2->real^K) x - V2 x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\x. (W1:real^2->real^K) x - W2 x`;
                 `\x. (V1:real^2->real^K) x - V2 x`] CMR_DIR_SUB_LE_P) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN MATCH_MP_TAC CMR_W12_PARTIALS THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o BETA_RULE o CONJUNCT2)]);;

let CMR_ZEXT_SHIFT_DIR = prove
 (`!(h:real^2->real^K) (c:real^2) (rn:num->real) r0.
     h continuous_on (:real^2) /\ (!x. ~(x IN ball(vec 0,&1)) ==> h x = vec 0) /\
     wan_w12 (:real^2) h /\
     (!n. &0 < rn n) /\ &0 < r0 /\ (rn ---> r0) sequentially
     ==> ((\n. wan_dir (:real^2)
                 (\x. h(inv(rn n) % x + --(inv(rn n) % c)) - h(inv r0 % x + --(inv r0 % c))))
          ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. wan_w12 (:real^2)
          (\x. (h:real^2->real^K)(inv((rn:num->real) n) % x + --(inv(rn n) % c)) -
               h(inv r0 % x + --(inv r0 % c)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`h:real^2->real^K`; `inv((rn:num->real) n)`;
                     `--(inv((rn:num->real) n) % c):real^2`] CMR_DIL_UNIV_W12);
      MP_TAC(ISPECL [`h:real^2->real^K`; `inv r0`; `--(inv r0 % c):real^2`]
                    CMR_DIL_UNIV_W12)] THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. wan_dir (ball(c:real^2,&2 * r0))
                    (\x. (h:real^2->real^K)(inv((rn:num->real) n) % x + --(inv(rn n) % c)) -
                         h(inv r0 % x + --(inv r0 % c)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CMR_DIL_DIR_SEQ THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ;
                 REWRITE_RULE[DIMINDEX_2] (ISPEC `(:real^2)` CMR_W12_PARTIALS)] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      MATCH_MP_TAC LIM_NEG THEN MATCH_MP_TAC LIM_VMUL THEN
      REWRITE_TAC[GSYM TENDSTO_REAL] THEN MATCH_MP_TAC REALLIM_INV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ]]] THEN
  UNDISCH_TAC `(rn ---> r0) sequentially` THEN REWRITE_TAC[tendsto_real] THEN
  DISCH_THEN(MP_TAC o SPEC `r0:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `D = \x. (h:real^2->real^K)(inv((rn:num->real) n) % x + --(inv(rn n) % c)) -
            h(inv r0 % x + --(inv r0 % c))` THEN
  MP_TAC(ISPECL [`D:real^2->real^K`; `c:real^2`; `&2 * r0`] CMR_DIR_SPLIT_ID) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `!i. 1 <= i /\ i <= 2
          ==> ?v. v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i (D:real^2->real^K) v`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[DIMINDEX_2] (ISPEC `(:real^2)` CMR_W12_PARTIALS)) THEN
      EXPAND_TAC "D" THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN REWRITE_TAC[ARITH] THEN
    MESON_TAC[wan_wpd];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b = &0 ==> a = a + b`) THEN
  MATCH_MP_TAC CMR_DIR_ZERO_ON THEN
  SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL] THEN DISCH_TAC THEN
  EXPAND_TAC "D" THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(inv((rn:num->real) n) % x + --(inv(rn n) % c) IN ball(vec 0:real^2,&1)) /\
    ~(inv r0 % x + --(inv r0 % c) IN ball(vec 0:real^2,&1))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CMR_AFF_IN_BALL; IN_BALL] THEN
    UNDISCH_TAC `abs((rn:num->real) n - r0) < r0` THEN
    UNDISCH_TAC `~(dist(c:real^2,x) <= &2 * r0)` THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[VECTOR_SUB_REFL]]);;

let CMR_ZT_W12_UNIV = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\
     cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\
     wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> wan_w12 (:real^2) (cmr_zt S G Q c r u) /\
         !m b. &0 < m ==> wan_w12 (:real^2) (\x. cmr_zt S G Q c r u (m % x + b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r:real`; `u:real^3->real^K`] CMR_ZT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 (:real^2) (cmr_zt S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r
                                     (u:real^3->real^K))`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[wan_w12; DIMINDEX_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[CMR_DIL_UNIV_W12]);;

let CMR_REP1_DIR_BOUND = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r1 (u1:real^3->real^K) r2 u2.
     cmw_repex S G e /\ cmw_repcont S G e /\ CMR_GCOND G Lam /\ orthogonal_matrix Q /\
     cm_smap S u1 /\ cm_smap S u2 /\ &0 < r1 /\ &0 < r2 /\
     wan_gdir (ball(c,r1)) G (\x. u1(cm_capmap Q x)) <= e /\
     wan_gdir (ball(c,r2)) G (\x. u2(cm_capmap Q x)) <= e
     ==> wan_dir wan_shell (\z. wan_rext (cmr_rep1 S G Q c r1 u1) z -
                                wan_rext (cmr_rep1 S G Q c r2 u2) z) <=
         &2 * wan_dir wan_shell (\z. wan_rext u1 z - wan_rext u2 z) +
         &12 * wan_dir (ball(vec 0,&1))
                 (\x. cmr_minw S G (vec 0) (&1) (cmr_dat Q c r1 u1) x -
                      cmr_minw S G (vec 0) (&1) (cmr_dat Q c r2 u2) x) +
         &12 * wan_dir (ball(vec 0,&1)) (\x. cmr_dat Q c r1 u1 x - cmr_dat Q c r2 u2 x) +
         &6 * wan_dir (:real^2)
                (\x. cmr_zt S G Q c r2 u2 (inv r1 % x + --(inv r1 % c)) -
                     cmr_zt S G Q c r2 u2 (inv r2 % x + --(inv r2 % c)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`; `c:real^2`;
                 `r1:real`; `u1:real^3->real^K`] CMR_REP1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`; `c:real^2`;
                 `r2:real`; `u2:real^3->real^K`] CMR_REP1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`cmr_rep1 S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r1 (u1:real^3->real^K)`;
                 `cmr_rep1 S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r2 (u2:real^3->real^K)`;
                 `Q:real^3^3`] CMR_S2_DIR_DIFF_CHART) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r1:real`; `u1:real^3->real^K`] CMR_REP1_REPR) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r2:real`; `u2:real^3->real^K`] CMR_REP1_REPR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `z1 = cmr_zt S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r1 (u1:real^3->real^K)` THEN
  ABBREV_TAC `z2 = cmr_zt S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r2 (u2:real^3->real^K)` THEN
  ABBREV_TAC `A = \x. (u1:real^3->real^K)(cm_capmap Q x) - u2(cm_capmap Q x)` THEN
  ABBREV_TAC `C = \x. (z1:real^2->real^K)(inv r1 % x + --(inv r1 % c)) -
                      (z2:real^2->real^K)(inv r1 % x + --(inv r1 % c))` THEN
  ABBREV_TAC `D = \x. (z2:real^2->real^K)(inv r1 % x + --(inv r1 % c)) -
                      z2(inv r2 % x + --(inv r2 % c))` THEN
  SUBGOAL_THEN
   `(\x. ((u1:real^3->real^K)(cm_capmap Q x) + (z1:real^2->real^K)(inv r1 % x + --(inv r1 % c))) -
         (u2(cm_capmap Q x) + (z2:real^2->real^K)(inv r2 % x + --(inv r2 % c)))) =
    (\x. (A:real^2->real^K) x + ((C:real^2->real^K) x + (D:real^2->real^K) x))`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "C"; "D"] THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r1:real`; `u1:real^3->real^K`] CMR_ZT_W12_UNIV) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r2:real`; `u2:real^3->real^K`] CMR_ZT_W12_UNIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 (:real^2) (C:real^2->real^K) /\ wan_w12 (:real^2) (D:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C"; "D"] THEN CONJ_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:2)
        ==> ?v. v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i (A:real^2->real^K) v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u1:real^3->real^K`; `u2:real^3->real^K`; `Q:real^3^3`]
                  CMR_CHART_DIFF_FACTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `C:real^2->real^K`; `D:real^2->real^K`] CMR_DIR_ADD_LE_P) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THEN MATCH_MP_TAC CMR_W12_PARTIALS THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE)] THEN
  MP_TAC(ISPECL [`(:real^2)`; `A:real^2->real^K`; `\x. (C:real^2->real^K) x + D x`]
                CMR_DIR_ADD_LE_P) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_UNIV]; DISCH_THEN(ASSUME_TAC o BETA_RULE o CONJUNCT2)] THEN
  SUBGOAL_THEN
   `wan_dir (:real^2) (A:real^2->real^K) =
    &2 / &3 * wan_dir wan_shell (\z. wan_rext (u1:real^3->real^K) z - wan_rext u2 z)`
  ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    MP_TAC(ISPECL [`u1:real^3->real^K`; `u2:real^3->real^K`; `Q:real^3^3`]
                  CMR_S2_DIR_DIFF_CHART) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir (:real^2) (C:real^2->real^K) =
    wan_dir (:real^2) (\x. (z1:real^2->real^K) x - (z2:real^2->real^K) x)`
  ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    MP_TAC(ISPECL [`\x. (z1:real^2->real^K) x - (z2:real^2->real^K) x`; `inv r1`;
                   `--(inv r1 % c):real^2`] CMR_DIL_UNIV_W12) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC WAN_W12_SUB THEN
      ASM_REWRITE_TAC[ETA_AX];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r1:real`; `u1:real^3->real^K`; `r2:real`; `u2:real^3->real^K`]
                CMR_ZT_DIFF_DIR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= wan_dir (:real^2) (D:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMR_REP1_DIR_POS = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0
    (rn:num->real) r0.
     cmw_repex S G e /\ cmw_repcont S G e /\ CMR_GCOND G Lam /\
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     (!e'. &0 < e'
           ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u0 y) < e')
                          sequentially) /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (!n. &0 < rn n) /\ &0 < r0 /\ (rn ---> r0) sequentially /\
     (!n. wan_gdir (ball(c,rn n)) G (\x. un n (cm_capmap Q x)) <= e) /\
     wan_gdir (ball(c,r0)) G (\x. u0(cm_capmap Q x)) <= e
     ==> ((\n. wan_dir wan_shell
                 (\z. wan_rext (cmr_rep1 S G Q c (rn n) (un n)) z -
                      wan_rext (cmr_rep1 S G Q c r0 u0) z)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. &2 * wan_dir wan_shell
               (\z. wan_rext ((un:num->real^3->real^K) n) z - wan_rext u0 z) +
        &12 * wan_dir (ball(vec 0,&1))
                (\x. cmr_minw S (G:real^K->real^K^K) (vec 0) (&1)
                       (cmr_dat (Q:real^3^3) (c:real^2) ((rn:num->real) n) (un n)) x -
                     cmr_minw S G (vec 0) (&1) (cmr_dat Q c r0 u0) x) +
        &12 * wan_dir (ball(vec 0,&1)) (\x. cmr_dat Q c (rn n) (un n) x - cmr_dat Q c r0 u0 x) +
        &6 * wan_dir (:real^2)
               (\x. cmr_zt S G Q c r0 u0 (inv(rn n) % x + --(inv(rn n) % c)) -
                    cmr_zt S G Q c r0 u0 (inv r0 % x + --(inv r0 % c)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                   `c:real^2`; `(rn:num->real) n`; `(un:num->real^3->real^K) n`; `r0:real`;
                   `u0:real^3->real^K`] CMR_REP1_DIR_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a <= b ==> abs a <= b`) THEN
    MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
    REWRITE_TAC[GSYM wan_s2_w12; ETA_AX] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`;
                     `c:real^2`; `(rn:num->real) n`; `(un:num->real^3->real^K) n`]
                    CMR_REP1_FACTS);
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`;
                     `c:real^2`; `r0:real`; `u0:real^3->real^K`] CMR_REP1_FACTS)] THEN
    ASM_SIMP_TAC[cm_smap];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_NULL_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                   `c:real^2`; `un:num->real^3->real^K`; `u0:real^3->real^K`; `rn:num->real`;
                   `r0:real`] CMR_MINW_CONV_POS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_NULL_LMUL THEN MATCH_MP_TAC CMR_DAT_DIR_POS THEN
    EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN MATCH_MP_TAC CMR_ZEXT_SHIFT_DIR THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r0:real`; `u0:real^3->real^K`] CMR_ZT_FACTS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r0:real`; `u0:real^3->real^K`] CMR_ZT_W12_UNIV) THEN
  ASM_SIMP_TAC[]);;

let CMR_CMAP_WMAP = prove
 (`!S (s:real^2->bool) (u:real^2->real^K). cm_cmap S s u ==> cm_wmap S s u`,
  REWRITE_TAC[cm_cmap; cm_wmap] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `{}:real^2->bool` THEN REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
  ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]);;

let CMR_ZT_DIR_LE = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?C. &0 < C /\
             !e Lg (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
               cmw_repex S G e /\ CMR_GCOND G Lg /\
               cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\
               wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
               ==> wan_dir (:real^2) (cmr_zt S G Q c r u) <=
                   C * wan_dir (ball(vec 0,&1)) (cmr_dat Q c r u)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CMW_TARGET_FACTS) THEN STRIP_TAC THEN
  EXISTS_TAC `&2 * Lam / lam + &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 * x + &2`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lg:real`; `Q:real^3^3`;
                 `c:real^2`; `r:real`; `u:real^3->real^K`] CMR_DAT_MINW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = cmr_dat (Q:real^3^3) (c:real^2) r (u:real^3->real^K)` THEN
  ABBREV_TAC `W = cmr_minw S (G:real^K->real^K^K) (vec 0) (&1) (V:real^2->real^K)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `cmr_zt S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K) =
    (\x. if x IN ball(vec 0,&1) then (\x. (W:real^2->real^K) x - V x) x else vec 0)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[cmr_zt]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\x. (W:real^2->real^K) x - V x`] CMR_ZEXT_DIR) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `wan_w12 (ball(vec 0:real^2,&1)) (W:real^2->real^K) /\
                wan_w12 (ball(vec 0:real^2,&1)) (V:real^2->real^K)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `W:real^2->real^K`; `V:real^2->real^K`]
                CMR_DIR_SUB_LE_P) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN MATCH_MP_TAC CMR_W12_PARTIALS THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN
   `wan_gdir (ball(vec 0:real^2,&1)) G (W:real^2->real^K) <=
    wan_gdir (ball(vec 0,&1)) G (V:real^2->real^K)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_minimizer S (G:real^K->real^K^K) (ball(vec 0,&1)) (W:real^2->real^K)` THEN
    REWRITE_TAC[cm_minimizer; cm_gen] THEN
    DISCH_THEN(MP_TAC o SPEC `V:real^2->real^K` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CMR_CMAP_WMAP] THEN
      SUBGOAL_THEN `(\x. (V:real^2->real^K) x - W x) = (\x. --((\x. W x - V x) x))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC WAN_W120_NEG THEN ASM_REWRITE_TAC[OPEN_BALL];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `G:real^K->real^K^K`; `W:real^2->real^K`;
                 `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `G:real^K->real^K^K`; `V:real^2->real^K`;
                 `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_LE] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_dir (ball(vec 0:real^2,&1)) (W:real^2->real^K) <=
    Lam / lam * wan_dir (ball(vec 0,&1)) (V:real^2->real^K)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `Lam / lam * x = (Lam * x) / lam`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMR_REP1_DIR_ZERO = prove
 (`!S (G:real^K->real^K^K) d e Lam (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0
    (rn:num->real).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     CMR_GCOND G Lam /\
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (rn ---> &0) sequentially /\
     (!n. &0 < rn n ==> wan_gdir (ball(c,rn n)) G (\x. un n (cm_capmap Q x)) <= e)
     ==> ((\n. wan_dir wan_shell
                 (\z. wan_rext (cmr_rep1 S G Q c (rn n) (un n)) z - wan_rext u0 z)) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC o MATCH_MP CMR_ZT_DIR_LE) THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. &2 * wan_dir wan_shell
               (\z. wan_rext ((un:num->real^3->real^K) n) z - wan_rext u0 z) +
        &3 * C * (if &0 < (rn:num->real) n
                  then wan_dir (ball(vec 0,&1)) (cmr_dat (Q:real^3^3) (c:real^2) (rn n) (un n))
                  else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&0 <= wan_dir wan_shell (\z. wan_rext ((un:num->real^3->real^K) n) z - wan_rext u0 z)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
      REWRITE_TAC[GSYM wan_s2_w12; ETA_AX] THEN ASM_MESON_TAC[cm_smap];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 < (rn:num->real) n` THENL
     [ALL_TAC;
      ASM_SIMP_TAC[CMR_REP1_NONPOS; REAL_ARITH `~(&0 < r) ==> r <= &0`] THEN
      ASM_REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 < (rn:num->real) n`) o SPEC `n:num` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_gdir"))
                           (concl th))) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`; `c:real^2`;
                   `(rn:num->real) n`; `(un:num->real^3->real^K) n`] CMR_REP1_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN
     `&0 <= wan_dir wan_shell
              (\z. wan_rext (cmr_rep1 S G (Q:real^3^3) (c:real^2) ((rn:num->real) n)
                               ((un:num->real^3->real^K) n)) z - wan_rext u0 z)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
      REWRITE_TAC[GSYM wan_s2_w12; ETA_AX] THEN ASM_MESON_TAC[cm_smap];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`] THEN
    MP_TAC(ISPECL [`cmr_rep1 S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) ((rn:num->real) n)
                      ((un:num->real^3->real^K) n)`;
                   `u0:real^3->real^K`; `Q:real^3^3`] CMR_S2_DIR_DIFF_CHART) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                   `c:real^2`; `(rn:num->real) n`; `(un:num->real^3->real^K) n`] CMR_REP1_REPR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ABBREV_TAC `z1 = cmr_zt S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) ((rn:num->real) n)
                       ((un:num->real^3->real^K) n)` THEN
    ABBREV_TAC `A = \x. (un:num->real^3->real^K) n (cm_capmap Q x) - u0(cm_capmap Q x)` THEN
    ABBREV_TAC `Z = \x. (z1:real^2->real^K)(inv((rn:num->real) n) % x + --(inv(rn n) % c))` THEN
    SUBGOAL_THEN
     `(\x. ((un:num->real^3->real^K) n (cm_capmap Q x) +
            (z1:real^2->real^K)(inv((rn:num->real) n) % x + --(inv(rn n) % c))) -
           u0(cm_capmap Q x)) =
      (\x. (A:real^2->real^K) x + (Z:real^2->real^K) x)`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["A"; "Z"] THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                   `c:real^2`; `(rn:num->real) n`; `(un:num->real^3->real^K) n`]
                  CMR_ZT_W12_UNIV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `wan_w12 (:real^2) (Z:real^2->real^K) /\
                  wan_dir (:real^2) (Z:real^2->real^K) = wan_dir (:real^2) (z1:real^2->real^K)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Z" THEN MATCH_MP_TAC CMR_DIL_UNIV_W12 THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. 1 <= i /\ i <= dimindex(:2)
          ==> ?v. v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i (A:real^2->real^K) v`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`un (n:num):real^3->real^K`; `u0:real^3->real^K`; `Q:real^3^3`]
                    CMR_CHART_DIFF_FACTS) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
      ASM_REWRITE_TAC[DIMINDEX_2] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(:real^2)`; `A:real^2->real^K`; `Z:real^2->real^K`] CMR_DIR_ADD_LE_P) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC CMR_W12_PARTIALS THEN ASM_REWRITE_TAC[];
      DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
    SUBGOAL_THEN
     `wan_dir (:real^2) (A:real^2->real^K) =
      &2 / &3 * wan_dir wan_shell
                  (\z. wan_rext ((un:num->real^3->real^K) n) z - wan_rext u0 z)`
    ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN
      MP_TAC(ISPECL [`un (n:num):real^3->real^K`; `u0:real^3->real^K`; `Q:real^3^3`]
                    CMR_S2_DIR_DIFF_CHART) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:real`; `Lam:real`; `Q:real^3^3`; `c:real^2`;
                                  `(rn:num->real) n`; `(un:num->real^3->real^K) n`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "cmr_zt"))
                           (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_NULL_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
  REWRITE_TAC[tendsto_real; REAL_SUB_RZERO] THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `Q:real^3^3`; `c:real^2`; `un:num->real^3->real^K`;
                 `u0:real^3->real^K`; `rn:num->real`] CMR_DAT_DIR_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ABS_0] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 < (rn:num->real) n`) o SPEC `n:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_gdir"))
                         (concl th))) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `(rn:num->real) n`; `(un:num->real^3->real^K) n`]
                CMR_DAT_MINW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= wan_dir (ball(vec 0,&1))
           (cmr_dat (Q:real^3^3) (c:real^2) ((rn:num->real) n) ((un:num->real^3->real^K) n))`
  MP_TAC THENL [MATCH_MP_TAC WAN_DIR_POS THEN ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Continuity of one-cap replacement in (map, radius), for any               *)
(* limit radius >= 0: uniform and Dirichlet convergence on S^2.             *)
(* ========================================================================= *)

let CMR_REP1_CONT_SEQ = prove
 (`!S (G:real^K->real^K^K) d e (Q:real^3^3) (c:real^2) (un:num->real^3->real^K) u0
    (rn:num->real) r0.
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     orthogonal_matrix Q /\ (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     (!e'. &0 < e'
           ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u0 y) < e')
                          sequentially) /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     &0 <= r0 /\ (rn ---> r0) sequentially /\
     (!n. &0 < rn n ==> wan_gdir (ball(c,rn n)) G (\x. un n (cm_capmap Q x)) <= e) /\
     (&0 < r0 ==> wan_gdir (ball(c,r0)) G (\x. u0(cm_capmap Q x)) <= e)
     ==> (!e'. &0 < e'
               ==> eventually
                     (\n. !y. y IN sphere(vec 0,&1)
                              ==> norm(cmr_rep1 S G Q c (rn n) (un n) y -
                                       cmr_rep1 S G Q c r0 u0 y) < e')
                     sequentially) /\
         ((\n. wan_dir wan_shell
                 (\z. wan_rext (cmr_rep1 S G Q c (rn n) (un n)) z -
                      wan_rext (cmr_rep1 S G Q c r0 u0) z)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP CMR_TARGET_GCOND) THEN
  ASM_CASES_TAC `&0 < r0` THENL
   [ALL_TAC;
    SUBGOAL_THEN `r0 = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP CMR_REP1_NONPOS (SPEC `&0` REAL_LE_REFL)] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMR_REP1_C0_ZERO THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `e:real`; `Lam:real`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMR_REP1_DIR_ZERO THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `e:real`; `Lam:real`] THEN ASM_REWRITE_TAC[]]] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 < r0`) o
    check (fun th -> is_imp(concl th) && fst(dest_imp(concl th)) = `&0 < r0`)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `eventually (\n. r0 / &2 < (rn:num->real) n) sequentially` ASSUME_TAC THENL
   [UNDISCH_TAC `(rn ---> r0) sequentially` THEN REWRITE_TAC[tendsto_real] THEN
    DISCH_THEN(MP_TAC o SPEC `r0 / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `rn' = \n. if r0 / &2 < (rn:num->real) n then rn n else r0` THEN
  ABBREV_TAC `un' = \n. if r0 / &2 < (rn:num->real) n then (un:num->real^3->real^K) n else u0` THEN
  SUBGOAL_THEN
   `eventually (\n. (rn':num->real) n = rn n /\
                    (un':num->real^3->real^K) n = un n) sequentially`
  ASSUME_TAC THENL
   [UNDISCH_TAC `eventually (\n. r0 / &2 < (rn:num->real) n) sequentially` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    MAP_EVERY EXPAND_TAC ["rn'"; "un'"] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. &0 < (rn':num->real) n) /\ (!n. cm_smap S ((un':num->real^3->real^K) n)) /\
    (!n. wan_gdir (ball(c,(rn':num->real) n)) G
           (\x. (un':num->real^3->real^K) n (cm_capmap Q x)) <= e) /\
    ((rn':num->real) ---> r0) sequentially /\
    (!e'. &0 < e'
          ==> eventually (\n. !y. y IN sphere(vec 0,&1)
                                  ==> norm((un':num->real^3->real^K) n y - u0 y) < e')
                         sequentially) /\
    ((\n. wan_dir wan_shell (\z. wan_rext ((un':num->real^3->real^K) n) z - wan_rext u0 z))
     ---> &0) sequentially`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "rn'" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_REAL_ARITH_TAC;
      GEN_TAC THEN EXPAND_TAC "un'" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN MAP_EVERY EXPAND_TAC ["rn'"; "un'"] THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN EXISTS_TAC `rn:num->real` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `eventually (\n. (rn':num->real) n = rn n /\
                                   (un':num->real^3->real^K) n = un n) sequentially` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN SIMP_TAC[];
      X_GEN_TAC `e':real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e':real` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> is_const t && fst(dest_const t) = "sphere"))
                             (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC `n:num` THEN EXPAND_TAC "un'" THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0];
      MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC `\n. wan_dir wan_shell
                        (\z. wan_rext ((un:num->real^3->real^K) n) z - wan_rext u0 z)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `eventually (\n. (rn':num->real) n = rn n /\
                                   (un':num->real^3->real^K) n = un n) sequentially` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `e':real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                   `Q:real^3^3`; `c:real^2`; `un':num->real^3->real^K`; `u0:real^3->real^K`;
                   `rn':num->real`; `r0:real`] CMR_REP1_C0_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e':real`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `eventually (\n. (rn':num->real) n = rn n /\
                                 (un':num->real^3->real^K) n = un n) sequentially` THEN
    REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\n. wan_dir wan_shell
            (\z. wan_rext (cmr_rep1 S G (Q:real^3^3) (c:real^2) ((rn':num->real) n)
                             ((un':num->real^3->real^K) n)) z -
                 wan_rext (cmr_rep1 S G Q c r0 u0) z)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `eventually (\n. (rn':num->real) n = rn n /\
                                   (un':num->real^3->real^K) n = un n) sequentially` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN SIMP_TAC[];
      MATCH_MP_TAC CMR_REP1_DIR_POS THEN EXISTS_TAC `e:real` THEN
      EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[]]]);;


(* ========================================================================= *)
(* Continuity of sequential replacement cmr_repn on finitely                 *)
(* many (possibly overlapping) caps, with converging radii, given small    *)
(* energies of the intermediate maps on each cap.                           *)
(* ========================================================================= *)

let CMR_REP1_SMAP = prove
 (`!S (G:real^K->real^K^K) e (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ cm_smap S u /\ orthogonal_matrix Q /\
     (&0 < r ==> wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e)
     ==> cm_smap S (cmr_rep1 S G Q c r u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 < r` THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`; `c:real^2`;
                   `r:real`; `u:real^3->real^K`] CMR_REP1_FACTS) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[CMR_REP1_NONPOS; REAL_ARITH `~(&0 < r) ==> r <= &0`]]);;

let CMR_REPN_CONT_SEQ = prove
 (`!S (G:real^K->real^K^K) d e (Q:num->real^3^3) (c:num->real^2) (rr:num->num->real) r0
    (un:num->real^3->real^K) u0.
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     (!j. orthogonal_matrix (Q j)) /\
     (!n. cm_smap S (un n)) /\ cm_smap S u0 /\
     (!e'. &0 < e'
           ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u0 y) < e')
                          sequentially) /\
     ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u0 z)) ---> &0) sequentially /\
     (!j. &0 <= r0 j /\ ((\n. rr n j) ---> r0 j) sequentially) /\
     (!n m. &0 < rr n (SUC m)
            ==> wan_gdir (ball(c(SUC m),rr n (SUC m))) G
                  (\x. cmr_repn S G m Q c (rr n) (un n) (cm_capmap (Q(SUC m)) x)) <= e) /\
     (!m. &0 < r0 (SUC m)
          ==> wan_gdir (ball(c(SUC m),r0 (SUC m))) G
                (\x. cmr_repn S G m Q c r0 u0 (cm_capmap (Q(SUC m)) x)) <= e)
     ==> !m. (!n. cm_smap S (cmr_repn S G m Q c (rr n) (un n))) /\
             cm_smap S (cmr_repn S G m Q c r0 u0) /\
             (!e'. &0 < e'
                   ==> eventually
                         (\n. !y. y IN sphere(vec 0,&1)
                                  ==> norm(cmr_repn S G m Q c (rr n) (un n) y -
                                           cmr_repn S G m Q c r0 u0 y) < e')
                         sequentially) /\
             ((\n. wan_dir wan_shell
                     (\z. wan_rext (cmr_repn S G m Q c (rr n) (un n)) z -
                          wan_rext (cmr_repn S G m Q c r0 u0) z)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[cmr_repn]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    can (find_term (fun t -> is_var t && fst(dest_var t) = "m")) (concl th) &&
    is_conj (concl th))) THEN
  REWRITE_TAC[cmr_repn] THEN
  SUBGOAL_THEN
   `(!n. cm_smap S (cmr_rep1 S G ((Q:num->real^3^3)(SUC m)) ((c:num->real^2)(SUC m))
                     ((rr:num->num->real) n (SUC m))
                     (cmr_repn S G m Q c (rr n) ((un:num->real^3->real^K) n)))) /\
    cm_smap S (cmr_rep1 S (G:real^K->real^K^K) ((Q:num->real^3^3)(SUC m))
                 ((c:num->real^2)(SUC m)) (r0(SUC m)) (cmr_repn S G m Q c r0 u0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [GEN_TAC; ALL_TAC] THEN MATCH_MP_TAC CMR_REP1_SMAP THEN
    EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`;
                 `(Q:num->real^3^3)(SUC m)`; `(c:num->real^2)(SUC m)`;
                 `\n. cmr_repn S (G:real^K->real^K^K) m (Q:num->real^3^3) (c:num->real^2)
                        ((rr:num->num->real) n) ((un:num->real^3->real^K) n)`;
                 `cmr_repn S (G:real^K->real^K^K) m (Q:num->real^3^3) (c:num->real^2) r0
                    (u0:real^3->real^K)`;
                 `\n. (rr:num->num->real) n (SUC m)`; `(r0:num->real)(SUC m)`]
                CMR_REP1_CONT_SEQ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;


(* ========================================================================= *)
(* Replacement only sees the values on S^2; replacement keeps                *)
(* maps that are constant on S^2 constant; zero radii change nothing.       *)
(* ========================================================================= *)

let CMR_REP1_SPHERE_CONG = prove
 (`!S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K) v.
     orthogonal_matrix Q /\ (!y. y IN sphere(vec 0,&1) ==> u y = v y)
     ==> !y. y IN sphere(vec 0,&1) ==> cmr_rep1 S G Q c r u y = cmr_rep1 S G Q c r v y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (u:real^3->real^K)(cm_capmap Q x)) = (\x. v(cm_capmap Q x))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS]; ALL_TAC] THEN
  REWRITE_TAC[cmr_rep1] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let CMR_REPN_SPHERE_CONG = prove
 (`!S (G:real^K->real^K^K) (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K) v.
     (!j. orthogonal_matrix (Q j)) /\ (!y. y IN sphere(vec 0,&1) ==> u y = v y)
     ==> !m y. y IN sphere(vec 0,&1)
               ==> cmr_repn S G m Q c r u y = cmr_repn S G m Q c r v y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[cmr_repn] THEN
  MATCH_MP_TAC CMR_REP1_SPHERE_CONG THEN ASM_REWRITE_TAC[]);;

let CMR_REP1_CONST = prove
 (`!S (G:real^K->real^K^K) d e (Q:real^3^3) (c:real^2) r (q:real^K).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 <= e /\
     orthogonal_matrix Q /\ q IN S
     ==> !y. y IN sphere(vec 0,&1) ==> cmr_rep1 S G Q c r (\y. q) y = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  ASM_CASES_TAC `&0 < r` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CMR_REP1_NONPOS; REAL_ARITH `~(&0 < r) ==> r <= &0`]] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `q:real^K`; `c:real^2`; `r:real`;
                 `Lam:real`] CMW_CONST_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `r:real`;
                 `\x:real^2. (q:real^K)`; `\x:real^2. (q:real^K)`] CMR_MINW_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[cmr_rep1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
  ASM_SIMP_TAC[CMR_CAPMAP_FACTS] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]);;

let CMR_REPN_CONST = prove
 (`!S (G:real^K->real^K^K) d e (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K) q.
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 <= e /\
     (!j. orthogonal_matrix (Q j)) /\ q IN S /\ (!y. y IN sphere(vec 0,&1) ==> u y = q)
     ==> !m y. y IN sphere(vec 0,&1) ==> cmr_repn S G m Q c r u y = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[cmr_repn] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS
   `cmr_rep1 S (G:real^K->real^K^K) ((Q:num->real^3^3)(SUC m)) ((c:num->real^2)(SUC m))
      ((r:num->real)(SUC m)) (\y:real^3. (q:real^K)) y` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `(Q:num->real^3^3)(SUC m)`;
                   `(c:num->real^2)(SUC m)`; `(r:num->real)(SUC m)`;
                   `cmr_repn S (G:real^K->real^K^K) m (Q:num->real^3^3) (c:num->real^2) r
                      (u:real^3->real^K)`;
                   `\y:real^3. (q:real^K)`] CMR_REP1_SPHERE_CONG) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`;
                   `(Q:num->real^3^3)(SUC m)`; `(c:num->real^2)(SUC m)`;
                   `(r:num->real)(SUC m)`; `q:real^K`] CMR_REP1_CONST) THEN
    ASM_SIMP_TAC[]]);;

let CMR_REPN_ZERO = prove
 (`!S (G:real^K->real^K^K) (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K).
     (!j. r j <= &0) ==> !m. cmr_repn S G m Q c r u = u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[cmr_repn; CMR_REP1_NONPOS]);;

let CMR_REPN_SMAP = prove
 (`!S (G:real^K->real^K^K) e (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ cm_smap S u /\ (!j. orthogonal_matrix (Q j)) /\
     (!m. &0 < r(SUC m)
          ==> wan_gdir (ball(c(SUC m),r(SUC m))) G
                (\x. cmr_repn S G m Q c r u (cm_capmap (Q(SUC m)) x)) <= e)
     ==> !m. cm_smap S (cmr_repn S G m Q c r u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[cmr_repn] THEN
  MATCH_MP_TAC CMR_REP1_SMAP THEN EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[]);;


(* ========================================================================= *)
(* Families.  Given a sweepout sigma, rotations Q j, centres                 *)
(* c j and continuous radius functions R j on [0,1], cmr_fam ... s y t is   *)
(* the sequential replacement of the slice sigma(.,t) on the caps with      *)
(* radii s * R j t.  Under small intermediate energies, cmr_fam ... (&1) is *)
(* a sweepout, and s |-> cmr_fam ... s is a homotopy of sweepouts from      *)
(* sigma to it (shrinking the caps).                                         *)
(* ========================================================================= *)

let cmr_fam = new_definition
 `cmr_fam S (G:real^K->real^K^K) N (Q:num->real^3^3) (c:num->real^2) (R:num->real->real)
          (sigma:real^3->real->real^K) s (y:real^3) t =
    cmr_repn S G N Q c (\j. s * R j t) (\y. sigma y t) y`;;

let cmr_famok = new_definition
 `cmr_famok S (G:real^K->real^K^K) e (Q:num->real^3^3) (c:num->real^2) (R:num->real->real)
            (sigma:real^3->real->real^K) <=>
    cm_sweep S sigma /\ (!j. orthogonal_matrix (Q j)) /\
    (!j. R j real_continuous_on real_interval[&0,&1] /\
         !t. t IN real_interval[&0,&1] ==> &0 <= R j t) /\
    (!s t m. s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1] /\ &0 < s * R (SUC m) t
             ==> wan_gdir (ball(c(SUC m),s * R (SUC m) t)) G
                   (\x. cmr_repn S G m Q c (\j. s * R j t) (\y. sigma y t)
                          (cm_capmap (Q(SUC m)) x)) <= e)`;;

(* A copy of GRGT_REALLIM_WITHINREAL_SEQUENTIALLY (pc_grg_rfint), which this *)
(* unit does not load.                                                        *)

let CMR_REALLIM_WITHINREAL_SEQ = prove
 (`!f:real->real l a s.
        (f ---> l) (atreal a within s) <=>
        !x. (!n. x n IN s DELETE a) /\ (x ---> a) sequentially
            ==> ((f o x) ---> l) sequentially`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REALLIM_WITHINREAL_WITHIN; TENDSTO_REAL; LIM_WITHIN_SEQUENTIALLY] THEN
  GEN_REWRITE_TAC LAND_CONV [FORALL_LIFT_FUN] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IN_DELETE; IN_IMAGE_LIFT_DROP; LIFT_EQ]);;

let CMR_REAL_CONT_SEQ = prove
 (`!f s x (xn:num->real).
     f real_continuous_on s /\ x IN s /\ (!n. xn n IN s) /\ (xn ---> x) sequentially
     ==> ((\n. f(xn n)) ---> f x) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_continuous_on] THEN STRIP_TAC THEN
  REWRITE_TAC[tendsto_real] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(xn ---> x) sequentially` THEN REWRITE_TAC[tendsto_real] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN ASM_SIMP_TAC[]);;

let CMR_FAM_SMAP = prove
 (`!S (G:real^K->real^K^K) e N (Q:num->real^3^3) (c:num->real^2) R
    (sigma:real^3->real->real^K) s t.
     cmw_repex S G e /\ cmr_famok S G e Q c R sigma /\
     s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1]
     ==> cm_smap S (\y. cmr_fam S G N Q c R sigma s y t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_famok; cmr_fam] THEN STRIP_TAC THEN
  REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:num->real^3^3`;
                 `c:num->real^2`; `\j. s * (R:num->real->real) j t`;
                 `\y. (sigma:real^3->real->real^K) y t`] CMR_REPN_SMAP) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[cm_sweep]) THEN ASM_SIMP_TAC[];
    DISCH_THEN(ACCEPT_TAC o SPEC `N:num`)]);;

let CMR_FAM_SEQ = prove
 (`!S (G:real^K->real^K^K) d e N (Q:num->real^3^3) (c:num->real^2) R
    (sigma:real^3->real->real^K) s t (sn:num->real) (tn:num->real).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     cmr_famok S G e Q c R sigma /\
     s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1] /\
     (!n. sn n IN real_interval[&0,&1] /\ tn n IN real_interval[&0,&1]) /\
     (sn ---> s) sequentially /\ (tn ---> t) sequentially
     ==> (!e'. &0 < e'
               ==> eventually
                     (\n. !y. y IN sphere(vec 0,&1)
                              ==> norm(cmr_fam S G N Q c R sigma (sn n) y (tn n) -
                                       cmr_fam S G N Q c R sigma s y t) < e')
                     sequentially) /\
         ((\n. wan_dir wan_shell
                 (\z. wan_rext (\y. cmr_fam S G N Q c R sigma (sn n) y (tn n)) z -
                      wan_rext (\y. cmr_fam S G N Q c R sigma s y t) z)) ---> &0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_famok S (G:real^K->real^K^K) e (Q:num->real^3^3) (c:num->real^2) R
                 (sigma:real^3->real->real^K)` THEN
  REWRITE_TAC[cmr_famok; FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `sigma:real^3->real->real^K`; `tn:num->real`; `t:real`]
                CMW_SWEEP_SEQ_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[cmr_fam; ETA_AX] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`;
                 `Q:num->real^3^3`; `c:num->real^2`;
                 `\n j. (sn:num->real) n * (R:num->real->real) j (tn n)`;
                 `\j. s * (R:num->real->real) j t`;
                 `\n y. (sigma:real^3->real->real^K) y ((tn:num->real) n)`;
                 `\y. (sigma:real^3->real->real^K) y t`] CMR_REPN_CONT_SEQ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!t. t IN real_interval[&0,&1]
                      ==> cm_smap S (\y. (sigma:real^3->real->real^K) y t)`
    ASSUME_TAC THENL [ASM_MESON_TAC[cm_sweep]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    X_GEN_TAC `j:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `s IN real_interval[&0,&1]` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CMR_REAL_CONT_SEQ THEN
      EXISTS_TAC `real_interval[&0,&1]` THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]]);;

let CMR_FAM_CONT = prove
 (`!S (G:real^K->real^K^K) d e N (Q:num->real^3^3) (c:num->real^2) R
    (sigma:real^3->real->real^K).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     cmr_famok S G e Q c R sigma
     ==> continuous_map
           (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
              (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1]))),
            euclidean)
           (\(s,(y,t)). cmr_fam S G N Q c R sigma s y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMW_PROD3_SEQ_CONT THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((sn:num->real) ---> s) sequentially /\ ((tn:num->real) ---> t) sequentially`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[TENDSTO_REAL; o_DEF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `N:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `R:num->real->real`;
                 `sigma:real^3->real->real^K`; `s:real`; `t:real`; `sn:num->real`;
                 `tn:num->real`] CMR_FAM_SEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "u" o CONJUNCT1) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `N:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `R:num->real->real`;
                 `sigma:real^3->real->real^K`; `s:real`; `t:real`] CMR_FAM_SMAP) THEN
  ASM_REWRITE_TAC[cm_smap] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPECL [`yn:num->real^3`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[o_DEF] THEN REWRITE_TAC[tendsto] THEN DISCH_TAC THEN
  REWRITE_TAC[tendsto] THEN X_GEN_TAC `e':real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e' / &2` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 < e' / &2`) o SPEC `e' / &2`) THEN
  USE_THEN "u" (MP_TAC o C MP (ASSUME `&0 < e' / &2`) o SPEC `e' / &2`) THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[dist] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(yn:num->real^3) n`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `norm(cmr_fam S (G:real^K->real^K^K) N (Q:num->real^3^3) (c:num->real^2) R
          (sigma:real^3->real->real^K) s ((yn:num->real^3) n) t -
         cmr_fam S G N Q c R sigma s y t) < e' / &2` THEN
  CONV_TAC NORM_ARITH);;

let CMR_FAM_ENDS = prove
 (`!S (G:real^K->real^K^K) d e N (Q:num->real^3^3) (c:num->real^2) R
    (sigma:real^3->real->real^K) s y y'.
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 <= e /\
     cmr_famok S G e Q c R sigma /\ y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
     ==> cmr_fam S G N Q c R sigma s y (&0) = cmr_fam S G N Q c R sigma s y' (&0) /\
         cmr_fam S G N Q c R sigma s y (&1) = cmr_fam S G N Q c R sigma s y' (&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_famok] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_SWEEP_FACTS) THEN
  REWRITE_TAC[cmr_fam] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`;
                   `Q:num->real^3^3`; `c:num->real^2`; `\j. s * (R:num->real->real) j (&0)`;
                   `\y. (sigma:real^3->real->real^K) y (&0)`;
                   `(sigma:real^3->real->real^K) (basis 3) (&0)`] CMR_REPN_CONST);
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`;
                   `Q:num->real^3^3`; `c:num->real^2`; `\j. s * (R:num->real->real) j (&1)`;
                   `\y. (sigma:real^3->real->real^K) y (&1)`;
                   `(sigma:real^3->real->real^K) (basis 3) (&1)`] CMR_REPN_CONST)] THEN
  (ANTS_TAC THENL
    [ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC[IN_REAL_INTERVAL; IN_SPHERE_0] THEN
     SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
     DISCH_THEN(fun th -> ASM_SIMP_TAC[th])]));;

let CMR_FAM_ZERO = prove
 (`!S (G:real^K->real^K^K) N (Q:num->real^3^3) (c:num->real^2) R
    (sigma:real^3->real->real^K) y t.
     cmr_fam S G N Q c R sigma (&0) y t = sigma y t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_fam; REAL_MUL_LZERO] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Q:num->real^3^3`; `c:num->real^2`;
                 `\j:num. &0`; `\y. (sigma:real^3->real->real^K) y t`] CMR_REPN_ZERO) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN SIMP_TAC[]);;

let CMR_FAM_SWEEP = prove
 (`!S (G:real^K->real^K^K) d e N (Q:num->real^3^3) (c:num->real^2) R
    (sigma:real^3->real->real^K).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     cmr_famok S G e Q c R sigma
     ==> cm_sweep S (cmr_fam S G N Q c R sigma (&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN real_interval[&0,&1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[cm_sweep] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMW_END_CONT THEN MATCH_MP_TAC CMR_FAM_CONT THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMR_FAM_SMAP THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[CMR_REALLIM_WITHINREAL_SEQ] THEN
    X_GEN_TAC `x:num->real` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `N:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `R:num->real->real`;
                   `sigma:real^3->real->real^K`; `&1`; `t:real`; `\n:num. &1`;
                   `x:num->real`] CMR_FAM_SEQ) THEN
    ASM_REWRITE_TAC[REALLIM_CONST] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[o_DEF];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMR_FAM_ENDS THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let CMR_FAM_HOMOTOPIC = prove
 (`!S (G:real^K->real^K^K) d e N (Q:num->real^3^3) (c:num->real^2) R
    (sigma:real^3->real->real^K).
     cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
     cmr_famok S G e Q c R sigma
     ==> cm_shomotopic S sigma (cmr_fam S G N Q c R sigma (&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cm_shomotopic] THEN
  EXISTS_TAC `cmr_fam S (G:real^K->real^K^K) N (Q:num->real^3^3) (c:num->real^2) R
                (sigma:real^3->real->real^K)` THEN
  REWRITE_TAC[CMR_FAM_ZERO] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMR_FAM_CONT THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `N:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `R:num->real->real`;
                   `sigma:real^3->real->real^K`; `s:real`; `t:real`] CMR_FAM_SMAP) THEN
    ASM_SIMP_TAC[cm_smap];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMR_FAM_ENDS THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let CMR_REPN_SEN_LE = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:num->real^3^3) (c:num->real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ (!j. orthogonal_matrix (Q j)) /\
     (!m. &0 < r(SUC m)
          ==> wan_gdir (ball(c(SUC m),r(SUC m))) G
                (\x. cmr_repn S G m Q c r u (cm_capmap (Q(SUC m)) x)) <= e)
     ==> !m. cm_sen G (cmr_repn S G m Q c r u) <= cm_sen G u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:num->real^3^3`;
                 `c:num->real^2`; `r:num->real`; `u:real^3->real^K`] CMR_REPN_SMAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[cmr_repn; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `cm_sen G (cmr_repn S (G:real^K->real^K^K) m (Q:num->real^3^3) (c:num->real^2) r
                          (u:real^3->real^K))` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 < (r:num->real)(SUC m)` THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`;
                   `(Q:num->real^3^3)(SUC m)`; `(c:num->real^2)(SUC m)`;
                   `(r:num->real)(SUC m)`;
                   `cmr_repn S (G:real^K->real^K^K) m (Q:num->real^3^3) (c:num->real^2) r
                      (u:real^3->real^K)`; `Lam:real`] CMR_REP1_SEN_LE) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[CMR_REP1_NONPOS; REAL_ARITH `~(&0 < r) ==> r <= &0`; REAL_LE_REFL]]);;

let CMR_FAM_SEN_LE = prove
 (`!S (G:real^K->real^K^K) d e N (Q:num->real^3^3) (c:num->real^2) R
    (sigma:real^3->real->real^K) t.
     cm_target S G d /\ cmw_repex S G e /\ cmr_famok S G e Q c R sigma /\
     t IN real_interval[&0,&1]
     ==> cm_sen G (\y. cmr_fam S G N Q c R sigma (&1) y t) <= cm_sen G (\y. sigma y t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_famok] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP CMR_TARGET_GCOND) THEN
  REWRITE_TAC[cmr_fam; ETA_AX] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                 `Q:num->real^3^3`; `c:num->real^2`; `\j. &1 * (R:num->real->real) j t`;
                 `\y. (sigma:real^3->real->real^K) y t`] CMR_REPN_SEN_LE) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[cm_sweep]) THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    DISCH_THEN(ACCEPT_TAC o SPEC `N:num`)]);;

