(* ========================================================================= *)
(* Unit pc_p3_c172f: MT Lemma 17.2, part D (subcase (ii), MT p. 398-401) and *)
(* the route theorem P3_LEMMA_17_2_ROUTE.  It uses the route statements of   *)
(* pc_p3_route in the forms: Prop 16.5 with a cutoff, R14 with eps0 before   *)
(* C, and Prop 12.7 in the route.                                            *)
(*                                                                           *)
(* The final assembly of the constants of part D, and the route theorem from *)
(* P3H_LEMMA_17_2_FROM_D_V (pc_p3_c172v: the canonv form of Lemma 17.2).     *)
(* Each constant is chosen with its properties (no min or max equations in  *)
(* the assumptions, which keeps the arithmetic fast).                       *)
(* ========================================================================= *)

needs "src/pc_p3_c172e.ml";;
needs "src/pc_p3_route.ml";;
needs "src/pc_p3_c172v.ml";;

prioritize_real();;
type_invention_error := true;;

let P3H_PART_D = prove
 (`!u:A->bool.
     P3_PROP_16_5_STATEMENT u /\ P3_STD_C2_BOUND_STATEMENT /\ P2_THM_12_32_STATEMENT /\
     P2_PROP_12_31_STATEMENT /\ P2_PROP_12_7_STATEMENT /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> P3H_PART_D_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P3_PROP_16_5_STATEMENT; P3_STD_C2_BOUND_STATEMENT; P2_THM_12_32_STATEMENT;
              P2_PROP_12_31_STATEMENT; P2_PROP_12_7_STATEMENT; P2C_HISTORY_REGULAR_STATEMENT;
              P3H_PART_D_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps165:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "165")))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps0R:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R14")))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `eps0T:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1232")))
        (CONJUNCTS_THEN2 (LABEL_TAC "1231")
          (CONJUNCTS_THEN2 (LABEL_TAC "127") (LABEL_TAC "reg")))))) THEN
  MP_TAC P3H_D_CLAIM THEN
  DISCH_THEN(X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CL"))) THEN
  MP_TAC P3H_D_FINISH THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1F:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FN"))) THEN
  MP_TAC P3H_CAP_TO_HIST THEN
  DISCH_THEN(X_CHOOSE_THEN `KC:real` (X_CHOOSE_THEN `eps0C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))))) THEN
  EXISTS_TAC `min (&1 / &8) (min eps165 (min eps3 (min eps1F (min eps0C (min eps0T eps0R)))))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `g0:real^3->real^3^3`; `A0:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  (* stage 2: eps_in and the cap constant C_in of Thm 12.32 *)
  SUBGOAL_THEN `?eps_in. &0 < eps_in /\ eps_in <= eps /\ eps_in <= &1 / &2 /\
                         KC * eps_in <= eps /\ eps_in * (&7 * (inv eps + &5) + &1) <= &1`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `eps / max KC (&40)` THEN MATCH_MP_TAC P3H_NUM_EPSIN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "1232" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps_in:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C_in:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T"))) THEN
  EXISTS_TAC `&2 * C_in + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `hf:real->real->real`; `md:real->real`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `r':real`] THEN
  STRIP_TAC THEN
  (* stage 4: the constants depending on C *)
  USE_THEN "R14" (MP_TAC o SPECL [`C_in:real`; `eps_in:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K"))) THEN
  USE_THEN "CF" (MP_TAC o SPECL [`C_in:real`; `eps_in:real`; `C:real`; `eps:real`; `Kr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CFd"))) THEN
  USE_THEN "1231" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c"))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &4`] P3H_STD_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M = &6 * D` THEN
  SUBGOAL_THEN `?dq. &0 < dq /\ dq <= &1 / &300 /\ &72 * sqrt Kr * dq <= &1 / &2 /\
                     &1 + &72 * dq < (&1 + eps_in) * (&1 - &72 * sqrt Kr * dq)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1 / &300) (eps_in / (&500 * (&1 + sqrt Kr)))` THEN
    MATCH_MP_TAC P3H_NUM_DQ THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?theta0 theta1. &0 <= theta0 /\ theta0 < theta1 /\ theta1 < &1 /\ &1 / &2 <= theta1 /\
                    !s. theta0 <= s /\ s < theta1 ==> &2 * M + &144 * dq < c / (&1 - s)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`max (&0) (&1 - c / (&2 * M + &144 * dq + &1))`;
                          `(&1 + max (&0) (&1 - c / (&2 * M + &144 * dq + &1))) / &2`] THEN
    MATCH_MP_TAC P3H_NUM_THETA THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?eps_n. &0 < eps_n /\ eps_n <= &1 / &4 /\
                        &3 * eps_n * (inv eps + &5 + C_in) <= sqrt(&1 - theta1)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1 / &4) (sqrt(&1 - theta1) / (&3 * (inv eps + &5 + C_in)))` THEN
    MATCH_MP_TAC P3H_NUM_EPSN THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "FN" (MP_TAC o SPEC `eps_n:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ddx:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FN2"))) THEN
  SUBGOAL_THEN `?epsp. &0 < epsp /\ epsp <= eps_n /\ epsp <= ddx` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min eps_n ddx` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "127" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `theta1:real`; `epsp:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A1"))) THEN
  SUBGOAL_THEN `&0 < inv eps_n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?d1 m. A0 + &4 < d1 /\ inv eps_n < d1 /\ A1 + inv eps_n < d1 /\
                       d1 + inv eps_n + inv eps_n < m /\ &0 < m`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`abs A0 + abs A1 + inv eps_n + &5`;
                          `abs A0 + abs A1 + inv eps_n + &5 + inv eps_n + inv eps_n + &1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < delta / &3 pow (rfs_kreg delta)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?dq2. &0 < dq2 /\ dq2 <= dq /\ dq2 <= delta / &3 pow (rfs_kreg delta) /\
                      dq2 <= eps_n /\ dq2 <= ddx`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (min dq (delta / &3 pow (rfs_kreg delta))) (min eps_n ddx)` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?dd3. &0 < dd3 /\ dd3 <= &1 / &10 /\ A0 + &4 < inv dd3 /\
                      &72 * (&1 + D) * dd3 <= D`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1 / &10) (min (inv(abs A0 + &5)) (D / (&72 * (&1 + D))))` THEN
    MATCH_MP_TAC P3H_NUM_DD3 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&72 * sqrt Kr * dq2 <= &1 / &2 /\
                (!s. theta0 <= s /\ s < theta1 ==> &2 * M + &144 * dq2 < c / (&1 - s))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&72 * sqrt Kr * dq` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `theta0:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "165" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                                  `g0:real^3->real^3^3`; `A0:real`; `r':real`; `m:real`;
                                  `dq2:real`; `theta1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "165d"))) THEN
  SUBGOAL_THEN `&0 < (md:real->real) dd3` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `dd3:real` o REWRITE_RULE[p3_modulus] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_modulus")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min d0 ((md:real->real) dd3)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?dlt. dlt = min d0 ((md:real->real) dd3)` (X_CHOOSE_TAC `dlt:real`) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dlt <= d0 /\ dlt <= (md:real->real) dd3` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `dlt:real`)) THEN
  (* stage 5: the history *)
  MAP_EVERY X_GEN_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`;
                       `ts:real`; `x:A`; `e:real^3->A`; `p1:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[p3_step_hyp; p3_struct] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_step_hyp")) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [USE_THEN "reg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `r':real`; `dlt:real`; `rs':num->real`;
                 `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`; `ts:real`; `x:A`;
                 `e:real^3->A`; `p1:real`] P3H_D_HIST_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `Phi:real^3->A`
    (X_CHOOSE_THEN `xi:real^3->real^3` (X_CHOOSE_THEN `y0:real^3`
    (X_CHOOSE_THEN `qy:real^3` STRIP_ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `hs_time (hs:(A)rfs_history) k`)) THEN
  SUBGOAL_THEN `!tau. hs_time (hs:(A)rfs_history) k < tau /\ tau <= ts
                      ==> (Phi:real^3->A) qy IN topspace(rfs_top_at hs tau)` ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(e:real^3->A) y0 = (Phi:real^3->A) qy`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `h = p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time (hs:(A)rfs_history) k)` THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `dlt:real`; `rs':num->real`; `ks':num->real`; `dd:num->real`;
                 `hs:(A)rfs_history`; `ts:real`; `r':real`; `m:real`; `dq2:real`; `theta1:real`;
                 `d0:real`; `k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `qy:real^3`;
                 `h:real`] P3H_D_165) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "CL" (MP_TAC o SPECL
   [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`; `hs:(A)rfs_history`;
    `k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `md:real->real`; `p3_stepf dd`;
    `p3_hscale hf (p3_stepf rs') (p3_stepf dd)`; `ts:real`; `x:A`; `eps:real`; `e:real^3->A`;
    `y0:real^3`; `qy:real^3`; `C_in:real`; `eps_in:real`; `Kr:real`; `c:real`; `D:real`;
    `M:real`; `dq2:real`; `theta0:real`; `theta1:real`; `m:real`; `dd3:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[ASSUME
    `p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time (hs:(A)rfs_history) k) = h`]) THEN
  DISCH_TAC THEN
  USE_THEN "FN2" (MP_TAC o SPECL
   [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`; `hs:(A)rfs_history`;
    `hs_time (hs:(A)rfs_history) k`; `ts:real`; `h:real`; `Phi:real^3->A`; `x:A`; `eps:real`;
    `e:real^3->A`; `y0:real^3`; `qy:real^3`; `C:real`; `C_in:real`; `eps_in:real`; `Kr:real`;
    `dq:real`; `delta:real`; `ddx:real`; `A1:real`; `epsp:real`; `d1:real`; `m:real`;
    `dq2:real`; `theta1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let P3_LEMMA_17_2_ROUTE = prove
 (`!u:A->bool. P3_LEMMA_17_2_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_LEMMA_17_2_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P3H_LEMMA_17_2_FROM_D_V THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3H_PART_D THEN ASM_REWRITE_TAC[]);;

