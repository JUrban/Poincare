(* ========================================================================= *)
(* Unit pc_p3_c177b: MT Lemma 17.7 (p. 403-406) from the                    *)
(* route inputs and the case (2b) statement P3H_177_FARNECK_STATEMENT       *)
(* (pc_p3_c177a).  It uses the route statements of pc_p3_route in the       *)
(* forms Prop 16.5 with a cutoff, R14 with eps0 first, and R12 with         *)
(* hs_time hs k < ts.                                                       *)
(*                                                                         *)
(* The assembly of the constants (as P3H_PART_D in                          *)
(* pc_p3_c172f: each constant is chosen with its properties).               *)
(* ========================================================================= *)

needs "src/pc_p3_c177a.ml";;
needs "src/pc_p3_route.ml";;

prioritize_real();;
type_invention_error := true;;

let P3H_LEMMA_17_7_FROM_FAR = prove
 (`!u:A->bool.
     P3_PROP_16_5_STATEMENT u /\ P3_STD_C2_BOUND_STATEMENT /\ P2_THM_12_32_STATEMENT /\
     P2_PROP_12_31_STATEMENT /\ P2_PROP_12_7_STATEMENT /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\ P2_PROP_9_79_NECK_STATEMENT (:real^3) u /\
     P3H_177_FARNECK_STATEMENT u
     ==> P3_LEMMA_17_7_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P3_PROP_16_5_STATEMENT; P3_STD_C2_BOUND_STATEMENT; P2_THM_12_32_STATEMENT;
              P2_PROP_12_31_STATEMENT; P2_PROP_12_7_STATEMENT; P2C_HISTORY_REGULAR_STATEMENT;
              P2C_FLOW_VIEW_REGULAR_STATEMENT; P2_PROP_9_79_NECK_STATEMENT;
              P3H_177_FARNECK_STATEMENT; P3_LEMMA_17_7_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps165:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "165")))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps0R:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R14")))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `eps0T:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1232")))
        (CONJUNCTS_THEN2 (LABEL_TAC "1231")
          (CONJUNCTS_THEN2 (LABEL_TAC "127")
            (CONJUNCTS_THEN2 (LABEL_TAC "reg")
              (CONJUNCTS_THEN2 (LABEL_TAC "freg")
                (CONJUNCTS_THEN2 (LABEL_TAC "N979")
                  (X_CHOOSE_THEN `epsF:real`
                     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FAR"))))))))))) THEN
  MP_TAC P3H_CAP_TO_HIST_GEN THEN
  DISCH_THEN(X_CHOOSE_THEN `KC:real` (X_CHOOSE_THEN `eps0C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))))) THEN
  MP_TAC P3H_NECK_IN_REGION THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1N:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NIR"))) THEN
  EXISTS_TAC `min (&1 / &8) (min eps165 (min eps1N (min eps0C (min eps0T
                (min eps0R (min epsF (&1 / &5)))))))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `g0:real^3->real^3^3`; `A0:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  (* stage 2 *)
  USE_THEN "FAR" (MP_TAC o SPECL [`eps:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `KF:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FAR2"))) THEN
  SUBGOAL_THEN `?eps_in. &0 < eps_in /\ eps_in <= eps /\ eps_in <= &1 / &2 /\
                         KC * eps_in <= eps /\ KF * eps_in <= eps /\ eps_in < eps`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `eps / max (max KC KF) (&40)` THEN
    MP_TAC(SPECL [`eps:real`; `max KC KF`; `eps / max (max KC KF) (&40)`] P3H_NUM_EPSIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `ei = eps / max (max KC KF) (&40)` THEN
    SUBGOAL_THEN `KC * ei <= max KC KF * ei /\ KF * ei <= max KC KF * ei` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&40 * ei` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `max (max KC KF) (&40) * ei` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "ei" THEN
      SUBGOAL_THEN `&0 < max (max KC KF) (&40)` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  USE_THEN "1232" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps_in:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C_in:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T"))) THEN
  USE_THEN "N979" (MP_TAC o SPECL [`eps_in:real`; `eps:real`; `&1 + eps_in`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `deltaN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N2"))) THEN
  EXISTS_TAC `&2 * C_in + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `hf:real->real->real`; `md:real->real`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `Ap:real`;
                       `Dp:real`; `tb:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `tb:real` P3H_NUM_RSTAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `inv(&8 * (&1 + tb))` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r':real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `tb * r' pow 2 <= &1 / &64` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tb * inv(&8 * (&1 + tb)) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* stage 4: the constants after r' *)
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
  SUBGOAL_THEN
   `?theta0 theta1. &0 <= theta0 /\ theta0 < theta1 /\ theta1 < &1 /\ &1 / &2 <= theta1 /\
                    !s. theta0 <= s /\ s < theta1
                        ==> &2 * (&4 * Dp * tb) + &144 * (&1 / &1000) < c / (&1 - s)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`max (&0) (&1 - c / (&2 * (&4 * Dp * tb) + &144 * (&1 / &1000) + &1))`;
      `(&1 + max (&0) (&1 - c / (&2 * (&4 * Dp * tb) + &144 * (&1 / &1000) + &1))) / &2`] THEN
    MATCH_MP_TAC P3H_NUM_THETA THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `Dp:real`; `Ap:real`; `C_in:real`; `eps_in:real`; `theta1:real`]
               P3H_177_NUM_EPSN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps_n:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `eps_n:real` P3H_CAP_IN_REGION_GEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0n:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CIR"))) THEN
  USE_THEN "NIR" (MP_TAC o SPEC `eps_n:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NIR2"))) THEN
  MP_TAC(SPEC `eps_n:real` P3H_LIFT_SHORT_CURVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0l:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LF"))) THEN
  SUBGOAL_THEN `?ddx. &0 < ddx /\ ddx <= dd0n /\ ddx <= dd0r /\ ddx <= dd0l /\ ddx <= &1 / &2`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (min dd0n dd0r) (min dd0l (&1 / &2))` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
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
  USE_THEN "FAR2" (MP_TAC o SPECL [`eps_in:real`; `C:real`; `hf:real->real->real`;
                                   `md:real->real`; `i:num`; `rs:num->real`; `ks:num->real`;
                                   `ds:num->real`; `r':real`; `m:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dF:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FAR3"))) THEN
  MP_TAC(SPECL [`Kr:real`; `c:real`; `delta:real`; `deltaN:real`; `eps_n:real`; `ddx:real`;
                `dF:real`; `&1 / &1000`] P3H_NUM_DQ2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dq2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s. theta0 <= s /\ s < theta1 ==> &2 * (&4 * Dp * tb) + &144 * dq2 < c / (&1 - s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `theta0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`A0:real`; `D:real`; `c:real`] P3H_NUM_DD3C) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd3:real` STRIP_ASSUME_TAC) THEN
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
  EXISTS_TAC `min (min d0 ((md:real->real) dd3)) dF` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?dlt. dlt = min (min d0 ((md:real->real) dd3)) dF` (X_CHOOSE_TAC `dlt:real`) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dlt <= d0 /\ dlt <= (md:real->real) dd3 /\ dlt <= dF` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `dlt:real`)) THEN
  (* stage 5: the history *)
  MAP_EVERY X_GEN_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`;
                       `ts:real`; `x:A`; `y:A`; `k:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_canonical_assumption (rfs_trunc (rfs_view (hs:(A)rfs_history)) ts) C eps
                  (p3_stepf rs')` ASSUME_TAC THENL
   [MATCH_MP_TAC P3_CANONV_ASSUMPTION_IMP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[p3_step_hyp; p3_struct] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_step_hyp")) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [USE_THEN "reg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `r':real`; `dlt:real`; `rs':num->real`; `ks':num->real`;
                 `dd:num->real`; `hs:(A)rfs_history`; `ts:real`; `x:A`; `y:A`; `k:num`;
                 `j:num`; `tb:real`] P3H_177_HIST_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->A` (X_CHOOSE_THEN `xi:real^3->real^3`
    (X_CHOOSE_THEN `qy:real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `(y:A) = (Phi:real^3->A) qy`)) THEN
  ABBREV_TAC `h = p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time (hs:(A)rfs_history) k)` THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `dlt:real`; `rs':num->real`; `ks':num->real`; `dd:num->real`;
                 `hs:(A)rfs_history`; `ts:real`; `r':real`; `m:real`; `dq2:real`; `theta1:real`;
                 `d0:real`; `k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `qy:real^3`;
                 `h:real`] P3H_D_165) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`; `c:real`;
                 `C_in:real`; `eps_in:real`; `Kr:real`] P3H_STD_FLOW_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "freg" (MP_TAC o ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                                    `&0`; `&1`; `G:real->real^3->real^3^3`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN] THEN
    UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[p3_std_flow; p3_partial_std];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`;
                 `hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`;
                 `md:real->real`; `p3_stepf dd`; `p3_hscale hf (p3_stepf rs') (p3_stepf dd)`;
                 `ts:real`; `(Phi:real^3->A) qy`; `qy:real^3`; `c:real`; `D:real`; `Dp:real`;
                 `tb:real`; `Q:real`; `Kr:real`; `theta0:real`; `theta1:real`; `m:real`;
                 `dd3:real`; `dq2:real`] P3H_177_CLAIM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the normalized time t' = tq and the closeness read at ts *)
  ABBREV_TAC `tq = (ts - hs_time (hs:(A)rfs_history) k) / h pow 2` THEN
  SUBGOAL_THEN `&0 < tq /\ hs_time (hs:(A)rfs_history) k + tq * h pow 2 = ts`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tq" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `{x:real^3 | p3_std_dist g0 x < m}`;
                 `hs:(A)rfs_history`; `hs_time (hs:(A)rfs_history) k`; `h:real`; `Phi:real^3->A`;
                 `{s | &0 <= s /\ s < theta1 /\ hs_time (hs:(A)rfs_history) k + s * h pow 2 <= ts /\
                       hs_time hs k + s * h pow 2 < rfs_horizon hs}`;
                 `dq2:real`; `tq:real`] P3H_VIEW_CLOSE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `hausdorff_space (rfs_top_at (hs:(A)rfs_history) ts) /\
                smooth_manifold_atlas (rfs_top_at hs ts) (rfs_atlas_at hs ts) /\
                riemannian_metric (rfs_atlas_at hs ts) (rfs_metric_at hs ts) /\
                compact_space (rfs_top_at hs ts)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts:real`] P3_HIST_VIEW_SLICES) THEN
    ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `p2c_regular_view (rfs_view (hs:(A)rfs_history))` THEN
      REWRITE_TAC[p2c_regular_view; P2C_RFS_VIEW_PARTS] THEN
      DISCH_THEN(MP_TAC o SPEC `ts:real` o CONJUNCT1) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      MATCH_MP_TAC P3H_HIST_COMPACT_AT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (:real^3) ((G:real->real^3->real^3^3) tq)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. A1 < p3_std_dist g0 z
        ==> lck_dist2 (rfs_kreg epsp) (mpullback (p3_std_nc g0 A0) (cylinder_flow tq))
              ((G:real->real^3->real^3^3) tq) z < epsp pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "A1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `(G:real->real^3->real^3^3) tq`; `tq:real`;
                 `A1:real`; `epsp:real`; `eps_n:real`; `ddx:real`; `d1:real`]
                P3H_SHELL_CLOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!y. p3_std_dist g0 y < m
        ==> lck_dist2 (rfs_kreg eps_n) ((G:real->real^3->real^3^3) tq)
              (\z. inv(h pow 2) %%
                   rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) ts) (Phi:real^3->A)
                                (rfs_metric_at hs ts) z) y < ddx pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg dq2) ((G:real->real^3->real^3^3) tq)
                  (\w. inv(h pow 2) %%
                       rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) ts) (Phi:real^3->A)
                                    (rfs_metric_at hs ts) w) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `{w:real^3 | p3_std_dist g0 w < m}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN
        MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) ts`; `rfs_atlas_at (hs:(A)rfs_history) ts`;
                       `{w:real^3 | p3_std_dist g0 w < m}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
         [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
          EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) ts` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]];
        MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `dq2 pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the lift of the path from y = Phi qy to x *)
  MP_TAC(ISPECL [`h:real`; `Q:real`; `c:real`; `Dp:real`; `tq:real`; `theta1:real`;
                 `eps_n:real`; `Ap:real`] P3H_177_LIFT_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `rfs_top_at (hs:(A)rfs_history) ts`;
                 `rfs_atlas_at (hs:(A)rfs_history) ts`; `rfs_metric_at (hs:(A)rfs_history) ts`;
                 `Phi:real^3->A`; `m:real`; `h:real`; `(G:real->real^3->real^3^3) tq`; `tq:real`;
                 `d1:real`; `ddx:real`; `dd0l:real`; `eps_n:real`; `x:A`; `(Phi:real^3->A) qy`;
                 `qy:real^3`; `Ap * inv(sqrt Q)`] P3H_177_LIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(ASM_REAL_ARITH_TAC) THEN
    UNDISCH_TAC `(Phi:real^3->A) qy IN rfs_vball (rfs_view (hs:(A)rfs_history)) ts x
                                     (Ap * inv(sqrt Q))` THEN
    REWRITE_TAC[rfs_view; rfs_vball];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  (* Thm 12.32, R14 and Prop 12.31 at (q, t') *)
  SUBGOAL_THEN `tq < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "T" (MP_TAC o SPECL [`G:real->real^3->real^3^3`; `q:real^3`; `tq:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!z U. rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3))
            ((G:real->real^3->real^3^3) tq) C_in eps_in z U
          ==> !y l. y IN U /\ l <= 2
                    ==> lrm_deriv_norm2 l
                          (metric_local (open_set_atlas (:real^3))
                             (chart_at (open_set_atlas (:real^3)) y)
                             (\w. mfd_scalar (open_set_atlas (:real^3)) (G tq) z %% G tq w))
                          (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "K" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c <= mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tq) q`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / (&1 - tq)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `tq < &1 ==> &0 < &1 - tq`] THEN
      SUBGOAL_THEN `&0 <= c * tq` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      USE_THEN "c" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 - theta1) / (&2 * eps_n) <= sqrt(&1 - tq) / (&2 * eps_n)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < e ==> &0 < &2 * e`] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* case (2b): the far neck of short length, by P3H_177_FARNECK_STATEMENT *)
  SUBGOAL_THEN
   `!e. rfs_evolving_neck
          (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
          eps_in q tq (tq * mfd_scalar (open_set_atlas (:real^3))
                                       ((G:real->real^3->real^3^3) tq) q) e /\
        (!z. z IN IMAGE e (rfs_neck_dom eps_in) ==> A0 + &5 <= p3_std_dist g0 z) /\
        tq * mfd_scalar (open_set_atlas (:real^3)) (G tq) q < &1 + eps_in
        ==> p3_canonv_at (rfs_view (hs:(A)rfs_history)) C eps x ts`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^3->real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `rfs_neck (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tq)
                           eps_in q e` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_evolving_neck
          (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                         (G:real->real^3->real^3^3)) eps_in q tq
          (tq * mfd_scalar (open_set_atlas (:real^3)) (G tq) q) e` THEN
      REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
      REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in) SUBSET
                  {z | p3_std_dist g0 z < (d1 + inv eps_n) + inv eps_n}` ASSUME_TAC THENL
     [USE_THEN "NIR2" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`A0:real`; `(G:real->real^3->real^3^3) tq`; `tq:real`; `m:real`;
                            `ddx:real`; `q:real^3`; `c:real`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC P3H_SHELL_CLOSE THEN
      MAP_EVERY EXISTS_TAC [`A1:real`; `epsp:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "FAR3" (MP_TAC o SPECL
     [`dlt:real`; `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`;
      `k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `ts:real`; `x:A`;
      `G:real->real^3->real^3^3`; `theta1:real`; `dq2:real`; `tq:real`;
      `q:real^3`; `e:real^3->real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(ASM_REAL_ARITH_TAC) THEN
      UNDISCH_TAC `IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in) SUBSET
                   {z | p3_std_dist g0 z < (d1 + inv eps_n) + inv eps_n}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC `(d1 + inv eps_n) + inv eps_n` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`; `hs:(A)rfs_history`;
    `hs_time (hs:(A)rfs_history) k`; `ts:real`; `h:real`; `Phi:real^3->A`; `theta1:real`;
    `dq2:real`; `m:real`; `tq:real`; `q:real^3`; `x:A`; `C:real`; `eps:real`; `C_in:real`;
    `eps_in:real`; `Kr:real`; `c:real`; `delta:real`; `deltaN:real`; `eps_n:real`;
    `eps1N:real`; `dd0n:real`; `dd0r:real`; `ddx:real`; `d1 + inv eps_n`; `A1:real`;
    `epsp:real`; `d:real`] P3H_177_CASES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

