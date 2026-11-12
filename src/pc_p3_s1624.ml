(* ========================================================================= *)
(* Unit pc_p3_s1624 (Part 3 proofs; MT Ch 16): MT Cor 16.24 (p. 388). In the *)
(* setting of Prop 16.4, a curve from x of L-length <= Lb back to T(i-1)     *)
(* gives a minimizing L-geodesic from x to its endpoint: a minimizing        *)
(* sequence to the endpoint stays in the compact set of Prop 16.21, and      *)
(* Lemma 7.2 gives a limit. The headline P3N_COR_16_24_FIX (with the second  *)
(* scale rr <= r') is stated against Prop 16.21 and the corrected Lemma 7.2  *)
(* body (its minimizer clause also gives the endpoint); route theorem        *)
(* P3N_COR_16_24_ROUTE.                                                      *)
(* ========================================================================= *)

needs "src/pc_p3_s1621.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Cor 16.24: MT Cor 16.24 (p. 388) with the second scale rr (passed through *)
(* to Prop 16.21) from Prop 16.21 and the corrected Lemma 7.2 (its minimizer *)
(* clause also gives the endpoint).  eps1624 = eps1621, dlt from             *)
(* 16.21 at (r',rr,Lb).  For the endpoint q of the given curve, a            *)
(* minimizing sequence of admissible curves to q with L <= Lb (the infimum   *)
(* rfs_Lx is approached since L is bounded below by -6 tau0 sqrt tau0,       *)
(* P3N_L_LOWER); 16.21 puts them in one compact K; Lemma 7.2 gives a         *)
(* limit, a minimizing L-geodesic to q.                                      *)
(* ========================================================================= *)

let P3N_COR_16_24_FIX = prove
 (`!u:A->bool.
     P3_PROP_16_21_STATEMENT u /\
     (!(hs:(A)rfs_history) x tt tau0 K gs Lb.
         rfs_history_ok hs /\ &0 < tau0 /\ tau0 < tt /\ p3_st_compact hs K /\
         (!n. rfs_L_adm hs tt x tau0 (gs n) /\ rfs_L_length hs tt (gs n) tau0 <= Lb /\
              !tau. &0 < tau /\ tau <= tau0 ==> gs n tau IN K (tt - tau))
         ==> ?sub gamma K'.
                p3_subseq sub /\ p3_st_compact hs K' /\ gamma (&0) = x /\
                (!tau. &0 < tau /\ tau <= tau0 ==> gamma tau IN K' (tt - tau)) /\
                (!eta. &0 < eta
                       ==> (?gamma'. rfs_L_adm hs tt x tau0 gamma' /\ gamma' tau0 = gamma tau0 /\
                                     (!tau. &0 < tau /\ tau <= tau0
                                            ==> gamma' tau IN K' (tt - tau)) /\
                                     ?N. !n. N <= n
                                         ==> rfs_L_length hs tt gamma' tau0 <=
                                             rfs_L_length hs tt (gs (sub n)) tau0 + eta) /\
                           (?N. !n. N <= n
                                ==> !tau. &0 <= tau /\ tau <= tau0
                                          ==> mfd_dist (rfs_top_at hs (tt - tau),
                                                        rfs_atlas_at hs (tt - tau))
                                                       (rfs_metric_at hs (tt - tau))
                                                       (gs (sub n) tau) (gamma tau) < eta)) /\
                !q. (!n. gs n tau0 = q) /\
                    (!eta. &0 < eta
                           ==> ?N. !n. N <= n
                                   ==> rfs_L_length hs tt (gs n) tau0 <=
                                       rfs_Lx hs tt x tau0 q + eta)
                    ==> rfs_min_Lgeod hs tt x tau0 gamma /\ gamma tau0 = q)
     ==> P3_COR_16_24_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_16_21_STATEMENT; P3_COR_16_24_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps1621:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1621")))
    (LABEL_TAC "l72")) THEN
  EXISTS_TAC `eps1621:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`] THEN
  STRIP_TAC THEN
  USE_THEN "p1621" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                                    `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "q1621")] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `r':real`;
                       `rr:real`; `Lb:real`] THEN
  STRIP_TAC THEN
  USE_THEN "q1621" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
                                    `r':real`; `rr:real`; `Lb:real`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k1621"))) THEN
  EXISTS_TAC `dlt:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`;
                       `x:A`; `tt:real`; `r:real`; `tau0:real`; `gamma:real->A`] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  (* the compact set of Prop 16.21 *)
  USE_THEN "k1621" (MP_TAC o SPECL [`rs':num->real`; `ks':num->real`; `dd:num->real`;
                                    `hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real->A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inK"))) THEN
  (* the setting *)
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ rfs_pinched (rfs_view hs)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd)
                                (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_p16_setting; p3_step_hyp; p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3_T (i - 1)` ASSUME_TAC THENL
   [REWRITE_TAC[p3_T] THEN SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_ARITH `&0 < &2 /\ &0 < &32`];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau0 < tt` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = (gamma:real->A) tau0` THEN
  (* a minimizing sequence of curves to q with L <= Lb *)
  SUBGOAL_THEN
   `!n. ?c:real->A. rfs_L_adm (hs:(A)rfs_history) tt x tau0 c /\ c tau0 = q /\
                    rfs_L_length hs tt c tau0 <= Lb /\
                    rfs_L_length hs tt c tau0 < rfs_Lx hs tt x tau0 q + inv(&n + &1)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`{rfs_L_length (hs:(A)rfs_history) tt c tau0 | c |
                     rfs_L_adm hs tt x tau0 c /\ (c:real->A) tau0 = q}`;
                   `rfs_Lx (hs:(A)rfs_history) tt x tau0 q + inv(&n + &1)`] INF_APPROACH) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        EXISTS_TAC `rfs_L_length (hs:(A)rfs_history) tt gamma tau0` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `--(&6 * tau0 * sqrt tau0)` THEN REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `y:real` THEN DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3N_L_LOWER THEN EXISTS_TAC `x:A` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[rfs_Lx] THEN MATCH_MP_TAC(REAL_ARITH `&0 < e ==> a < a + e`) THEN
        MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_CASES_TAC `rfs_L_length (hs:(A)rfs_history) tt c tau0 <= rfs_L_length hs tt gamma tau0`
    THENL
     [EXISTS_TAC `c:real->A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `gs:num->real->A` (LABEL_TAC "gs"))] THEN
  (* Lemma 7.2 *)
  USE_THEN "l72" (MP_TAC o SPECL [`hs:(A)rfs_history`; `x:A`; `tt:real`; `tau0:real`;
                                  `K:real->A->bool`; `gs:num->real->A`; `Lb:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN USE_THEN "gs" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    USE_THEN "inK" (MATCH_MP_TAC o SPECL [`tau0:real`; `(gs:num->real->A) n`]) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `gamma1:real->A`
    (X_CHOOSE_THEN `K':real->A->bool` (LABEL_TAC "lim")))) THEN
  EXISTS_TAC `gamma1:real->A` THEN
  USE_THEN "lim" (MP_TAC o SPEC `q:A` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                  CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "gs" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `eta:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "gs" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&N)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      MAP_EVERY UNDISCH_TAC [`~((N:num) = 0)`; `(N:num) <= n`] THEN ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
        [`inv(&N) < eta`; `inv(&n + &1) <= inv(&N)`;
         `rfs_L_length (hs:(A)rfs_history) tt ((gs:num->real->A) n) tau0 <
          rfs_Lx hs tt x tau0 q + inv(&n + &1)`] THEN
      REAL_ARITH_TAC];
    DISCH_THEN ACCEPT_TAC]);;

(* ========================================================================= *)
(* The route theorem for Cor 16.24 (the statement of Lemma 7.2 in the route, *)
(* with the endpoint in the minimizer clause, equals the hypothesis of       *)
(* P3N_COR_16_24_FIX).                                                       *)
(* ========================================================================= *)

let P3N_COR_16_24_ROUTE = prove
 (`!u:A->bool. P3_COR_16_24_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_COR_16_24_ROUTE_STATEMENT] THEN
  MP_TAC(ISPEC `u:A->bool` P3N_COR_16_24_FIX) THEN
  REWRITE_TAC[GSYM P2_LEMMA_7_2_STATEMENT]);;

