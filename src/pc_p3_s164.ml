(* ========================================================================= *)
(* Unit pc_p3_s164 (Part 3 proofs; MT Ch 16): MT Prop 16.4 (p. 389, proof    *)
(* pp. 389-391). In the setting of Prop 16.4, the set U of points reached    *)
(* from x by admissible curves with Lx < Lbar over [T(i-1),tt) is open in    *)
(* space-time, reached by minimizing L-geodesics (Cor 16.24), has nonempty   *)
(* slices with attained slice minima of Lx at most 3 sqrt(tt - t) (Lemma     *)
(* 7.2, Prop 16.21, the corrected Cor 7.12), and its slice minimizers over   *)
(* compact time intervals lie in a compact set. The headline                 *)
(* P3N_PROP_16_4_FIX (with the second scale rr <= r') is stated against      *)
(* Prop 16.21, Cor 16.24 and the corrected Cor 7.12 body; route theorem      *)
(* P3N_PROP_16_4_ROUTE.                                                      *)
(* ========================================================================= *)

needs "src/pc_p3_s1621.ml";;
needs "src/pc_p2a_l72w.ml";;
needs "src/pc_p2a_p164.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Prop 16.4: the reached set U (MT p. 389: points y at time               *)
(* t in [T(i-1),tt) reached from x by admissible curves, with Lx(y) < Lbar)*)
(* and basic facts on the reduced length infimum rfs_Lx: it is bounded     *)
(* below and approached (that it is below the L-length of every admissible *)
(* curve is P2AO_LX_LE_HIST), and the end point of an admissible curve     *)
(* persists two-sidedly.                                                    *)
(* ========================================================================= *)

let p3n_u164 = new_definition
 `p3n_u164 (hs:(A)rfs_history) (tt:real) (x:A) (T0:real) (Lbar:real) (t:real) =
    {y | T0 <= t /\ t < tt /\
         (?gamma. rfs_L_adm hs tt x (tt - t) gamma /\ gamma (tt - t) = y) /\
         rfs_Lx hs tt x (tt - t) y < Lbar}`;;

let P3N_LX_SET_FACTS = prove
 (`!(hs:(A)rfs_history) tt x b q.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     (?gamma. rfs_L_adm hs tt x b gamma /\ gamma b = q)
     ==> ~({rfs_L_length hs tt gamma b | gamma | rfs_L_adm hs tt x b gamma /\ gamma b = q} = {}) /\
         (!z. z IN {rfs_L_length hs tt gamma b | gamma | rfs_L_adm hs tt x b gamma /\ gamma b = q}
              ==> --(&6 * b * sqrt b) <= z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `c:real->A`))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `rfs_L_length (hs:(A)rfs_history) tt c b` THEN EXISTS_TAC `c:real->A` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P3N_L_LOWER THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]]);;

let P3N_LX_LOWER = prove
 (`!(hs:(A)rfs_history) tt x b q.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     (?gamma. rfs_L_adm hs tt x b gamma /\ gamma b = q)
     ==> --(&6 * b * sqrt b) <= rfs_Lx hs tt x b q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `b:real`; `q:A`]
                P3N_LX_SET_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[rfs_Lx] THEN MATCH_MP_TAC REAL_LE_INF THEN ASM_REWRITE_TAC[]);;

let P3N_LX_APPROACH = prove
 (`!(hs:(A)rfs_history) tt x b q c.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     (?gamma. rfs_L_adm hs tt x b gamma /\ gamma b = q) /\ rfs_Lx hs tt x b q < c
     ==> ?gamma. rfs_L_adm hs tt x b gamma /\ gamma b = q /\ rfs_L_length hs tt gamma b < c`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `b:real`; `q:A`]
                P3N_LX_SET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{rfs_L_length (hs:(A)rfs_history) tt gamma b | gamma |
                   rfs_L_adm hs tt x b gamma /\ (gamma:real->A) b = q}`; `c:real`]
                INF_APPROACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM rfs_Lx] THEN EXISTS_TAC `--(&6 * b * sqrt b)` THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;

(* the end point of an admissible curve persists for a while in both directions *)

let P3N_REACHED_PERSISTS = prove
 (`!(hs:(A)rfs_history) tt x b (gamma:real->A).
     rfs_history_ok hs /\ rfs_L_adm hs tt x b gamma /\ b < tt
     ==> ?W eta. &0 < eta /\ gamma b IN W /\
                 rfs_persists (rfs_view hs) W (tt - b - eta) (tt - b + eta)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_L_adm] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_smooth_pt" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_smooth_pt] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(gamma:real->A) b IN topspace(rfs_top_at hs (tt - b))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_st_curve (hs:(A)rfs_history) tt (gamma:real->A) (&0) b` THEN
    REWRITE_TAC[rfs_st_curve] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - b`; `(gamma:real->A) b`] P2A_TOPSPACE_LIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - b`] P2AB_LIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`;
                        `min eta ((hs_time (hs:(A)rfs_history) (k + 1) - (tt - b)) / &2)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W (tt - b - eta) (tt - b)` THEN
  REWRITE_TAC[rfs_persists; rfs_view] THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s <= tt - b` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tt - b:real`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `tt - b:real`] APX_RFS_SLAB) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Prop 16.4: the minimum of Lx on a nonempty slice of the                *)
(* reached set is attained (MT p. 389): a minimizing sequence of curves    *)
(* with L < Lbar lies in the compact set K of Prop 16.21, so by Lemma 7.2  *)
(* it subconverges, and the competitor curves to the limit end point show  *)
(* that Lx there is at most the infimum.                                    *)
(* ========================================================================= *)

let P3N_INV_SUC_LE = prove
 (`!m n. m <= n ==> inv(&n + &1) <= inv(&m + &1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC);;

let P3N_U164_MIN = prove
 (`!(hs:(A)rfs_history) tt x T0 Lbar K t.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ &0 < T0 /\ T0 <= t /\ t < tt /\
     p3_st_compact hs K /\
     (!b gamma. &0 < b /\ b <= tt - T0 /\ rfs_L_adm hs tt x b gamma /\
                rfs_L_length hs tt gamma b <= Lbar
                ==> !tau. &0 < tau /\ tau <= b ==> gamma tau IN K (tt - tau)) /\
     ~(p3n_u164 hs tt x T0 Lbar t = {})
     ==> ?m. m IN p3n_u164 hs tt x T0 Lbar t /\
             !z. z IN p3n_u164 hs tt x T0 Lbar t
                 ==> rfs_Lx hs tt x (tt - t) m <= rfs_Lx hs tt x (tt - t) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `b = tt - t:real` THEN
  SUBGOAL_THEN `&0 < b /\ b < tt /\ b <= tt - T0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Us = p3n_u164 (hs:(A)rfs_history) tt x T0 Lbar t` THEN
  SUBGOAL_THEN
   `!z:A. z IN Us <=> (?gamma. rfs_L_adm (hs:(A)rfs_history) tt x b gamma /\ gamma b = z) /\
                     rfs_Lx hs tt x b z < Lbar`
  ASSUME_TAC THENL
   [EXPAND_TAC "Us" THEN EXPAND_TAC "b" THEN REWRITE_TAC[p3n_u164; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> LABEL_TAC "us1" (GEN `z:A` (fst(EQ_IMP_RULE(SPEC `z:A` th)))) THEN
                          LABEL_TAC "us2" (GEN `z:A` (snd(EQ_IMP_RULE(SPEC `z:A` th))))) THEN
  (* the infimum *)
  ABBREV_TAC `I0 = inf(IMAGE (rfs_Lx (hs:(A)rfs_history) tt x b) Us)` THEN
  SUBGOAL_THEN `~(IMAGE (rfs_Lx (hs:(A)rfs_history) tt x b) Us = {}) /\
                (!w. w IN IMAGE (rfs_Lx hs tt x b) Us ==> --(&6 * b * sqrt b) <= w)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:A` THEN
    DISCH_TAC THEN USE_THEN "us1" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN Us`)) THEN
    STRIP_TAC THEN MATCH_MP_TAC P3N_LX_LOWER THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. z IN Us ==> I0 <= rfs_Lx (hs:(A)rfs_history) tt x b z` (LABEL_TAC "inf")
  THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "I0" THEN MATCH_MP_TAC INF_LE_ELEMENT THEN
    CONJ_TAC THENL
     [EXISTS_TAC `--(&6 * b * sqrt b)` THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* a minimizing sequence of curves *)
  SUBGOAL_THEN
   `!n. ?c:real->A. rfs_L_adm (hs:(A)rfs_history) tt x b c /\ c b IN Us /\
                    rfs_L_length hs tt c b < Lbar /\
                    rfs_L_length hs tt c b < I0 + &2 * inv(&n + &1)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 < inv(&n + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (rfs_Lx (hs:(A)rfs_history) tt x b) Us`; `I0 + inv(&n + &1)`]
                  INF_APPROACH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `--(&6 * b * sqrt b)` THEN FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    USE_THEN "us1" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN Us`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `b:real`; `z:A`;
                   `min Lbar (rfs_Lx (hs:(A)rfs_history) tt x b z + inv(&n + &1))`]
                  P3N_LX_APPROACH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real->A` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_L_length (hs:(A)rfs_history) tt c b <
                 min Lbar (rfs_Lx hs tt x b z + inv(&n + &1))` THEN
    UNDISCH_TAC `rfs_Lx (hs:(A)rfs_history) tt x b z < I0 + inv(&n + &1)` THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `gs:num->real->A` (LABEL_TAC "gs"))] THEN
  (* Lemma 7.2 *)
  MP_TAC(SPECL [`hs:(A)rfs_history`; `x:A`; `tt:real`; `b:real`; `K:real->A->bool`;
                `gs:num->real->A`; `Lbar:real`]
         (REWRITE_RULE[P2_LEMMA_7_2_STATEMENT] (ISPEC `(:A)` P2AY_LEMMA_7_2))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "gs" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE];
      FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`b:real`; `(gs:num->real->A) n`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `K:real->A->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `gam:real->A`
    (X_CHOOSE_THEN `K':real->A->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN
    UNDISCH_TAC `p3_subseq (sub:num->num)` THEN REWRITE_TAC[p3_subseq];
    ALL_TAC] THEN
  (* the limit end point m *)
  SUBGOAL_THEN
   `!eta. &0 < eta
          ==> ?gamma'. rfs_L_adm (hs:(A)rfs_history) tt x b gamma' /\
                       gamma' b = (gam:real->A) b /\
                       rfs_L_length hs tt gamma' b < I0 + eta`
  (LABEL_TAC "comp") THENL
   [X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `eta / &3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `p3_st_compact:(A)rfs_history->(real->A->bool)->bool`))
          (concl th) = false &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_dist" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(X_CHOOSE_TAC `c:real->A`) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `N:num`)) THEN
    SUBGOAL_THEN `?N0. ~(N0 = 0) /\ &0 < inv(&N0) /\ inv(&N0) < eta / &3`
    (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THENL
     [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `c:real->A` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `MAX N N0`) THEN REWRITE_TAC[ARITH_RULE `N <= MAX N N0`] THEN
    USE_THEN "gs" (MP_TAC o SPEC `(sub:num->num) (MAX N N0)`) THEN
    SUBGOAL_THEN `inv(&((sub:num->num) (MAX N N0)) + &1) <= inv(&N0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&(MAX N N0) + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC P3N_INV_SUC_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `inv(&N0) < eta / &3` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(?gamma. rfs_L_adm (hs:(A)rfs_history) tt x b gamma /\ gamma b = (gam:real->A) b)`
  ASSUME_TAC THENL
   [USE_THEN "comp" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_Lx (hs:(A)rfs_history) tt x b ((gam:real->A) b) <= I0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AB_LE_EPS THEN
    X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
    USE_THEN "comp" (MP_TAC o C MP (ASSUME `&0 < eta`) o SPEC `eta:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `b:real`; `c:real->A`]
                  P2AO_LX_LE_HIST) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_L_length (hs:(A)rfs_history) tt c b < I0 + eta` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(gam:real->A) b` THEN CONJ_TAC THENL
   [USE_THEN "us2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(Us:A->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:A`) THEN
    USE_THEN "inf" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN Us`)) THEN
    USE_THEN "us1" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN Us`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `rfs_Lx (hs:(A)rfs_history) tt x b ((gam:real->A) b) <= I0` THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `I0:real` THEN ASM_REWRITE_TAC[] THEN USE_THEN "inf" MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* ========================================================================= *)
(* Prop 16.4: the setting p3n_ctx164 of the proof (the                     *)
(* compact set K of Prop 16.21 and the minimizing L-geodesics of Cor 16.24  *)
(* for curves with L <= Lbar over [T0,tt)), and basic facts on the reached  *)
(* set U = p3n_u164: membership, change of the start time, U is open in     *)
(* space-time (P2AO_LX_USC_ST), its points lie in K and are reached by      *)
(* minimizing L-geodesics, and the vertical path at x puts x into U at all  *)
(* times close to tt (P2AO_CONST_BASE).                                     *)
(* ========================================================================= *)

let p3n_ctx164 = new_definition
 `p3n_ctx164 (hs:(A)rfs_history) (tt:real) (x:A) (T0:real) (Lbar:real) (K:real->A->bool) <=>
    rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ x IN topspace(rfs_top_at hs tt) /\
    &0 < T0 /\ T0 < tt /\ tt < rfs_horizon hs /\ &0 < Lbar /\
    (?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt) /\
    p3_st_compact hs K /\
    (!b gamma. &0 < b /\ b <= tt - T0 /\ rfs_L_adm hs tt x b gamma /\
               rfs_L_length hs tt gamma b <= Lbar
               ==> (!tau. &0 < tau /\ tau <= b ==> gamma tau IN K (tt - tau)) /\
                   (?gamma'. rfs_min_Lgeod hs tt x b gamma' /\ gamma' b = gamma b))`;;

let P3N_U164_IN = prove
 (`!(hs:(A)rfs_history) tt x T0 Lbar t y.
     y IN p3n_u164 hs tt x T0 Lbar t <=>
     T0 <= t /\ t < tt /\ (?gamma. rfs_L_adm hs tt x (tt - t) gamma /\ gamma (tt - t) = y) /\
     rfs_Lx hs tt x (tt - t) y < Lbar`,
  REWRITE_TAC[p3n_u164; IN_ELIM_THM]);;

let P3N_U164_SHIFT = prove
 (`!(hs:(A)rfs_history) tt x T0 a Lbar t.
     T0 <= a /\ a <= t ==> p3n_u164 hs tt x a Lbar t = p3n_u164 hs tt x T0 Lbar t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `T0 <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EXTENSION; P3N_U164_IN]);;

let P3N_U164_OPEN = prove
 (`!(hs:(A)rfs_history) tt x a Lbar.
     rfs_history_ok hs /\ &0 < a /\ x IN topspace(rfs_top_at hs tt) /\
     (?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt)
     ==> p3_st_open hs (p3n_u164 hs tt x a Lbar) a tt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3_st_open; P3N_U164_IN] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - t:real`; `gamma:real->A`]
                P3N_REACHED_PERSISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - t:real`; `y:A`;
                 `(Lbar - rfs_Lx (hs:(A)rfs_history) tt x (tt - t) y) / &2`] P2AO_LX_USC_ST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `rfs_Lx (hs:(A)rfs_history) tt x (tt - t) y < Lbar` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `a <= t` THEN REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`r:real`; `dt:real`] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `tt - (tt - t) = t:real`] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `eta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "usc"))))))) THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `eta:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[SUBSET; P3N_U164_IN] THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  USE_THEN "usc" (MP_TAC o SPECL [`s:real`; `q:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t - eta < s` THEN UNDISCH_TAC `s < t + eta` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `gamma':real->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `rfs_Lx (hs:(A)rfs_history) tt x (tt - s) q <=
               rfs_Lx hs tt x (tt - t) y + (Lbar - rfs_Lx hs tt x (tt - t) y) / &2` THEN
  UNDISCH_TAC `rfs_Lx (hs:(A)rfs_history) tt x (tt - t) y < Lbar` THEN REAL_ARITH_TAC);;

(* a point of U is the end of an admissible curve with L < Lbar *)

let P3N_U164_CURVE = prove
 (`!(hs:(A)rfs_history) tt x T0 Lbar t y.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ y IN p3n_u164 hs tt x T0 Lbar t
     ==> ?gamma. rfs_L_adm hs tt x (tt - t) gamma /\ gamma (tt - t) = y /\
                 rfs_L_length hs tt gamma (tt - t) < Lbar`,
  REWRITE_TAC[P3N_U164_IN] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P3N_LX_APPROACH THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]);;

(* points of U lie in K and are reached by minimizing L-geodesics *)

let P3N_U164_IN_K = prove
 (`!(hs:(A)rfs_history) tt x T0 a Lbar K t y.
     p3n_ctx164 hs tt x T0 Lbar K /\ T0 <= a /\ y IN p3n_u164 hs tt x a Lbar t
     ==> y IN K t /\ ?gamma. rfs_min_Lgeod hs tt x (tt - t) gamma /\ gamma (tt - t) = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[p3n_ctx164])
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `a:real`; `Lbar:real`; `t:real`;
                 `y:A`] P3N_U164_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(y:A) IN p3n_u164 hs tt x a Lbar t` THEN REWRITE_TAC[P3N_U164_IN] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt - t:real`; `c:real->A`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_min_Lgeod" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_L_length (hs:(A)rfs_history) tt c (tt - t) < Lbar` THEN
    UNDISCH_TAC `t < tt` THEN UNDISCH_TAC `T0 <= a` THEN UNDISCH_TAC `a <= t` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `tt - t:real`) ASSUME_TAC) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `t < tt` THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_ARITH `tt - (tt - t) = t:real`] THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `?gamma'. rfs_min_Lgeod (hs:(A)rfs_history) tt x (tt - t) gamma' /\
                        gamma' (tt - t) = c (tt - t)` THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* the vertical path at x: x is in U at all times close to tt *)

let P3N_U164_TOP = prove
 (`!(hs:(A)rfs_history) tt x T0 Lbar K.
     p3n_ctx164 hs tt x T0 Lbar K
     ==> ?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt /\
                !a s. a <= s /\ tt - dt < s /\ s < tt ==> x IN p3n_u164 hs tt x a Lbar s`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[p3n_ctx164]) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `dt:real`]
                P2AO_CONST_BASE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `Kc:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb")))) THEN
  ABBREV_TAC `dt' = min (min dt t0) (min (&1) (Lbar / (abs Kc + &1)))` THEN
  SUBGOAL_THEN `&0 < Lbar / (abs Kc + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dt' /\ dt' <= dt /\ dt' <= t0 /\ dt' <= &1 /\ dt' <= Lbar / (abs Kc + &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dt'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `dt':real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r dt` THEN
    REWRITE_TAC[rfs_parabolic_exists] THEN DISCH_TAC THEN
    MATCH_MP_TAC P3N_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`tt - dt:real`; `tt:real`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dt' <= dt` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `s:real`] THEN STRIP_TAC THEN
  USE_THEN "cb" (MP_TAC o SPEC `tt - s:real`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `s < tt` THEN UNDISCH_TAC `tt - dt' < s` THEN UNDISCH_TAC `dt' <= t0` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  REWRITE_TAC[P3N_U164_IN] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `(\s:real. (x:A))` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - s:real`; `(\s:real. (x:A))`]
                P2AO_LX_LE_HIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `b = tt - s:real` THEN
  SUBGOAL_THEN `&0 < b /\ b <= &1 /\ b < Lbar / (abs Kc + &1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN
    UNDISCH_TAC `s < tt` THEN UNDISCH_TAC `tt - dt' < s` THEN UNDISCH_TAC `dt' <= &1` THEN
    UNDISCH_TAC `dt' <= Lbar / (abs Kc + &1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Kc * b * sqrt b < Lbar` MP_TAC THENL
   [SUBGOAL_THEN `&0 <= sqrt b /\ sqrt b <= &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(abs Kc + &1) * b` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs Kc * b * sqrt b` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs Kc * b` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE];
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]];
      UNDISCH_TAC `b < Lbar / (abs Kc + &1)` THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs Kc + &1`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_Lx (hs:(A)rfs_history) tt x b x <= rfs_L_length hs tt (\s:real. (x:A)) b` THEN
  UNDISCH_TAC `rfs_L_length (hs:(A)rfs_history) tt (\s:real. (x:A)) b <= Kc * b * sqrt b` THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.4: vertical extension of curves from points of the               *)
(* compact set K (MT p. 390, the flow lines of chi).  R is bounded on a     *)
(* closed time interval inside one slab (the slices are compact); just     *)
(* after a time t the points of K have backward neighbourhoods persisting  *)
(* to before t, uniformly (from the pieces of p3_st_compact); so Lx at the *)
(* same point one step earlier is at most Lx + sqrt(tau) B D + e           *)
(* (P2AO_VERT_EXT).                                                          *)
(* ========================================================================= *)

let P3N_SLAB_SCALAR_BOUND = prove
 (`!(hs:(A)rfs_history) k s1 s2.
     rfs_history_ok hs /\ k <= hs_count hs /\ hs_time hs k <= s1 /\ s2 < hs_time hs (k + 1)
     ==> ?B. !s y. s1 <= s /\ s <= s2 /\ y IN topspace(hs_top hs k)
                   ==> mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3N_SLAB_SCALAR_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact_space (hs_top (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology euclideanreal
                      {t | hs_time (hs:(A)rfs_history) k <= t /\ t < hs_time hs (k + 1)})
                   (subtopology (hs_top hs k) (topspace(hs_top hs k)))`;
    `euclideanreal`;
    `\z. mfd_scalar (hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k (FST z)) (SND z)`;
    `real_interval[s1,s2] CROSS topspace(hs_top (hs:(A)rfs_history) k)`] IMAGE_COMPACT_IN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    REWRITE_TAC[COMPACT_IN_CROSS; COMPACT_IN_SUBTOPOLOGY; SUBTOPOLOGY_TOPSPACE; SUBSET_REFL] THEN
    REPEAT DISJ2_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL; SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      X_GEN_TAC `u:real` THEN
      UNDISCH_TAC `hs_time (hs:(A)rfs_history) k <= s1` THEN
      UNDISCH_TAC `s2 < hs_time (hs:(A)rfs_history) (k + 1)` THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[GSYM compact_space]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM real_compact_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(s:real,y:A)`) THEN
  ASM_REWRITE_TAC[IN_CROSS; IN_REAL_INTERVAL; FST; SND] THEN REAL_ARITH_TAC);;

(* uniform data just after a time t for the points of K *)

let P3N_K_RIGHT_DATA = prove
 (`!(hs:(A)rfs_history) K t.
     rfs_history_ok hs /\ p3_st_compact hs K /\ &0 <= t /\ t < rfs_horizon hs
     ==> ?d B eta. &0 < d /\ &0 <= B /\ &0 < eta /\
           !t' y. t <= t' /\ t' < t + d /\ y IN K t'
                  ==> (?W. y IN W /\ rfs_persists (rfs_view hs) W (t - eta) t') /\
                      (!s. t <= s /\ s <= t'
                           ==> mfd_scalar (rfs_atlas_at hs s) (rfs_metric_at hs s) y <= B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AB_LIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `p3_st_compact hs (K:real->A->bool)` THEN REWRITE_TAC[p3_st_compact] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `W:num->A->bool`
    (X_CHOOSE_THEN `C:num->A->bool` (X_CHOOSE_THEN `a:num->real`
    (X_CHOOSE_THEN `b:num->real` (X_CHOOSE_THEN `eta0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "box") (LABEL_TAC "cov"))))))))) THEN
  ABBREV_TAC `d = min ((hs_time (hs:(A)rfs_history) (k + 1) - t) / &2) (eta0 / &2)` THEN
  SUBGOAL_THEN `&0 < d /\ t + d < hs_time (hs:(A)rfs_history) (k + 1) /\ d <= eta0 / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    UNDISCH_TAC `t < hs_time (hs:(A)rfs_history) (k + 1)` THEN UNDISCH_TAC `&0 < eta0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `t:real`; `t + d:real`] P3N_SLAB_SCALAR_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t + d < hs_time (hs:(A)rfs_history) (k + 1)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "B")) THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `max (&0) B`; `eta0 / &2`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; REAL_ARITH_TAC; UNDISCH_TAC `&0 < eta0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t':real`; `y:A`] THEN STRIP_TAC THEN
  USE_THEN "cov" (MP_TAC o C MP (ASSUME `(y:A) IN K (t':real)`) o SPECL [`t':real`; `y:A`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "box" (STRIP_ASSUME_TAC o C MP (ASSUME `j:num < n`) o SPEC `j:num`) THEN
  (* the slab at t' *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `t':real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hs_time (hs:(A)rfs_history) k <= t` THEN UNDISCH_TAC `t <= t'` THEN
    UNDISCH_TAC `t' < t + d` THEN UNDISCH_TAC `t + d < hs_time (hs:(A)rfs_history) (k + 1)` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(hs_top (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [SUBGOAL_THEN `compact_in (rfs_top_at (hs:(A)rfs_history) t') ((C:num->A->bool) j)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "compact_in" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:A) IN (C:num->A->bool) j` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `(W:num->A->bool) j` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(C:num->A->bool) j SUBSET (W:num->A->bool) j` THEN
      UNDISCH_TAC `(y:A) IN (C:num->A->bool) j` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P3N_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(a:num->real) j - eta0`; `(b:num->real) j`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a:num->real) j <= t'` THEN UNDISCH_TAC `t' <= (b:num->real) j` THEN
    UNDISCH_TAC `t' < t + d` THEN UNDISCH_TAC `d <= eta0 / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hs_time (hs:(A)rfs_history) k <= t` THEN UNDISCH_TAC `t <= s` THEN
    UNDISCH_TAC `s <= t'` THEN UNDISCH_TAC `t' < t + d` THEN
    UNDISCH_TAC `t + d < hs_time (hs:(A)rfs_history) (k + 1)` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max (&0) B`) THEN
  USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `s <= t'` THEN UNDISCH_TAC `t' < t + d` THEN REAL_ARITH_TAC);;

(* the vertical extension step for Lx *)

let P3N_VEXT_LX = prove
 (`!(hs:(A)rfs_history) tt x t t' y B eta e.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ x IN topspace(rfs_top_at hs tt) /\
     (?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt) /\
     &0 < t /\ t < t' /\ t' < tt /\ &0 <= B /\ &0 < eta /\ &0 < e /\
     (?gamma. rfs_L_adm hs tt x (tt - t') gamma /\ gamma (tt - t') = y) /\
     (?W. y IN W /\ rfs_persists (rfs_view hs) W (t - eta) t') /\
     (!s. t <= s /\ s <= t' ==> mfd_scalar (rfs_atlas_at hs s) (rfs_metric_at hs s) y <= B)
     ==> (?gamma. rfs_L_adm hs tt x (tt - t) gamma /\ gamma (tt - t) = y) /\
         rfs_Lx hs tt x (tt - t) y <=
         rfs_Lx hs tt x (tt - t') y + sqrt(tt - t) * B * (t' - t) + e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "par") MP_TAC)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) (LABEL_TAC "Rb"))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - t':real`; `y:A`;
                 `rfs_Lx (hs:(A)rfs_history) tt x (tt - t') y + e / &2`] P3N_LX_APPROACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - t':real`; `c:real->A`;
                 `t' - t:real`; `B:real`; `e / &2`] P2AO_VERT_EXT) THEN
  REWRITE_TAC[REAL_ARITH `(tt - t') + (t' - t) = tt - t:real`;
              REAL_ARITH `tt - (tt - t') = t':real`; REAL_ARITH `t' - (t' - t) = t:real`] THEN
  REWRITE_TAC[ASSUME `(c:real->A) (tt - t') = y`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           MAP_EVERY EXISTS_TAC [`W:A->bool`; `eta:real`] THEN ASM_REWRITE_TAC[];
           UNDISCH_TAC `t < t'` THEN UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `&0 < e` THEN
           REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real->A` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL [EXISTS_TAC `c':real->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - t:real`; `c':real->A`]
                P2AO_LX_LE_HIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `rfs_Lx (hs:(A)rfs_history) tt x (tt - t) y <= rfs_L_length hs tt c' (tt - t)` THEN
  UNDISCH_TAC `rfs_L_length (hs:(A)rfs_history) tt c' (tt - t) <=
               rfs_L_length hs tt c (tt - t') + sqrt(tt - t) * B * (t' - t) + e / &2` THEN
  UNDISCH_TAC `rfs_L_length (hs:(A)rfs_history) tt c (tt - t') <
               rfs_Lx hs tt x (tt - t') y + e / &2` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.4: lower semicontinuity of the slice minimum of                 *)
(* Lx on U (MT Claim 16.25, the part used by the corrected Cor 7.12): for  *)
(* points y' of U at times t' near t there is a point of U at t with Lx at *)
(* most Lx(y') + e.  If the minimum at t is already that small take the    *)
(* minimizer; otherwise restrict a near-optimal curve to y' (t' < t,       *)
(* P2AO_LADM_RESTRICT) or extend it vertically (t' > t, P3N_VEXT_LX with   *)
(* the uniform data of P3N_K_RIGHT_DATA).  Then the same for the reduced    *)
(* length lx = Lx / (2 sqrt tau), the form of hypothesis (7) of Cor 7.12.  *)
(* ========================================================================= *)

(* arithmetic only: drop the assumptions with binders, then linear arithmetic *)

let P3N_ARITH164_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t -> is_forall t || is_exists t || is_abs t)) (concl th)
    then ALL_TAC else NO_TAC)) THEN
  ASM_REAL_ARITH_TAC;;

let P3N_LSC_ARITH = prove
 (`!s S B u d Q e.
     &0 <= s /\ s <= S /\ &0 <= B /\ &0 <= u /\ u <= d /\ S * B <= Q /\ Q * d <= e
     ==> s * B * u <= e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * d` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(S * B) * d` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3N_U164_LSC = prove
 (`!(hs:(A)rfs_history) tt x T0 a Lbar K t e.
     p3n_ctx164 hs tt x T0 Lbar K /\ T0 <= a /\ a <= t /\ t < tt /\ &0 < e /\
     (!s. a <= s /\ s < tt ==> ~(p3n_u164 hs tt x a Lbar s = {}))
     ==> ?d. &0 < d /\
             !t' y'. a <= t' /\ t' < tt /\ abs(t' - t) < d /\ y' IN p3n_u164 hs tt x a Lbar t'
                     ==> ?y. y IN p3n_u164 hs tt x a Lbar t /\
                             rfs_Lx hs tt x (tt - t) y <= rfs_Lx hs tt x (tt - t') y' + e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
                                        STRIP_ASSUME_TAC(REWRITE_RULE[p3n_ctx164] th))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ne")))))) THEN
  SUBGOAL_THEN
   `?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r dt`
  (LABEL_TAC "par") THENL
   [MAP_EVERY EXISTS_TAC [`r:real`; `dt:real`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a /\ &0 < t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < T0` THEN UNDISCH_TAC `T0 <= a` THEN UNDISCH_TAC `a <= t` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b gamma. &0 < b /\ b <= tt - a /\ rfs_L_adm (hs:(A)rfs_history) tt x b gamma /\
              rfs_L_length hs tt gamma b <= Lbar
              ==> !tau. &0 < tau /\ tau <= b ==> gamma tau IN (K:real->A->bool) (tt - tau)`
  (LABEL_TAC "Ka") THENL
   [MAP_EVERY X_GEN_TAC [`b:real`; `g:real->A`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`b:real`; `g:real->A`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_min_Lgeod" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `b <= tt - a` THEN UNDISCH_TAC `T0 <= a` THEN
      REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the minimum at t *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `a:real`; `Lbar:real`;
                 `K:real->A->bool`; `t:real`] P3N_U164_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "ne" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m0:A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  SUBGOAL_THEN `rfs_Lx (hs:(A)rfs_history) tt x (tt - t) m0 < Lbar` ASSUME_TAC THENL
   [UNDISCH_TAC `(m0:A) IN p3n_u164 hs tt x a Lbar t` THEN SIMP_TAC[P3N_U164_IN]; ALL_TAC] THEN
  (* uniform data just after t *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `K:real->A->bool`; `t:real`] P3N_K_RIGHT_DATA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `t < tt` THEN
    UNDISCH_TAC `tt < rfs_horizon (hs:(A)rfs_history)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real` (X_CHOOSE_THEN `eta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rd"))))))) THEN
  ABBREV_TAC `Q = &6 * sqrt tt + sqrt tt * B + &1` THEN
  SUBGOAL_THEN `&0 <= sqrt tt /\ &0 < Q /\ sqrt tt * &6 <= Q /\ sqrt tt * B <= Q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= sqrt tt` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN UNDISCH_TAC `T0 < tt` THEN UNDISCH_TAC `&0 < T0` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt tt * B` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Q" THEN
    UNDISCH_TAC `&0 <= sqrt tt` THEN UNDISCH_TAC `&0 <= sqrt tt * B` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e / (&2 * Q) /\ Q * (e / (&2 * Q)) = e / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < Q` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  EXISTS_TAC `min d1 (e / (&2 * Q))` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < d1` THEN UNDISCH_TAC `&0 < e / (&2 * Q)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t':real`; `y':A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `Q * abs(t' - t) <= e / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * (e / (&2 * Q))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < Q` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `abs(t' - t) < min d1 (e / (&2 * Q))` THEN REAL_ARITH_TAC];
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `rfs_Lx (hs:(A)rfs_history) tt x (tt - t) m0 <= rfs_Lx hs tt x (tt - t') y' + e`
  THENL [EXISTS_TAC `m0:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ASSUME `(y':A) IN p3n_u164 hs tt x a Lbar t'`) THEN REWRITE_TAC[P3N_U164_IN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  MP_TAC(REAL_ARITH `t' < t \/ t' = t \/ t < t'`) THEN STRIP_TAC THENL
   [(* t' < t: restriction of a near-optimal curve *)
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - t':real`; `y':A`;
                   `rfs_Lx (hs:(A)rfs_history) tt x (tt - t') y' + e / &2`] P3N_LX_APPROACH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - t':real`; `tt - t:real`;
                   `c:real->A`] P2AO_LADM_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t' < t` THEN UNDISCH_TAC `t < tt` THEN UNDISCH_TAC `&0 < a` THEN
      UNDISCH_TAC `a <= t'` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `sqrt(tt - t') * &6 * ((tt - t') - (tt - t)) <= e / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC P3N_LSC_ARITH THEN
      MAP_EVERY EXISTS_TAC [`sqrt tt`; `abs(t' - t)`; `Q:real`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC SQRT_POS_LE THEN P3N_ARITH164_TAC;
             MATCH_MP_TAC SQRT_MONO_LE THEN P3N_ARITH164_TAC;
             P3N_ARITH164_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `(c:real->A) (tt - t)` THEN REWRITE_TAC[P3N_U164_IN] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN P3N_ARITH164_TAC;
    (* t' = t *)
    EXISTS_TAC `y':A` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `t':real = t`)) THEN
    REWRITE_TAC[P3N_U164_IN] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[]; UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC];
    (* t < t': vertical extension *)
    SUBGOAL_THEN `(y':A) IN (K:real->A->bool) t'` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                     `K:real->A->bool`; `t':real`; `y':A`] P3N_U164_IN_K) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "rd" (MP_TAC o SPECL [`t':real`; `y':A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN P3N_ARITH164_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Rb")) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `t:real`; `t':real`; `y':A`;
                   `B:real`; `eta:real`; `e / &2`] P3N_VEXT_LX) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC;
             EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[];
             P3N_ARITH164_TAC];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `sqrt(tt - t) * B * (t' - t) <= e / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC P3N_LSC_ARITH THEN
      MAP_EVERY EXISTS_TAC [`sqrt tt`; `abs(t' - t)`; `Q:real`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC SQRT_POS_LE THEN P3N_ARITH164_TAC;
             MATCH_MP_TAC SQRT_MONO_LE THEN P3N_ARITH164_TAC;
             P3N_ARITH164_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `y':A` THEN REWRITE_TAC[P3N_U164_IN] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN P3N_ARITH164_TAC]);;

(* continuity of tau -> 1/(2 sqrt tau) *)

let P3N_INVSQRT_CONT = prove
 (`!tt t e. t < tt /\ &0 < e
            ==> ?d. &0 < d /\
                    !t'. abs(t' - t) < d
                         ==> abs(inv(&2 * sqrt(tt - t')) - inv(&2 * sqrt(tt - t))) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\s. inv(&2 * sqrt(tt - s))) real_continuous atreal t` MP_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_INV THEN REWRITE_TAC[NETLIMIT_ATREAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_SQRT_COMPOSE THEN
      MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_AT_ID];
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&2 * x = &0)`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN UNDISCH_TAC `t < tt` THEN REAL_ARITH_TAC];
    REWRITE_TAC[real_continuous_atreal] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let P3N_LX_DIV_ARITH = prove
 (`!L L' s s' e1 Lam e.
     &0 < s /\ &0 < s' /\ abs L' <= Lam /\ L <= L' + e1 /\
     abs(inv(&2 * s') - inv(&2 * s)) * Lam <= e / &2 /\ e1 * inv(&2 * s) <= e / &2
     ==> L / (&2 * s) <= L' / (&2 * s') + e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  ABBREV_TAC `p = inv(&2 * s)` THEN ABBREV_TAC `p' = inv(&2 * s')` THEN
  SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L * p <= (L' + e1) * p` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L' * (p - p') <= abs(p' - p) * Lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(L') * abs(p' - p)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs(x) <= y ==> x <= y`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  UNDISCH_TAC `L * p <= (L' + e1) * p` THEN UNDISCH_TAC `L' * (p - p') <= abs(p' - p) * Lam` THEN
  UNDISCH_TAC `abs(p' - p) * Lam <= e / &2` THEN UNDISCH_TAC `e1 * p <= e / &2` THEN
  REAL_ARITH_TAC);;

let P3N_DIVLAM_ARITH = prove
 (`!A Lam e. &0 <= A /\ &0 <= Lam /\ A < e / (&2 * (Lam + &1)) ==> A * Lam <= e / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * (Lam + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A * (&2 * (Lam + &1)) < e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `A * Lam <= A * (Lam + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* hypothesis (7) of the corrected Cor 7.12 for U *)

let P3N_U164_LSC_LX = prove
 (`!(hs:(A)rfs_history) tt x T0 a Lbar K.
     p3n_ctx164 hs tt x T0 Lbar K /\ T0 <= a /\
     (!s. a <= s /\ s < tt ==> ~(p3n_u164 hs tt x a Lbar s = {}))
     ==> !t e. a <= t /\ t < tt /\ &0 < e
               ==> ?d. &0 < d /\
                       !t' y'. a <= t' /\ t' < tt /\ abs(t' - t) < d /\
                               y' IN p3n_u164 hs tt x a Lbar t'
                               ==> ?y. y IN p3n_u164 hs tt x a Lbar t /\
                                       rfs_lx hs tt x (tt - t) y <=
                                       rfs_lx hs tt x (tt - t') y' + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `e:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p3n_ctx164] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "p3n_ctx164" with Failure _ -> false)) THEN
  ABBREV_TAC `Lam = Lbar + &6 * tt * sqrt tt` THEN
  SUBGOAL_THEN `&0 < sqrt(tt - t) /\ &0 <= sqrt tt /\ &0 <= tt * sqrt tt` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN P3N_ARITH164_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN P3N_ARITH164_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [P3N_ARITH164_TAC; MATCH_MP_TAC SQRT_POS_LE THEN P3N_ARITH164_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lam` ASSUME_TAC THENL
   [EXPAND_TAC "Lam" THEN P3N_ARITH164_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                 `K:real->A->bool`; `t:real`; `e * sqrt(tt - t)`] P3N_U164_LSC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l1"))) THEN
  MP_TAC(ISPECL [`tt:real`; `t:real`; `e / (&2 * (Lam + &1))`] P3N_INVSQRT_CONT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    P3N_ARITH164_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l2"))) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [P3N_ARITH164_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t':real`; `y':A`] THEN STRIP_TAC THEN
  USE_THEN "l1" (MP_TAC o SPECL [`t':real`; `y':A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN P3N_ARITH164_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  USE_THEN "l2" (MP_TAC o SPEC `t':real`) THEN
  ANTS_TAC THENL [P3N_ARITH164_TAC; DISCH_TAC] THEN
  (* the bound on Lx at y' *)
  SUBGOAL_THEN `abs(rfs_Lx (hs:(A)rfs_history) tt x (tt - t') y') <= Lam` ASSUME_TAC THENL
   [MP_TAC(ASSUME `(y':A) IN p3n_u164 hs tt x a Lbar t'`) THEN REWRITE_TAC[P3N_U164_IN] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - t':real`; `y':A`]
                  P3N_LX_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `(tt - t') * sqrt(tt - t') <= tt * sqrt tt` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC SQRT_POS_LE THEN P3N_ARITH164_TAC;
             MATCH_MP_TAC SQRT_MONO_LE THEN P3N_ARITH164_TAC;
             P3N_ARITH164_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "Lam" THEN P3N_ARITH164_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[rfs_lx] THEN
  MATCH_MP_TAC P3N_LX_DIV_ARITH THEN
  MAP_EVERY EXISTS_TAC [`e * sqrt(tt - t)`; `Lam:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN P3N_ARITH164_TAC;
    MATCH_MP_TAC P3N_DIVLAM_ARITH THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN
    UNDISCH_TAC `&0 < sqrt(tt - t)` THEN CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* Prop 16.4: the corrected Cor 7.12 applied to U from a                   *)
(* start time a with nonempty slices on [a,tt) (MT Lemma 16.26): every     *)
(* hypothesis holds (U open, minimizing L-geodesics, x in U near tt, the   *)
(* slice minimizers lie in K and exist, lower semicontinuity), so each     *)
(* slice contains y with Lx(y) <= 3 sqrt(tt - t).                           *)
(* ========================================================================= *)

let P3N_CTX_KA = prove
 (`!(hs:(A)rfs_history) tt x T0 a Lbar K.
     p3n_ctx164 hs tt x T0 Lbar K /\ T0 <= a
     ==> !b gamma. &0 < b /\ b <= tt - a /\ rfs_L_adm hs tt x b gamma /\
                   rfs_L_length hs tt gamma b <= Lbar
                   ==> !tau. &0 < tau /\ tau <= b ==> gamma tau IN K (tt - tau)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[p3n_ctx164]) ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`b:real`; `g:real->A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`b:real`; `g:real->A`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_min_Lgeod" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `b <= tt - a` THEN UNDISCH_TAC `T0 <= a` THEN
    REAL_ARITH_TAC;
    SIMP_TAC[]]);;

let P3N_U164_LMIN = prove
 (`!(hs:(A)rfs_history) tt x T0 a Lbar K t.
     p3n_ctx164 hs tt x T0 Lbar K /\ T0 <= a /\ a <= t /\ t < tt /\
     ~(p3n_u164 hs tt x a Lbar t = {})
     ==> ?m. m IN p3_Lmin_set hs tt x (p3n_u164 hs tt x a Lbar) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                 `K:real->A->bool`] P3N_CTX_KA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p3n_ctx164] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "p3n_ctx164" with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `a:real`; `Lbar:real`;
                 `K:real->A->bool`; `t:real`] P3N_U164_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < T0` THEN UNDISCH_TAC `T0 <= a` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p3_Lmin_set; IN_ELIM_THM] THEN MESON_TAC[]);;

let P3N_U164_712 = prove
 (`!(hs:(A)rfs_history) tt x T0 a Lbar K.
     p3n_ctx164 hs tt x T0 Lbar K /\ T0 <= a /\ a < tt /\
     (!s. a <= s /\ s < tt ==> ~(p3n_u164 hs tt x a Lbar s = {})) /\
     (!(hs:(A)rfs_history) x tt a U r dt.
         rfs_history_ok hs /\ a < tt /\ x IN topspace(rfs_top_at hs tt) /\
         p3_st_open hs U a tt /\
         (!t y. y IN U t ==> ?gamma. rfs_min_Lgeod hs tt x (tt - t) gamma /\
                                     gamma (tt - t) = y) /\
         &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt /\
         (!s. tt - dt < s /\ s < tt /\ a <= s ==> x IN U s) /\
         (!a' b'. a <= a' /\ a' <= b' /\ b' < tt
                  ==> p3_st_compact hs (\t. if a' <= t /\ t <= b' then p3_Lmin_set hs tt x U t
                                            else {}) /\
                      !t. a' <= t /\ t <= b' ==> ~(p3_Lmin_set hs tt x U t = {})) /\
         (!t e. a <= t /\ t < tt /\ &0 < e
                ==> ?d. &0 < d /\
                        !t' y'. a <= t' /\ t' < tt /\ abs(t' - t) < d /\ y' IN U t'
                                ==> ?y. y IN U t /\
                                        rfs_lx hs tt x (tt - t) y <=
                                        rfs_lx hs tt x (tt - t') y' + e)
         ==> !t. a <= t /\ t < tt ==> ?y. y IN U t /\ rfs_lx hs tt x (tt - t) y <= &3 / &2)
     ==> !t. a <= t /\ t < tt
             ==> ?y. y IN p3n_u164 hs tt x a Lbar t /\
                     rfs_Lx hs tt x (tt - t) y <= &3 * sqrt(tt - t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ne") (LABEL_TAC "c712"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p3n_ctx164] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "p3n_ctx164" with Failure _ -> false)) THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < T0` THEN UNDISCH_TAC `T0 <= a` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `Lbar:real`;
                 `K:real->A->bool`] P3N_U164_TOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `dt0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "top")))))) THEN
  USE_THEN "c712" (MP_TAC o SPECL [`hs:(A)rfs_history`; `x:A`; `tt:real`; `a:real`;
                                   `p3n_u164 (hs:(A)rfs_history) tt x a Lbar`;
                                   `r0:real`; `dt0:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      (* (2) U is open *)
      MATCH_MP_TAC P3N_U164_OPEN THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`r0:real`; `dt0:real`] THEN ASM_REWRITE_TAC[];
      (* (3) minimizing L-geodesics *)
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                     `K:real->A->bool`; `s:real`; `y:A`] P3N_U164_IN_K) THEN
      ASM_SIMP_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      (* (5) x in U near tt *)
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "top" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      (* (6) slice minimizers: compact and nonempty *)
      MAP_EVERY X_GEN_TAC [`a':real`; `b':real`] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC P3N_STC_MONO THEN EXISTS_TAC `K:real->A->bool` THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN
        COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET] THEN
        REWRITE_TAC[SUBSET; p3_Lmin_set; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                       `K:real->A->bool`; `s:real`; `z:A`] P3N_U164_IN_K) THEN
        ASM_SIMP_TAC[];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                       `K:real->A->bool`; `s:real`] P3N_U164_LMIN) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
           [UNDISCH_TAC `a <= a'` THEN UNDISCH_TAC `a' <= s` THEN REAL_ARITH_TAC;
            UNDISCH_TAC `s <= b'` THEN UNDISCH_TAC `b' < tt` THEN REAL_ARITH_TAC;
            USE_THEN "ne" MATCH_MP_TAC THEN
            UNDISCH_TAC `a <= a'` THEN UNDISCH_TAC `a' <= s` THEN UNDISCH_TAC `s <= b'` THEN
            UNDISCH_TAC `b' < tt` THEN REAL_ARITH_TAC];
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]]];
      (* (7) lower semicontinuity *)
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                     `K:real->A->bool`] P3N_U164_LSC_LX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `&3 / &2`)) (concl th) &&
    not (can (find_term (fun t -> try fst(dest_const t) = "p3_st_open" with Failure _ -> false))
             (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &2 * sqrt(tt - t)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < &2 * x`) THEN MATCH_MP_TAC SQRT_POS_LT THEN
    UNDISCH_TAC `t < tt` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_lx (hs:(A)rfs_history) tt x (tt - t) y <= &3 / &2` THEN
  REWRITE_TAC[rfs_lx] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Prop 16.4: every slice of U over [T0,tt) is nonempty (MT                *)
(* pp. 390-391, the set S).  Let a* be the infimum of the start times a    *)
(* such that all slices over [a,tt) are nonempty (x itself lies in U near  *)
(* tt).  The slice at a* is nonempty: Cor 7.12 at a start time a just above *)
(* a* gives y at a with Lx(y) <= 3 sqrt(tt - a), and the vertical path at  *)
(* y down to a* (uniform data of P3N_K_RIGHT_DATA) keeps L < Lbar.  If     *)
(* a* > T0, Cor 7.12 at a* and the openness of P2AO_LX_USC_ST give a       *)
(* smaller admissible start time, a contradiction.                          *)
(* ========================================================================= *)

let P3N_U164_NONEMPTY = prove
 (`!(hs:(A)rfs_history) tt x T0 Lbar K.
     p3n_ctx164 hs tt x T0 Lbar K /\ &3 * sqrt tt + &3 <= Lbar /\
     (!(hs:(A)rfs_history) x tt a U r dt.
         rfs_history_ok hs /\ a < tt /\ x IN topspace(rfs_top_at hs tt) /\
         p3_st_open hs U a tt /\
         (!t y. y IN U t ==> ?gamma. rfs_min_Lgeod hs tt x (tt - t) gamma /\
                                     gamma (tt - t) = y) /\
         &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt /\
         (!s. tt - dt < s /\ s < tt /\ a <= s ==> x IN U s) /\
         (!a' b'. a <= a' /\ a' <= b' /\ b' < tt
                  ==> p3_st_compact hs (\t. if a' <= t /\ t <= b' then p3_Lmin_set hs tt x U t
                                            else {}) /\
                      !t. a' <= t /\ t <= b' ==> ~(p3_Lmin_set hs tt x U t = {})) /\
         (!t e. a <= t /\ t < tt /\ &0 < e
                ==> ?d. &0 < d /\
                        !t' y'. a <= t' /\ t' < tt /\ abs(t' - t) < d /\ y' IN U t'
                                ==> ?y. y IN U t /\
                                        rfs_lx hs tt x (tt - t) y <=
                                        rfs_lx hs tt x (tt - t') y' + e)
         ==> !t. a <= t /\ t < tt ==> ?y. y IN U t /\ rfs_lx hs tt x (tt - t) y <= &3 / &2)
     ==> !t. T0 <= t /\ t < tt ==> ~(p3n_u164 hs tt x T0 Lbar t = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c712"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p3n_ctx164] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "p3n_ctx164" with Failure _ -> false)) THEN
  SUBGOAL_THEN
   `?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r dt`
  (LABEL_TAC "par") THENL
   [MAP_EVERY EXISTS_TAC [`r:real`; `dt:real`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt tt` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN P3N_ARITH164_TAC; ALL_TAC] THEN
  (* Cor 7.12 from any admissible start time, in terms of U at T0 *)
  SUBGOAL_THEN
   `!a. T0 <= a /\ a < tt /\
        (!t. a <= t /\ t < tt ==> ~(p3n_u164 (hs:(A)rfs_history) tt x T0 Lbar t = {}))
        ==> ?y. y IN p3n_u164 hs tt x a Lbar a /\
                rfs_Lx hs tt x (tt - a) y <= &3 * sqrt(tt - a)`
  (LABEL_TAC "app") THENL
   [X_GEN_TAC `a:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                   `K:real->A->bool`] P3N_U164_712) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                       `s:real`] P3N_U164_SHIFT) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "c712" ACCEPT_TAC];
      DISCH_THEN(MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the set S of admissible start times *)
  ABBREV_TAC `S = {a:real | T0 <= a /\ a < tt /\
                            !t. a <= t /\ t < tt
                                ==> ~(p3n_u164 (hs:(A)rfs_history) tt x T0 Lbar t = {})}` THEN
  SUBGOAL_THEN
   `!a. a IN S <=> T0 <= a /\ a < tt /\
                   !t. a <= t /\ t < tt ==> ~(p3n_u164 (hs:(A)rfs_history) tt x T0 Lbar t = {})`
  MP_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN(fun th -> LABEL_TAC "S1" (GEN `a:real` (fst(EQ_IMP_RULE(SPEC `a:real` th)))) THEN
                       LABEL_TAC "S2" (GEN `a:real` (snd(EQ_IMP_RULE(SPEC `a:real` th))))) THEN
  (* S is nonempty: x is in U near tt *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `Lbar:real`;
                 `K:real->A->bool`] P3N_U164_TOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `dt0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "top")))))) THEN
  SUBGOAL_THEN `max T0 (tt - dt0 / &2) IN S` ASSUME_TAC THENL
   [USE_THEN "S2" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      UNDISCH_TAC `T0 < tt` THEN UNDISCH_TAC `&0 < dt0` THEN REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `x:A` THEN USE_THEN "top" MATCH_MP_TAC THEN
      UNDISCH_TAC `max T0 (tt - dt0 / &2) <= s` THEN UNDISCH_TAC `s < tt` THEN
      UNDISCH_TAC `&0 < dt0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(S:real->bool = {}) /\ (!a. a IN S ==> T0 <= a)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `max T0 (tt - dt0 / &2)` THEN
      FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `a:real` THEN DISCH_TAC THEN
      USE_THEN "S1" (MP_TAC o C MATCH_MP (ASSUME `(a:real) IN S`)) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `ast = inf(S:real->bool)` THEN
  SUBGOAL_THEN `T0 <= ast /\ ast < tt` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "ast" THEN MATCH_MP_TAC REAL_LE_INF THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `max T0 (tt - dt0 / &2)` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "ast" THEN MATCH_MP_TAC INF_LE_ELEMENT THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `T0:real` THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `T0 < tt` THEN UNDISCH_TAC `&0 < dt0` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. a IN S ==> ast <= a` (LABEL_TAC "lb") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN EXPAND_TAC "ast" THEN
    MATCH_MP_TAC INF_LE_ELEMENT THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `T0:real` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. ast < c ==> ?a. a IN S /\ a < c` (LABEL_TAC "appr") THENL
   [X_GEN_TAC `c:real` THEN DISCH_TAC THEN MATCH_MP_TAC INF_APPROACH THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `T0:real` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the slices over [ast,tt) are nonempty *)
  SUBGOAL_THEN
   `!t. ast <= t /\ t < tt ==> ~(p3n_u164 (hs:(A)rfs_history) tt x T0 Lbar t = {})`
  (LABEL_TAC "Nas") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `ast < t` THENL
     [USE_THEN "appr" (MP_TAC o C MP (ASSUME `ast < t`) o SPEC `t:real`) THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "S1" (MP_TAC o C MATCH_MP (ASSUME `(a:real) IN S`)) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `a < t` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t = ast:real` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `ast <= t` THEN UNDISCH_TAC `~(ast < t)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    (* the slice at ast itself *)
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `K:real->A->bool`; `ast:real`] P3N_K_RIGHT_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN P3N_ARITH164_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `B:real` (X_CHOOSE_THEN `eta:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rd"))))))) THEN
    ABBREV_TAC `Q = sqrt tt * B + &1` THEN
    SUBGOAL_THEN `&0 < Q /\ sqrt tt * B <= Q` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= sqrt tt * B` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; EXPAND_TAC "Q" THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `dl = min d (inv Q)` THEN
    SUBGOAL_THEN `&0 < dl /\ dl <= d /\ Q * dl <= &1` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < inv Q /\ Q * inv Q = &1` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_INV; REAL_MUL_RINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
      EXPAND_TAC "dl" THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 < inv Q` THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * inv Q` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN
          UNDISCH_TAC `&0 < Q` THEN REAL_ARITH_TAC;
          ASM_REWRITE_TAC[REAL_LE_REFL]]];
      ALL_TAC] THEN
    USE_THEN "appr" (MP_TAC o SPEC `ast + dl`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ast <= a` ASSUME_TAC THENL
     [USE_THEN "lb" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "S1" (MP_TAC o C MATCH_MP (ASSUME `(a:real) IN S`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Na"))) THEN
    ASM_CASES_TAC `a = ast:real` THENL
     [USE_THEN "Na" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `ast < a` ASSUME_TAC THENL
     [UNDISCH_TAC `ast <= a` THEN UNDISCH_TAC `~(a = ast:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "app" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "Na" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:A) IN (K:real->A->bool) a` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `a:real`; `Lbar:real`;
                     `K:real->A->bool`; `a:real`; `y:A`] P3N_U164_IN_K) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "rd" (MP_TAC o SPECL [`a:real`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN P3N_ARITH164_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Rb")) THEN
    MP_TAC(ASSUME `(y:A) IN p3n_u164 hs tt x a Lbar a`) THEN REWRITE_TAC[P3N_U164_IN] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `ast:real`; `a:real`; `y:A`;
                   `B:real`; `eta:real`; `&1`] P3N_VEXT_LX) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC;
             EXISTS_TAC `g:real->A` THEN ASM_REWRITE_TAC[];
             P3N_ARITH164_TAC];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `sqrt(tt - ast) * B * (a - ast) <= &1` ASSUME_TAC THENL
     [MATCH_MP_TAC P3N_LSC_ARITH THEN
      MAP_EVERY EXISTS_TAC [`sqrt tt`; `dl:real`; `Q:real`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC SQRT_POS_LE THEN P3N_ARITH164_TAC;
             MATCH_MP_TAC SQRT_MONO_LE THEN P3N_ARITH164_TAC;
             P3N_ARITH164_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(tt - a) <= sqrt tt` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN P3N_ARITH164_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:A` THEN
    REWRITE_TAC[P3N_U164_IN] THEN ASM_REWRITE_TAC[] THEN P3N_ARITH164_TAC;
    ALL_TAC] THEN
  (* ast = T0 *)
  SUBGOAL_THEN `ast = T0:real` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `T0 <= ast /\ ~(T0 < ast) ==> ast = T0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "app" (MP_TAC o SPEC `ast:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "Nas" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ASSUME `(y:A) IN p3n_u164 hs tt x ast Lbar ast`) THEN REWRITE_TAC[P3N_U164_IN] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - ast:real`; `g:real->A`]
                  P3N_REACHED_PERSISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN P3N_ARITH164_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - ast:real`; `y:A`; `&1`]
                  P2AO_LX_USC_ST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
       [P3N_ARITH164_TAC; EXISTS_TAC `g:real->A` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `tt - (tt - t) = t:real`] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `eta:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "usc"))))))) THEN
    SUBGOAL_THEN `max T0 (ast - eta / &2) IN S` MP_TAC THENL
     [USE_THEN "S2" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC;
        UNDISCH_TAC `T0 < ast` THEN UNDISCH_TAC `ast < tt` THEN UNDISCH_TAC `&0 < eta` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `ast <= s` THENL
       [USE_THEN "Nas" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "usc" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN P3N_ARITH164_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `sqrt(tt - ast) <= sqrt tt` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN P3N_ARITH164_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:A` THEN
      REWRITE_TAC[P3N_U164_IN] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [P3N_ARITH164_TAC;
        CONJ_TAC THENL [EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[]; P3N_ARITH164_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> USE_THEN "lb" (MP_TAC o C MATCH_MP th)) THEN
    UNDISCH_TAC `T0 < ast` THEN UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "Nas" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Prop 16.4: the five properties of U in the setting                      *)
(* p3n_ctx164 (MT pp. 389-391): U is open in space-time, its points are    *)
(* reached by minimizing L-geodesics, its slices over [T0,tt) are nonempty, *)
(* each slice minimum of Lx is attained and at most 3 sqrt(tt - t), and     *)
(* the slice minimizers over compact time intervals lie in the compact K.   *)
(* ========================================================================= *)

let P3N_PROP_16_4_CORE = prove
 (`!(hs:(A)rfs_history) tt x T0 Lbar K.
     p3n_ctx164 hs tt x T0 Lbar K /\ &3 * sqrt tt + &3 <= Lbar /\
     (!(hs:(A)rfs_history) x tt a U r dt.
         rfs_history_ok hs /\ a < tt /\ x IN topspace(rfs_top_at hs tt) /\
         p3_st_open hs U a tt /\
         (!t y. y IN U t ==> ?gamma. rfs_min_Lgeod hs tt x (tt - t) gamma /\
                                     gamma (tt - t) = y) /\
         &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt /\
         (!s. tt - dt < s /\ s < tt /\ a <= s ==> x IN U s) /\
         (!a' b'. a <= a' /\ a' <= b' /\ b' < tt
                  ==> p3_st_compact hs (\t. if a' <= t /\ t <= b' then p3_Lmin_set hs tt x U t
                                            else {}) /\
                      !t. a' <= t /\ t <= b' ==> ~(p3_Lmin_set hs tt x U t = {})) /\
         (!t e. a <= t /\ t < tt /\ &0 < e
                ==> ?d. &0 < d /\
                        !t' y'. a <= t' /\ t' < tt /\ abs(t' - t) < d /\ y' IN U t'
                                ==> ?y. y IN U t /\
                                        rfs_lx hs tt x (tt - t) y <=
                                        rfs_lx hs tt x (tt - t') y' + e)
         ==> !t. a <= t /\ t < tt ==> ?y. y IN U t /\ rfs_lx hs tt x (tt - t) y <= &3 / &2)
     ==> p3_st_open hs (p3n_u164 hs tt x T0 Lbar) T0 tt /\
         (!t y. y IN p3n_u164 hs tt x T0 Lbar t
                ==> ?gamma. rfs_min_Lgeod hs tt x (tt - t) gamma /\ gamma (tt - t) = y) /\
         (!t. T0 <= t /\ t < tt ==> ~(p3n_u164 hs tt x T0 Lbar t = {})) /\
         (!t. T0 <= t /\ t < tt
              ==> ?y. y IN p3_Lmin_set hs tt x (p3n_u164 hs tt x T0 Lbar) t /\
                      rfs_Lx hs tt x (tt - t) y <= &3 * sqrt(tt - t)) /\
         (!a b. T0 <= a /\ a <= b /\ b < tt
                ==> p3_st_compact hs
                      (\t. if a <= t /\ t <= b
                           then p3_Lmin_set hs tt x (p3n_u164 hs tt x T0 Lbar) t else {}))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c712"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p3n_ctx164] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "p3n_ctx164" with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `Lbar:real`;
                 `K:real->A->bool`] P3N_U164_NONEMPTY) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; USE_THEN "c712" ACCEPT_TAC];
    DISCH_THEN(LABEL_TAC "ne")] THEN
  REPEAT CONJ_TAC THENL
   [(* open *)
    MATCH_MP_TAC P3N_U164_OPEN THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `dt:real`] THEN ASM_REWRITE_TAC[];
    (* minimizing L-geodesics *)
    MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `T0:real`; `Lbar:real`;
                   `K:real->A->bool`; `t:real`; `y:A`] P3N_U164_IN_K) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    (* nonempty slices *)
    USE_THEN "ne" ACCEPT_TAC;
    (* the slice minimum is attained and at most 3 sqrt(tt - t) *)
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `T0:real`; `Lbar:real`;
                   `K:real->A->bool`] P3N_U164_712) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[REAL_LE_REFL]; FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "ne" ACCEPT_TAC; USE_THEN "c712" ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `T0:real`; `Lbar:real`;
                   `K:real->A->bool`; `t:real`] P3N_U164_LMIN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN USE_THEN "ne" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:A`) THEN EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(m:A) IN p3_Lmin_set hs tt x (p3n_u164 hs tt x T0 Lbar) t` THEN
    REWRITE_TAC[p3_Lmin_set; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:A` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_Lx (hs:(A)rfs_history) tt x (tt - t) y <= &3 * sqrt(tt - t)` THEN
    REAL_ARITH_TAC;
    (* the slice minimizers over compact intervals lie in K *)
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P3N_STC_MONO THEN EXISTS_TAC `K:real->A->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN
    COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET] THEN
    REWRITE_TAC[SUBSET; p3_Lmin_set; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `T0:real`; `T0:real`; `Lbar:real`;
                   `K:real->A->bool`; `s:real`; `z:A`] P3N_U164_IN_K) THEN
    ASM_SIMP_TAC[REAL_LE_REFL]]);;

(* ========================================================================= *)
(* Prop 16.4: the headline.  MT Prop 16.4 (p. 389, proof pp. 389-391) with   *)
(* the second scale rr (0 < rr <= r', rr <= r, so 0 < r) from Prop 16.21,    *)
(* Cor 16.24 (both with rr) and the corrected Cor 7.12.  Constants:          *)
(* eps164 = min eps1621 eps1624; Lbar = 3 sqrt T(i+1) + 3 (MT use 8 sqrt     *)
(* T(i+1) (1 + T(i+1)); any Lbar > 3 sqrt T(i+1) + 2 works here); dlt = min  *)
(* of the dlt of 16.21 and 16.24 at (r',rr,Lbar); U is the reached set       *)
(* p3n_u164 over [T(i-1),tt).                                                *)
(* ========================================================================= *)

let P3N_PROP_16_4_FIX = prove
 (`!u:A->bool.
     P3_PROP_16_21_STATEMENT u /\ P3_COR_16_24_STATEMENT u /\
     (!(hs:(A)rfs_history) x tt a U r dt.
         rfs_history_ok hs /\ a < tt /\ x IN topspace(rfs_top_at hs tt) /\
         p3_st_open hs U a tt /\
         (!t y. y IN U t ==> ?gamma. rfs_min_Lgeod hs tt x (tt - t) gamma /\
                                     gamma (tt - t) = y) /\
         &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt /\
         (!s. tt - dt < s /\ s < tt /\ a <= s ==> x IN U s) /\
         (!a' b'. a <= a' /\ a' <= b' /\ b' < tt
                  ==> p3_st_compact hs (\t. if a' <= t /\ t <= b' then p3_Lmin_set hs tt x U t
                                            else {}) /\
                      !t. a' <= t /\ t <= b' ==> ~(p3_Lmin_set hs tt x U t = {})) /\
         (!t e. a <= t /\ t < tt /\ &0 < e
                ==> ?d. &0 < d /\
                        !t' y'. a <= t' /\ t' < tt /\ abs(t' - t) < d /\ y' IN U t'
                                ==> ?y. y IN U t /\
                                        rfs_lx hs tt x (tt - t) y <=
                                        rfs_lx hs tt x (tt - t') y' + e)
         ==> !t. a <= t /\ t < tt ==> ?y. y IN U t /\ rfs_lx hs tt x (tt - t) y <= &3 / &2)
     ==> P3_PROP_16_4_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P3_PROP_16_21_STATEMENT; P3_COR_16_24_STATEMENT; P3_PROP_16_4_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps1621:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1621")))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps1624:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1624")))
      (LABEL_TAC "c712"))) THEN
  EXISTS_TAC `min eps1621 eps1624` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < eps1621` THEN UNDISCH_TAC `&0 < eps1624` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`] THEN
  STRIP_TAC THEN
  USE_THEN "p1621" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                                    `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `eps <= min eps1621 eps1624` THEN REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "q1621")] THEN
  USE_THEN "p1624" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                                    `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `eps <= min eps1621 eps1624` THEN REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "q1624")] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `r':real`;
                       `rr:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `Lbar = &3 * sqrt(p3_T (SUC i)) + &3` THEN
  SUBGOAL_THEN `&0 < Lbar` ASSUME_TAC THENL
   [EXPAND_TAC "Lbar" THEN
    SUBGOAL_THEN `&0 <= sqrt(p3_T (SUC i))` MP_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[p3_T] THEN
      SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_ARITH `&0 <= &2 /\ &0 <= &32`];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "q1621" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
                                    `r':real`; `rr:real`; `Lbar:real`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k1621"))) THEN
  USE_THEN "q1624" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
                                    `r':real`; `rr:real`; `Lbar:real`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g1624"))) THEN
  EXISTS_TAC `min dlt1 dlt2` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < dlt1` THEN UNDISCH_TAC `&0 < dlt2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`;
                       `x:A`; `tt:real`; `r:real`] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  (* the settings at dlt1 and dlt2 *)
  SUBGOAL_THEN
   `p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt1 (rs',ks',dd) (hs:(A)rfs_history) /\
    p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt2 (rs',ks',dd) hs`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P3N_P16_SETTING_MONO THEN EXISTS_TAC `min dlt1 dlt2` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the compact set of Prop 16.21 at Lbar *)
  USE_THEN "k1621" (MP_TAC o SPECL [`rs':num->real`; `ks':num->real`; `dd:num->real`;
                                    `hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real->A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inK"))) THEN
  (* the setting *)
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ rfs_pinched (rfs_view hs) /\
                rfs_horizon hs <= p3_T (SUC i)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' (min dlt1 dlt2) (rs',ks',dd)
                                (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_p16_setting; p3_step_hyp; p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3_T (i - 1) /\ p3_T (i - 1) < p3_T i` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p3_T] THEN CONJ_TAC THENL
     [SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_ARITH `&0 < &2 /\ &0 < &32`];
      SIMP_TAC[REAL_LT_DIV2_EQ; REAL_ARITH `&0 < &32`] THEN
      MATCH_MP_TAC REAL_POW_MONO_LT THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `p3n_u164 (hs:(A)rfs_history) tt x (p3_T (i - 1)) Lbar` THEN
  MATCH_MP_TAC P3N_PROP_16_4_CORE THEN EXISTS_TAC `K:real->A->bool` THEN
  REPEAT CONJ_TAC THENL
   [(* the setting p3n_ctx164 *)
    REWRITE_TAC[p3n_ctx164] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `p3_T (i - 1) < p3_T i` THEN UNDISCH_TAC `p3_T i <= tt` THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY EXISTS_TAC [`r:real`; `r pow 2`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
      UNDISCH_TAC `&0 < rr` THEN UNDISCH_TAC `rr <= r` THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`b:real`; `gamma:real->A`] THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "inK" (MATCH_MP_TAC o SPECL [`b:real`; `gamma:real->A`]) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "g1624" (MATCH_MP_TAC o SPECL [`rs':num->real`; `ks':num->real`;
                                                `dd:num->real`; `hs:(A)rfs_history`; `x:A`;
                                                `tt:real`; `r:real`; `b:real`;
                                                `gamma:real->A`]) THEN
        ASM_REWRITE_TAC[]]];
    (* 3 sqrt tt + 3 <= Lbar *)
    EXPAND_TAC "Lbar" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> &3 * x + &3 <= &3 * y + &3`) THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN
    UNDISCH_TAC `tt < rfs_horizon (hs:(A)rfs_history)` THEN
    UNDISCH_TAC `rfs_horizon (hs:(A)rfs_history) <= p3_T (SUC i)` THEN REAL_ARITH_TAC;
    (* the corrected Cor 7.12 *)
    USE_THEN "c712" ACCEPT_TAC]);;

(* ========================================================================= *)
(* The route theorem for Prop 16.4 (the statement of Cor 7.12 in the route   *)
(* equals the third hypothesis of P3N_PROP_16_4_FIX).                        *)
(* ========================================================================= *)

let P3N_PROP_16_4_ROUTE = prove
 (`!u:A->bool. P3_PROP_16_4_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_16_4_ROUTE_STATEMENT] THEN
  MP_TAC(ISPEC `u:A->bool` P3N_PROP_16_4_FIX) THEN
  REWRITE_TAC[GSYM P2_COR_7_12_STATEMENT] THEN MESON_TAC[]);;

