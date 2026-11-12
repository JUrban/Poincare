(* ========================================================================= *)
(* Unit pc_p3_c17trunc: truncation of a surgery history at a                *)
(* time ts in (0, horizon]: the events before ts, the same stages, times and *)
(* metrics, the last slab cut at ts.  Its view is the truncated view, it is *)
(* extended by the original history, and p3_struct, p3h_plus_disc and the  *)
(* step hypotheses p3_step_hyp (when p3_T i < ts) pass to it.  Used by MT    *)
(* Lemmas 17.2, 17.7 and Prop 17.1, which apply Prop 16.5 and the           *)
(* noncollapsing proposition to the history truncated at a first bad time. *)
(*                                                                         *)
(* Definitions, the slab of ts, rfs_history_ok, rfs_extends,                *)
(* the view.                                                                *)
(* ========================================================================= *)

needs "src/pc_p3e_flowext.ml";;

prioritize_real();;
type_invention_error := true;;

let p3h_tslab = new_definition
 `p3h_tslab (hs:(A)rfs_history) (ts:real) =
    @k. k <= hs_count hs /\ hs_time hs k < ts /\ ts <= hs_time hs (k + 1)`;;

let p3h_trunc = new_definition
 `p3h_trunc (hs:(A)rfs_history) (ts:real) =
    RfsHistory (p3h_tslab hs ts)
               (\k. if k <= p3h_tslab hs ts then hs_time hs k else ts)
               (hs_top hs) (hs_atlas hs) (hs_metric hs) (hs_event hs)`;;

let P3H_TRUNC_FIELDS = prove
 (`!(hs:(A)rfs_history) ts.
     hs_count (p3h_trunc hs ts) = p3h_tslab hs ts /\
     hs_time (p3h_trunc hs ts) = (\k. if k <= p3h_tslab hs ts then hs_time hs k else ts) /\
     hs_top (p3h_trunc hs ts) = hs_top hs /\
     hs_atlas (p3h_trunc hs ts) = hs_atlas hs /\
     hs_metric (p3h_trunc hs ts) = hs_metric hs /\
     hs_event (p3h_trunc hs ts) = hs_event hs`,
  REWRITE_TAC[p3h_trunc; hs_count; hs_time; hs_top; hs_atlas; hs_metric; hs_event]);;

let P3H_TSLAB = prove
 (`!(hs:(A)rfs_history) ts.
     rfs_history_ok hs /\ &0 < ts /\ ts <= rfs_horizon hs
     ==> p3h_tslab hs ts <= hs_count hs /\ hs_time hs (p3h_tslab hs ts) < ts /\
         ts <= hs_time hs (p3h_tslab hs ts + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3h_tslab] THEN
  CONV_TAC SELECT_CONV THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!k. k <= hs_count hs + 1 ==> hs_time (hs:(A)rfs_history) k < ts`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `hs_time (hs:(A)rfs_history) 0 = &0` SUBST1_TAC THENL
       [ASM_MESON_TAC[rfs_history_ok]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < ts /\ k <= hs_count hs` STRIP_ASSUME_TAC
    THENL
     [CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[ADD1; REAL_NOT_LE];
    DISCH_THEN(MP_TAC o SPEC `hs_count (hs:(A)rfs_history) + 1`) THEN
    UNDISCH_TAC `ts <= rfs_horizon (hs:(A)rfs_history)` THEN
    REWRITE_TAC[rfs_horizon; LE_REFL] THEN REAL_ARITH_TAC]);;

let P3H_TRUNC_OK = prove
 (`!(hs:(A)rfs_history) ts.
     rfs_history_ok hs /\ &0 < ts /\ ts <= rfs_horizon hs
     ==> rfs_history_ok (p3h_trunc hs ts) /\ rfs_extends (p3h_trunc hs ts) hs /\
         rfs_horizon (p3h_trunc hs ts) = ts /\ hs_count (p3h_trunc hs ts) <= hs_count hs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `ts:real`] P3H_TSLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `n = p3h_tslab (hs:(A)rfs_history) ts` THEN STRIP_TAC THEN
  REWRITE_TAC[P3H_TRUNC_FIELDS; rfs_horizon; rfs_extends; rfs_history_ok] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(n + 1 <= n)`] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "times")
    (CONJUNCTS_THEN2 (LABEL_TAC "stages") (LABEL_TAC "events")))) THEN
  ASM_REWRITE_TAC[LE_0; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k + 1 <= n` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "times" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `k = n:num` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "stages" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k + 1 <= n` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `k = n:num` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`hs_time (hs:(A)rfs_history) n`;
                          `hs_time (hs:(A)rfs_history) (n + 1)`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `k <= n:num` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "events" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REFL_TAC]);;

let P3H_VIEW_TRUNC_HORIZON = prove
 (`!hs:(A)rfs_history. rfs_trunc (rfs_view hs) (rfs_horizon hs) = rfs_view hs`,
  GEN_TAC THEN REWRITE_TAC[rfs_view; rfs_trunc; PAIR_EQ; FUN_EQ_THM] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `t:real` THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_metric_at; rfs_live] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[rfs_horizon] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let P3H_TRUNC_VIEW = prove
 (`!(hs:(A)rfs_history) ts.
     rfs_history_ok hs /\ &0 < ts /\ ts <= rfs_horizon hs
     ==> rfs_view (p3h_trunc hs ts) = rfs_trunc (rfs_view hs) ts`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `ts:real`] P3H_TRUNC_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p3h_trunc (hs:(A)rfs_history) ts`; `hs:(A)rfs_history`; `ts:real`]
                RFS_EXTENDS_TRUNC) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[P3H_VIEW_TRUNC_HORIZON]);;

let P3H_TRUNC_TRUNC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    a b. b <= a ==> rfs_trunc (rfs_trunc V a) b = rfs_trunc V b`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_trunc; PAIR_EQ; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x < a:real` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The structural invariant and the step hypotheses pass to                 *)
(* truncations (the event clauses read only times before the event, via the *)
(* iff lemmas P3E_*_EXTEND of pc_p3e_flowext applied to the truncation      *)
(* extended by the original history).                                       *)
(* ========================================================================= *)

let P3H_PINCHED_TRUNC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tau. rfs_pinched V ==> rfs_pinched (rfs_trunc V tau)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_trunc; rfs_pinched] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]);;

let P3H_STRUCT_TRUNC = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) ts.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ &0 < ts /\ ts <= rfs_horizon hs
     ==> p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (p3h_trunc hs ts)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `ts:real`] P3H_TRUNC_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `ts:real`] P3H_TRUNC_VIEW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `hs_top (p3h_trunc hs ts) = hs_top (hs:(A)rfs_history) /\
                hs_atlas (p3h_trunc hs ts) = hs_atlas hs /\
                hs_metric (p3h_trunc hs ts) = hs_metric hs /\
                hs_event (p3h_trunc hs ts) = hs_event hs` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[P3H_TRUNC_FIELDS]; ALL_TAC] THEN
  ABBREV_TAC `h = p3h_trunc (hs:(A)rfs_history) ts` THEN
  REWRITE_TAC[p3_struct] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* the surgery necks of length 2 (p3_neck2_ok) *)
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p3_neck2_ok (dl,p3_hscale hf rp dl) (hs:(A)rfs_history) k <=>
                  p3_neck2_ok (dl,p3_hscale hf rp dl) (h:(A)rfs_history) k`
    (fun th -> REWRITE_TAC[GSYM th]) THENL
     [MATCH_MP_TAC P3E_NECK2_EXTEND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_neck2_ok")) (concl th))) THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:(A)rfs_history`; `hs:(A)rfs_history`; `C:real`; `eps:real`;
                   `dl:real->real`; `p3_hscale hf rp dl`; `k:num`] P3E_SURGERY_OK_EXTEND) THEN
    MP_TAC(ISPECL [`h:(A)rfs_history`; `hs:(A)rfs_history`; `rp:real->real`; `dl:real->real`;
                   `k:num`] P3E_OMEGA_RHO_EXTEND) THEN
    MP_TAC(ISPECL [`h:(A)rfs_history`; `hs:(A)rfs_history`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`; `p3_hscale hf rp dl`;
                   `k:num`] P3E_CAP_OK_EXTEND) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_surgery_ok")) (concl th))) THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:(A)rfs_history`; `hs:(A)rfs_history`; `k:num`]
                  P3E_SLAB_MAXIMAL_EXTEND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_slab_maximal")) (concl th))) THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC P3H_PINCHED_TRUNC THEN ASM_REWRITE_TAC[]]);;

let P3H_STEP_HYP_TRUNC = prove
 (`!C eps hf md g0 A0 i rs ks ds dlt rs' ks' dd (hs:(A)rfs_history) ts.
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
     p3_T i < ts /\ ts <= rfs_horizon hs
     ==> p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) (p3h_trunc hs ts)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_step_hyp] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < ts` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `p3_T i` THEN ASM_REWRITE_TAC[p3_T] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_struct]; ALL_TAC] THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `ts:real`] P3H_TRUNC_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `ts:real`] P3H_TRUNC_VIEW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[P3H_TRUNC_TRUNC; REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P3H_STRUCT_TRUNC THEN ASM_REWRITE_TAC[]);;

