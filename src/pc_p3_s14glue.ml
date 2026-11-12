(* ========================================================================= *)
(* Unit pc_p3_s14glue (Part 3 proofs): MT Lemma 14.11 for                  *)
(* histories.  P3_LEMMA_14_11_ROUTE |- !u. P3_LEMMA_14_11_ROUTE_STATEMENT u  *)
(* (the route obligation of pc_p3_route: PDE_GLUE_STATEMENT u (:3) implies   *)
(* P3_LEMMA_14_11_STATEMENT u) and, with PDE_GLUE of pc_rf_glue,            *)
(* P3_LEMMA_14_11 |- !u. P3_LEMMA_14_11_STATEMENT u.  Two gaps of MT's proof *)
(* do not arise in this form: the stages are fixed manifolds (no glued       *)
(* space-time has to be paracompact), and the statement is already local to  *)
(* an open set W of retained points of one event.                            *)
(* ========================================================================= *)

needs "src/pc_p3_s14jet.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The data of a history around an event k: smooth stages,                 *)
(* slab flows, the event, the ordering of the times, and the slices at     *)
(* times of slab k - 1 and of slab k.                                       *)
(* ------------------------------------------------------------------------- *)

let P3S_STAGE_FACTS = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs
     ==> smooth_manifold_atlas (hs_top hs (k - 1)) (hs_atlas hs (k - 1)) /\
         smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
         ricci_flow_from (hs_top hs (k - 1),hs_atlas hs (k - 1))
                         (hs_time hs (k - 1)) (hs_time hs k) (hs_metric hs (k - 1)) /\
         ricci_flow_from (hs_top hs k,hs_atlas hs k)
                         (hs_time hs k) (hs_time hs (k + 1)) (hs_metric hs k) /\
         rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1))
                      (hs_metric hs (k - 1)) (hs_time hs k)
                      (hs_top hs k,hs_atlas hs k) (hs_metric hs k)
                      (hs_event hs k) /\
         hs_time hs (k - 1) < hs_time hs k /\ hs_time hs k < hs_time hs (k + 1) /\
         (!s. hs_time hs (k - 1) <= s /\ s < hs_time hs k
              ==> rfs_top_at hs s = hs_top hs (k - 1) /\
                  rfs_atlas_at hs s = hs_atlas hs (k - 1) /\
                  rfs_metric_at hs s = hs_metric hs (k - 1) s) /\
         (!s. hs_time hs k <= s /\ s < hs_time hs (k + 1)
              ==> rfs_top_at hs s = hs_top hs k /\
                  rfs_atlas_at hs s = hs_atlas hs k /\
                  rfs_metric_at hs s = hs_metric hs k s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `k - 1 <= hs_count (hs:(A)rfs_history) /\ k - 1 + 1 = k`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "TM")
    (CONJUNCTS_THEN2 (LABEL_TAC "ST") (LABEL_TAC "EV")))) THEN
  USE_THEN "ST" (MP_TAC o SPEC `k - 1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "ST" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "TM" (MP_TAC o SPEC `k - 1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "TM" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "EV" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `k - 1 + 1 = k`]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB);
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB)] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> k - 1 + 1 = k`]);;

(* ------------------------------------------------------------------------- *)
(* MT Lemma 14.11 for histories.  The route obligation                     *)
(* P3_LEMMA_14_11_ROUTE (from PDE_GLUE_STATEMENT) and, with PDE_GLUE of     *)
(* pc_rf_glue, P3_LEMMA_14_11.  The glued family of p3_region_flow is the  *)
(* old slab flow transported to the new atlas before the event time        *)
(* (P3S_RFO_TRANSPORT_W) and the new slab flow from it; PDE_GLUE joins them *)
(* using the jets of P3S_EVENT_JETS; P2CF_RFO_UPTO gives rfs_flow_upto.     *)
(* ------------------------------------------------------------------------- *)

let P3_LEMMA_14_11_ROUTE = prove
 (`!u:A->bool. P3_LEMMA_14_11_ROUTE_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P3_LEMMA_14_11_ROUTE_STATEMENT; P3_LEMMA_14_11_STATEMENT;
              PDE_GLUE_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "GLUE") THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `k:num`; `W:A->bool`; `a:real`; `b:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3S_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topX = hs_top (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `atlasX = hs_atlas (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `gX = hs_metric (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `topY = hs_top (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `atlasY = hs_atlas (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `gY = hs_metric (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `ts = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `t0 = hs_time (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `t2 = hs_time (hs:(A)rfs_history) (k + 1)` THEN
  ABBREV_TAC `ev = hs_event (hs:(A)rfs_history) k` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "FX") (CONJUNCTS_THEN2 (LABEL_TAC "FY")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "S1") (LABEL_TAC "S2"))))))))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `W:A->bool`] P3S_EVENT_RETAINED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3_region_flow] THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_view; rfs_persists] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < ts` THENL
     [USE_THEN "S1" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "S2" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "S2" (MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ABBREV_TAC
   `G = \s. restrict_metric (atlasY:((A->bool)#(A->real^3))->bool) W
              (\x. if s = b then (gY:real->A->real^3^3) b x
                   else mfd_pullback_metric atlasY (rfs_atlas_at (hs:(A)rfs_history) s)
                          (\y. y) (rfs_metric_at hs s) x)` THEN
  SUBGOAL_THEN
   `!t. a < t /\ t < ts
        ==> (G:real->A->real^3^3) t =
            restrict_metric atlasY W
              (mfd_pullback_metric atlasY atlasX (\x. x) ((gX:real->A->real^3^3) t))`
  (LABEL_TAC "GM") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "G" THEN
    USE_THEN "S1" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(t:real = b)` (fun th -> REWRITE_TAC[th; ETA_AX]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. ts <= t /\ t < t2 /\ x IN W
          ==> (G:real->A->real^3^3) t x =
              restrict_metric atlasY W ((gY:real->A->real^3^3) t) x`
  (LABEL_TAC "GP") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN
    USE_THEN "S2" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `t:real = b` THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC P2CF_RESTRICT_METRIC_CONG THEN EXISTS_TAC `topY:A topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CF_PULLBACK_ID THEN
    EXISTS_TAC `topY:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ricci_flow_on (subtopology topY W,restrict_atlas atlasY W) a ts (G:real->A->real^3^3)`
  (LABEL_TAC "F1") THENL
   [MATCH_MP_TAC P2CF_RFO_CONG THEN
    EXISTS_TAC `\t. restrict_metric (atlasY:((A->bool)#(A->real^3))->bool) W
                      (mfd_pullback_metric atlasY atlasX (\x:A. x) ((gX:real->A->real^3^3) t))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RFO_TRANSPORT_W THEN EXISTS_TAC `topX:A topology` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`t0:real`; `ts:real`] THEN
      USE_THEN "FX" (fun th -> REWRITE_TAC[CONJUNCT1(GEN_REWRITE_RULE I [ricci_flow_from] th)]) THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "GM" (fun th -> ASM_SIMP_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ricci_flow_from (subtopology topY W,restrict_atlas atlasY W) ts ((b + t2) / &2)
                    (G:real->A->real^3^3)`
  (LABEL_TAC "F2") THENL
   [MATCH_MP_TAC PDE_RFF_CONG THEN
    EXISTS_TAC `\t. restrict_metric (atlasY:((A->bool)#(A->real^3))->bool) W
                      ((gY:real->A->real^3^3) t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CF_RFF_RESTRICT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`ts:real`; `t2:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      USE_THEN "GP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `W:A->bool`; `a:real`; `G:real->A->real^3^3`]
                P3S_EVENT_JETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "FX" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
      REWRITE_TAC[ricci_flow_on] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "F1" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "F2" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
      SIMP_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "GM" (fun th -> ASM_SIMP_TAC[th]);
      REPEAT STRIP_TAC THEN USE_THEN "GP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    DISCH_TAC] THEN
  USE_THEN "GLUE" (MP_TAC o ISPECL
   [`subtopology topY (W:A->bool)`; `restrict_atlas (atlasY:((A->bool)#(A->real^3))->bool) W`;
    `a:real`; `ts:real`; `(b + t2) / &2`; `G:real->A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a:real`; `(b + t2) / &2`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC);;

let P3_LEMMA_14_11 = prove
 (`!u:A->bool. P3_LEMMA_14_11_STATEMENT u`,
  GEN_TAC THEN
  MP_TAC(ISPEC `u:A->bool` P3_LEMMA_14_11_ROUTE) THEN
  REWRITE_TAC[P3_LEMMA_14_11_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_ACCEPT_TAC(INST_TYPE [`:3`,`:N`] (ISPEC `u:A->bool` PDE_GLUE)));;

