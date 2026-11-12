(* ========================================================================= *)
(* Unit pc_p3e_surgevent: steps S6 and S7 of MT Lemma 15.11 (Sec 15.4): the  *)
(* history extended by one surgery event at the horizon T (stage n+1 = the   *)
(* retained part Y of the cut-and-capped Z, the new slab G' on [T,T')), its  *)
(* rfs_history_ok and rfs_extends, and the structural invariant p3_struct of *)
(* the extended history from the event data (11.19, 11.30, 11.31 outputs, S2 *)
(* cutcap, S3 retain, S4 surgmetric, S9 curvpersist).                        *)
(* ========================================================================= *)

needs "src/pc_p3e_surgmetric.ml";;
needs "src/pc_p3e_retain.ml";;
needs "src/pc_p3e_flowext.ml";;
needs "src/pc_p3e_curvpersist.ml";;
needs "src/pc_p3e_orient.ml";;
needs "src/pc_lim_restrict.ml";;
needs "src/pc_rfs_assembly.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Evolving necks.  P3E_EVNECK_SHORTEN: a neck of rescaled length a is one   *)
(* of any length 0 < b <= a (the statement of P3H_EVNECK_SHORTEN of          *)
(* pc_p3_c177a, proved here to keep the load closure of this unit small).    *)
(* P3E_EVNECK_UPTO: an evolving neck at time t only reads the view at times *)
(* <= t (the scalar curvature at the centre is positive).                   *)
(* ------------------------------------------------------------------------- *)

let P3E_EVNECK_SHORTEN = prove
 (`!V eps (x:A) t a b e.
     rfs_evolving_neck V eps x t a e /\ &0 < b /\ b <= a
     ==> rfs_evolving_neck V eps x t b e`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `x:A`; `t:real`; `a:real`; `b:real`; `e:real^3->A`] THEN
  REWRITE_TAC[rfs_evolving_neck; rfs_persists; rfs_close_fam; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) (G t) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck ((TM:real->A topology) t,(AT:real->((A->bool)#(A->real^3))->bool) t)
                          (G t) eps x e` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t - b / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) (G t) x` THEN
    ASM_REWRITE_TAC[REAL_ARITH `t - a <= t - b <=> b <= a`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3E_EVNECK_UPTO_IMP = prove
 (`!TM1 TM2 AT1 AT2 G1 G2 eps (x:A) t len e.
     (!s. s <= t ==> TM1 s = TM2 s /\ AT1 s = AT2 s /\ G1 s = G2 s) /\
     rfs_evolving_neck (TM1,AT1,G1) eps x t len e
     ==> rfs_evolving_neck (TM2,AT2,G2) eps x t len e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ag") MP_TAC) THEN
  USE_THEN "ag" (MP_TAC o SPEC `t:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THEN
  REWRITE_TAC[rfs_evolving_neck; rfs_persists; rfs_close_fam; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_scalar ((AT2:real->((A->bool)#(A->real^3))->bool) t) (G2 t) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck ((TM2:real->A topology) t,(AT2:real->((A->bool)#(A->real^3))->bool) t)
                          (G2 t) eps x e` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "ag" (fun th -> MP_TAC(MP (SPEC `s:real` th) (ASSUME `s:real <= t`))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `t + s / mfd_scalar ((AT2:real->((A->bool)#(A->real^3))->bool) t) (G2 t) x <= t`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> t + x <= t`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
      ALL_TAC] THEN
    USE_THEN "ag" (fun th -> MP_TAC(MP (SPEC
     `t + s / mfd_scalar ((AT2:real->((A->bool)#(A->real^3))->bool) t) (G2 t) x` th)
     (ASSUME `t + s / mfd_scalar ((AT2:real->((A->bool)#(A->real^3))->bool) t) (G2 t) x
              <= t`))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P3E_EVNECK_UPTO = prove
 (`!TM1 TM2 AT1 AT2 G1 G2 eps (x:A) t len e.
     (!s. s <= t ==> TM1 s = TM2 s /\ AT1 s = AT2 s /\ G1 s = G2 s)
     ==> (rfs_evolving_neck (TM1,AT1,G1) eps x t len e <=>
          rfs_evolving_neck (TM2,AT2,G2) eps x t len e)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC P3E_EVNECK_UPTO_IMP THENL
   [MAP_EVERY EXISTS_TAC [`TM1:real->A topology`; `AT1:real->((A->bool)#(A->real^3))->bool`;
                          `G1:real->A->real^3^3`];
    MAP_EVERY EXISTS_TAC [`TM2:real->A topology`; `AT2:real->((A->bool)#(A->real^3))->bool`;
                          `G2:real->A->real^3^3`]] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* S6: the history extended by one event at the horizon T:                   *)
(* stage n+1 = (topY, atlasY) with the slab flow G' on [T,T'), event ev.     *)
(* P3E_HIST_EVENT: rfs_history_ok, rfs_extends, the fields, and the view on  *)
(* [T,T') (the flow G' on Y).                                                *)
(* ------------------------------------------------------------------------- *)

let p3e_hevent = new_definition
 `p3e_hevent (hs:(A)rfs_history) (topY:A topology) (atlasY:((A->bool)#(A->real^3))->bool)
             (G':real->A->real^3^3) (T':real) (ev:(A)rfs_event) =
    RfsHistory (SUC(hs_count hs))
      (\k. if k = SUC(hs_count hs) + 1 then T' else hs_time hs k)
      (\k. if k = SUC(hs_count hs) then topY else hs_top hs k)
      (\k. if k = SUC(hs_count hs) then atlasY else hs_atlas hs k)
      (\k. if k = SUC(hs_count hs) then G' else hs_metric hs k)
      (\k. if k = SUC(hs_count hs) then ev else hs_event hs k)`;;

let P3E_HEVENT_FIELDS = prove
 (`!(hs:(A)rfs_history) topY atlasY G' T' ev.
     hs_count (p3e_hevent hs topY atlasY G' T' ev) = SUC(hs_count hs) /\
     (!k. hs_time (p3e_hevent hs topY atlasY G' T' ev) k =
          if k = SUC(hs_count hs) + 1 then T' else hs_time hs k) /\
     (!k. hs_top (p3e_hevent hs topY atlasY G' T' ev) k =
          if k = SUC(hs_count hs) then topY else hs_top hs k) /\
     (!k. hs_atlas (p3e_hevent hs topY atlasY G' T' ev) k =
          if k = SUC(hs_count hs) then atlasY else hs_atlas hs k) /\
     (!k. hs_metric (p3e_hevent hs topY atlasY G' T' ev) k =
          if k = SUC(hs_count hs) then G' else hs_metric hs k) /\
     (!k. hs_event (p3e_hevent hs topY atlasY G' T' ev) k =
          if k = SUC(hs_count hs) then ev else hs_event hs k)`,
  REWRITE_TAC[p3e_hevent; hs_count; hs_time; hs_top; hs_atlas; hs_metric; hs_event]);;

let P3E_HIST_EVENT = prove
 (`!(hs:(A)rfs_history) topY atlasY G' T' ev.
     rfs_history_ok hs /\ rfs_horizon hs < T' /\
     hausdorff_space topY /\ smooth_manifold_atlas topY atlasY /\ compact_space topY /\
     ricci_flow_from (topY,atlasY) (rfs_horizon hs) T' G' /\
     rfs_event_ok (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                  (hs_metric hs (hs_count hs)) (rfs_horizon hs) (topY,atlasY) G' ev
     ==> rfs_history_ok (p3e_hevent hs topY atlasY G' T' ev) /\
         rfs_extends hs (p3e_hevent hs topY atlasY G' T' ev) /\
         hs_count (p3e_hevent hs topY atlasY G' T' ev) = SUC(hs_count hs) /\
         hs_time (p3e_hevent hs topY atlasY G' T' ev) (SUC(hs_count hs)) = rfs_horizon hs /\
         rfs_horizon (p3e_hevent hs topY atlasY G' T' ev) = T' /\
         (!k. k <= hs_count hs
              ==> hs_time (p3e_hevent hs topY atlasY G' T' ev) k = hs_time hs k /\
                  hs_top (p3e_hevent hs topY atlasY G' T' ev) k = hs_top hs k /\
                  hs_atlas (p3e_hevent hs topY atlasY G' T' ev) k = hs_atlas hs k /\
                  hs_metric (p3e_hevent hs topY atlasY G' T' ev) k = hs_metric hs k) /\
         (!k. 1 <= k /\ k <= hs_count hs
              ==> hs_event (p3e_hevent hs topY atlasY G' T' ev) k = hs_event hs k) /\
         hs_top (p3e_hevent hs topY atlasY G' T' ev) (SUC(hs_count hs)) = topY /\
         hs_atlas (p3e_hevent hs topY atlasY G' T' ev) (SUC(hs_count hs)) = atlasY /\
         hs_metric (p3e_hevent hs topY atlasY G' T' ev) (SUC(hs_count hs)) = G' /\
         hs_event (p3e_hevent hs topY atlasY G' T' ev) (SUC(hs_count hs)) = ev /\
         (!t. rfs_horizon hs <= t /\ t < T'
              ==> rfs_top_at (p3e_hevent hs topY atlasY G' T' ev) t = topY /\
                  rfs_atlas_at (p3e_hevent hs topY atlasY G' T' ev) t = atlasY /\
                  rfs_metric_at (p3e_hevent hs topY atlasY G' T' ev) t = G' t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `G':real->A->real^3^3`;
                 `T':real`; `ev:(A)rfs_event`] P3E_HEVENT_FIELDS) THEN
  ABBREV_TAC `hs' = p3e_hevent (hs:(A)rfs_history) topY atlasY G' T' ev` THEN
  ABBREV_TAC `n = hs_count (hs:(A)rfs_history)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_horizon (hs:(A)rfs_history) = hs_time hs (n + 1)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[rfs_horizon]; ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs':(A)rfs_history) (SUC n) = rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `~(SUC n = SUC n + 1)`; ADD1]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_horizon (hs':(A)rfs_history) = T'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfs_horizon]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k <= n
        ==> hs_time (hs':(A)rfs_history) k = hs_time hs k /\
            hs_top hs' k = hs_top hs k /\ hs_atlas hs' k = hs_atlas hs k /\
            hs_metric hs' k = hs_metric hs k`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = SUC n + 1) /\ ~(k = SUC n)`]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= n ==> hs_event (hs':(A)rfs_history) k = hs_event hs k`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = SUC n)`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `hs_time (hs:(A)rfs_history) 0 = &0`)) THEN
    MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rfs_history_ok (hs':(A)rfs_history)` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_history_ok] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `~(0 = SUC n + 1)`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `k = SUC n` THENL
       [ASM_REWRITE_TAC[ARITH_RULE `~(SUC n = SUC n + 1)`] THEN
        SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (SUC n) = rfs_horizon hs` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[ADD1]; ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(k:num) <= n` ASSUME_TAC THENL
         [UNDISCH_TAC `k <= SUC n` THEN UNDISCH_TAC `~(k = SUC n)` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = SUC n + 1) /\ ~(k + 1 = SUC n + 1)`] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `(<):real->real->bool`)) (concl th) &&
          not (can (find_term ((=) `rfs_horizon:(A)rfs_history->real`)) (concl th)) &&
          not (can (find_term ((=) `hs':(A)rfs_history`)) (concl th)))) THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `k = SUC n` THENL
       [ASM_REWRITE_TAC[ARITH_RULE `~(SUC n = SUC n + 1)`] THEN
        SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (SUC n) = rfs_horizon hs` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[ADD1]; ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(k:num) <= n` ASSUME_TAC THENL
         [UNDISCH_TAC `k <= SUC n` THEN UNDISCH_TAC `~(k = SUC n)` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = SUC n + 1) /\ ~(k + 1 = SUC n + 1)`] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `hausdorff_space:A topology->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `k = SUC n` THENL
       [ASM_REWRITE_TAC[SUC_SUB1; ARITH_RULE `~(n = SUC n)`;
                        ARITH_RULE `~(SUC n = SUC n + 1)`] THEN
        UNDISCH_TAC `rfs_event_ok (hs_top (hs:(A)rfs_history) n,hs_atlas hs n) (hs_metric hs n)
                       (rfs_horizon hs) (topY,atlasY) G' (ev:(A)rfs_event)` THEN
        ASM_REWRITE_TAC[ADD1];
        SUBGOAL_THEN `(k:num) <= n` ASSUME_TAC THENL
         [UNDISCH_TAC `k <= SUC n` THEN UNDISCH_TAC `~(k = SUC n)` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[ARITH_RULE `1 <= k /\ k <= n
                                 ==> ~(k = SUC n + 1) /\ ~(k - 1 = SUC n) /\ ~(k = SUC n)`] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun tm -> is_const tm && fst(dest_const tm) = "rfs_event_ok"))
              (concl th))) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hs_time (hs':(A)rfs_history) (SUC n + 1) = T' /\ hs_top hs' (SUC n) = topY /\
    hs_atlas hs' (SUC n) = atlasY /\ hs_metric hs' (SUC n) = G' /\
    hs_event hs' (SUC n) = ev /\ hs_count hs' = SUC n`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_forall(concl th) && is_eq(snd(strip_forall(concl th))) &&
    can (find_term ((=) `hs':(A)rfs_history`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_extends] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      ASM_REWRITE_TAC[GSYM ADD1; REAL_LE_REFL];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_slab (hs':(A)rfs_history) t = SUC n` ASSUME_TAC THENL
   [MATCH_MP_TAC RFS_SLAB_UNIQUE THEN ASM_REWRITE_TAC[LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_metric_at; rfs_live] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= t /\ t < T'` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The pre-surgery view of the extended history at the new                   *)
(* event agrees with the maximal extension p3_maxext of the old history at  *)
(* all times <= T (the metrics differ after T), so evolving necks at T      *)
(* transfer (P3E_HEVENT_EVNECK); its scalar curvature at T on Omega is that *)
(* of the limit metric (P3E_HEVENT_SCALAR); its atlas and metric at T are    *)
(* the restrictions to Omega (P3E_HEVENT_PREVIEW_T).                        *)
(* ------------------------------------------------------------------------- *)

let P3E_HEVENT_PREVIEW_T = prove
 (`!(hs:(A)rfs_history) hs' ev.
     rfs_extends hs hs' /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\ hs_event hs' (SUC(hs_count hs)) = ev
     ==> rfs_vtop (rfs_preview hs' (SUC(hs_count hs))) (rfs_horizon hs) =
         subtopology (hs_top hs (hs_count hs)) (ev_omega ev) /\
         rfs_vatlas (rfs_preview hs' (SUC(hs_count hs))) (rfs_horizon hs) =
         restrict_atlas (hs_atlas hs (hs_count hs)) (ev_omega ev) /\
         rfs_vmetric (rfs_preview hs' (SUC(hs_count hs))) (rfs_horizon hs) =
         restrict_metric (hs_atlas hs (hs_count hs)) (ev_omega ev) (ev_limit ev)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `hs_count (hs:(A)rfs_history)` o CONJUNCT1 o CONJUNCT2 o
    CONJUNCT2 o GEN_REWRITE_RULE I [rfs_extends]) THEN
  REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[rfs_preview; rfs_vtop; rfs_vatlas; rfs_vmetric; SUC_SUB1]);;

let P3E_HEVENT_AGREE = prove
 (`!(hs:(A)rfs_history) hs' ev s.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\
     hs_event hs' (SUC(hs_count hs)) = ev /\ s <= rfs_horizon hs
     ==> rfs_vtop (rfs_preview hs' (SUC(hs_count hs))) s =
         rfs_vtop (p3_maxext hs (ev_omega ev) (ev_limit ev)) s /\
         rfs_vatlas (rfs_preview hs' (SUC(hs_count hs))) s =
         rfs_vatlas (p3_maxext hs (ev_omega ev) (ev_limit ev)) s /\
         rfs_vmetric (rfs_preview hs' (SUC(hs_count hs))) s =
         rfs_vmetric (p3_maxext hs (ev_omega ev) (ev_limit ev)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = rfs_horizon (hs:(A)rfs_history)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `ev:(A)rfs_event`]
      P3E_HEVENT_PREVIEW_T) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[p3_maxext; rfs_vtop; rfs_vatlas; rfs_vmetric];
    SUBGOAL_THEN `s < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `s:real`] RFS_EXTENDS_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[rfs_preview; p3_maxext; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NE]]);;

let P3E_HEVENT_EVNECK = prove
 (`!(hs:(A)rfs_history) hs' ev eps y len e.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\ hs_event hs' (SUC(hs_count hs)) = ev
     ==> (rfs_evolving_neck (rfs_preview hs' (SUC(hs_count hs))) eps y (rfs_horizon hs) len e <=>
          rfs_evolving_neck (p3_maxext hs (ev_omega ev) (ev_limit ev)) eps y (rfs_horizon hs)
                            len e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `rfs_preview (hs':(A)rfs_history) (SUC(hs_count (hs:(A)rfs_history)))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `TM1:real->A topology` (X_CHOOSE_THEN `R1:(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `R1:(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `AT1:real->((A->bool)#(A->real^3))->bool`
    (X_CHOOSE_THEN `G1:real->A->real^3^3` (SUBST_ALL_TAC))) THEN
  MP_TAC(ISPEC `p3_maxext (hs:(A)rfs_history) (ev_omega ev) (ev_limit ev)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `TM2:real->A topology` (X_CHOOSE_THEN `R2:(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `R2:(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `AT2:real->((A->bool)#(A->real^3))->bool`
    (X_CHOOSE_THEN `G2:real->A->real^3^3` (SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3E_EVNECK_UPTO THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `ev:(A)rfs_event`; `s:real`]
    P3E_HEVENT_AGREE) THEN
  ASM_REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P3E_HEVENT_SCALAR = prove
 (`!(hs:(A)rfs_history) hs' ev y.
     rfs_history_ok hs /\ rfs_extends hs hs' /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\ hs_event hs' (SUC(hs_count hs)) = ev /\
     open_in (hs_top hs (hs_count hs)) (ev_omega ev) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs)) (ev_omega ev)
                      (rfs_horizon hs) (hs_metric hs (hs_count hs)) (ev_limit ev) /\
     y IN ev_omega ev
     ==> rfs_vscalar (rfs_preview hs' (SUC(hs_count hs))) (rfs_horizon hs) y =
         mfd_scalar (hs_atlas hs (hs_count hs)) (ev_limit ev) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!V t (x:A). rfs_vscalar V t x = mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t) x`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vatlas; rfs_vmetric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `ev:(A)rfs_event`]
    P3E_HEVENT_PREVIEW_T) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (hs_top hs (hs_count hs))
                  (hs_atlas (hs:(A)rfs_history) (hs_count hs))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `hs_count (hs:(A)rfs_history)` o CONJUNCT1 o CONJUNCT2 o
      CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    SIMP_TAC[LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_SCALAR_RESTRICT_LOCAL THEN
  EXISTS_TAC `hs_top (hs:(A)rfs_history) (hs_count hs)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIM_RESTRICT_RIEMANNIAN THEN
  MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (hs_count hs)`; `rfs_horizon (hs:(A)rfs_history)`;
                        `hs_metric (hs:(A)rfs_history) (hs_count hs)`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* S7, assembly: p3_struct of the extended history from that                 *)
(* of the old one and the clauses of the new event (orientable new stage,   *)
(* p3_neck2_ok, rfs_surgery_ok, p3_omega_rho_ok, p3_cap_ok, pinching of the *)
(* new view).  The events k <= n transfer by the lemmas of pc_p3e_flowext;  *)
(* the old last slab stays maximal (P3E_SLAB_MAXIMAL_LAST).                 *)
(* ------------------------------------------------------------------------- *)

let P3E_SLAB_MAXIMAL_LAST = prove
 (`!hs hs':(A)rfs_history.
     rfs_history_ok hs /\ rfs_extends hs hs' /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs
     ==> (rfs_slab_maximal hs' (hs_count hs) <=> rfs_slab_maximal hs (hs_count hs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_extends]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `hs_count (hs:(A)rfs_history)` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
  REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_slab_maximal] THEN ASM_REWRITE_TAC[GSYM ADD1] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (SUC(hs_count hs)) = rfs_horizon hs`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[rfs_horizon; ADD1]; ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `B:real` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) o
    SPEC `B:real`) THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `x:A`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `hs_metric (hs':(A)rfs_history) (hs_count hs) t =
                hs_metric hs (hs_count hs) t`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM rfs_horizon] THEN ASM_REWRITE_TAC[]);;

let P3E_STRUCT_EVENT = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) hs'.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ rfs_slab_maximal hs (hs_count hs) /\
     rfs_history_ok hs' /\ rfs_extends hs hs' /\ hs_count hs' = SUC(hs_count hs) /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\
     mfd_orientable (hs_top hs' (SUC(hs_count hs))) (hs_atlas hs' (SUC(hs_count hs))) /\
     p3_neck2_ok (dl,p3_hscale hf rp dl) hs' (SUC(hs_count hs)) /\
     rfs_surgery_ok hs' C eps dl (p3_hscale hf rp dl) (SUC(hs_count hs)) /\
     p3_omega_rho_ok hs' (rp,dl) (SUC(hs_count hs)) /\
     (!i. i IN ev_index(hs_event hs' (SUC(hs_count hs)))
          ==> p3_cap_ok (md,g0,A0) (dl,p3_hscale hf rp dl) hs' (SUC(hs_count hs)) i) /\
     rfs_pinched (rfs_view hs')
     ==> p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_struct] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`] RFS_EXTENDS_INITIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_extends]) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k = SUC(hs_count (hs:(A)rfs_history))` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `k <= hs_count (hs:(A)rfs_history)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `k = SUC(hs_count (hs:(A)rfs_history))` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `k <= hs_count (hs:(A)rfs_history)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `dl:real->real`;
                   `p3_hscale hf rp dl`; `k:num`] P3E_NECK2_EXTEND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `k = SUC(hs_count (hs:(A)rfs_history))` THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `k <= hs_count (hs:(A)rfs_history)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_EXTENDS_STAGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[P3E_SURGERY_OK_EXTEND; P3E_OMEGA_RHO_EXTEND; P3E_CAP_OK_EXTEND];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k = hs_count (hs:(A)rfs_history)` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`] P3E_SLAB_MAXIMAL_LAST) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `k < hs_count (hs:(A)rfs_history)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`]
      P3E_SLAB_MAXIMAL_EXTEND) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* S7, event clauses: the clauses of the new event of the                    *)
(* extended history from the data at T: the 11.31 y-necks (evolving, length *)
(* 2, in the maximal extension; centres in Omega with R(gl) = h^-2) give     *)
(* p3_neck2_ok and the neck part of rfs_surgery_ok (P3E_EVENT_NECKS); the    *)
(* disappearing-region time t1 for the old view gives the rest of           *)
(* rfs_surgery_ok (P3E_EVENT_SURGERY_OK); Omega_rho inside the new stage     *)
(* gives p3_omega_rho_ok (P3E_EVENT_OMEGA_RHO); the raw cap parametrization *)
(* of pc_p3e_surgmetric gives p3_cap_ok (P3E_EVENT_CAP_OK).                 *)
(* ------------------------------------------------------------------------- *)

let P3E_EVENT_NECKS = prove
 (`!(hs:(A)rfs_history) hs' ev dl h.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\ hs_event hs' (SUC(hs_count hs)) = ev /\
     open_in (hs_top hs (hs_count hs)) (ev_omega ev) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs)) (ev_omega ev)
                      (rfs_horizon hs) (hs_metric hs (hs_count hs)) (ev_limit ev) /\
     (!i. i IN ev_index ev
          ==> ?y. y IN ev_omega ev /\
                  rfs_evolving_neck (p3_maxext hs (ev_omega ev) (ev_limit ev))
                                    (dl(rfs_horizon hs)) y (rfs_horizon hs) (&2) (ev_neck ev i) /\
                  mfd_scalar (hs_atlas hs (hs_count hs)) (ev_limit ev) y =
                  inv(h(rfs_horizon hs) pow 2))
     ==> p3_neck2_ok (dl,h) hs' (SUC(hs_count hs)) /\
         (!i. i IN ev_index(hs_event hs' (SUC(hs_count hs)))
              ==> ?y. rfs_strong_neck (rfs_preview hs' (SUC(hs_count hs)))
                                      (dl(hs_time hs' (SUC(hs_count hs)))) y
                                      (hs_time hs' (SUC(hs_count hs)))
                                      (ev_neck(hs_event hs' (SUC(hs_count hs))) i) /\
                      rfs_vscalar (rfs_preview hs' (SUC(hs_count hs)))
                                  (hs_time hs' (SUC(hs_count hs))) y =
                      inv(h(hs_time hs' (SUC(hs_count hs))) pow 2))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk")))))))) THEN
  REWRITE_TAC[p3_neck2_ok; rfs_strong_neck] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i. i IN ev_index ev
        ==> ?y. rfs_evolving_neck (rfs_preview (hs':(A)rfs_history) (SUC(hs_count hs)))
                                  (dl(rfs_horizon hs)) y (rfs_horizon hs) (&2) (ev_neck ev i) /\
                rfs_vscalar (rfs_preview hs' (SUC(hs_count hs))) (rfs_horizon hs) y =
                inv(h(rfs_horizon (hs:(A)rfs_history)) pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "nk" (fun th -> MP_TAC(MP (SPEC `i:num` th)
      (ASSUME `(i:num) IN ev_index (ev:(A)rfs_event)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN EXISTS_TAC `y:A` THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `ev:(A)rfs_event`;
                   `dl(rfs_horizon (hs:(A)rfs_history)):real`; `y:A`; `&2`;
                   `(ev_neck ev:num->real^3->A) i`] P3E_HEVENT_EVNECK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `ev:(A)rfs_event`; `y:A`]
      P3E_HEVENT_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN EXISTS_TAC `y:A` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3E_EVNECK_SHORTEN THEN
  EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3E_EVENT_SURGERY_OK = prove
 (`!(hs:(A)rfs_history) hs' C eps dl h.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\
     (!i. i IN ev_index(hs_event hs' (SUC(hs_count hs)))
          ==> ?y. rfs_strong_neck (rfs_preview hs' (SUC(hs_count hs)))
                                  (dl(hs_time hs' (SUC(hs_count hs)))) y
                                  (hs_time hs' (SUC(hs_count hs)))
                                  (ev_neck(hs_event hs' (SUC(hs_count hs))) i) /\
                  rfs_vscalar (rfs_preview hs' (SUC(hs_count hs)))
                              (hs_time hs' (SUC(hs_count hs))) y =
                  inv(h(hs_time hs' (SUC(hs_count hs))) pow 2)) /\
     (?t1. hs_time hs (hs_count hs) <= t1 /\ t1 < rfs_horizon hs /\
           !t x. t1 < t /\ t < rfs_horizon hs /\
                 x IN topspace(hs_top hs (hs_count hs)) DIFF
                      topspace(hs_top hs' (SUC(hs_count hs)))
                 ==> ?U. rfs_strong_canonical (rfs_view hs) C eps x t U)
     ==> rfs_surgery_ok hs' C eps dl h (SUC(hs_count hs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfs_surgery_ok; SUC_SUB1] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `hs_count (hs:(A)rfs_history)` o CONJUNCT1 o CONJUNCT2 o
    CONJUNCT2 o GEN_REWRITE_RULE I [rfs_extends]) THEN
  REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `C:real`; `eps:real`; `x:A`;
                 `t:real`] P3E_CANONICAL_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3E_EVENT_OMEGA_RHO = prove
 (`!(hs:(A)rfs_history) hs' ev rp dl.
     rfs_history_ok hs /\ rfs_extends hs hs' /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\ hs_event hs' (SUC(hs_count hs)) = ev /\
     open_in (hs_top hs (hs_count hs)) (ev_omega ev) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs)) (ev_omega ev)
                      (rfs_horizon hs) (hs_metric hs (hs_count hs)) (ev_limit ev) /\
     (!x. x IN ev_omega ev /\
          mfd_scalar (hs_atlas hs (hs_count hs)) (ev_limit ev) x <=
          inv((dl(rfs_horizon hs) * rp(rfs_horizon hs)) pow 2)
          ==> x IN topspace(hs_top hs' (SUC(hs_count hs))))
     ==> p3_omega_rho_ok hs' (rp,dl) (SUC(hs_count hs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3_omega_rho_ok] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `ev:(A)rfs_event`; `x:A`]
    P3E_HEVENT_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let P3E_EVENT_CAP_OK = prove
 (`!(hs:(A)rfs_history) hs' ev md g0 A0 dl h i Phi xi.
     rfs_extends hs hs' /\
     hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\ hs_event hs' (SUC(hs_count hs)) = ev /\
     p3e_capraw (md,g0,A0) (dl(rfs_horizon hs),h(rfs_horizon hs))
       (hs_top hs' (SUC(hs_count hs)),hs_atlas hs' (SUC(hs_count hs)),
        hs_metric hs' (SUC(hs_count hs)) (rfs_horizon hs))
       (ev_neck ev i) (ev_capm ev i)
       (rfs_pullback (restrict_atlas (hs_atlas hs (hs_count hs)) (ev_omega ev)) (ev_neck ev i)
                     (restrict_metric (hs_atlas hs (hs_count hs)) (ev_omega ev) (ev_limit ev)))
       Phi xi
     ==> p3_cap_ok (md,g0,A0) (dl,h) hs' (SUC(hs_count hs)) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3_cap_ok] THEN
  MAP_EVERY EXISTS_TAC [`Phi:real^3->A`; `xi:real^3->real^3`] THEN
  REWRITE_TAC[P3E_CAP_PARAM_RAW] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `ev:(A)rfs_event`]
    P3E_HEVENT_PREVIEW_T) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The new event p3e_newev (Omega, gl, the necks, the cap maps,              *)
(* Z, its atlas, D) and its rfs_event_ok from the cut-cap data, the retained *)
(* part (pc_p3e_retain) and the metric of Y at T (pc_p3e_surgmetric).       *)
(* ------------------------------------------------------------------------- *)

let p3e_newev = new_definition
 `p3e_newev (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (Om:B->bool)
            (gl:B->real^3^3) (J:num->bool) (e:num->real^3->B) (nw:num->bool->real^3->B)
            (D:B->bool) =
    RfsEvent Om gl J e (p3e_ccp e nw) (p3e_ccm e nw) (p3e_ctop topX J e nw)
             (p3e_catlas topX atlasX J e nw) D`;;

let P3E_NEWEV_FIELDS = prove
 (`!(topX:B topology) atlasX Om gl J e nw D.
     ev_omega (p3e_newev topX atlasX Om gl J e nw D) = Om /\
     ev_limit (p3e_newev topX atlasX Om gl J e nw D) = gl /\
     ev_index (p3e_newev topX atlasX Om gl J e nw D) = J /\
     ev_neck (p3e_newev topX atlasX Om gl J e nw D) = e /\
     ev_capp (p3e_newev topX atlasX Om gl J e nw D) = p3e_ccp e nw /\
     ev_capm (p3e_newev topX atlasX Om gl J e nw D) = p3e_ccm e nw /\
     ev_ztop (p3e_newev topX atlasX Om gl J e nw D) = p3e_ctop topX J e nw /\
     ev_zatlas (p3e_newev topX atlasX Om gl J e nw D) = p3e_catlas topX atlasX J e nw /\
     ev_disc (p3e_newev topX atlasX Om gl J e nw D) = D`,
  REWRITE_TAC[p3e_newev; ev_omega; ev_limit; ev_index; ev_neck; ev_capp; ev_capm;
              ev_ztop; ev_zatlas; ev_disc]);;

let P3E_EVENT_OK = prove
 (`!(topX:B topology) atlasX J e nw Om P gX gl ts (G':real->B->real^3^3).
     p3e_rhyp topX atlasX J e nw Om P /\
     rfs_limit_metric (topX,atlasX) Om ts gX gl /\
     rfs_same_metric_on atlasX gl
       (p3e_yatlas topX atlasX J e nw (p3e_rdisc topX J e nw Om P)) (G' ts)
       (topspace (p3e_ytop topX J e nw (p3e_rdisc topX J e nw Om P)) INTER topspace topX)
     ==> rfs_event_ok (topX,atlasX) gX ts
           (p3e_ytop topX J e nw (p3e_rdisc topX J e nw Om P),
            p3e_yatlas topX atlasX J e nw (p3e_rdisc topX J e nw Om P)) G'
           (p3e_newev topX atlasX Om gl J e nw (p3e_rdisc topX J e nw Om P))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p3e_rhyp] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP P3E_RETAIN_GENERIC th)) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_CUTCAP_FACTS) THEN
  REWRITE_TAC[rfs_event_ok; P3E_NEWEV_FIELDS] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[p3e_ytop; p3e_yatlas; p3e_ysp] THEN NO_TAC) THEN
  REWRITE_TAC[p3e_ytop; p3e_ysp; TOPSPACE_SUBTOPOLOGY] THEN
  UNDISCH_TAC `(topspace (p3e_ctop topX J e nw) DIFF p3e_rdisc topX J e nw Om P) INTER
               topspace topX = p3e_wret (topX:B topology) J e Om P` THEN
  UNDISCH_TAC `p3e_wret (topX:B topology) J e Om P SUBSET Om` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pinching and orientability of the extended history, and the main theorem  *)
(* P3E_SURGEVENT: from the data at the horizon T of hs (the event hypotheses *)
(* p3e_rhyp of the retained part, the 11.19 limit metric gl on Omega,        *)
(* Omega_rho inside P, the 11.31 y-necks, the disappearing-region time t1 on *)
(* X DIFF W, the stage Y with the metric G' T of pc_p3e_surgmetric and its   *)
(* raw cap parametrizations, and the new slab G' on [T,T') pinched) the      *)
(* extended history p3e_hevent hs Y atlasY G' T' (p3e_newev ...) extends hs  *)
(* by one event at T, ends at T', and keeps p3_struct.                       *)
(* ------------------------------------------------------------------------- *)

let P3E_HEVENT_PINCHED = prove
 (`!(hs:(A)rfs_history) topY atlasY G' T' ev.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ rfs_horizon hs < T' /\
     hausdorff_space topY /\ smooth_manifold_atlas topY atlasY /\ compact_space topY /\
     ricci_flow_from (topY,atlasY) (rfs_horizon hs) T' G' /\
     rfs_event_ok (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                  (hs_metric hs (hs_count hs)) (rfs_horizon hs) (topY,atlasY) G' ev /\
     (!t p. rfs_horizon hs <= t /\ t < T' /\ p IN topspace topY
            ==> rfs_pinched_at atlasY (G' t) t p)
     ==> rfs_pinched (rfs_view (p3e_hevent hs topY atlasY G' T' ev))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `G':real->A->real^3^3`;
                 `T':real`; `ev:(A)rfs_event`] P3E_HIST_EVENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `hs' = p3e_hevent (hs:(A)rfs_history) topY atlasY G' T' ev` THEN
  UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
  REWRITE_TAC[rfs_view; rfs_pinched] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t < rfs_horizon (hs:(A)rfs_history)` THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `t:real`] RFS_EXTENDS_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:A) IN topspace (rfs_top_at hs' t)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t < T'` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `rfs_top_at (hs':(A)rfs_history)`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `(x:A) IN topspace (rfs_top_at hs' t)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(x:A) IN topspace (rfs_top_at hs' t)` THEN
    REWRITE_TAC[rfs_top_at; rfs_live] THEN ASM_REWRITE_TAC[GSYM rfs_horizon] THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]]);;

let P3E_HEVENT_ORIENT = prove
 (`!hs':(A)rfs_history k.
     RFS_CUTCAP_SC_STATEMENT (:A) (:A) /\ rfs_history_ok hs' /\
     rfs_components_sc (hs_top hs' 0) /\ k <= hs_count hs'
     ==> mfd_orientable (hs_top hs' k) (hs_atlas hs' k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `hs':(A)rfs_history` RFS_HISTORY_SC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC P3E_ORIENTABLE_COMPONENTS THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_SIMP_TAC[]);;

let P3E_SURGEVENT = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) X atlasX J e nw Om P gl D topY atlasY G' T'.
     X = hs_top hs (hs_count hs) /\ atlasX = hs_atlas hs (hs_count hs) /\
     D = p3e_rdisc X J e nw Om P /\
     topY = p3e_ytop X J e nw D /\ atlasY = p3e_yatlas X atlasX J e nw D /\
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ rfs_slab_maximal hs (hs_count hs) /\
     RFS_CUTCAP_SC_STATEMENT (:A) (:A) /\
     p3e_rhyp X atlasX J e nw Om P /\
     rfs_limit_metric (X,atlasX) Om (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     (!x. x IN Om /\
          mfd_scalar atlasX gl x <= inv((dl(rfs_horizon hs) * rp(rfs_horizon hs)) pow 2)
          ==> x IN P) /\
     (!i. i IN J
          ==> ?y. y IN Om /\
                  rfs_evolving_neck (p3_maxext hs Om gl) (dl(rfs_horizon hs)) y
                                    (rfs_horizon hs) (&2) (e i) /\
                  mfd_scalar atlasX gl y = inv(p3_hscale hf rp dl (rfs_horizon hs) pow 2)) /\
     (?t1. hs_time hs (hs_count hs) <= t1 /\ t1 < rfs_horizon hs /\
           !t x. t1 < t /\ t < rfs_horizon hs /\ x IN topspace X DIFF p3e_wret X J e Om P
                 ==> ?U. rfs_strong_canonical (rfs_view hs) C eps x t U) /\
     hausdorff_space topY /\ smooth_manifold_atlas topY atlasY /\ compact_space topY /\
     rfs_same_metric_on atlasX gl atlasY (G' (rfs_horizon hs))
                        (topspace topY INTER topspace X) /\
     (!i. i IN J
          ==> ?Phi xi.
                p3e_capraw (md,g0,A0) (dl(rfs_horizon hs),p3_hscale hf rp dl (rfs_horizon hs))
                  (topY,atlasY,G' (rfs_horizon hs)) (e i) (p3e_ccm e nw i)
                  (rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl))
                  Phi xi) /\
     rfs_horizon hs < T' /\ ricci_flow_from (topY,atlasY) (rfs_horizon hs) T' G' /\
     (!t p. rfs_horizon hs <= t /\ t < T' /\ p IN topspace topY
            ==> rfs_pinched_at atlasY (G' t) t p)
     ==> rfs_extends hs (p3e_hevent hs topY atlasY G' T' (p3e_newev X atlasX Om gl J e nw D)) /\
         hs_count (p3e_hevent hs topY atlasY G' T' (p3e_newev X atlasX Om gl J e nw D)) =
         SUC(hs_count hs) /\
         hs_time (p3e_hevent hs topY atlasY G' T' (p3e_newev X atlasX Om gl J e nw D))
                 (SUC(hs_count hs)) = rfs_horizon hs /\
         rfs_horizon (p3e_hevent hs topY atlasY G' T' (p3e_newev X atlasX Om gl J e nw D)) = T' /\
         hs_top (p3e_hevent hs topY atlasY G' T' (p3e_newev X atlasX Om gl J e nw D))
                (SUC(hs_count hs)) = topY /\
         hs_event (p3e_hevent hs topY atlasY G' T' (p3e_newev X atlasX Om gl J e nw D))
                  (SUC(hs_count hs)) = p3e_newev X atlasX Om gl J e nw D /\
         p3_struct (C,eps,hf,md,g0,A0) (rp,dl)
                   (p3e_hevent hs topY atlasY G' T' (p3e_newev X atlasX Om gl J e nw D))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
                        is_eq(concl th) && lhs(concl th) = v)))
   [`X:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `D:A->bool`] THEN
  ABBREV_TAC `n = hs_count (hs:(A)rfs_history)` THEN
  ABBREV_TAC `ev = p3e_newev (hs_top hs n) (hs_atlas hs n) Om gl J e nw
                     (p3e_rdisc (hs_top (hs:(A)rfs_history) n) J e nw Om P)` THEN
  SUBGOAL_THEN
   `ev_omega (ev:(A)rfs_event) = Om /\ ev_limit ev = gl /\ ev_index ev = J /\
    ev_neck ev = e /\ ev_capm ev = p3e_ccm e nw`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ev" THEN REWRITE_TAC[P3E_NEWEV_FIELDS]; ALL_TAC] THEN
  (* facts from p3_struct *)
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ rfs_pinched (rfs_view hs) /\
                rfs_components_sc (hs_top hs 0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    SIMP_TAC[p3_struct];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) n) Om` ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_rhyp (hs_top (hs:(A)rfs_history) n) (hs_atlas hs n) J e nw Om P` THEN
    SIMP_TAC[p3e_rhyp];
    ALL_TAC] THEN
  (* the retained part *)
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_RETAIN_GENERIC o check (fun th ->
    is_comb(concl th) &&
    (try fst(dest_const(fst(strip_comb(concl th)))) = "p3e_rhyp" with Failure _ -> false))) THEN
  (* the new event is ok *)
  SUBGOAL_THEN
   `rfs_event_ok (hs_top hs n,hs_atlas hs n) (hs_metric hs n) (rfs_horizon hs)
                 (topY,atlasY) G' (ev:(A)rfs_event)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "ev" THEN
    MATCH_MP_TAC P3E_EVENT_OK THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_same_metric_on (hs_atlas hs n) gl atlasY (G' (rfs_horizon hs))
                   (topspace topY INTER topspace (hs_top (hs:(A)rfs_history) n))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace (topY:A topology) =
    topspace (p3e_ctop (hs_top hs n) J e nw) DIFF
    p3e_rdisc (hs_top (hs:(A)rfs_history) n) J e nw Om P`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p3e_ytop; p3e_ysp; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) &&
    (lhs(concl th) = `topY:A topology` ||
     lhs(concl th) = `atlasY:((A->bool)#(A->real^3))->bool`)))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `G':real->A->real^3^3`;
                 `T':real`; `ev:(A)rfs_event`] P3E_HIST_EVENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `G':real->A->real^3^3`;
                 `T':real`; `ev:(A)rfs_event`] P3E_HEVENT_PINCHED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `hs' = p3e_hevent (hs:(A)rfs_history) topY atlasY G' T' ev` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3E_STRUCT_EVENT THEN EXISTS_TAC `hs:(A)rfs_history` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* orientable new stage *)
    SUBGOAL_THEN `mfd_orientable (hs_top (hs':(A)rfs_history) (SUC n)) (hs_atlas hs' (SUC n))`
    MP_TAC THENL
     [MATCH_MP_TAC P3E_HEVENT_ORIENT THEN ASM_REWRITE_TAC[LE_REFL] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`] RFS_EXTENDS_INITIAL) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    (* necks of rescaled length 2 *)
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `ev:(A)rfs_event`;
                   `dl:real->real`; `p3_hscale hf rp dl`] P3E_EVENT_NECKS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    (* surgery clauses *)
    EXPAND_TAC "n" THEN MATCH_MP_TAC P3E_EVENT_SURGERY_OK THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `ev:(A)rfs_event`;
                     `dl:real->real`; `p3_hscale hf rp dl`] P3E_EVENT_NECKS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:A) IN topspace (hs_top hs n) DIFF
                    (topspace (p3e_ctop (hs_top hs n) J e nw) DIFF
                     p3e_rdisc (hs_top (hs:(A)rfs_history) n) J e nw Om P)` THEN
      UNDISCH_TAC `(topspace (p3e_ctop (hs_top hs n) J e nw) DIFF
                    p3e_rdisc (hs_top (hs:(A)rfs_history) n) J e nw Om P) INTER
                   topspace (hs_top hs n) = p3e_wret (hs_top hs n) J e Om P` THEN
      SET_TAC[]];
    (* Omega_rho retained *)
    EXPAND_TAC "n" THEN MATCH_MP_TAC P3E_EVENT_OMEGA_RHO THEN EXISTS_TAC `ev:(A)rfs_event` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `P SUBSET topspace (p3e_ctop (hs_top hs n) J e nw) DIFF
                 p3e_rdisc (hs_top (hs:(A)rfs_history) n) J e nw Om P` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* caps *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3e_capraw")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->A` (X_CHOOSE_THEN `xi:real^3->real^3`
      ASSUME_TAC)) THEN
    EXPAND_TAC "n" THEN MATCH_MP_TAC P3E_EVENT_CAP_OK THEN
    MAP_EVERY EXISTS_TAC [`ev:(A)rfs_event`; `Phi:real^3->A`; `xi:real^3->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

