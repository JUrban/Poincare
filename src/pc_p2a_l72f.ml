(* ========================================================================= *)
(* pc_p2a_l72f: FL2 (MT Lemma 7.2, existence of minimizers) for flows, from  *)
(* the single-box case (c) of pc_p2a_l72e: P2AK_FL2_FROM_FL0 (generic N: FL0 *)
(* implies FL2) and P2AK_FLOW_MIN_EXISTS_3 (N = 3, with P2AW_FLOW_VIEW_3     *)
(* of pc_p2a_wk1).  Inputs from pc_p2a_flow: P2AU_ADM_EXISTS, P2AU_L_LOWER,  *)
(* P2AU_FLOW_PROPER (FL1), P2AU_CBFLOW_FACTS.                                *)
(* ========================================================================= *)

needs "src/pc_p2a_l72e.ml";;
needs "src/pc_p2a_flow.ml";;

prioritize_real();;
type_invention_error := true;;

(* FL2 from FL0 (generic N): minimizers exist in the view of a complete     *)
(* flow with bounded curvature.  The infimum Lam of the L-lengths of         *)
(* admissible curves to q is finite (P2AU_ADM_EXISTS, P2AU_L_LOWER); a       *)
(* minimizing sequence stays in a compact set (FL1, P2AU_FLOW_PROPER); one   *)
(* box over (a,b] (FL0 regions, P2AK_BXD_EXISTS); a pointwise limit         *)
(* (P2AK_SB_LIMIT) is a minimizer to q (P2AK_SB_7_2_C).                      *)

let P2AK_FL2_FROM_FL0 = prove
 (`!(u:A->bool) (n:N->bool).
     P2A_FLOW_VIEW_STATEMENT u n ==> P2A_FLOW_MIN_EXISTS_STATEMENT u n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2A_FLOW_VIEW_STATEMENT; P2A_FLOW_MIN_EXISTS_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`; `g:real->A->real^N^N`;
                       `p:A`; `q:A`; `tau:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                                `g:real->A->real^N^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "REG") (K ALL_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^N^N)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (topspace top) a b /\ p2a_atlas_lc V /\ p2a_vtop V b = top`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "REG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; REAL_LE_REFL];
      EXPAND_TAC "V" THEN REWRITE_TAC[P2A_ATLAS_LC_FLOW_VIEW];
      EXPAND_TAC "V" THEN REWRITE_TAC[P2AU_FLOW_VIEW_PARTS; IN_REAL_INTERVAL; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* the lower bound of the lengths and an admissible curve to q *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`; `g:real->A->real^N^N`]
                P2AU_L_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`; `g:real->A->real^N^N`;
                 `p:A`; `q:A`; `tau:real`] P2AU_ADM_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gamma0:real->A` STRIP_ASSUME_TAC)] THEN
  (* the infimum *)
  ABBREV_TAC `S = {p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b gamma tau | gamma | p2a_adm V b p tau gamma /\ gamma tau = q}` THEN
  SUBGOAL_THEN `~(S:real->bool = {}) /\ (?c. !y. y IN S ==> c <= y)`
  (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b (gamma0:real->A) tau` THEN
      EXISTS_TAC `gamma0:real->A` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `--(C0 * tau * sqrt tau)` THEN X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C0:real`)) (concl th))) THEN
      EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Lam = inf(S:real->bool)` THEN
  MP_TAC(ISPEC `S:real->bool` INF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "INF1") (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `!gamma':real->A. p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b p tau gamma' /\ gamma' tau = q
                     ==> Lam <= p2a_L_length V b gamma' tau`
  (LABEL_TAC "LE") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "INF1" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `gamma':real->A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?gamma:real->A. p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b p tau gamma /\ gamma tau = q /\
                        p2a_L_length V b gamma tau < Lam + inv(&n + &1)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`S:real->bool`; `Lam + inv(&n + &1)`] INF_APPROACH) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_LT_ADDR; REAL_LT_INV_EQ] THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `gs:num->real->A` (LABEL_TAC "GS")) THEN
  (* the compact set (FL1) *)
  MP_TAC(ISPECL [`u:A->bool`; `n:N->bool`] P2AU_FLOW_PROPER) THEN
  REWRITE_TAC[P2A_FLOW_PROPER_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                             `g:real->A->real^N^N`; `p:A`; `abs Lam + &1`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CMP"))) THEN
  SUBGOAL_THEN
   `!n. p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b p tau ((gs:num->real->A) n) /\
        p2a_L_length V b (gs n) tau <= abs Lam + &1 /\
        (!s. &0 <= s /\ s <= tau ==> gs n s IN C) /\ gs n tau = q /\
        p2a_L_length V b (gs n) tau < Lam + inv(&n + &1)`
  (LABEL_TAC "GS2") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "GS" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b ((gs:num->real->A) n) tau <= abs Lam + &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lam + inv(&n + &1)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> Lam + x <= abs Lam + &1`) THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "CMP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* one box over (a,b] *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `topspace top:A->bool`; `a:real`; `b:real`; `C:A->bool`; `tau:real`]
                P2AK_BXD_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]];
    DISCH_THEN(X_CHOOSE_THEN `Fs:A->bool` (X_CHOOSE_THEN `R:A->real` (X_CHOOSE_THEN `r:real`
      (X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Gm:real` (X_CHOOSE_TAC `Rm:real`))))))] THEN
  (* the pointwise limit *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `topspace top:A->bool`; `a:real`; `C:A->bool`; `tau:real`;
                 `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                 `b:real`; `p:A`; `tau:real`; `gs:num->real->A`; `abs Lam + &1`]
                P2AK_SB_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN USE_THEN "GS2" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    ASM_SIMP_TAC[P2AX_ADM_IMP];
    DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC))] THEN
  (* the limit datum and case (c) *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `topspace top:A->bool`; `a:real`; `C:A->bool`; `tau:real`;
                 `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                 `b:real`; `p:A`; `tau:real`; `gs:num->real->A`; `abs Lam + &1`; `q:A`;
                 `sub:num->num`; `gamma:real->A`; `Lam:real`] P2AK_SB_7_2_C) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p2ak_lim] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      X_GEN_TAC `k:num` THEN USE_THEN "LE" MATCH_MP_TAC THEN
      USE_THEN "GS2" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) k`) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `eta:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      USE_THEN "GS2" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) k`) THEN
      SUBGOAL_THEN `inv(&((sub:num->num) k) + &1) <= inv(&N)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN
        SUBGOAL_THEN `k <= (sub:num->num) k` MP_TAC THENL
         [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN ANTS_TAC THENL
           [UNDISCH_TAC `p3_subseq (sub:num->num)` THEN REWRITE_TAC[p3_subseq]; SIMP_TAC[]];
          ALL_TAC] THEN
        UNDISCH_TAC `N <= k:num` THEN UNDISCH_TAC `~(N = 0)` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
        MP_TAC(SPEC `N:num` REAL_POS) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]);;

(* FL2 at N = 3 (FL0 at N = 3 is P2AW_FLOW_VIEW_3 of pc_p2a_wk1).            *)

let P2AK_FLOW_MIN_EXISTS_3 = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_MIN_EXISTS_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2AK_FL2_FROM_FL0 THEN REWRITE_TAC[P2AW_FLOW_VIEW_3]);;

