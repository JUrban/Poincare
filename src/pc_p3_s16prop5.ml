(* ========================================================================= *)
(* Unit pc_p3_s16prop5 (Part 3 proofs; Ch 16, fifth unit): MT Lemma 16.8 and *)
(* Prop 16.5 in the form with the cutoff tc.  The persistence time Tf of the *)
(* core ball, closeness below a level, the base change and window runs       *)
(* (P3N_RUN), the closed end at tc (P3N_CLOSE_END), the per-history case     *)
(* analysis (P3N_FINAL_ONE) and the discard along sequences                  *)
(* (P3N_DISCARD_SEQ, P3N_FINISH), the endpoint and top cases (P3N_ENDPT,     *)
(* P3N_TOP), the extension step (P3N_EXTEND), Lemma 16.8 in sequence form    *)
(* (P3N_SEQ_CONCL) and Prop 16.5 (P3N_PROP_16_5_TC).                         *)
(* ========================================================================= *)

needs "src/pc_p3_s16lim.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The persistence time of the core ball with the cutoff tc                  *)
(* (p3n_tf: capped at th and at the normalized cutoff (tc - ts) Q), the     *)
(* closeness of the cap sequence along D to a standard flow G below a level *)
(* (p3n_close_below: in every order, on compacts, on [0,b] for b < tl or at *)
(* b = 0), and the level-0 case from the cap closeness (P3N_CLOSE_BELOW_0). *)
(* ========================================================================= *)

let p3n_tf = new_definition
 `p3n_tf (g0:real^3->real^3^3) (hs:num->(A)rfs_history) Phi ts Q (tc:num->real) ms th =
    \n. p3n_ptime g0 (hs n) (Phi n) (ts n) (Q n) (&ms) (min th ((tc n - ts n) * Q n))`;;

let p3n_close_below = new_definition
 `p3n_close_below (g0:real^3->real^3^3) (hs:num->(A)rfs_history) Phi ts Q (D:num->num) tl
                  (G:real->real^3->real^3^3) <=>
    !b K m e. &0 <= b /\ (b < tl \/ b = &0) /\ compact K /\ &0 < e
              ==> ?N. !j s y. N <= j /\ &0 <= s /\ s <= b /\ y IN K
                              ==> lck_dist2 m (G s)
                                    (p3n_cfl (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j)) s) y
                                  < e`;;

let P3N_COMPACT_DIST_BOUND = prove
 (`!g0 A0 K. p3_std_initial g0 A0 /\ compact K
             ==> ?R. &1 <= R /\ !y:real^3. y IN K ==> p3_std_dist g0 y < R`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max (&1) (p3s_rad_rho g0 B + &1)` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`; `B:real`] P3S_RHO_LT_EQ) THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p3s_rad_rho g0 (norm(y:real^3)) <= p3s_rad_rho g0 B` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC]);;

let P3N_SEQ_FIELD0 = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
     p3_std_initial g0 A0
     ==> !R. ?N. !n. N <= n
                     ==> ?U. {x | p3_std_dist g0 x < R} SUBSET U /\ metric_field U g0 /\
                             metric_field U (p3n_cfl (hs n) (Phi n) (ts n) (Q n) (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `R:real` THEN
  MP_TAC(SPEC `R:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) n`; `(k:num->num) n`] P3N_VIEW_AT_EVENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ABBREV_TAC `U = {x:real^3 | --(inv((dl:num->real->real) n (ts n))) <
                               A0 + &4 - p3_std_dist g0 x}` THEN
  EXISTS_TAC `U:real^3->bool` THEN
  SUBGOAL_THEN `mfd_param (hs_top ((hs:num->(A)rfs_history) n) (k n)) (hs_atlas (hs n) (k n))
                  U ((Phi:num->real^3->A) n)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_cap_param (md,g0,A0) (dl n,p3_hscale hf (rp n) (dl n))
                   ((hs:num->(A)rfs_history) n) (k n) (i n) (Phi n) (xi n)` THEN
    REWRITE_TAC[p3_cap_param] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top ((hs:num->(A)rfs_history) n) (k n)`;
                 `hs_atlas ((hs:num->(A)rfs_history) n) (k n)`;
                 `U:real^3->bool`; `(Phi:num->real^3->A) n`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `R <= inv((dl:num->real->real) n ((ts:num->real) n))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n + &1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N2` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP P3S_A0_POS (ASSUME `p3_std_initial g0 A0`)) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_OSA_RIEM THEN
    ASM_MESON_TAC[p3_std_initial];
    MATCH_MP_TAC P3N_CFL_FIELD THEN ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID]]);;

let P3N_CLOSE_BELOW_0 = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc (D:num->num) G.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
     p3_modulus md /\ p3_std_initial g0 A0 /\ (!m n. m < n ==> D m < D n) /\
     p3_std_flow g0 (&1) G
     ==> p3n_close_below g0 hs Phi ts Q D (&0) G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3n_close_below] THEN
  MAP_EVERY X_GEN_TAC [`b:real`; `K:real^3->bool`; `m:num`; `e:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `b = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(G:real->real^3->real^3^3) (&0) = g0` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_std_flow; p3_partial_std]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `K:real^3->bool`] P3N_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `R1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `dd = min (min e (&1 / &2)) (min (inv(R1 + &1)) (inv(&m + &2)))` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= e /\ dd <= &1 / &2 /\ R1 < inv dd /\ dd < inv(&m + &1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(R1 + &1) /\ &0 < inv(&m + &2) /\ inv(&m + &2) < inv(&m + &1)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV2 THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < dd /\ dd <= e /\ dd <= &1 / &2 /\ dd <= inv(R1 + &1) /\
                  dd <= inv(&m + &2)`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "dd" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `R1 + &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`] P3N_SEQ_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "cap")) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`] P3N_SEQ_FIELD0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "fld") o SPEC `R1:real`) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `N1 + N2 <= (D:num->num) j` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "fld" (MP_TAC o SPEC `(D:num->num) j`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `{x:real^3 | p3_std_dist g0 x < R1} SUBSET U` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg dd) g0
                (p3n_cfl ((hs:num->(A)rfs_history) ((D:num->num) j)) ((Phi:num->real^3->A) (D j))
                         ((ts:num->real) (D j)) ((Q:num->real) (D j)) (&0)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P3S_KREG_GE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `dd pow 2` THEN CONJ_TAC THENL
     [USE_THEN "cap" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `R1:real` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dd * &1` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]]]);;

(* ========================================================================= *)
(* Change of base metric in the lck closeness (P3N_BASE_CHANGE).             *)
(* If fields Hs i tend to M = G(T) in every C^m (base M) near a compact K,  *)
(* and times s i tend to T for a Ricci flow G from 0 on R^N, then Hs i tend *)
(* to G(s i) in every C^k with the moving base G(s i) (P2CM_LCK_NEAR2 with  *)
(* P3N_RF_MNEAR; jets of Hs i from P2CJ_JB_FROM_LCK, C^0 by P3N_LCK_ENTRY). *)
(* ========================================================================= *)

let P3N_NUM_OF_REAL = prove
 (`!i:num. (@j:num. &j = &i) = i`,
  GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[REAL_OF_NUM_EQ]);;

let P3N_IN_NUMSET = prove
 (`!N i. &i IN {&j | N <= j} <=> N <= i`,
  REWRITE_TAC[IN_ELIM_THM; REAL_OF_NUM_EQ] THEN MESON_TAC[]);;

let P3N_HS_NEAR = prove
 (`!V K' (M:real^N->real^N^N) (Hs:num->real^N->real^N^N) z0 r.
     open V /\ compact K' /\ K' SUBSET V /\ &0 < r /\ ball(z0,r) SUBSET K' /\
     metric_field V M /\ (!i. metric_field V (Hs i)) /\
     (!m e. &0 < e ==> ?N. !i y. N <= i /\ y IN K' ==> lck_dist2 m M (Hs i) y < e)
     ==> p2ci_near z0 (\i. vectorize o Hs i) (vectorize o M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ci_near] THEN EXISTS_TAC `r:real` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball(z0:real^N,r) SUBSET V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `0` THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[metric_field];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[metric_field];
    X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `&1`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
    REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MP_TAC(ISPECL [`{&i | N <= i}`; `V:real^N->bool`; `K':real^N->bool`; `M:real^N->real^N^N`;
                   `\t:real. (Hs:num->real^N->real^N^N) (@j:num. &j = t)`; `m:num`; `&1`]
                  P2CJ_JB_FROM_LCK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[P3N_NUM_OF_REAL] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\i:num. N <= i`; `V:real^N->bool`; `K':real^N->bool`; `m:num`;
                   `Hs:num->real^N->real^N^N`] P3N_VEC_JET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `q:num`]) THEN ASM_REWRITE_TAC[rfa_jb] THEN
      DISCH_THEN(X_CHOOSE_TAC `C:real` o CONJUNCT2) THEN EXISTS_TAC `C:real` THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`&i:real`; `l:num list`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[P3N_NUM_OF_REAL; P3N_IN_NUMSET];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
    EXISTS_TAC `&(CARD(pde_index_lists m (:N))) * C` THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC SUM_BOUND THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `l:num list`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?L. &0 <= L /\ !y p. y IN K' /\ 1 <= p /\ p <= dimindex(:N)
                                       ==> (M:real^N->real^N^N) y$p$p <= L`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `!p. ?C. 1 <= p /\ p <= dimindex(:N)
                            ==> !y. y IN K' ==> (M:real^N->real^N^N) y$p$p <= C`
      MP_TAC THENL
       [X_GEN_TAC `p:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`{&0}`; `V:real^N->bool`; `K':real^N->bool`; `0`;
                       `\z. (M:real^N->real^N^N) z$p$p`] P3S_JB_FIXED) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_SMOOTH_G_ENTRY THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[rfa_jb] THEN
        DISCH_THEN(X_CHOOSE_TAC `C:real` o CONJUNCT2) THEN EXISTS_TAC `C:real` THEN
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `[]:num list`; `y:real^N`]) THEN
        ASM_REWRITE_TAC[IN_SING; pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_0;
                        iterated_partial; LIFT_DROP] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Cp:num->real`) THEN
      EXISTS_TAC `sum(1..dimindex(:N)) (\p. abs((Cp:num->real) p))` THEN
      SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_ABS_POS] THEN
      MAP_EVERY X_GEN_TAC [`y:real^N`; `p:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Cp:num->real) p)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= abs c`) THEN ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`\p. abs((Cp:num->real) p)`;
                       `sum(1..dimindex(:N)) (\p. abs((Cp:num->real) p))`;
                       `1..dimindex(:N)`] SUM_POS_BOUND) THEN
        REWRITE_TAC[FINITE_NUMSEG; REAL_ABS_POS; REAL_LE_REFL] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]];
      ALL_TAC] THEN
    ABBREV_TAC `e1 = e / (&2 * &(dimindex(:N) * dimindex(:N)))` THEN
    SUBGOAL_THEN `&0 < e1` ASSUME_TAC THENL
     [EXPAND_TAC "e1" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      SIMP_TAC[LT_MULT; DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`; ARITH];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `e1 pow 2 / (&2 * (L pow 2 + &1))`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      MP_TAC(SPEC `L:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN K' /\ y IN V` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&(dimindex(:N) * dimindex(:N)) * e1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3N_VEC_C0 THEN MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC P3N_C0_ARITH THEN
      MAP_EVERY EXISTS_TAC [`(M:real^N->real^N^N) y$p$p`; `(M:real^N->real^N^N) y$q$q`;
                            `L:real`; `e1 pow 2 / (&2 * (L pow 2 + &1))`;
                            `lck_dist2 0 (M:real^N->real^N^N) ((Hs:num->real^N->real^N^N) i) y`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC P3N_LCK_ENTRY THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2C_LCK_DIST2_POS THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P3N_MF_DIAG_POS THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P3N_MF_DIAG_POS THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `&0 < L pow 2 + &1` ASSUME_TAC THENL
         [MP_TAC(SPEC `L:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `e1 pow 2 / (&2 * (L pow 2 + &1)) * (L pow 2 + &1) = e1 pow 2 / &2`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < L pow 2 + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &2 < x`) THEN ASM_SIMP_TAC[REAL_POW_LT];
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `~(&(dimindex(:N) * dimindex(:N)) = &0)` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ; MULT_EQ_0] THEN
        SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> ~(n = 0)`];
        ALL_TAC] THEN
      EXPAND_TAC "e1" THEN
      SUBGOAL_THEN `&(dimindex(:N) * dimindex(:N)) * e / (&2 * &(dimindex(:N) * dimindex(:N))) =
                    e / &2` SUBST1_TAC THENL
       [UNDISCH_TAC `~(&(dimindex(:N) * dimindex(:N)) = &0)` THEN CONV_TAC REAL_FIELD;
        UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]]]);;

let P3N_BASE_CHANGE = prove
 (`!V K K' (Hs:num->real^3->real^3^3) T0 (G:real->real^3->real^3^3) tb (s:num->real).
     open V /\ compact K /\ compact K' /\ K SUBSET K' /\ K' SUBSET V /\
     (!z. z IN K ==> ?r. &0 < r /\ ball(z,r) SUBSET K') /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) T0 G /\ &0 <= tb /\ tb < T0 /\
     (!i. &0 <= s i /\ s i < T0) /\ (!e. &0 < e ==> ?N. !i. N <= i ==> abs(s i - tb) < e) /\
     (!i. metric_field V (Hs i)) /\
     (!m e. &0 < e ==> ?N. !i y. N <= i /\ y IN K' ==> lck_dist2 m (G tb) (Hs i) y < e)
     ==> !k e. &0 < e ==> ?N. !i y. N <= i /\ y IN K ==> lck_dist2 k (G (s i)) (Hs i) y < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`k:num`; `e:real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:real^3->bool`;
                 `\i:num y:real^3. lift(lck_dist2 k ((G:real->real^3->real^3^3) ((s:num->real) i))
                                     ((Hs:num->real^3->real^3^3) i) y)`;
                 `\y:real^3. vec 0:real^1`] P2CI_NEAR_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2CM_LCK_NEAR2 THEN EXISTS_TAC `(G:real->real^3->real^3^3) tb` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`T0:real`; `G:real->real^3->real^3^3`; `tb:real`; `s:num->real`;
                     `z:real^3`] P3N_RF_MNEAR) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX];
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC P3N_HS_NEAR THEN
      MAP_EVERY EXISTS_TAC [`V:real^3->bool`; `K':real^3->bool`; `r:real`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN
      EXISTS_TAC `T0:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `y:real^3`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
  REMOVE_THEN "N" (MP_TAC o SPECL [`i:num`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; NORM_LIFT]);;

(* ========================================================================= *)
(* Tools for the window runs of Lemma 16.8.  The moving                      *)
(* bases tl - tl/(n+2) (P3N_BB_FACTS, P3N_BB_LIM); unit balls around a     *)
(* closed ball                                                              *)
(* (P3N_CBALL_BALLS); metric fields of the rescaled coordinate flows while   *)
(* a ball persists (P3N_CFL_FIELD_P); C^0 closeness at the bases from lck   *)
(* closeness with the moving base (P3N_BASE_C0E); the diagonal subsequence  *)
(* of a closeness below a level (P3N_DIAG_CLOSE); and the uniform change of *)
(* base metric near a time (P3N_BASE_UNIF, from P3N_BASE_CHANGE).           *)
(* ========================================================================= *)

let P3N_BB_FACTS = prove
 (`!tl i. &0 <= tl
          ==> &0 <= tl - tl / (&i + &2) /\ tl - tl / (&i + &2) <= tl /\
              (tl - tl / (&i + &2) < tl \/ tl - tl / (&i + &2) = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `tl = &0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_SUB_REFL; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tl / (&i + &2) /\ tl / (&i + &2) <= tl` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &i + &2`] THEN
      MP_TAC(SPECL [`tl:real`; `&i`] REAL_LE_MUL) THEN ASM_REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let P3N_BB_LIM = prove
 (`!tl e. &0 <= tl /\ &0 < e
          ==> ?N. !i. N <= i ==> abs((tl - tl / (&i + &2)) - tl) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `tl / e` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `(a - b) - a = --b`; REAL_ABS_NEG] THEN
  SUBGOAL_THEN `&0 < &i + &2` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_ABS_REFL;
               REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `tl <= e * &N` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `tl / e <= &N` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e * &N <= e * &i` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3N_CBALL_BALLS = prove
 (`!R (z:real^N). z IN cball(vec 0,R) ==> ball(z,&1) SUBSET cball(vec 0,R + &1)`,
  REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL_0; dist] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `z:real^N`] NORM_TRIANGLE_SUB) THEN
  MP_TAC(ISPECL [`z:real^N`; `x:real^N`] NORM_SUB) THEN ASM_REAL_ARITH_TAC);;

let P3N_CFL_FIELD_P = prove
 (`!(hs:num->(A)rfs_history) Phi ts Q g0 (sg:num->num) m n s.
     p2cv_hyp (\n. rfs_view (hs (sg n))) (\n. Phi (sg n) (vec 0)) (\n. ts (sg n))
              (\n. Q (sg n)) {&0} (euclidean,open_set_atlas (:real^3)) g0 (vec 0)
              (\m. {x | p3_std_dist g0 x < &m + &1}) (\n. Phi (sg n)) /\
     m <= n /\ &0 <= s /\
     rfs_persists (rfs_view (hs (sg n)))
                  (IMAGE (Phi (sg n)) {x | p3_std_dist g0 x < &m + &1})
                  (ts (sg n)) (ts (sg n) + s / Q (sg n))
     ==> metric_field {x | p3_std_dist g0 x < &m + &1}
                      (p3n_cfl (hs (sg n)) (Phi (sg n)) (ts (sg n)) (Q (sg n)) s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o BETA_RULE o MATCH_MP P2CV_HYP_ONE o C CONJ (ASSUME `m:num <= n`)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) ((sg:num->num) n))`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `{x:real^3 | p3_std_dist g0 x < &m + &1}`; `(Phi:num->real^3->A) ((sg:num->num) n)`;
                 `(ts:num->real) ((sg:num->num) n)`; `(Q:num->real) ((sg:num->num) n)`; `&0`;
                 `s:real`; `s:real`;
                 `((:real^3),(\x:real^3. x))`] P2CV_P_FIELD_AT) THEN
  ASM_REWRITE_TAC[P3N_OSA_IN; P3N_OSA_CHART_IMAGE; P3N_CFL_LOCAL; REAL_LE_REFL;
                  P2CV_DIV_LZERO; REAL_ADD_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P3N_BASE_C0E = prove
 (`!T0 (G:real->real^N->real^N^N) tl V Kc (bb:num->real) (Hs:num->real^N->real^N^N).
     ricci_flow_from (euclidean,open_set_atlas (:real^N)) (&0) T0 G /\ tl < T0 /\
     compact Kc /\ open V /\ Kc SUBSET V /\
     (!i. &0 <= bb i /\ bb i <= tl) /\
     (!e. &0 < e ==> ?N. !i. N <= i ==> abs(bb i - tl) < e) /\
     (?N0. !i. N0 <= i ==> metric_field V (Hs i)) /\
     (!e. &0 < e ==> ?N. !i y. N <= i /\ y IN Kc ==> lck_dist2 0 (G (bb i)) (Hs i) y < e)
     ==> !ep. &0 < ep
              ==> ?N. !i y p q. N <= i /\ y IN Kc /\
                                1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                                ==> abs(Hs i y$p$q - G tl y$p$q) < ep`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "bbc")
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N0:num` (LABEL_TAC "mf")) (LABEL_TAC "lck"))))))))) THEN
  X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= tl` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `bb:num->real`)) (concl th) &&
      not (is_imp(snd(strip_forall(concl th)))))) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`T0:real`; `G:real->real^N->real^N^N`; `&0`; `tl:real`; `Kc:real^N->bool`]
         P3N_RF_UC) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `B:real` (LABEL_TAC "B"))
    (MP_TAC o SPEC `ep / &2`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  USE_THEN "bbc" (MP_TAC o SPEC `mu:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  SUBGOAL_THEN `&0 < B pow 2 + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `B:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "lck" (MP_TAC o SPEC `(ep / &2) pow 2 / (B pow 2 + &1)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `MAX N0 (MAX N1 N2)` THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`; `p:num`; `q:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field V ((Hs:num->real^N->real^N^N) i)` ASSUME_TAC THENL
   [USE_THEN "mf" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((bb:num->real) i - tl) < mu /\
                lck_dist2 0 ((G:real->real^N->real^N^N) (bb i)) ((Hs:num->real^N->real^N^N) i) y
                < (ep / &2) pow 2 / (B pow 2 + &1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "N1" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (bb:num->real) i /\ bb i <= tl` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field V ((G:real->real^N->real^N^N) ((bb:num->real) i))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN
    EXISTS_TAC `T0:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!h g1 g2 ep. abs(h - g1) < ep / &2 /\ abs(g1 - g2) < ep / &2 ==> abs(h - g2) < ep`) THEN
  EXISTS_TAC `(G:real->real^N->real^N^N) ((bb:num->real) i) y$p$q` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3N_C0_ARITH THEN
    MAP_EVERY EXISTS_TAC [`(G:real->real^N->real^N^N) ((bb:num->real) i) y$p$p`;
                          `(G:real->real^N->real^N^N) ((bb:num->real) i) y$q$q`; `B:real`;
                          `lck_dist2 0 ((G:real->real^N->real^N^N) ((bb:num->real) i))
                                       ((Hs:num->real^N->real^N^N) i) y`;
                          `lck_dist2 0 ((G:real->real^N->real^N^N) ((bb:num->real) i))
                                       ((Hs:num->real^N->real^N^N) i) y`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3N_LCK_ENTRY THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_LCK_DIST2_POS THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC P3N_MF_DIAG_POS THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `abs x <= B ==> x <= B`) THEN USE_THEN "B" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3N_MF_DIAG_POS THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `abs x <= B ==> x <= B`) THEN USE_THEN "B" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `lck_dist2 0 ((G:real->real^N->real^N^N) ((bb:num->real) i))
                     ((Hs:num->real^N->real^N^N) i) y < (ep / &2) pow 2 / (B pow 2 + &1)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
      ASM_REAL_ARITH_TAC];
    USE_THEN "uc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

let P3N_DIAG_CLOSE = prove
 (`!g0 (hs:num->(A)rfs_history) Phi ts Q (D:num->num) tl (G:real->real^3->real^3^3)
    (e:num->real).
     p3n_close_below g0 hs Phi ts Q D tl G /\ &0 <= tl /\
     (!b. &0 <= b /\ (b < tl \/ b = &0) ==> ?N. !j. N <= j ==> b < e (D j))
     ==> ?J:num->num. (!m n. m < n ==> J m < J n) /\
             (!n. tl - tl / (&n + &2) < e (D (J n))) /\
             !K kk ep. compact K /\ &0 < ep
                       ==> ?N. !n s y. N <= n /\ &0 <= s /\ s <= tl - tl / (&n + &2) /\
                                       y IN K
                                       ==> lck_dist2 kk (G s)
                                             (p3n_cfl (hs (D (J n))) (Phi (D (J n)))
                                                      (ts (D (J n))) (Q (D (J n))) s) y < ep`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eb"))) THEN
  SUBGOAL_THEN
   `!i. ?N. !j. N <= j
           ==> tl - tl / (&i + &2) < (e:num->real) ((D:num->num) j) /\
               !kk s y. kk <= i /\ &0 <= s /\ s <= tl - tl / (&i + &2) /\
                        y IN cball(vec 0:real^3,&i)
                        ==> lck_dist2 kk ((G:real->real^3->real^3^3) s)
                              (p3n_cfl ((hs:num->(A)rfs_history) (D j)) (Phi (D j))
                                       (ts (D j)) (Q (D j)) s) y < inv(&i + &1)`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(SPECL [`tl:real`; `i:num`] P3N_BB_FACTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    USE_THEN "eb" (MP_TAC o SPEC `tl - tl / (&i + &2)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    MP_TAC(ISPEC `\kk j. !s y. &0 <= s /\ s <= tl - tl / (&i + &2) /\
                               y IN cball(vec 0:real^3,&i)
                               ==> lck_dist2 kk ((G:real->real^3->real^3^3) s)
                                     (p3n_cfl ((hs:num->(A)rfs_history) ((D:num->num) j))
                                              (Phi (D j)) (ts (D j)) (Q (D j)) s) y
                                   < inv(&i + &1)` P3N_EVENT_FIN) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `kk:num` THEN
      UNDISCH_TAC `p3n_close_below g0 (hs:num->(A)rfs_history) Phi ts Q (D:num->num) tl
                     (G:real->real^3->real^3^3)` THEN
      REWRITE_TAC[p3n_close_below] THEN
      DISCH_THEN(MP_TAC o SPECL [`tl - tl / (&i + &2)`; `cball(vec 0:real^3,&i)`; `kk:num`;
                                 `inv(&i + &1)`]) THEN
      ASM_REWRITE_TAC[COMPACT_CBALL; REAL_LT_INV_EQ; REAL_ARITH `&0 < &i + &1`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num` o SPEC `i:num`) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`kk:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `kk:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP P3N_DIAG_SEQ) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `J:num->num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "P")) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "P" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:real^3->bool`; `kk:num`; `ep:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `ep:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N0 + N1 + kk:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN CONJ_TAC THENL
   [USE_THEN "P" (MP_TAC o CONJUNCT2 o SPEC `n:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_CBALL_0] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N1` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N0)` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

let P3N_BASE_UNIF = prove
 (`!V K K' T0 (G:real->real^3->real^3^3) tb.
     open V /\ compact K /\ compact K' /\ K SUBSET K' /\ K' SUBSET V /\
     (!z. z IN K ==> ?r. &0 < r /\ ball(z,r) SUBSET K') /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) T0 G /\ &0 <= tb /\ tb < T0
     ==> !k ep. &0 < ep
                ==> ?mu kk dd. &0 < mu /\ &0 < dd /\
                      !s (H:real^3->real^3^3).
                        &0 <= s /\ s < T0 /\ abs(s - tb) < mu /\ metric_field V H /\
                        (!y. y IN K' ==> lck_dist2 kk (G tb) H y < dd)
                        ==> !y. y IN K ==> lck_dist2 k (G s) H y < ep`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`k:num`; `ep:real`] THEN
  DISCH_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!i. ?s (H:real^3->real^3^3) y.
          &0 <= s /\ s < T0 /\ abs(s - tb) < inv(&i + &1) /\ metric_field V H /\
          (!y'. y' IN K' ==> lck_dist2 i ((G:real->real^3->real^3^3) tb) H y' < inv(&i + &1)) /\
          y IN K /\ ~(lck_dist2 k (G s) H y < ep)`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`inv(&i + &1)`; `i:num`; `inv(&i + &1)`]) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &i + &1`] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `H:real^3->real^3^3`
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`s:real`; `H:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ss:num->real` (X_CHOOSE_THEN `Hs:num->real^3->real^3^3`
    (X_CHOOSE_THEN `ys:num->real^3` (LABEL_TAC "bad")))) THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `K:real^3->bool`; `K':real^3->bool`;
                 `Hs:num->real^3->real^3^3`; `T0:real`; `G:real->real^3->real^3^3`; `tb:real`;
                 `ss:num->real`] P3N_BASE_CHANGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&i + &1)` THEN
      CONJ_TAC THENL [USE_THEN "bad" (fun th -> SIMP_TAC[th]); ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`mm:num`; `e:real`] THEN DISCH_TAC THEN
      MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N + mm:num` THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `y:real^3`] THEN STRIP_TAC THEN
      USE_THEN "bad" (MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `lck_dist2 i ((G:real->real^3->real^3^3) tb) ((Hs:num->real^3->real^3^3) i) y` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `V:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
        MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN
        EXISTS_TAC `T0:real` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&i + &1)` THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `ep:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPECL [`N:num`; `(ys:num->real^3) N`])) THEN
  USE_THEN "bad" (STRIP_ASSUME_TAC o SPEC `N:num`) THEN ASM_REWRITE_TAC[LE_REFL]);;

(* ========================================================================= *)
(* Window runs along the cap sequence.  P3N_RUN_WINDOW is                    *)
(* P3N_WINDOW for the rescaled coordinate flows of a subsequence sg (bases  *)
(* b n with C^0 closeness to a fixed model M on K', curvature and           *)
(* persistence of the ball m + 2 before e n).  P3N_RUN combines it with the *)
(* diagonal closeness below a level tl (P3N_DIAG_CLOSE) and the uniform     *)
(* change of base metric (P3N_BASE_UNIF): along a further subsequence the   *)
(* flows are close to G(s) itself on [0, min(e, tl + lam)).                 *)
(* ========================================================================= *)

let P3N_RUN_WINDOW = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> !C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc
          (sg:num->num) (b:num->real) (e:num->real) (M:real^3->real^3^3) m K K'.
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
           &0 < eps /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           (!m n. m < n ==> sg m < sg n) /\ (!n. &0 <= b n /\ e n <= &1) /\
           metric_field (:real^3) M /\
           (?CM N. !n. N <= n
                  ==> p3n_gat g0 (hs (sg n)) (Phi (sg n)) (ts (sg n)) (Q (sg n)) (e n) CM
                              (m + 2) (&1)) /\
           compact K /\ compact K' /\ K SUBSET K' /\
           K' SUBSET {x | p3_std_dist g0 x < &m + &1} /\
           (!z. z IN K ==> ?r. &0 < r /\ ball(z,r) SUBSET K') /\
           (!ep. &0 < ep
                 ==> ?N. !n y p q. N <= n /\ y IN K' /\ 1 <= p /\ p <= 3 /\ 1 <= q /\ q <= 3
                                   ==> abs(p3n_cfl (hs (sg n)) (Phi (sg n)) (ts (sg n))
                                                   (Q (sg n)) (b n) y$p$q - M y$p$q) < ep)
           ==> !kk dd. &0 < dd
                 ==> ?lam N. &0 < lam /\
                       !n s y. N <= n /\ b n <= s /\ s < e n /\ s < b n + lam /\ y IN K
                               ==> lck_dist2 kk M
                                     (p3n_cfl (hs (sg n)) (Phi (sg n)) (ts (sg n)) (Q (sg n)) s) y
                                   < dd`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `CM:real` (X_CHOOSE_THEN `N1:num` (LABEL_TAC "g2")))
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))))))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`kk:num`; `dd:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. &0 < (Q:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                   `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                   `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`;
                   `Q:num->real`; `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2cv_hyp (\n. rfs_view ((hs:num->(A)rfs_history) ((sg:num->num) n)))
             (\n. (Phi:num->real^3->A) (sg n) (vec 0))
             (\n. (ts:num->real) (sg n)) (\n. (Q:num->real) (sg n)) {&0}
             (euclidean,open_set_atlas (:real^3)) g0 (vec 0)
             (\m. {x | p3_std_dist g0 x < &m + &1}) (\n. Phi (sg n))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P3N_SEQ_HYP) THEN
    DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
      `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
      `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`;
      `sg:num->num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) ((sg:num->num) n))`;
                 `\n. (Phi:num->real^3->A) ((sg:num->num) n) (vec 0)`;
                 `\n. (ts:num->real) ((sg:num->num) n)`; `\n. (Q:num->real) ((sg:num->num) n)`;
                 `{&0:real}`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `vec 0:real^3`;
                 `\m:num. {x:real^3 | p3_std_dist g0 x < &m + &1}`;
                 `\n. (Phi:num->real^3->A) ((sg:num->num) n)`;
                 `{x:real^3 | p3_std_dist g0 x <= &(m + 2) + &1}`] P2CV_QF_TIME0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&(m + 2) + &1`] P3N_STD_SUBLEVEL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "qf") o
             REWRITE_RULE[P2CV_P_PB; GSYM P3N_CFL_PB]) THEN
  SUBGOAL_THEN `&0 <= max CM (&0) /\ m + 2 <= N1 + N2 + m + 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s. N1 + N2 + m + 2 <= n /\ &0 <= s /\ s < (e:num->real) n
          ==> rfs_persists (rfs_view ((hs:num->(A)rfs_history) ((sg:num->num) n)))
                (IMAGE ((Phi:num->real^3->A) (sg n)) {x | p3_std_dist g0 x < &(m + 2) + &1})
                ((ts:num->real) (sg n) + &0 / (Q:num->real) (sg n)) (ts (sg n) + s / Q (sg n)) /\
              (!z. z IN IMAGE (Phi (sg n)) {x | p3_std_dist g0 x < &(m + 2) + &1}
                   ==> p3_vrm (rfs_view (hs (sg n))) (ts (sg n) + s / Q (sg n)) z
                       <= max CM (&0) * Q (sg n))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "g2" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p3n_gat] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(e:num->real) n` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CM * (Q:num->real) ((sg:num->num) n)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n y u. N1 + N2 + m + 2 <= n /\ y IN {x | p3_std_dist g0 x < &(m + 2) + &1}
            ==> abs(u dot (p3n_cfl ((hs:num->(A)rfs_history) ((sg:num->num) n))
                             ((Phi:num->real^3->A) (sg n)) ((ts:num->real) (sg n))
                             ((Q:num->real) (sg n)) (&0) y ** u) - u dot (g0 y ** u))
                <= inv(&2) * (u dot (g0 y ** u))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`; `u:real^3`] THEN STRIP_TAC THEN
    USE_THEN "qf" (MP_TAC o SPECL [`n:num`; `y:real^3`; `u:real^3`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN {x | p3_std_dist g0 x < &(m + 2) + &1}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field {x:real^3 | p3_std_dist g0 x < &m + &1} M` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&m + &1`] P3N_STD_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) ((sg:num->num) n))`;
                 `\n. (Phi:num->real^3->A) ((sg:num->num) n) (vec 0)`;
                 `\n. (ts:num->real) ((sg:num->num) n)`; `\n. (Q:num->real) ((sg:num->num) n)`;
                 `{&0:real}`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `vec 0:real^3`;
                 `\m:num. {x:real^3 | p3_std_dist g0 x < &m + &1}`;
                 `\n. (Phi:num->real^3->A) ((sg:num->num) n)`;
                 `m:num`; `b:num->real`; `e:num->real`; `max CM (&0)`; `N1 + N2 + m + 2`;
                 `((:real^3),(\x:real^3. x))`; `K:real^3->bool`; `K':real^3->bool`;
                 `M:real^3->real^3^3`] P3N_WINDOW) THEN
  REWRITE_TAC[P3N_OSA_CHART_IMAGE; P3N_OSA_IN; P2CV_P_PB; P3N_CFL_LOCAL] THEN
  REWRITE_TAC[GSYM P3N_CFL_PB] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`kk:num`; `dd:real`]) THEN ASM_REWRITE_TAC[]);;

let P3N_RUN = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> !C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc
          (D:num->num) (G:real->real^3->real^3^3) tl (e:num->real) m R.
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
           &0 < eps /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           (!m n. m < n ==> D m < D n) /\ p3_std_flow g0 (&1) G /\ &0 <= tl /\ tl < &1 /\
           p3n_close_below g0 hs Phi ts Q D tl G /\ (!n. e n <= &1) /\
           (!b. &0 <= b /\ (b < tl \/ b = &0) ==> ?N. !j. N <= j ==> b < e (D j)) /\
           (?CM N. !j. N <= j
                  ==> p3n_gat g0 (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j)) (e (D j)) CM
                              (m + 2) (&1)) /\
           &0 <= R /\ cball(vec 0,R + &2) SUBSET {x | p3_std_dist g0 x < &m + &1}
           ==> ?J:num->num. (!m n. m < n ==> J m < J n) /\
                   !kk ep. &0 < ep
                     ==> ?lam N. &0 < lam /\
                           !n s y. N <= n /\ &0 <= s /\ s < e (D (J n)) /\ s < tl + lam /\
                                   y IN cball(vec 0,R)
                                   ==> lck_dist2 kk (G s)
                                         (p3n_cfl (hs (D (J n))) (Phi (D (J n))) (ts (D (J n)))
                                                  (Q (D (J n))) s) y < ep`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC [el 0 cs; el 1 cs; el 2 cs; el 3 cs; el 4 cs; el 5 cs; el 6 cs;
                          el 7 cs; el 8 cs; el 9 cs; el 10 cs; el 13 cs; el 14 cs] THEN
    LABEL_TAC "eb" (el 11 cs) THEN
    X_CHOOSE_THEN `CM:real` (X_CHOOSE_THEN `Ng:num` (LABEL_TAC "g2")) (el 12 cs)) THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_std_flow; p3_partial_std]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < &m + &1} /\
                {x:real^3 | p3_std_dist g0 x < &m + &1} SUBSET
                {x | p3_std_dist g0 x < &(m + 2) + &1}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&m + &1`] P3N_STD_BALL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cball(vec 0:real^3,R) SUBSET cball(vec 0,R + &1) /\
    cball(vec 0:real^3,R + &1) SUBSET cball(vec 0,R + &2) /\
    cball(vec 0:real^3,R + &1) SUBSET {x | p3_std_dist g0 x < &m + &1} /\
    (!z. z IN cball(vec 0:real^3,R) ==> ?r. &0 < r /\ ball(z,r) SUBSET cball(vec 0,R + &1)) /\
    (!z. z IN cball(vec 0:real^3,R + &1)
         ==> ?r. &0 < r /\ ball(z,r) SUBSET cball(vec 0,R + &2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL_0] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(vec 0:real^3,R + &2)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_CBALL_0] THEN REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
      MATCH_MP_TAC P3N_CBALL_BALLS THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
      REWRITE_TAC[REAL_ARITH `R + &2 = (R + &1) + &1`] THEN
      MATCH_MP_TAC P3N_CBALL_BALLS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `hs:num->(A)rfs_history`; `Phi:num->real^3->A`;
                 `ts:num->real`; `Q:num->real`; `D:num->num`; `tl:real`;
                 `G:real->real^3->real^3^3`; `e:num->real`] P3N_DIAG_CLOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "bbe") (LABEL_TAC "R1")))) THEN
  EXISTS_TAC `J:num->num` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`kk:num`; `ep:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. n <= (J:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (D:num->num) ((J:num->num) m) < D (J n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2cv_hyp (\n. rfs_view ((hs:num->(A)rfs_history) ((D:num->num) ((J:num->num) n))))
             (\n. (Phi:num->real^3->A) (D (J n)) (vec 0))
             (\n. (ts:num->real) (D (J n))) (\n. (Q:num->real) (D (J n))) {&0}
             (euclidean,open_set_atlas (:real^3)) g0 (vec 0)
             (\m. {x | p3_std_dist g0 x < &m + &1}) (\n. Phi (D (J n)))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P3N_SEQ_HYP) THEN
    DISCH_THEN(MP_TAC o BETA_RULE o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
      `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
      `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
      `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
      `tc:num->real`; `\n. (D:num->num) ((J:num->num) n)`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* persistence of the ball m + 2 below e along D o J *)
  SUBGOAL_THEN
   `!n s. Ng <= n /\ &0 <= s /\ s < (e:num->real) ((D:num->num) ((J:num->num) n))
          ==> rfs_persists (rfs_view ((hs:num->(A)rfs_history) (D (J n))))
                (IMAGE ((Phi:num->real^3->A) (D (J n))) {x | p3_std_dist g0 x < &(m + 2) + &1})
                ((ts:num->real) (D (J n))) (ts (D (J n)) + s / (Q:num->real) (D (J n)))`
  (LABEL_TAC "pers") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "g2" (MP_TAC o SPEC `(J:num->num) n`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[p3n_gat] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(e:num->real) ((D:num->num) ((J:num->num) n))` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* metric fields of the flows on the ball m *)
  SUBGOAL_THEN
   `!n s. Ng + m + 2 <= n /\ &0 <= s /\ s < (e:num->real) ((D:num->num) ((J:num->num) n))
          ==> metric_field {x:real^3 | p3_std_dist g0 x < &m + &1}
                (p3n_cfl ((hs:num->(A)rfs_history) (D (J n))) ((Phi:num->real^3->A) (D (J n)))
                         ((ts:num->real) (D (J n))) ((Q:num->real) (D (J n))) s)`
  (LABEL_TAC "mf") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `{x:real^3 | p3_std_dist g0 x < &(m + 2) + &1}` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(BETA_RULE(ISPECL [`hs:num->(A)rfs_history`; `Phi:num->real^3->A`; `ts:num->real`;
                   `Q:num->real`; `g0:real^3->real^3^3`; `\n. (D:num->num) ((J:num->num) n)`;
                   `m + 2`; `n:num`; `s:real`] P3N_CFL_FIELD_P)) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pers" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* C^0 closeness at the bases to the model G tl *)
  SUBGOAL_THEN
   `!ep. &0 < ep
         ==> ?N. !n y p q. N <= n /\ y IN cball(vec 0:real^3,R + &2) /\
                           1 <= p /\ p <= 3 /\ 1 <= q /\ q <= 3
                           ==> abs(p3n_cfl ((hs:num->(A)rfs_history) ((D:num->num) ((J:num->num) n)))
                                     ((Phi:num->real^3->A) (D (J n))) ((ts:num->real) (D (J n)))
                                     ((Q:num->real) (D (J n))) (tl - tl / (&n + &2)) y$p$q -
                                   (G:real->real^3->real^3^3) tl y$p$q) < ep`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&1`; `G:real->real^3->real^3^3`; `tl:real`;
                   `{x:real^3 | p3_std_dist g0 x < &m + &1}`; `cball(vec 0:real^3,R + &2)`;
                   `\n:num. tl - tl / (&n + &2)`;
                   `\n. p3n_cfl ((hs:num->(A)rfs_history) ((D:num->num) ((J:num->num) n)))
                          ((Phi:num->real^3->A) (D (J n))) ((ts:num->real) (D (J n)))
                          ((Q:num->real) (D (J n))) (tl - tl / (&n + &2))`] P3N_BASE_C0E) THEN
    BETA_TAC THEN REWRITE_TAC[DIMINDEX_3] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_CBALL] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `nn:num` THEN MP_TAC(SPECL [`tl:real`; `nn:num`] P3N_BB_FACTS) THEN ASM_SIMP_TAC[];
        X_GEN_TAC `e':real` THEN DISCH_TAC THEN MATCH_MP_TAC P3N_BB_LIM THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `Ng + m + 2` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`tl:real`; `n:num`] P3N_BB_FACTS) THEN ASM_SIMP_TAC[];
        X_GEN_TAC `e':real` THEN DISCH_TAC THEN
        USE_THEN "R1" (MP_TAC o SPECL [`cball(vec 0:real^3,R + &2)`; `0`; `e':real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
        MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
        USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        MP_TAC(SPECL [`tl:real`; `n:num`] P3N_BB_FACTS) THEN ASM_SIMP_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the uniform base change near tl *)
  MP_TAC(ISPECL [`{x:real^3 | p3_std_dist g0 x < &m + &1}`; `cball(vec 0:real^3,R)`;
                 `cball(vec 0:real^3,R + &1)`; `&1`; `G:real->real^3->real^3^3`; `tl:real`]
         P3N_BASE_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`kk:num`; `ep:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` (X_CHOOSE_THEN `kk':num` (X_CHOOSE_THEN `dd:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif")))))) THEN
  (* the window lemma towards G tl *)
  SUBGOAL_THEN `metric_field (:real^3) ((G:real->real^3->real^3^3) tl)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= tl - tl / (&n + &2) /\ (e:num->real) ((D:num->num) ((J:num->num) n)) <= &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPECL [`tl:real`; `n:num`] P3N_BB_FACTS) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?CM N. !n. N <= n
       ==> p3n_gat g0 ((hs:num->(A)rfs_history) ((D:num->num) ((J:num->num) n)))
             ((Phi:num->real^3->A) (D (J n))) ((ts:num->real) (D (J n)))
             ((Q:num->real) (D (J n))) ((e:num->real) (D (J n))) CM (m + 2) (&1)`
  ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`CM:real`; `Ng:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "g2" MATCH_MP_TAC THEN ASM_MESON_TAC[LE_TRANS];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3N_RUN_WINDOW) THEN
  DISCH_THEN(MP_TAC o BETA_RULE o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
      `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
      `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
      `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
      `tc:num->real`; `\n. (D:num->num) ((J:num->num) n)`; `\n:num. tl - tl / (&n + &2)`;
      `\n. (e:num->real) ((D:num->num) ((J:num->num) n))`; `(G:real->real^3->real^3^3) tl`;
      `m:num`; `cball(vec 0:real^3,R + &1)`; `cball(vec 0:real^3,R + &2)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`kk':num`; `dd:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `N3:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "win")))) THEN
  (* combine *)
  ABBREV_TAC `lam' = min (lam / &2) (mu / &2)` THEN
  SUBGOAL_THEN `&0 < lam' /\ lam' <= lam / &2 /\ lam' <= mu / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`tl:real`; `lam':real`] P3N_BB_LIM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4")) THEN
  USE_THEN "R1" (MP_TAC o SPECL [`cball(vec 0:real^3,R)`; `kk:num`; `ep:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  MAP_EVERY EXISTS_TAC [`lam':real`; `N1 + N3 + N4 + Ng + m + 2`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s <= tl - tl / (&n + &2)` THENL
   [USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((tl - tl / (&n + &2)) - tl) < lam'` ASSUME_TAC THENL
   [USE_THEN "N4" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(e:num->real) ((D:num->num) ((J:num->num) n))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPECL [`s:real`;
    `p3n_cfl ((hs:num->(A)rfs_history) ((D:num->num) ((J:num->num) n)))
             ((Phi:num->real^3->A) (D (J n))) ((ts:num->real) (D (J n)))
             ((Q:num->real) (D (J n))) s`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN USE_THEN "win" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The closed end of the closeness at the cutoff time (Prop 16.5 with the    *)
(* cutoff tc).  A Ricci flow from 0 on R^3 is a smooth family of metrics on  *)
(* every open set (P3N_RF_LSMOOTH).  If a family H on (a,b] agrees with a    *)
(* smooth map FF on (a,b+e) x V, then the C^k distance from a smooth family  *)
(* G to H at a point is continuous from the left at b (P3N_LCK_END_CONT:     *)
(* symmetrized extension, positive near (b,y0) by RFA_LOCAL_LSMOOTH,         *)
(* P2BL_LCK_FAMILY_SMOOTH).  The rescaled coordinate flows have such         *)
(* extensions up to the end of a persistence interval (P3N_CFL_EXT, from     *)
(* P2CQ_PB_UPTO), so a bound on the C^k distance before the end holds at the *)
(* end (P3N_CLOSE_END).                                                      *)
(* ========================================================================= *)

let P3N_RF_LSMOOTH = prove
 (`!T0 (G:real->real^N->real^N^N) U ta tb.
     ricci_flow_from (euclidean,open_set_atlas (:real^N)) (&0) T0 G /\
     open U /\ &0 <= ta /\ ta < tb /\ tb <= T0
     ==> lrg_lsmooth U ta tb G`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC) o
    MATCH_MP P3N_RF_REP) THEN
  REWRITE_TAC[lrg_lsmooth] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `T0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod` THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [GSYM LIFT_DROP] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(--e),lift T0) PCROSS (:real^N)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC]);;

let P3N_LCK_END_CONT = prove
 (`!V a b e (H:real->real^3->real^3^3) (FF:real^(1,3)finite_sum->real^(3,3)finite_prod)
    (G:real->real^3->real^3^3) ta tb y0 k.
     open V /\ &0 < e /\ a < b /\ y0 IN V /\
     (!t. a < t /\ t <= b ==> metric_field V (H t)) /\
     smooth_map_on (interval(lift a,lift(b + e)) PCROSS V) FF /\
     (!t y. a < t /\ t <= b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(H t y)) /\
     lrg_lsmooth V ta tb G /\ ta < b /\ b < tb
     ==> !ep. &0 < ep
              ==> ?d. &0 < d /\
                      !t. b - d < t /\ t <= b
                          ==> abs(lck_dist2 k (G t) (H t) y0 - lck_dist2 k (G b) (H b) y0) < ep`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `O = interval(lift a,lift(b + e)) PCROSS (V:real^3->bool)` THEN
  SUBGOAL_THEN `open(O:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `!t y. a < t /\ t <= b /\ y IN V
                      ==> transp((H:real->real^3->real^3^3) t y) = H t y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `Fs = (\m. vectorize(inv(&2) %% (matrify m + transp(matrify m)):real^3^3)) o
                   (FF:real^(1,3)finite_sum->real^(3,3)finite_prod)` THEN
  SUBGOAL_THEN
   `smooth_map_on O (Fs:real^(1,3)finite_sum->real^(3,3)finite_prod) /\
    (!w. transp(matrify(Fs w)) = matrify(Fs w):real^3^3) /\
    (!t y. a < t /\ t <= b /\ y IN V
           ==> Fs(pastecart (lift t) y) = vectorize((H:real->real^3->real^3^3) t y))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL;
                  GSYM VECTORIZE_ADD; GSYM VECTORIZE_CMUL] THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[o_THM; MATRIFY_VECTORIZE; TRANSP_MATRIX_CMUL;
                               TRANSP_MATRIX_ADD; TRANSP_TRANSP] THEN
      AP_TERM_TAC THEN MATCH_ACCEPT_TAC MATRIX_ADD_SYM;
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[o_THM; MATRIFY_VECTORIZE] THEN AP_TERM_TAC THEN
      REWRITE_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `w0 = pastecart (lift b) (y0:real^3)` THEN
  SUBGOAL_THEN `(w0:real^(1,3)finite_sum) IN O` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w0"; "O"] THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. ~(v = vec 0)
                    ==> &0 < v dot (matrify((Fs:real^(1,3)finite_sum->real^(3,3)finite_prod) w0)
                                    :real^3^3 ** v)` ASSUME_TAC THENL
   [SUBGOAL_THEN `matrify((Fs:real^(1,3)finite_sum->real^(3,3)finite_prod) w0) =
                  (H:real->real^3->real^3^3) b y0` SUBST1_TAC THENL
     [EXPAND_TAC "w0" THEN ASM_SIMP_TAC[MATRIFY_VECTORIZE; REAL_LE_REFL]; ALL_TAC] THEN
    UNDISCH_TAC `!t. a < t /\ t <= b ==> metric_field V ((H:real->real^3->real^3^3) t)` THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL; metric_field] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,3)finite_sum->bool`; `Fs:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                 `w0:real^(1,3)finite_sum`] RFA_LOCAL_LSMOOTH) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "w0" THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(y0:real^3,d) SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `interval(lift(b - d),lift(b + d)) PCROSS ball(y0:real^3,d) SUBSET O` THEN
    EXPAND_TAC "O" THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift b`; `z:real^3`]) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `ta' = max ta (b - d)` THEN ABBREV_TAC `tb' = min tb (b + d)` THEN
  SUBGOAL_THEN `ta' < b /\ b < tb' /\ ta <= ta' /\ b - d <= ta' /\ tb' <= tb /\ tb' <= b + d`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ta'"; "tb'"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lrg_lsmooth (ball(y0:real^3,d)) ta' tb' (G:real->real^3->real^3^3) /\
                lrg_lsmooth (ball(y0:real^3,d)) ta' tb'
                  (\t y. matrify((Fs:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                 (pastecart (lift t) y)):real^3^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFU_LSMOOTH_SUB THENL
     [MAP_EVERY EXISTS_TAC [`V:real^3->bool`; `ta:real`; `tb:real`] THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`ball(y0:real^3,d)`; `b - d`; `b + d`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `ball(y0:real^3,d)`; `ta':real`; `tb':real`;
                 `G:real->real^3->real^3^3`;
                 `\t y. matrify((Fs:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                (pastecart (lift t) y)):real^3^3`]
                P2BL_LCK_FAMILY_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift b) (y0:real^3)`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[continuous_at; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `ep:real` THEN DISCH_TAC THEN MP_TAC(SPEC `ep:real` th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d1 / &2) (min (b - a) (b - ta'))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift t) (y0:real^3)`) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  ANTS_TAC THENL
   [EXPAND_TAC "w0" THEN
    MP_TAC(ISPECL [`pastecart (lift b) (y0:real^3)`; `t:real`; `y0:real^3`; `d1 / &2`]
           RFA_PCROSS_BOX_DIST) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; DIST_REFL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DIST_LIFT] THEN
  SUBGOAL_THEN `a < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a < s /\ s <= b
        ==> lck_dist2 k ((G:real->real^3->real^3^3) s)
              (\y. matrify((Fs:real^(1,3)finite_sum->real^(3,3)finite_prod)
                           (pastecart (lift s) y)):real^3^3) y0 =
            lck_dist2 k (G s) ((H:real->real^3->real^3^3) s) y0`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `ball(y0:real^3,d)` THEN REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^3) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_REFL]);;

let P3N_CFL_EXT = prove
 (`!(hs:(A)rfs_history) Phi ts Q (Wb:real^3->bool) sc.
     p2cv_one (rfs_view hs) (euclidean,open_set_atlas (:real^3)) Wb Phi ts Q /\ &0 < sc /\
     rfs_persists (rfs_view hs) (IMAGE Phi Wb) ts (ts + sc / Q)
     ==> ?e Fx. &0 < e /\
                smooth_map_on (interval(lift(&0),lift(sc + e)) PCROSS Wb) Fx /\
                !t y. &0 < t /\ t <= sc /\ y IN Wb
                      ==> Fx(pastecart (lift t) y) = vectorize(p3n_cfl hs Phi ts Q t y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `euclidean:(real^3)topology`;
                 `open_set_atlas (:real^3)`; `Wb:real^3->bool`; `Phi:real^3->A`;
                 `ts:real`; `Q:real`; `&0`; `sc:real`; `&0`; `sc:real`] P2CQ_PB_UPTO) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; P2CV_DIV_LZERO; REAL_ADD_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_upto] THEN
  DISCH_THEN(MP_TAC o SPEC `((:real^3) INTER Wb,(\x:real^3. x))` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[restrict_atlas; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `\x:real^3. x`] THEN REWRITE_TAC[P3N_OSA_IN];
    ALL_TAC] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^3`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `Wb:real^3->bool`;
                 `p2cv_pb (rfs_view (hs:(A)rfs_history)) ts Q (open_set_atlas (:real^3)) Phi t`;
                 `((:real^3),(\x:real^3. x))`; `y:real^3`] P2CQ_REGION_REP) THEN
  REWRITE_TAC[FST; SND; INTER_UNIV; IMAGE_ID; P3N_OSA_IN; P3N_CFL_LOCAL; GEOL_EUCLID_FACTS] THEN
  ASM_REWRITE_TAC[]);;

let P3N_CLOSE_END = prove
 (`!(hs:(A)rfs_history) Phi ts Q (Wb:real^3->bool) sc (G:real->real^3->real^3^3) y0 k dd d0.
     p2cv_one (rfs_view hs) (euclidean,open_set_atlas (:real^3)) Wb Phi ts Q /\
     y0 IN Wb /\ &0 < sc /\ sc < &1 /\ &0 < d0 /\
     rfs_persists (rfs_view hs) (IMAGE Phi Wb) ts (ts + sc / Q) /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\
     (!t. sc - d0 < t /\ t < sc ==> lck_dist2 k (G t) (p3n_cfl hs Phi ts Q t) y0 <= dd)
     ==> lck_dist2 k (G sc) (p3n_cfl hs Phi ts Q sc) y0 <= dd`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast cs) THEN LABEL_TAC "bd" (last cs)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  SUBGOAL_THEN `open(Wb:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_EUCLIDEAN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `Q:real`; `Wb:real^3->bool`;
                 `sc:real`] P3N_CFL_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!t. &0 < t /\ t <= sc ==> metric_field Wb (p3n_cfl (hs:(A)rfs_history) Phi ts Q t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `euclidean:(real^3)topology`;
                   `open_set_atlas (:real^3)`; `Wb:real^3->bool`; `Phi:real^3->A`;
                   `ts:real`; `Q:real`; `&0`; `sc:real`; `t:real`;
                   `((:real^3),(\x:real^3. x))`] P2CV_P_FIELD_AT) THEN
    ASM_REWRITE_TAC[P3N_OSA_IN; P3N_OSA_CHART_IMAGE; P3N_CFL_LOCAL; REAL_LE_REFL;
                    P2CV_DIV_LZERO; REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&1`; `G:real->real^3->real^3^3`; `Wb:real^3->bool`; `sc / &2`;
                 `(&1 + sc) / &2`] P3N_RF_LSMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`Wb:real^3->bool`; `&0`; `sc:real`; `e:real`;
                 `p3n_cfl (hs:(A)rfs_history) Phi ts Q`;
                 `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                 `G:real->real^3->real^3^3`; `sc / &2`; `(&1 + sc) / &2`; `y0:real^3`; `k:num`]
                P3N_LCK_END_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "cont") THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  USE_THEN "cont" (MP_TAC o SPEC
    `lck_dist2 k ((G:real->real^3->real^3^3) sc) (p3n_cfl (hs:(A)rfs_history) Phi ts Q sc) y0 - dd`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `sc - min d (min d0 sc) / &2`))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "bd" (MP_TAC o SPEC `sc - min d (min d0 sc) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The conclusion of Prop 16.5 for one history (p3n_concl, the disjunction   *)
(* of P3_PROP_16_5_STATEMENT, with the cutoff tc), and the case analysis at  *)
(* the persistence time Tf of the core                                       *)
(* ball (P3N_FINAL_ONE): if the rescaled flows are close to G before Tf     *)
(* (with margin) and every event that cuts the core ball before tc         *)
(* discards it, then (a) or (b) holds.  Cases: Tf >= theta; the core ball   *)
(* fails before the cap (an event discards it); the cap is the cutoff, with  *)
(* tc the horizon, or the ball persisting through tc (closed end,           *)
(* P3N_CLOSE_END), or an event at tc discarding it.                         *)
(* ========================================================================= *)

let p3n_concl = new_definition
 `p3n_concl (g0:real^3->real^3^3) A theta dcl (hs:(A)rfs_history) k Phi ts h tc
            (G:real->real^3->real^3^3) <=>
    p3_view_close
      (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
      (&0) (&1) {x | p3_std_dist g0 x < A}
      (rfs_view hs) ts (inv(h pow 2)) Phi
      {s | &0 <= s /\ s < theta /\ ts + s * h pow 2 <= tc /\
           ts + s * h pow 2 < rfs_horizon hs} dcl \/
    ?k'. k < k' /\ k' <= hs_count hs /\ hs_time hs k' <= tc /\
         hs_time hs k' < ts + theta * h pow 2 /\
         p3_view_close
           (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
           (&0) (&1) {x | p3_std_dist g0 x < A}
           (rfs_view hs) ts (inv(h pow 2)) Phi
           {s | &0 <= s /\ ts + s * h pow 2 < hs_time hs k'} dcl /\
         DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < A}) (topspace(hs_top hs k'))`;;

let p3n_disc = new_definition
 `p3n_disc (g0:real^3->real^3^3) (hs:(A)rfs_history) k (Phi:real^3->A) ts h tc theta ms th <=>
    !j. k < j /\ j <= hs_count hs /\ hs_time hs j <= tc /\
        hs_time hs j < ts + theta * h pow 2 /\
        (!t. ts < t /\ t < hs_time hs j
             ==> rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < &ms}) ts t) /\
        ~(IMAGE Phi {x | p3_std_dist g0 x < &ms} SUBSET topspace (hs_top hs j) /\
          DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < &ms})
                   (mfd_cut_spheres (ev_index (hs_event hs j)) (ev_neck (hs_event hs j)))) /\
        (!s. &0 <= s /\ ts + s * h pow 2 < hs_time hs j
             ==> s < p3n_ptime g0 hs Phi ts (inv(h pow 2)) (&ms)
                               (min th ((tc - ts) * inv(h pow 2))))
        ==> DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < &ms}) (topspace (hs_top hs j))`;;

let P3N_ONE_FROM_PARAM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U Phi ts Q.
     p2c_regular_view V /\ open U /\ ~(U = {}) /\ &0 < Q /\
     mfd_param (rfs_vtop V ts) (rfs_vatlas V ts) U Phi
     ==> p2cv_one V (euclidean,open_set_atlas (:real^3)) U Phi ts Q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cv_one] THEN
  ASM_SIMP_TAC[P3N_REGULAR_FROM_SMOOTH; GEOL_EUCLID_FACTS; OPEN_IN_EUCLIDEAN] THEN
  ASM_MESON_TAC[mfd_param]);;

let P3N_VC_FROM = prove
 (`!(hs:(A)rfs_history) k Phi ts h (G:real->real^3->real^3^3) g0 A0 A ms Sj dcl.
     rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\ 1 <= k /\ k <= hs_count hs /\
     hs_time hs k = ts /\ &0 < h /\ p3_std_initial g0 A0 /\ &0 < A /\ A < &ms /\ &0 < dcl /\
     mfd_param (rfs_vtop (rfs_view hs) ts) (rfs_vatlas (rfs_view hs) ts)
               {x | p3_std_dist g0 x < &ms} Phi /\
     (!s. s IN Sj
          ==> &0 <= s /\ s < &1 /\
              (s = &0 \/
               rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < &ms})
                            ts (ts + s * h pow 2))) /\
     (!s x. s IN Sj /\ p3_std_dist g0 x < A
            ==> lck_dist2 (rfs_kreg dcl) (G s) (p3n_cfl hs Phi ts (inv(h pow 2)) s) x
                < dcl pow 2 / &2)
     ==> p3_view_close
           (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
           (&0) (&1) {x | p3_std_dist g0 x < A} (rfs_view hs) ts (inv(h pow 2)) Phi Sj dcl`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast cs)) THEN
    LABEL_TAC "sj" (el (length cs - 2) cs) THEN LABEL_TAC "cl" (last cs)) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (rfs_view (hs:(A)rfs_history)) ts)
                                      (rfs_vatlas (rfs_view hs) ts)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3N_VIEW_AT_EVENT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(h pow 2) /\ (!s. s / inv(h pow 2) = s * h pow 2)` STRIP_ASSUME_TAC
  THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; real_div; REAL_INV_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < &ms}` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&ms`] P3N_STD_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC P3N_VIEW_CLOSE_INTRO THEN
  MAP_EVERY EXISTS_TAC [`A0:real`; `{x:real^3 | p3_std_dist g0 x < &ms}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "sj" (fun th -> MESON_TAC[th]);
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "sj" (MP_TAC o C MP (ASSUME `(s:real) IN Sj`) o SPEC `s:real`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
    ASM_CASES_TAC `s = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s * h pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`;
                     `IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < &ms}`;
                     `ts:real`; `ts + s * h pow 2`; `ts + s * h pow 2`] P2CV_PERSISTS_AT) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC P3N_PARAM_LATER THEN EXISTS_TAC `ts:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

let P3N_FINAL_ONE = prove
 (`!(hs:(A)rfs_history) k Phi ts h tc (G:real->real^3->real^3^3) g0 A0 A theta dcl ms th.
     rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\ 1 <= k /\ k <= hs_count hs /\
     hs_time hs k = ts /\ &0 < h /\ ts < tc /\ tc <= rfs_horizon hs /\
     p3_std_initial g0 A0 /\ &0 < A /\ A < &ms /\ &0 < theta /\ theta < th /\ th < &1 /\
     &0 < dcl /\
     mfd_param (rfs_vtop (rfs_view hs) ts) (rfs_vatlas (rfs_view hs) ts)
               {x | p3_std_dist g0 x < &ms} Phi /\
     p3_std_flow g0 (&1) G /\
     (!s y. &0 <= s /\
            s < p3n_ptime g0 hs Phi ts (inv(h pow 2)) (&ms)
                          (min th ((tc - ts) * inv(h pow 2))) /\
            s < theta /\ p3_std_dist g0 y < A
            ==> lck_dist2 (rfs_kreg dcl) (G s) (p3n_cfl hs Phi ts (inv(h pow 2)) s) y
                <= dcl pow 2 / &4) /\
     p3n_disc g0 hs k Phi ts h tc theta ms th
     ==> p3n_concl g0 A theta dcl hs k Phi ts h tc G`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast cs)) THEN
    LABEL_TAC "close" (el (length cs - 2) cs) THEN
    LABEL_TAC "disc" (REWRITE_RULE[p3n_disc] (last cs))) THEN
  SUBGOAL_THEN `&0 < inv(h pow 2) /\ (!s. s / inv(h pow 2) = s * h pow 2) /\ &0 < h pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; real_div; REAL_INV_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_std_flow; p3_partial_std]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < &ms} /\
                ~({x:real^3 | p3_std_dist g0 x < &ms} = {})` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&ms`] P3N_STD_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&ms`] P3S_RINV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `p3s_rad_rho g0 (p3s_rad_rinv g0 (&ms)) = &ms` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[P3S_RHO_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2cv_one (rfs_view (hs:(A)rfs_history)) (euclidean,open_set_atlas (:real^3))
                  {x | p3_std_dist g0 x < &ms} Phi ts (inv(h pow 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_ONE_FROM_PARAM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) k)
                  (IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < &ms})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3N_VIEW_AT_EVENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `{x:real^3 | p3_std_dist g0 x < &ms}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < A} SUBSET
                IMAGE Phi {x | p3_std_dist g0 x < &ms}` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `W = IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < &ms}` THEN
  ABBREV_TAC `cap = min th ((tc - ts) * inv(h pow 2))` THEN
  ABBREV_TAC `Tf = p3n_ptime g0 (hs:(A)rfs_history) Phi ts (inv(h pow 2)) (&ms) cap` THEN
  SUBGOAL_THEN `&0 < (tc - ts) * inv(h pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cap /\ cap <= th /\ cap <= (tc - ts) * inv(h pow 2) /\
                (cap < th ==> cap = (tc - ts) * inv(h pow 2))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "cap" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                 `inv(h pow 2)`; `&ms`; `cap:real`] P3N_PTIME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pers") (LABEL_TAC "max")))) THEN
  (* the (b) alternative from an event discarding the core ball *)
  SUBGOAL_THEN
   `!j. k < j /\ j <= hs_count hs /\ hs_time (hs:(A)rfs_history) j <= tc /\
        hs_time hs j < ts + theta * h pow 2 /\
        (!t. ts < t /\ t < hs_time hs j ==> rfs_persists (rfs_view hs) W ts t) /\
        ~(W SUBSET topspace (hs_top hs j) /\
          DISJOINT W (mfd_cut_spheres (ev_index (hs_event hs j)) (ev_neck (hs_event hs j)))) /\
        (!s. &0 <= s /\ ts + s * h pow 2 < hs_time hs j ==> s < Tf /\ s < theta)
        ==> p3n_concl g0 A theta dcl hs k Phi ts h tc G`
  (LABEL_TAC "caseb") THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    USE_THEN "disc" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
    REWRITE_TAC[p3n_concl] THEN DISJ2_TAC THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3N_VC_FROM THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `A0:real`; `ms:num`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
          can (find_term (fun t -> t = `Tf:real`)) (concl th) && is_forall(concl th) &&
          not (can (find_term (fun t -> t = `y:real^3`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `hs_time (hs:(A)rfs_history) j`)) (concl th) &&
          is_forall(concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "rfs_persists" with Failure _ -> false))
              (concl th))) THEN
        ASM_REWRITE_TAC[REAL_LT_ADDR] THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
          can (find_term (fun t -> t = `Tf:real`)) (concl th) && is_forall(concl th) &&
          not (can (find_term (fun t -> t = `y:real^3`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dcl pow 2 / &4` THEN CONJ_TAC THENL
         [USE_THEN "close" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &4 < x / &2`) THEN
          ASM_SIMP_TAC[REAL_POW_LT]]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `theta <= Tf` THENL
   [(* case (a) from closeness up to theta *)
    REWRITE_TAC[p3n_concl] THEN DISJ1_TAC THEN
    MATCH_MP_TAC P3N_VC_FROM THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `A0:real`; `ms:num`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISJ2_TAC THEN USE_THEN "pers" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dcl pow 2 / &4` THEN CONJ_TAC THENL
       [USE_THEN "close" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &4 < x / &2`) THEN ASM_SIMP_TAC[REAL_POW_LT]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Tf < theta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `Tf < cap` THENL
   [(* the core ball fails before the cap *)
    ABBREV_TAC `s1 = (Tf + min cap theta) / &2` THEN
    SUBGOAL_THEN `Tf < s1 /\ s1 < cap /\ s1 < theta /\ &0 < s1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~rfs_persists (rfs_view (hs:(A)rfs_history)) W ts (ts + s1 * h pow 2)`
    ASSUME_TAC THENL
     [DISCH_TAC THEN USE_THEN "max" (MP_TAC o SPEC `s1:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `ts < ts + s1 * h pow 2 /\ ts + s1 * h pow 2 < tc /\
                  ts + s1 * h pow 2 < ts + theta * h pow 2`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_ADDR; REAL_LT_MUL; REAL_LT_LADD; REAL_LT_RMUL_EQ] THEN
      SUBGOAL_THEN `s1 < (tc - ts) / h pow 2` MP_TAC THENL
       [REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `W:A->bool`; `ts + s1 * h pow 2`]
                  P3N_FIRST_FAILURE2) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bef")
      (CONJUNCTS_THEN2 (LABEL_TAC "mx") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
    USE_THEN "caseb" (MATCH_MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ABBREV_TAC `u = (hs_time (hs:(A)rfs_history) j - ts) / h pow 2` THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) j = ts + u * h pow 2` ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `s < u /\ u <= s1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ts + s * h pow 2 < hs_time (hs:(A)rfs_history) j` THEN
      UNDISCH_TAC `hs_time (hs:(A)rfs_history) j <= ts + s1 * h pow 2` THEN
      ASM_REWRITE_TAC[REAL_LT_LADD; REAL_LE_LADD] THEN
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LE_RMUL_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(s + u) / &2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "max" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "bef" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LADD; REAL_LT_ADDR] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the cap is the cutoff *)
  SUBGOAL_THEN `ts + Tf * h pow 2 = tc /\ &0 < Tf` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `Tf = (tc - ts) * inv(h pow 2)` SUBST1_TAC THENL
     [SUBGOAL_THEN `Tf:real = cap` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!s. ts + s * h pow 2 < tc <=> s < Tf) /\
                (!s. ts + s * h pow 2 <= tc <=> s <= Tf) /\
                (!s. ts + s * h pow 2 = tc <=> s = Tf)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN GEN_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_SIMP_TAC[REAL_LT_LADD; REAL_LE_LADD; REAL_EQ_ADD_LCANCEL; REAL_LT_RMUL_EQ;
                 REAL_LE_RMUL_EQ; REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. ts <= t /\ t < tc ==> rfs_persists (rfs_view (hs:(A)rfs_history)) W ts t`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `t = ts + ((t - ts) / h pow 2) * h pow 2` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pers" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_SUB_LE; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `tc = rfs_horizon (hs:(A)rfs_history)` THENL
   [REWRITE_TAC[p3n_concl] THEN DISJ1_TAC THEN
    MATCH_MP_TAC P3N_VC_FROM THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `A0:real`; `ms:num`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISJ2_TAC THEN USE_THEN "pt" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LE_ADDR; REAL_LE_MUL; REAL_LT_IMP_LE];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dcl pow 2 / &4` THEN CONJ_TAC THENL
       [USE_THEN "close" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &4 < x / &2`) THEN ASM_SIMP_TAC[REAL_POW_LT]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W ts tc` THENL
   [(* the core ball persists through tc: closed end *)
    REWRITE_TAC[p3n_concl] THEN DISJ1_TAC THEN
    MATCH_MP_TAC P3N_VC_FROM THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `A0:real`; `ms:num`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISJ2_TAC THEN
      ASM_CASES_TAC `s:real = Tf` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "pt" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LE_ADDR; REAL_LE_MUL; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dcl pow 2 / &4` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &4 < x / &2`) THEN ASM_SIMP_TAC[REAL_POW_LT]] THEN
    ASM_CASES_TAC `s:real = Tf` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC P3N_CLOSE_END THEN
      MAP_EVERY EXISTS_TAC [`{x:real^3 | p3_std_dist g0 x < &ms}`; `Tf:real`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "close" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      USE_THEN "close" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* an event at tc discards the core ball *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `W:A->bool`; `tc:real`] P3N_FIRST_FAILURE2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bef")
    (CONJUNCTS_THEN2 (LABEL_TAC "mx") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) j = tc` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "mx" (MP_TAC o SPEC `(max ts (hs_time (hs:(A)rfs_history) j) + tc) / &2`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; USE_THEN "pt" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Tf * h pow 2 < theta * h pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RMUL_EQ]; ALL_TAC] THEN
  USE_THEN "caseb" (MATCH_MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Inputs of the discard step along the cap sequence.  The                   *)
(* shell of a standard flow is close to the shrinking cylinder in the order *)
(* rfs_kreg eps of Claim 16.10 (P3N_SHELL_CLOSE: P2_PROP_12_7 at the finer  *)
(* scale dd, then LCK_DIST_MONO on the neck band, P3S_NC_DIFFEO).           *)
(* ========================================================================= *)

let P3N_SHELL_CLOSE = prove
 (`P2_PROP_12_7_STATEMENT
   ==> !g0 A0 th eps dd.
         p3_std_initial g0 A0 /\ &0 <= th /\ th < &1 /\ &0 < dd /\ dd <= eps
         ==> ?A1. A0 <= A1 /\
                  !G t x d0. p3_std_flow g0 (&1) G /\ &0 <= t /\ t <= th /\
                             A1 + inv eps <= d0 /\
                             d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                             ==> lck_dist2 (rfs_kreg eps)
                                   (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x
                                 < dd pow 2`,
  REWRITE_TAC[P2_PROP_12_7_STATEMENT] THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `th:real`; `dd:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `A1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `t:real`; `x:real^3`; `d0:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps /\ &0 < inv eps /\ t < &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  ABBREV_TAC `V = {y:real^3 | A0 + &4 - (d0 + inv eps) < A0 + &4 - p3_std_dist g0 y /\
                             A0 + &4 - p3_std_dist g0 y < A0 + &4 - (d0 - inv eps)}` THEN
  SUBGOAL_THEN
   `diffeomorphism_on V
      {y:real^3 | exp((A0 + &4 - (d0 + inv eps)) / sqrt(&2)) < norm y /\
                  norm y < exp((A0 + &4 - (d0 - inv eps)) / sqrt(&2))}
      (p3_std_nc g0 A0) (p3s_ncinv g0 A0)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P3S_NC_DIFFEO THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN V /\ open V` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[diffeomorphism_on]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg dd) (mpullback (p3_std_nc g0 A0) (cylinder_flow t))
                ((G:real->real^3->real^3^3) t) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC
       [`{y:real^3 | exp((A0 + &4 - (d0 + inv eps)) / sqrt(&2)) < norm y /\
                     norm y < exp((A0 + &4 - (d0 - inv eps)) / sqrt(&2))}`;
        `p3s_ncinv g0 A0`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM annulus; OPEN_ANNULUS];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV; GSYM NORM_POS_LT] THEN
        MESON_TAC[REAL_EXP_POS_LT; REAL_LT_TRANS]];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[p3_std_flow; p3_partial_std];
      MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3N_SCAL_FROM_VRM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t z K Q.
     p2c_regular_view V /\ z IN topspace(rfs_vtop V t) /\ &0 <= Q /\
     p3_vrm V t z <= K * Q
     ==> mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t) z <= (&6 * max K (&0)) * Q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t`; `z:A`] P3N_SCALAR_LE_RM) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) t z <= K * Q` THEN
  REWRITE_TAC[p3_vrm] THEN
  SUBGOAL_THEN `K * Q <= max K (&0) * Q` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REAL_ARITH_TAC);;

let P3N_SEQ_PARAM = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
     p3_std_initial g0 A0
     ==> !R. &0 < R
             ==> ?N. !n. N <= n
                     ==> mfd_param (rfs_vtop (rfs_view (hs n)) (ts n))
                                   (rfs_vatlas (rfs_view (hs n)) (ts n))
                                   {x | p3_std_dist g0 x < R} (Phi n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `R:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `R:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) n`; `(k:num->num) n`] P3N_VIEW_AT_EVENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
  EXISTS_TAC `{x:real^3 | --(inv((dl:num->real->real) n (ts n))) <
                          A0 + &4 - p3_std_dist g0 x}` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `p3_cap_param (md,g0,A0) (dl n,p3_hscale hf (rp n) (dl n))
                   ((hs:num->(A)rfs_history) n) (k n) (i n) (Phi n) (xi n)` THEN
    REWRITE_TAC[p3_cap_param] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] P3N_STD_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `R <= inv((dl:num->real->real) n ((ts:num->real) n))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n + &1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N2` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP P3S_A0_POS (ASSUME `p3_std_initial g0 A0`)) THEN ASM_REAL_ARITH_TAC]);;

let P3N_DISCARD_SEQ = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?epsd. &0 < epsd /\
         !eps. &0 < eps /\ eps <= epsd
           ==> ?dd0. &0 < dd0 /\
               !C hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc
                (D:num->num) (G:real->real^3->real^3^3) theta th ms d0 m0 dd (e:num->real).
                 p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
                 p3_modulus md /\ p3_std_initial g0 A0 /\
                 (!m n. m < n ==> D m < D n) /\ p3_std_flow g0 (&1) G /\
                 &0 < theta /\ theta < th /\ th < &1 /\
                 inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= &ms /\ &0 < dd /\ dd <= dd0 /\
                 (!t x. &0 <= t /\ t <= th /\
                        d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                        ==> lck_dist2 (rfs_kreg eps)
                              (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x
                            < dd pow 2) /\
                 (!n. min (p3n_tf g0 hs Phi ts Q tc ms th n) theta = e n) /\
                 (?Kc. !m. ?N. !j. N <= j
                     ==> p3n_gat g0 (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j)) (e (D j))
                                 Kc m (&1)) /\
                 (?N. !j s y. N <= j /\ &0 <= s /\ s < e (D j) /\ p3_std_dist g0 y < m0
                      ==> lck_dist2 (rfs_kreg eps) (G s)
                            (p3n_cfl (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j)) s) y
                          < dd pow 2)
                 ==> ?N. !j. N <= j
                       ==> p3n_disc g0 (hs (D j)) (k (D j)) (Phi (D j)) (ts (D j))
                             (p3_hscale hf (rp (D j)) (dl (D j)) (ts (D j))) (tc (D j))
                             theta ms th`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `epsd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FD")) P3N_FAIL_DISCARD THEN
  EXISTS_TAC `epsd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "FD" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FD2"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast(butlast(butlast cs)))) THEN
    LABEL_TAC "shell" (el (length cs - 4) cs) THEN
    LABEL_TAC "edef" (el (length cs - 3) cs) THEN
    X_CHOOSE_THEN `Kc:real` (LABEL_TAC "gat") (el (length cs - 2) cs) THEN
    X_CHOOSE_THEN `Ncl:num` (LABEL_TAC "cl") (last cs)) THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 < &ms` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (e:num->real) n <= theta` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "edef" (fun th -> REWRITE_TAC[GSYM th]) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2cv_hyp (\n. rfs_view ((hs:num->(A)rfs_history) ((D:num->num) n)))
             (\n. (Phi:num->real^3->A) (D n) (vec 0))
             (\n. (ts:num->real) (D n)) (\n. (Q:num->real) (D n)) {&0}
             (euclidean,open_set_atlas (:real^3)) g0 (vec 0)
             (\m. {x | p3_std_dist g0 x < &m + &1}) (\n. Phi (D n))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P3N_SEQ_HYP) THEN
    DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
      `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
      `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`;
      `D:num->num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the metric bound on the closed core ball *)
  USE_THEN "gat" (MP_TAC o SPEC `ms:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ng:num` (LABEL_TAC "gms")) THEN
  MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) ((D:num->num) n))`;
                 `\n. (Phi:num->real^3->A) ((D:num->num) n) (vec 0)`;
                 `\n. (ts:num->real) ((D:num->num) n)`; `\n. (Q:num->real) ((D:num->num) n)`;
                 `{&0:real}`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `vec 0:real^3`;
                 `\m:num. {x:real^3 | p3_std_dist g0 x < &m + &1}`;
                 `\n. (Phi:num->real^3->A) ((D:num->num) n)`;
                 `{x:real^3 | p3_std_dist g0 x <= &ms + &1}`] P2CV_QF_TIME0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&ms + &1`] P3N_STD_SUBLEVEL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nq:num` (LABEL_TAC "qf") o
             REWRITE_RULE[P2CV_P_PB; GSYM P3N_CFL_PB]) THEN
  MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) ((D:num->num) n))`;
                 `\n. (Phi:num->real^3->A) ((D:num->num) n) (vec 0)`;
                 `\n. (ts:num->real) ((D:num->num) n)`; `\n. (Q:num->real) ((D:num->num) n)`;
                 `{&0:real}`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `vec 0:real^3`;
                 `\m:num. {x:real^3 | p3_std_dist g0 x < &m + &1}`;
                 `\n. (Phi:num->real^3->A) ((D:num->num) n)`;
                 `ms:num`; `\n. (e:num->real) ((D:num->num) n)`; `max Kc (&0)`;
                 `Ng + Nq + ms:num`; `((:real^3),(\x:real^3. x))`;
                 `{x:real^3 | p3_std_dist g0 x <= &ms}`] P3N_QF_BOUNDS_VAR) THEN
  REWRITE_TAC[P3N_OSA_CHART_IMAGE; P3N_OSA_IN; P2CV_P_PB; P3N_CFL_LOCAL] THEN
  REWRITE_TAC[GSYM P3N_CFL_PB] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `theta:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
      USE_THEN "gms" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[p3n_gat] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(e:num->real) ((D:num->num) n)` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `theta:real` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Kc * (Q:num->real) ((D:num->num) n)` THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                     `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                     `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`;
                     `i:num->num`; `Phi:num->real^3->A`; `xi:num->real^3->real^3`;
                     `ts:num->real`; `Q:num->real`; `tc:num->real`; `(D:num->num) n`]
                    P3N_SEQ_BASIC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`; `u:real^3`] THEN STRIP_TAC THEN
      USE_THEN "qf" (MP_TAC o SPECL [`n:num`; `y:real^3`; `u:real^3`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(y:real^3) IN {x | p3_std_dist g0 x < &ms + &1}` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        SIMP_TAC[]];
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&ms`] P3N_STD_SUBLEVEL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[COMPACT_CBALL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Lm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Lm"))) THEN
  (* the surgery control threshold for these bounds *)
  USE_THEN "FD2" (MP_TAC o SPECL [`&6 * max Kc (&0)`;
                                  `max Lm (p3s_rad_rinv g0 (&ms))`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FD3"))) THEN
  MP_TAC(SPEC `dl1:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ndl:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`] P3N_SEQ_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&ms`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Np:num` (LABEL_TAC "par")) THEN
  EXISTS_TAC `Ng + Nq + ms + Ncl + Ndl + Np:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j <= (D:num->num) j` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `n = (D:num->num) j` THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  ABBREV_TAC `h = p3_hscale hf ((rp:num->real->real) n) ((dl:num->real->real) n) ((ts:num->real) n)` THEN
  REWRITE_TAC[p3n_disc] THEN X_GEN_TAC `jj:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `ts n < hs_time ((hs:num->(A)rfs_history) n) jj` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `(ts:num->real) n`)) THEN
    MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. ts n + s / (Q:num->real) n = ts n + s * h pow 2` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `(Q:num->real) n`)) THEN
    REWRITE_TAC[real_div; REAL_INV_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s / (Q:num->real) n = s * h pow 2` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `(Q:num->real) n`)) THEN
    REWRITE_TAC[real_div; REAL_INV_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view ((hs:num->(A)rfs_history) n))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_surgery_ok ((hs:num->(A)rfs_history) n) C eps ((dl:num->real->real) n)
      (p3_hscale hf ((rp:num->real->real) n) (dl n)) jj /\
    &0 < dl n (hs_time (hs n) jj) /\ dl n (hs_time (hs n) jj) <= dl1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) ((rp:num->real->real) n,(dl:num->real->real) n)
                   ((hs:num->(A)rfs_history) n)` THEN
    REWRITE_TAC[p3_struct] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `jj:num` o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "rfs_surgery_ok" with Failure _ -> false))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `hs_time ((hs:num->(A)rfs_history) n) jj` o check (fun th ->
        is_forall(concl th) && not (is_imp(snd(dest_forall(concl th))) = false) &&
        can (find_term (fun t -> try fst(dest_const t) = "real_lt" with Failure _ -> false))
            (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dl:num->real->real) n (ts n)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`(ts:num->real) n`; `hs_time ((hs:num->(A)rfs_history) n) jj`] o
          check (fun th -> length(fst(strip_forall(concl th))) = 2 &&
            can (find_term (fun t -> t = `(dl:num->real->real) n`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&Ndl)` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop (rfs_view ((hs:num->(A)rfs_history) n)) (ts n))
                  (rfs_vatlas (rfs_view (hs n)) (ts n)) {x | p3_std_dist g0 x < &ms}
                  ((Phi:num->real^3->A) n)` ASSUME_TAC THENL
   [USE_THEN "par" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 < s /\ ts n + s * h pow 2 < hs_time ((hs:num->(A)rfs_history) n) jj /\
        rfs_persists (rfs_view (hs n)) (IMAGE ((Phi:num->real^3->A) n)
                      {x | p3_std_dist g0 x < &ms}) (ts n) (ts n + s * h pow 2)
        ==> metric_field (:real^3) ((G:real->real^3->real^3^3) s) /\ &0 <= s /\ s < &1 /\
            (!y. p3_std_dist g0 y < m0
                 ==> lck_dist2 (rfs_kreg eps) (G s)
                       (p3n_cfl (hs n) (Phi n) (ts n) ((Q:num->real) n) s) y < dd pow 2) /\
            (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                 ==> lck_dist2 (rfs_kreg eps)
                       (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) (G s) x < dd pow 2) /\
            (!y. p3_std_dist g0 y < &ms
                 ==> mfd_scalar (rfs_vatlas (rfs_view (hs n)) (ts n + s * h pow 2))
                                (rfs_vmetric (rfs_view (hs n)) (ts n + s * h pow 2)) (Phi n y)
                     <= (&6 * max Kc (&0)) * Q n /\
                     norm y <= max Lm (p3s_rad_rinv g0 (&ms)) /\
                     (!w. w dot (p3n_cfl (hs n) (Phi n) (ts n) (Q n) s y ** w) <=
                          max Lm (p3s_rad_rinv g0 (&ms)) * (w dot w)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s < theta` ASSUME_TAC THENL
     [SUBGOAL_THEN `s * h pow 2 < theta * h pow 2` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RMUL_EQ]];
      ALL_TAC] THEN
    SUBGOAL_THEN `s < (e:num->real) n` ASSUME_TAC THENL
     [USE_THEN "edef" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[p3n_tf; REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "p3n_ptime" with Failure _ -> false))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `(Q:num->real) n`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `s < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `p3_std_flow (g0:real^3->real^3^3) (&1) (G:real->real^3->real^3^3)` THEN
        SIMP_TAC[p3_std_flow; p3_partial_std];
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "cl" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o
                     SPECL [`j:num`; `s:real`; `y:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "shell" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "gms" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[p3n_gat] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `((Phi:num->real^3->A) n y) IN
                    IMAGE (Phi n) {x | p3_std_dist g0 x < &ms + &1}` ASSUME_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC P3N_SCAL_FROM_VRM THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) n)`;
                       `IMAGE ((Phi:num->real^3->A) n) {x | p3_std_dist g0 x < &ms + &1}`;
                       `(ts:num->real) n`; `(ts:num->real) n + s * h pow 2`;
                       `(ts:num->real) n + s * h pow 2`]
                      P2CV_PERSISTS_AT) THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_ADDR; REAL_LT_MUL]; ALL_TAC] THEN
        STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(y:real^3) IN ball(vec 0,p3s_rad_rinv g0 (&ms))` MP_TAC THENL
         [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&ms`] P3N_STD_BALL) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC];
        X_GEN_TAC `w:real^3` THEN
        USE_THEN "Lm" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o
                       SPECL [`j:num`; `s:real`; `y:real^3`; `w:real^3`]) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[NORM_POW_2] THEN
        MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  USE_THEN "FD3" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`C:real`; `eps:real`; `(dl:num->real->real) n`; `p3_hscale hf ((rp:num->real->real) n) (dl n)`;
    `(k:num->num) n`; `A0:real`; `(ts:num->real) n`; `(Q:num->real) n`; `h:real`; `m0:real`;
    `d0:real`; `dd:real`; `G:real->real^3->real^3^3`; `\s:real. s`; `&0`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; P2CV_DIV_LZERO; REAL_ADD_RID; REAL_MUL_LZERO]);;

(* ========================================================================= *)
(* The end of Lemma 16.8 along a subsequence.  Goodness with                 *)
(* a smaller end time (P3N_GAT_WEAKEN); the core ball persists for a        *)
(* positive time (P3N_TF_POS).  P3N_FINISH: if along a subsequence the      *)
(* rescaled flows are good and close to a standard flow G before            *)
(* min Tf theta, then for some index the conclusion p3n_concl of Prop 16.5  *)
(* holds (P3N_DISCARD_SEQ for the events, P3N_FINAL_ONE for the cases).     *)
(* ========================================================================= *)

let P3N_GAT_WEAKEN = prove
 (`!g0 (hs:(A)rfs_history) Phi ts Q tp tp' K m b b'.
     p3n_gat g0 hs Phi ts Q tp K m b /\ tp' <= tp /\ tp' <= b
     ==> p3n_gat g0 hs Phi ts Q tp' K m b'`,
  REWRITE_TAC[p3n_gat] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P3N_TF_POS = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc ms th.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
     p3_std_initial g0 A0 /\ 0 < ms /\ &0 < th
     ==> ?N. !n. N <= n ==> &0 < p3n_tf g0 hs Phi ts Q tc ms th n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`] P3N_SEQ_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&ms`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (hs_top ((hs:num->(A)rfs_history) n) (k n))
                  (IMAGE ((Phi:num->real^3->A) n) {x | p3_std_dist g0 x < &ms})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top ((hs:num->(A)rfs_history) n) (k n)`;
                   `hs_atlas ((hs:num->(A)rfs_history) n) (k n)`;
                   `{x:real^3 | p3_std_dist g0 x < &ms}`; `(Phi:num->real^3->A) n`]
                  GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time ((hs:num->(A)rfs_history) n) (k n) < hs_time (hs n) (k n + 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `cap = min th ((tc n - ts n) * (Q:num->real) n)` THEN
  SUBGOAL_THEN `&0 < cap` ASSUME_TAC THENL
   [EXPAND_TAC "cap" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s0 = min (cap / &2) ((hs_time ((hs:num->(A)rfs_history) n) (k n + 1) - ts n) *
                                   (Q:num->real) n / &2)` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 <= cap /\
                ts n + s0 / (Q:num->real) n < hs_time ((hs:num->(A)rfs_history) n) (k n + 1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (hs_time ((hs:num->(A)rfs_history) n) (k n + 1) - ts n) *
                       (Q:num->real) n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s0 /\ s0 <= cap /\
                  s0 <= (hs_time ((hs:num->(A)rfs_history) n) (k n + 1) - ts n) *
                        (Q:num->real) n / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s0 / (Q:num->real) n <=
                  (hs_time ((hs:num->(A)rfs_history) n) (k n + 1) - ts n) / &2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(hs:num->(A)rfs_history) n`; `(Phi:num->real^3->A) n`;
                 `(ts:num->real) n`; `(Q:num->real) n`; `&ms`; `cap:real`] P3N_PTIME_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s0:real` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `(ts:num->real) n`)) THEN
    MATCH_MP_TAC P3N_PERSIST_STAGE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p3n_tf] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3N_FINISH = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?epsd. &0 < epsd /\
         !eps. &0 < eps /\ eps <= epsd
           ==> ?dd0. &0 < dd0 /\
               !C hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc
                (D:num->num) (G:real->real^3->real^3^3) A theta dcl th ms d0 m0 dd.
                 p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
                 p3_modulus md /\ p3_std_initial g0 A0 /\
                 (!m n. m < n ==> D m < D n) /\ p3_std_flow g0 (&1) G /\
                 &0 < A /\ A < &ms /\ &0 < theta /\ theta < th /\ th < &1 /\ &0 < dcl /\
                 inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= &ms /\ &0 < dd /\ dd <= dd0 /\
                 (!t x. &0 <= t /\ t <= th /\
                        d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                        ==> lck_dist2 (rfs_kreg eps)
                              (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x
                            < dd pow 2) /\
                 (?Kc. !m. ?N. !j. N <= j
                     ==> p3n_gat g0 (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j))
                                 (min (p3n_tf g0 hs Phi ts Q tc ms th (D j)) theta) Kc m (&1)) /\
                 (?N. !j s y. N <= j /\ &0 <= s /\
                              s < min (p3n_tf g0 hs Phi ts Q tc ms th (D j)) theta /\
                              p3_std_dist g0 y < m0
                      ==> lck_dist2 (rfs_kreg eps) (G s)
                            (p3n_cfl (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j)) s) y
                          < dd pow 2) /\
                 (?N. !j s y. N <= j /\ &0 <= s /\
                              s < min (p3n_tf g0 hs Phi ts Q tc ms th (D j)) theta /\
                              p3_std_dist g0 y < A
                      ==> lck_dist2 (rfs_kreg dcl) (G s)
                            (p3n_cfl (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j)) s) y
                          <= dcl pow 2 / &4)
                 ==> ?n. p3n_concl g0 A theta dcl (hs n) (k n) (Phi n) (ts n)
                           (p3_hscale hf (rp n) (dl n) (ts n)) (tc n) G`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `epsd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DS")) o
              MATCH_MP P3N_DISCARD_SEQ) THEN
  EXISTS_TAC `epsd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "DS" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DS2"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast cs) THEN
    X_CHOOSE_THEN `NA:num` (LABEL_TAC "clA") (last cs)) THEN
  USE_THEN "DS2" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
    `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`; `D:num->num`;
    `G:real->real^3->real^3^3`; `theta:real`; `th:real`; `ms:num`; `d0:real`; `m0:real`;
    `dd:real`; `\n. min (p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th n) theta`]) THEN
  ANTS_TAC THENL [BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "disc")) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`] P3N_SEQ_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&ms`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Np:num` (LABEL_TAC "par")) THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `j = N1 + NA + Np:num` THEN
  SUBGOAL_THEN `j <= (D:num->num) j` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `n = (D:num->num) j` THEN EXISTS_TAC `n:num` THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  MATCH_MP_TAC P3N_FINAL_ONE THEN
  MAP_EVERY EXISTS_TAC [`A0:real`; `ms:num`; `th:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    USE_THEN "par" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "clA" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o
                    SPECL [`j:num`; `s:real`; `y:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[p3n_tf; REAL_LT_MIN] THEN ASM_ARITH_TAC;
      SIMP_TAC[]];
    USE_THEN "disc" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The model flow at a level (P3N_LIMIT_OR_START: P3N_LIMIT_STEP             *)
(* for a positive level, a standard flow from P2_THM_12_5 with the cap      *)
(* closeness at level 0) and the endpoint case of Lemma 16.8 (P3N_ENDPT:    *)
(* below the saturation level L the persistence times Tf tend to T < L      *)
(* along a subsequence; the window run P3N_RUN at T then gives closeness up *)
(* to Tf, and the goodness below L the curvature).                          *)
(* ========================================================================= *)

let P3N_LIMIT_OR_START = prove
 (`!u:A->bool.
     P2C_PROP_5_14_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_STD_EXTEND_STATEMENT /\ P2_THM_12_5_STATEMENT
     ==> !C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc
          (D:num->num) (Tf:num->real) tl.
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
           &0 < eps /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           (!m n. m < n ==> D m < D n) /\ &0 <= tl /\
           (!b. &0 <= b /\ b < tl ==> p3n_good g0 hs Phi ts Q Tf D b) /\
           (!b. b < tl ==> ?N. !j. N <= j ==> b < Tf (D j))
           ==> ?sub:num->num G. (!m n. m < n ==> sub m < sub n) /\ p3_std_flow g0 (&1) G /\
                                p3n_close_below g0 hs Phi ts Q (D o sub) tl G`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "125")))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `tl = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "125" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`] o
                    REWRITE_RULE[P2_THM_12_5_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `G:real->real^3->real^3^3` o CONJUNCT1) THEN
    MAP_EVERY EXISTS_TAC [`I:num->num`; `G:real->real^3->real^3^3`] THEN
    ASM_REWRITE_TAC[I_O_ID; I_THM] THEN
    MATCH_MP_TAC P3N_CLOSE_BELOW_0 THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`; `k:num->num`;
      `i:num->num`; `xi:num->real^3->real^3`; `tc:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `u:A->bool` P3N_LIMIT_STEP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `dl:num->real->real`;
    `\n. p3_hscale hf ((rp:num->real->real) n) ((dl:num->real->real) n)`;
    `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
    `Tf:num->real`; `D:num->num`; `tl:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                   `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                   `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`;
                   `Q:num->real`; `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
    REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sub:num->num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `G:real->real^3->real^3^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[p3n_close_below; o_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:real`; `K:real^3->bool`; `m:num`; `e:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `b:real`; `K:real^3->bool`; `m:num`; `e:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3N_TF_BOUNDS = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc ms th.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
     &0 <= th
     ==> !n. &0 <= p3n_tf g0 hs Phi ts Q tc ms th n /\ p3n_tf g0 hs Phi ts Q tc ms th n <= th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= min th (((tc:num->real) n - ts n) * (Q:num->real) n) /\
                min th ((tc n - ts n) * Q n) <= th` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < ((tc:num->real) n - ts n) * (Q:num->real) n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(hs:num->(A)rfs_history) n`; `(Phi:num->real^3->A) n`;
                 `(ts:num->real) n`; `(Q:num->real) n`; `&ms`;
                 `min th (((tc:num->real) n - ts n) * (Q:num->real) n)`] P3N_PTIME_FACTS) THEN
  ASM_REWRITE_TAC[p3n_tf] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let P3N_ENDPT = prove
 (`!u:A->bool.
     P2C_PROP_5_14_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_STD_EXTEND_STATEMENT /\ P2_THM_12_5_STATEMENT
     ==> !C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc
          (D:num->num) ms th theta tstar L R.
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
           &0 < eps /\ p3_modulus md /\ p3_std_initial g0 A0 /\ 0 < ms /\
           (!m n. m < n ==> D m < D n) /\ &0 < th /\ th < &1 /\
           &0 <= tstar /\ tstar < L /\ L <= th /\ &0 <= R /\
           (!b. &0 <= b /\ b < L
                ==> p3n_good g0 hs Phi ts Q (p3n_tf g0 hs Phi ts Q tc ms th) D b) /\
           (!b. b < tstar ==> ?N. !j. N <= j ==> b < p3n_tf g0 hs Phi ts Q tc ms th (D j)) /\
           (!b N. tstar < b ==> ?j. N <= j /\ p3n_tf g0 hs Phi ts Q tc ms th (D j) <= b)
           ==> ?D':num->num G.
                 (!m n. m < n ==> D' m < D' n) /\ p3_std_flow g0 (&1) G /\
                 (?Kc. !m. ?N. !j. N <= j
                     ==> p3n_gat g0 (hs (D' j)) (Phi (D' j)) (ts (D' j)) (Q (D' j))
                           (min (p3n_tf g0 hs Phi ts Q tc ms th (D' j)) theta) Kc m (&1)) /\
                 (!kk ep. &0 < ep
                     ==> ?N. !j s y. N <= j /\ &0 <= s /\
                                 s < min (p3n_tf g0 hs Phi ts Q tc ms th (D' j)) theta /\
                                 y IN cball(vec 0,R)
                                 ==> lck_dist2 kk (G s)
                                       (p3n_cfl (hs (D' j)) (Phi (D' j)) (ts (D' j))
                                                (Q (D' j)) s) y < ep)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast(butlast cs))) THEN
    LABEL_TAC "good" (el (length cs - 3) cs) THEN
    LABEL_TAC "below" (el (length cs - 2) cs) THEN LABEL_TAC "io" (last cs)) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `ms:num`; `th:real`] P3N_TF_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `ms:num`; `th:real`] P3N_TF_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Npos:num`) THEN
  ABBREV_TAC `Tf = p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th` THEN
  (* a subsequence along which Tf tends to tstar *)
  SUBGOAL_THEN `!i' N. ?j. N <= j /\ abs((Tf:num->real) ((D:num->num) j) - tstar) < inv(&i' + &1)`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i':num`; `N:num`] THEN
    SUBGOAL_THEN `&0 < inv(&i' + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "below" (MP_TAC o SPEC `tstar - inv(&i' + &1)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N2:num`)] THEN
    USE_THEN "io" (MP_TAC o SPECL [`tstar + inv(&i' + &1) / &2`; `N + N2:num`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `j:num` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP P3N_IO_SUBSEQ) THEN
  DISCH_THEN(X_CHOOSE_THEN `J1:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv"))) THEN
  SUBGOAL_THEN
   `!p:num->num. (!m n. m < n ==> p m < p n)
                 ==> !e. &0 < e ==> ?N. !j. N <= j
                        ==> abs((Tf:num->real) ((D:num->num) ((J1:num->num) (p j))) - tstar) < e`
  (LABEL_TAC "convp") THENL
   [GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&((p:num->num) j) + &1)` THEN
    USE_THEN "conv" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    MP_TAC(ISPEC `p:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (D:num->num) ((J1:num->num) m) < D (J1 n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= (J1:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the model flow at the level tstar *)
  FIRST_ASSUM(MP_TAC o MATCH_MP P3N_LIMIT_OR_START) THEN
  DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
    `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`;
    `(D:num->num) o (J1:num->num)`; `Tf:num->real`; `tstar:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `b:real` THEN STRIP_TAC THEN MATCH_MP_TAC P3N_GOOD_INHERIT THEN
      EXISTS_TAC `D:num->num` THEN CONJ_TAC THENL
       [USE_THEN "good" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P3N_ESUB_O THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `b:real` THEN DISCH_TAC THEN
      USE_THEN "below" (MP_TAC o C MP (ASSUME `b < tstar`) o SPEC `b:real`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `G:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `((D:num->num) o (J1:num->num)) o (sub:num->num) = (\j. D (J1 (sub j)))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n /\ n <= (sub:num->num) n` STRIP_ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
    MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:num->num. (!m n. m < n ==> p m < p n)
                             ==> (!m n. m < n ==> (D:num->num) (p m) < D (p n)) /\
                                 p3n_esub (\j. D (p j)) D`
  (LABEL_TAC "esub") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MP_TAC(ISPECL [`D:num->num`; `p:num->num`] P3N_ESUB_O) THEN
      ASM_REWRITE_TAC[o_DEF]];
    ALL_TAC] THEN
  ABBREV_TAC `b1 = (tstar + L) / &2` THEN
  SUBGOAL_THEN `tstar < b1 /\ b1 < L /\ &0 <= b1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:num->num. (!m n. m < n ==> p m < p n)
                 ==> p3n_good g0 (hs:num->(A)rfs_history) Phi ts Q Tf
                                       (\j. (D:num->num) (p j)) b1`
  (LABEL_TAC "goodp") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P3N_GOOD_INHERIT THEN
    EXISTS_TAC `D:num->num` THEN CONJ_TAC THENL
     [USE_THEN "good" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "esub" (MP_TAC o SPEC `p:num->num`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the ball for the window run *)
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `cball(vec 0:real^3,R + &2)`]
         P3N_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(X_CHOOSE_THEN `R1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `R1:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `mR:num`) THEN
  SUBGOAL_THEN `cball(vec 0:real^3,R + &2) SUBSET {x | p3_std_dist g0 x < &mR + &1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `R1:real` THEN ASM_SIMP_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* hypotheses of the window run along D o J1 o sub *)
  SUBGOAL_THEN `!m n. m < n ==> (D:num->num) ((J1:num->num) ((sub:num->num) m)) < D (J1 (sub n))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (J1:num->num) ((sub:num->num) m) < J1 (sub n)` ASSUME_TAC
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!b. &0 <= b /\ (b < tstar \/ b = &0)
                    ==> ?N. !j. N <= j ==> b < (Tf:num->real) ((D:num->num) ((J1:num->num)
                                                    ((sub:num->num) j)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
     [USE_THEN "below" (MP_TAC o C MP (ASSUME `b < tstar`) o SPEC `b:real`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[LE_TRANS];
      EXISTS_TAC `Npos:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[LE_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?CM N. !j. N <= j
         ==> p3n_gat g0 ((hs:num->(A)rfs_history) ((D:num->num) ((J1:num->num) ((sub:num->num) j))))
               ((Phi:num->real^3->A) (D (J1 (sub j)))) ((ts:num->real) (D (J1 (sub j))))
               ((Q:num->real) (D (J1 (sub j)))) ((Tf:num->real) (D (J1 (sub j)))) CM (mR + 2) (&1)`
  ASSUME_TAC THENL
   [USE_THEN "goodp" (MP_TAC o C MP (ASSUME `!m n. m < n ==> (J1:num->num) ((sub:num->num) m) <
                                                       J1 (sub n)`) o
                      BETA_RULE o SPEC `\j. (J1:num->num) ((sub:num->num) j)`) THEN
    REWRITE_TAC[p3n_good] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real` (MP_TAC o SPEC `mR + 2`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` ASSUME_TAC) THEN
    USE_THEN "convp" (MP_TAC o C MP (ASSUME `!m n. m < n ==> (sub:num->num) m < sub n`) o
                      SPEC `sub:num->num`) THEN
    DISCH_THEN(MP_TAC o SPEC `b1 - tstar`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `N1 + N2:num`] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3N_GAT_WEAKEN THEN
    MAP_EVERY EXISTS_TAC [`(Tf:num->real) ((D:num->num) ((J1:num->num) ((sub:num->num) j)))`;
                          `b1:real`] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the window run *)
  FIRST_ASSUM(MP_TAC o MATCH_MP P3N_RUN o CONJUNCT1 o CONJUNCT2 o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "P2C_HISTORY_REGULAR_STATEMENT"
                             with Failure _ -> false)) (concl th) && is_conj(concl th))) THEN
  DISCH_THEN(MP_TAC o BETA_RULE o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
    `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
    `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
    `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
    `tc:num->real`; `\j. (D:num->num) ((J1:num->num) ((sub:num->num) j))`;
    `G:real->real^3->real^3^3`; `tstar:real`; `Tf:num->real`; `mR:num`; `R:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `th:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "run"))) THEN
  MAP_EVERY EXISTS_TAC [`\j. (D:num->num) ((J1:num->num) ((sub:num->num) ((J:num->num) j)))`;
                        `G:real->real^3->real^3^3`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!m n. m < n ==> (sub:num->num) ((J:num->num) m) < sub (J n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    USE_THEN "goodp" (MP_TAC o SPEC `\j. (J1:num->num) ((sub:num->num) ((J:num->num) j))`) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[p3n_good] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN
    DISCH_TAC THEN X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `N1:num` o SPEC `m:num`) THEN
    USE_THEN "convp" (MP_TAC o SPEC `\j. (sub:num->num) ((J:num->num) j)`) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `b1 - tstar`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3N_GAT_WEAKEN THEN
    MAP_EVERY EXISTS_TAC
     [`(Tf:num->real) ((D:num->num) ((J1:num->num) ((sub:num->num) ((J:num->num) j))))`;
      `b1:real`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    MAP_EVERY X_GEN_TAC [`kk:num`; `ep:real`] THEN DISCH_TAC THEN
    USE_THEN "run" (MP_TAC o C MP (ASSUME `&0 < ep`) o SPECL [`kk:num`; `ep:real`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC)) THEN
    USE_THEN "convp" (MP_TAC o SPEC `\j. (sub:num->num) ((J:num->num) j)`) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `lam:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN ASM_REAL_ARITH_TAC]);;

let P3N_TOP = prove
 (`!u:A->bool.
     P2C_PROP_5_14_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_STD_EXTEND_STATEMENT /\ P2_THM_12_5_STATEMENT
     ==> !C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc
          (D:num->num) ms th theta R.
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
           &0 < eps /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           (!m n. m < n ==> D m < D n) /\ &0 <= theta /\ theta < th /\
           (!b. &0 <= b /\ b < th
                ==> p3n_good g0 hs Phi ts Q (p3n_tf g0 hs Phi ts Q tc ms th) D b) /\
           (!b. b < th ==> ?N. !j. N <= j ==> b < p3n_tf g0 hs Phi ts Q tc ms th (D j))
           ==> ?D':num->num G.
                 (!m n. m < n ==> D' m < D' n) /\ p3_std_flow g0 (&1) G /\
                 (?Kc. !m. ?N. !j. N <= j
                     ==> p3n_gat g0 (hs (D' j)) (Phi (D' j)) (ts (D' j)) (Q (D' j))
                           (min (p3n_tf g0 hs Phi ts Q tc ms th (D' j)) theta) Kc m (&1)) /\
                 (!kk ep. &0 < ep
                     ==> ?N. !j s y. N <= j /\ &0 <= s /\
                                 s < min (p3n_tf g0 hs Phi ts Q tc ms th (D' j)) theta /\
                                 y IN cball(vec 0,R)
                                 ==> lck_dist2 kk (G s)
                                       (p3n_cfl (hs (D' j)) (Phi (D' j)) (ts (D' j))
                                                (Q (D' j)) s) y < ep)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast cs)) THEN
    LABEL_TAC "good" (el (length cs - 2) cs) THEN LABEL_TAC "below" (last cs)) THEN
  ABBREV_TAC `Tf = p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3N_LIMIT_OR_START) THEN
  DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
    `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`;
    `D:num->num`; `Tf:num->real`; `th:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `G:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`\j. (D:num->num) ((sub:num->num) j)`; `G:real->real^3->real^3^3`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ABBREV_TAC `b2 = (theta + th) / &2` THEN
    SUBGOAL_THEN `theta < b2 /\ b2 < th /\ &0 <= b2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "b2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `p3n_good g0 (hs:num->(A)rfs_history) Phi ts Q Tf
                    (\j. (D:num->num) ((sub:num->num) j)) b2` MP_TAC THENL
     [MATCH_MP_TAC P3N_GOOD_INHERIT THEN EXISTS_TAC `D:num->num` THEN CONJ_TAC THENL
       [USE_THEN "good" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`D:num->num`; `sub:num->num`] P3N_ESUB_O) THEN
        ASM_REWRITE_TAC[o_DEF]];
      ALL_TAC] THEN
    REWRITE_TAC[p3n_good] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC P3N_GAT_WEAKEN THEN
    MAP_EVERY EXISTS_TAC
     [`(Tf:num->real) ((D:num->num) ((sub:num->num) j))`; `b2:real`] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`kk:num`; `ep:real`] THEN DISCH_TAC THEN
    UNDISCH_TAC `p3n_close_below g0 (hs:num->(A)rfs_history) Phi ts Q ((D:num->num) o sub) th
                   (G:real->real^3->real^3^3)` THEN
    REWRITE_TAC[p3n_close_below; o_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`theta:real`; `cball(vec 0:real^3,R)`; `kk:num`; `ep:real`]) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Ingredients of the extension step of Lemma 16.8.  The                     *)
(* curvature at a base time b0 below the level is O(Q) on every ball, with  *)
(* the constant K0 + 1 of a sectional bound K0 of the model G(b0)           *)
(* (P3N_EXT_BASE: closeness at b0 and P3N_BASE_RM); metric upper bounds on  *)
(* a ball from curvature bounds before the time and the time-0 comparison   *)
(* with g0 (P3N_EXT_METRIC: P2CV_QF_ALL, P2CV_QF_TIME0).                    *)
(* ========================================================================= *)

let P3N_EXT_BASE = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> !C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc (D:num->num)
          (G:real->real^3->real^3^3) tl b0 K0 (Tf:num->real).
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
           &0 < eps /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           (!m n. m < n ==> D m < D n) /\ p3_std_flow g0 (&1) G /\
           &0 <= b0 /\ (b0 < tl \/ b0 = &0) /\ b0 < &1 /\
           p3n_close_below g0 hs Phi ts Q D tl G /\ &0 <= K0 /\
           (!y u v. ~collinear {vec 0,u,v} ==> abs(lsectional (G b0) y u v) <= K0) /\
           (!m. ?K N. !j. N <= j
                  ==> p3n_gat g0 (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j)) (Tf (D j)) K m b0 /\
                      b0 < Tf (D j))
           ==> !m. ?N. !j y. N <= j /\ p3_std_dist g0 y < &m + &1
                      ==> p3_vrm (rfs_view (hs (D j))) (ts (D j) + b0 / Q (D j)) (Phi (D j) y)
                          <= (K0 + &1) * Q (D j)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast(butlast cs))) THEN
    ASSUME_TAC (el (length cs - 3) cs) THEN
    LABEL_TAC "sec" (el (length cs - 2) cs) THEN LABEL_TAC "gat" (last cs)) THEN
  X_GEN_TAC `m:num` THEN
  MP_TAC(SPEC `K0:real` P3N_BASE_RM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "brm"))) THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_std_flow; p3_partial_std]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < &m + &1} /\
                ~({x:real^3 | p3_std_dist g0 x < &m + &1} = {}) /\
                {x:real^3 | p3_std_dist g0 x < &m + &1} SUBSET
                cball(vec 0,p3s_rad_rinv g0 (&m + &1))` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&m + &1`] P3N_STD_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[OPEN_BALL; BALL_SUBSET_CBALL; BALL_EQ_EMPTY; REAL_NOT_LE] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&m + &1`] P3S_RINV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `p3s_rad_rho g0 (p3s_rad_rinv g0 (&m + &1)) = &m + &1` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[P3S_RHO_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `p3n_close_below g0 (hs:num->(A)rfs_history) Phi ts Q (D:num->num) tl
                 (G:real->real^3->real^3^3)` THEN
  REWRITE_TAC[p3n_close_below] THEN
  DISCH_THEN(MP_TAC o SPECL [`b0:real`; `cball(vec 0:real^3,p3s_rad_rinv g0 (&m + &1))`;
                             `2`; `eta pow 2`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_CBALL; REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "cl")) THEN
  USE_THEN "gat" (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N2:num` (LABEL_TAC "g")) o
                  SPEC `m:num`) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`] P3N_SEQ_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&m + &1`) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "par")) THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `N1 + N2 + N3:num` THEN MAP_EVERY X_GEN_TAC [`j:num`; `y:real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `n = (D:num->num) j` THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "g" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop (rfs_view ((hs:num->(A)rfs_history) n)) (ts n))
                  (rfs_vatlas (rfs_view (hs n)) (ts n)) {x | p3_std_dist g0 x < &m + &1}
                  ((Phi:num->real^3->A) n)` ASSUME_TAC THENL
   [USE_THEN "par" MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; EXPAND_TAC "n" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view ((hs:num->(A)rfs_history) n))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(hs:num->(A)rfs_history) n`; `(Phi:num->real^3->A) n`;
                 `(ts:num->real) n`; `(Q:num->real) n`; `(Tf:num->real) n`; `K:real`; `m:num`;
                 `b0:real`; `b0:real`] P3N_GAT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  USE_THEN "brm" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`{x:real^3 | p3_std_dist g0 x < &m + &1}`;
                        `(G:real->real^3->real^3^3) b0`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[];
    USE_THEN "cl" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o
                   SPECL [`j:num`; `b0:real`; `y:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
      SIMP_TAC[]]]);;

let P3N_EXT_METRIC = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> !C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc (D:num->num)
          m CM.
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
           &0 < eps /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           (!m n. m < n ==> D m < D n) /\ &0 <= CM
           ==> ?L N. &0 <= L /\
                 !j s y w.
                   N <= j /\ &0 < s /\ s <= &1 /\ p3_std_dist g0 y < &m + &1 /\
                   rfs_persists (rfs_view (hs (D j)))
                     (IMAGE (Phi (D j)) {x | p3_std_dist g0 x < &m + &1})
                     (ts (D j)) (ts (D j) + s / Q (D j)) /\
                   (!s' z. &0 <= s' /\ s' <= s /\
                           z IN IMAGE (Phi (D j)) {x | p3_std_dist g0 x < &m + &1}
                           ==> p3_vrm (rfs_view (hs (D j))) (ts (D j) + s' / Q (D j)) z
                               <= CM * Q (D j))
                   ==> w dot (p3n_cfl (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j)) s y ** w)
                       <= L * (w dot w)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2cv_hyp (\n. rfs_view ((hs:num->(A)rfs_history) ((D:num->num) n)))
             (\n. (Phi:num->real^3->A) (D n) (vec 0))
             (\n. (ts:num->real) (D n)) (\n. (Q:num->real) (D n)) {&0}
             (euclidean,open_set_atlas (:real^3)) g0 (vec 0)
             (\m. {x | p3_std_dist g0 x < &m + &1}) (\n. Phi (D n))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P3N_SEQ_HYP) THEN
    DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
      `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
      `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`;
      `D:num->num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K0 = {x:real^3 | p3_std_dist g0 x <= &m + &1}` THEN
  SUBGOAL_THEN `compact (K0:real^3->bool) /\ {x:real^3 | p3_std_dist g0 x < &m + &1} SUBSET K0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&m + &1`] P3N_STD_SUBLEVEL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[COMPACT_CBALL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) ((D:num->num) n))`;
                 `\n. (Phi:num->real^3->A) ((D:num->num) n) (vec 0)`;
                 `\n. (ts:num->real) ((D:num->num) n)`; `\n. (Q:num->real) ((D:num->num) n)`;
                 `{&0:real}`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `vec 0:real^3`;
                 `\m:num. {x:real^3 | p3_std_dist g0 x < &m + &1}`;
                 `\n. (Phi:num->real^3->A) ((D:num->num) n)`;
                 `K0:real^3->bool`] P2CV_QF_TIME0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "qf") o
             REWRITE_RULE[P2CV_P_PB; GSYM P3N_CFL_PB]) THEN
  MP_TAC(ISPECL [`open_set_atlas (:real^3)`; `g0:real^3->real^3^3`; `(:real^3)`;
                 `\x:real^3. x`; `K0:real^3->bool`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[P3N_OSA_IN; IMAGE_ID; SUBSET_UNIV; P2C_OPEN_SET_METRIC_LOCAL_UNIV] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `C0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g0b"))))) THEN
  MAP_EVERY EXISTS_TAC [`exp(&8 * CM) * &3 / &2 * C0`; `N1 + m:num`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `s:real`; `y:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN K0` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "qf" (MP_TAC o SPECL [`j:num`; `y:real^3`; `w:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  USE_THEN "g0b" (MP_TAC o C MP (ASSUME `(y:real^3) IN K0`) o SPECL [`y:real^3`; `w:real^3`]) THEN
  STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) ((D:num->num) n))`;
                 `\n. (Phi:num->real^3->A) ((D:num->num) n) (vec 0)`;
                 `\n. (ts:num->real) ((D:num->num) n)`; `\n. (Q:num->real) ((D:num->num) n)`;
                 `{&0:real}`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `vec 0:real^3`;
                 `\m:num. {x:real^3 | p3_std_dist g0 x < &m + &1}`;
                 `\n. (Phi:num->real^3->A) ((D:num->num) n)`; `m:num`; `j:num`] P2CV_HYP_ONE)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) ((D:num->num) j))`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `{x:real^3 | p3_std_dist g0 x < &m + &1}`; `(Phi:num->real^3->A) ((D:num->num) j)`;
                 `(ts:num->real) ((D:num->num) j)`; `(Q:num->real) ((D:num->num) j)`;
                 `&0`; `s:real`; `((:real^3),(\x:real^3. x))`; `CM:real`; `y:real^3`; `w:real^3`;
                 `s:real`; `&0`] P2CV_QF_ALL) THEN
  REWRITE_TAC[P3N_OSA_IN; P3N_OSA_CHART_IMAGE; P3N_CFL_LOCAL; P2CV_DIV_LZERO; REAL_ADD_RID;
              REAL_SUB_RZERO; REAL_LE_REFL; IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&8 * CM * s) <= exp(&8 * CM)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `CM * s <= CM * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `X = (w:real^3) dot (p3n_cfl ((hs:num->(A)rfs_history) ((D:num->num) j)) ((Phi:num->real^3->A) (D j))
                        ((ts:num->real) (D j)) ((Q:num->real) (D j)) (&0) y ** w)` THEN
  ABBREV_TAC `Y = (w:real^3) dot ((g0:real^3->real^3^3) y ** w)` THEN
  SUBGOAL_THEN `&0 <= X /\ X <= &3 / &2 * Y /\ Y <= C0 * ((w:real^3) dot w)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c0 * norm(w:real^3) pow 2 <= Y` THEN UNDISCH_TAC `Y <= C0 * norm(w:real^3) pow 2` THEN
    REWRITE_TAC[NORM_POW_2] THEN
    MP_TAC(ISPEC `w:real^3` DOT_POS_LE) THEN
    UNDISCH_TAC `abs(X - Y) <= inv(&2) * (Y:real)` THEN
    SUBGOAL_THEN `&0 <= c0 * ((w:real^3) dot w)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[DOT_POS_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&8 * CM) * X` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * Y` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P3N_EXT_CURV1 = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
         !(hs:(A)rfs_history) C eps r tc g0 Phi ts Q m b0 K0 K1 s.
           rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\ rfs_pinched (rfs_view hs) /\
           &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < r /\
           (!x t. &0 <= t /\ t < tc /\ x IN topspace(rfs_top_at hs t) /\
                  inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                  ==> p3_canon_at (rfs_view hs) C eps x t) /\
           &1 <= Q /\ inv(r pow 2) <= Q /\ &0 <= ts /\ &0 <= b0 /\ &0 <= K0 /\ &0 <= K1 /\
           (!s' y. &0 <= s' /\ s' < b0 /\ y IN IMAGE Phi {x | p3_std_dist g0 x < &m + &1}
                   ==> p3_vrm (rfs_view hs) (ts + s' / Q) y <= K0 * Q) /\
           (!y. y IN IMAGE Phi {x | p3_std_dist g0 x < &m + &1}
                ==> p3_vrm (rfs_view hs) (ts + b0 / Q) y <= K1 * Q) /\
           open_in (rfs_vtop (rfs_view hs) (ts + b0 / Q))
                   (IMAGE Phi {x | p3_std_dist g0 x < &m + &1}) /\
           &0 <= s /\ s <= b0 + inv(&16 * max C (&2) * (&6 * K1 + &1)) /\ ts + s / Q < tc /\
           rfs_persists (rfs_view hs) (IMAGE Phi {x | p3_std_dist g0 x < &m + &1})
                        ts (ts + s / Q)
           ==> !y. y IN IMAGE Phi {x | p3_std_dist g0 x < &m + &1}
                   ==> p3_vrm (rfs_view hs) (ts + s / Q) y <=
                       max K0 (&24 * K1 + &16 + &2 * exp(&4)) * Q`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3N_WINDOW_CURV) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "WC")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s < b0` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K0 * Q` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `K0:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&24 * K1 + &16 + &2 * exp(&4)) * Q` THEN CONJ_TAC THENL
   [USE_THEN "WC" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r:real`; `K1:real`;
      `IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < &m + &1}`; `ts + b0 / Q`; `Q:real`;
      `ts + s / Q`; `tc:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_LE_LADD] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_LE_LADD; real_div; GSYM REAL_ADD_RDISTRIB] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        MATCH_MP_TAC P2CV_PERSISTS_MONO THEN MAP_EVERY EXISTS_TAC [`ts:real`; `ts + s / Q`] THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        REWRITE_TAC[REAL_LE_ADDR] THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The extension step of Lemma 16.8 (P3N_EXTEND).                            *)
(* P3N_TF_FACTS: below the persistence time Tf the core ball persists and   *)
(* the real time stays below the cutoff tc.  P3N_EXT_PRE: the data at a     *)
(* base level b0 (b0 < L, or b0 = 0 from the cap curvature), namely         *)
(* b0 < Tf, the curvature on every ball up to b0 and openness of every ball *)
(* in the slice at b0.  P3N_EXT_CURV: curvature over the Lemma 11.2 window. *)
(* P3N_EXT_GOOD: goodness below the window end and the closeness end.       *)
(* ========================================================================= *)

let P3N_PERSISTS_REFL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a.
     rfs_persists V W a a`,
  REWRITE_TAC[P2C_VIEW_EXPAND] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `a < s /\ s <= a ==> F`)) THEN REWRITE_TAC[]);;

let P3N_TF_FACTS = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc ms th n s.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
     &0 <= th /\ &0 <= s /\ s < p3n_tf g0 hs Phi ts Q tc ms th n
     ==> rfs_persists (rfs_view (hs n)) (IMAGE (Phi n) {x | p3_std_dist g0 x < &ms})
                      (ts n) (ts n + s / Q n) /\
         ts n + s / Q n < tc n /\ s < th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc` THEN
  REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= min th (((tc:num->real) n - ts n) * (Q:num->real) n)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < ((tc:num->real) n - ts n) * (Q:num->real) n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(hs:num->(A)rfs_history) n`; `(Phi:num->real^3->A) n`;
                 `(ts:num->real) n`; `(Q:num->real) n`; `&ms`;
                 `min th (((tc:num->real) n - ts n) * (Q:num->real) n)`] P3N_PTIME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `s < p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th n` THEN
  REWRITE_TAC[p3n_tf] THEN DISCH_TAC THEN
  SUBGOAL_THEN `s < ((tc:num->real) n - ts n) * (Q:num->real) n /\ s < th` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `s / (Q:num->real) n < tc n - ts n` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LDIV_EQ]; REAL_ARITH_TAC]]);;

let P3N_EXT_PRE = prove
 (`!C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc (D:num->num) ms th
    L b0.
     p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\ &0 < eps /\
     p3_modulus md /\ p3_std_initial g0 A0 /\ 0 < ms /\ &0 < th /\
     (!m n. m < n ==> D m < D n) /\ &0 <= b0 /\ (b0 < L \/ b0 = &0) /\
     (!b. &0 <= b /\ b < L ==> p3n_good g0 hs Phi ts Q (p3n_tf g0 hs Phi ts Q tc ms th) D b) /\
     (!b. b < L ==> ?N. !j. N <= j ==> b < p3n_tf g0 hs Phi ts Q tc ms th (D j))
     ==> ?Kb. &0 <= Kb /\
         !m. ?K N. !j. N <= j
           ==> b0 < p3n_tf g0 hs Phi ts Q tc ms th (D j) /\
               p3n_gat g0 (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j))
                       (p3n_tf g0 hs Phi ts Q tc ms th (D j)) K m b0 /\
               (!s y. &0 <= s /\ s < b0 /\
                      y IN IMAGE (Phi (D j)) {x | p3_std_dist g0 x < &m + &1}
                      ==> p3_vrm (rfs_view (hs (D j))) (ts (D j) + s / Q (D j)) y
                          <= Kb * Q (D j)) /\
               open_in (rfs_vtop (rfs_view (hs (D j))) (ts (D j) + b0 / Q (D j)))
                       (IMAGE (Phi (D j)) {x | p3_std_dist g0 x < &m + &1})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast cs)) THEN
    LABEL_TAC "good" (el (length cs - 2) cs) THEN LABEL_TAC "below" (last cs)) THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < (Q:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                   `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                   `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`;
                   `Q:num->real`; `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `ms:num`; `th:real`] P3N_TF_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Npos:num` (LABEL_TAC "pos")) THEN
  ABBREV_TAC `Tf = p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th` THEN
  ASM_CASES_TAC `b0 = &0` THENL
   [(* base level 0: the curvature of the caps *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL] THEN
    X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                   `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                   `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`;
                   `Q:num->real`; `tc:num->real`] P3N_CAP_CURV0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&m + &1`) THEN
    DISCH_THEN(X_CHOOSE_THEN `CM:real` (X_CHOOSE_THEN `N1:num` (LABEL_TAC "cc"))) THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                   `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                   `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`;
                   `Q:num->real`; `tc:num->real`] P3N_SEQ_PARAM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&m + &1`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "par"))] THEN
    MAP_EVERY EXISTS_TAC [`CM:real`; `N1 + Npos + N3:num`] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `j <= (D:num->num) j` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "pos" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[p3n_gat] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID; P3N_PERSISTS_REFL] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "cc" (MP_TAC o SPECL [`(D:num->num) j`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`rfs_vtop (rfs_view ((hs:num->(A)rfs_history) ((D:num->num) j)))
                               ((ts:num->real) (D j))`;
                     `rfs_vatlas (rfs_view ((hs:num->(A)rfs_history) ((D:num->num) j)))
                                 ((ts:num->real) (D j))`;
                     `{x:real^3 | p3_std_dist g0 x < &m + &1}`; `(Phi:num->real^3->A) ((D:num->num) j)`]
                    GRGD_PARAM_FACTS) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                         `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                         `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`;
                         `i:num->num`; `Phi:num->real^3->A`; `xi:num->real^3->real^3`;
                         `ts:num->real`; `Q:num->real`; `tc:num->real`; `(D:num->num) j`]
                        P3N_SEQ_BASIC) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
          USE_THEN "par" MATCH_MP_TAC THEN ASM_ARITH_TAC];
        STRIP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* base level 0 < b0 < L: goodness at b0 *)
  SUBGOAL_THEN `b0 < L /\ &0 < b0` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "good" (MP_TAC o SPEC `b0:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3n_good] THEN DISCH_THEN(X_CHOOSE_THEN `Kg:real` (LABEL_TAC "kg")) THEN
  USE_THEN "below" (MP_TAC o C MP (ASSUME `b0 < L`) o SPEC `b0:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `Nb:num` (LABEL_TAC "nb")) THEN
  EXISTS_TAC `max Kg (&0)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN
  USE_THEN "kg" (X_CHOOSE_THEN `Ng:num` (LABEL_TAC "ng") o SPEC `m:num`) THEN
  MAP_EVERY EXISTS_TAC [`Kg:real`; `Ng + Nb:num`] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  USE_THEN "ng" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `b0 < (Tf:num->real) ((D:num->num) j)` ASSUME_TAC THENL
   [USE_THEN "nb" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kg * (Q:num->real) ((D:num->num) j)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `p3n_gat g0 ((hs:num->(A)rfs_history) ((D:num->num) j))
                     ((Phi:num->real^3->A) (D j)) ((ts:num->real) (D j)) ((Q:num->real) (D j))
                     ((Tf:num->real) (D j)) Kg m b0` THEN
      REWRITE_TAC[p3n_gat] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    UNDISCH_TAC `p3n_gat g0 ((hs:num->(A)rfs_history) ((D:num->num) j))
                   ((Phi:num->real^3->A) (D j)) ((ts:num->real) (D j)) ((Q:num->real) (D j))
                   ((Tf:num->real) (D j)) Kg m b0` THEN
    REWRITE_TAC[p3n_gat] THEN DISCH_THEN(MP_TAC o SPEC `b0:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) ((D:num->num) j))`;
                   `IMAGE ((Phi:num->real^3->A) ((D:num->num) j))
                          {x | p3_std_dist g0 x < &m + &1}`;
                   `(ts:num->real) ((D:num->num) j)`;
                   `(ts:num->real) ((D:num->num) j) + b0 / (Q:num->real) (D j)`;
                   `(ts:num->real) ((D:num->num) j) + b0 / (Q:num->real) (D j)`]
                  P2CV_PERSISTS_AT) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_ADDR] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; SIMP_TAC[]]]);;

(* The curvature on every ball over the window [0, b0 + wl] while the ball  *)
(* persists (wl the window of Lemma 11.2 for the base bound (K0 + 1) Q):    *)
(* the base bound from the model G at b0 (P3N_EXT_BASE) and Lemma 11.2      *)
(* (P3N_EXT_CURV1), uniformly in the ball.                                   *)

let P3N_EXT_CURV = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u /\ P2_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
         !C eps hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc (D:num->num)
          (G:real->real^3->real^3^3) ms th L b0 K0.
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ &1 < C /\
           p3_hfun C hf /\ &0 < eps /\ eps <= eps0 /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           &0 < r /\ 0 < ms /\ &0 < th /\
           (!m n. m < n ==> D m < D n) /\ p3_std_flow g0 (&1) G /\
           &0 <= b0 /\ (b0 < L \/ b0 = &0) /\ b0 < &1 /\
           p3n_close_below g0 hs Phi ts Q D L G /\ &0 <= K0 /\
           (!y u v. ~collinear {vec 0,u,v} ==> abs(lsectional (G b0) y u v) <= K0) /\
           (!b. &0 <= b /\ b < L
                ==> p3n_good g0 hs Phi ts Q (p3n_tf g0 hs Phi ts Q tc ms th) D b) /\
           (!b. b < L ==> ?N. !j. N <= j ==> b < p3n_tf g0 hs Phi ts Q tc ms th (D j))
           ==> ?Kx. &0 <= Kx /\
               !m. ?N. !j s.
                 N <= j /\ &0 <= s /\
                 s <= b0 + inv(&16 * max C (&2) * (&6 * (K0 + &1) + &1)) /\
                 ts (D j) + s / Q (D j) < tc (D j) /\
                 rfs_persists (rfs_view (hs (D j)))
                   (IMAGE (Phi (D j)) {x | p3_std_dist g0 x < &m + &1})
                   (ts (D j)) (ts (D j) + s / Q (D j))
                 ==> !y. y IN IMAGE (Phi (D j)) {x | p3_std_dist g0 x < &m + &1}
                         ==> p3_vrm (rfs_view (hs (D j))) (ts (D j) + s / Q (D j)) y
                             <= Kx * Q (D j)`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hreg") (MP_TAC o MATCH_MP P3N_EXT_CURV1)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C1")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast cs)) THEN
    LABEL_TAC "good" (el (length cs - 2) cs) THEN LABEL_TAC "below" (last cs)) THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `D:num->num`; `ms:num`; `th:real`; `L:real`; `b0:real`]
                P3N_EXT_PRE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pre"))) THEN
  USE_THEN "hreg" (MP_TAC o MATCH_MP P3N_EXT_BASE) THEN
  DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
    `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`; `D:num->num`;
    `G:real->real^3->real^3^3`; `L:real`; `b0:real`; `K0:real`;
    `p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN
    USE_THEN "pre" (X_CHOOSE_THEN `K:real` (X_CHOOSE_TAC `N:num`) o SPEC `m:num`) THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `N:num`] THEN ASM_SIMP_TAC[];
    DISCH_THEN(LABEL_TAC "base")] THEN
  EXISTS_TAC `max Kb (&24 * (K0 + &1) + &16 + &2 * exp(&4))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN
  USE_THEN "pre" (X_CHOOSE_THEN `Kp:real` (X_CHOOSE_THEN `N1:num` (LABEL_TAC "p1")) o
                  SPEC `m:num`) THEN
  USE_THEN "base" (X_CHOOSE_THEN `N2:num` (LABEL_TAC "b1") o SPEC `m:num`) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`] P3N_SEQ_Q_LARGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> X_CHOOSE_TAC `N3:num` (SPEC `&1` th) THEN
                       X_CHOOSE_TAC `N4:num` (SPEC `inv(r pow 2)` th)) THEN
  EXISTS_TAC `N1 + N2 + N3 + N4:num` THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `j <= (D:num->num) j` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "p1" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok ((hs:num->(A)rfs_history) ((D:num->num) j)) /\
                rfs_pinched (rfs_view (hs (D j))) /\ &0 <= (ts:num->real) (D j) /\
                p2c_regular_view (rfs_view (hs (D j)))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                   `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                   `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`;
                   `Q:num->real`; `tc:num->real`; `(D:num->num) j`] P3N_SEQ_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "hreg" (MATCH_MP_TAC o REWRITE_RULE[P2C_HISTORY_REGULAR_STATEMENT]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x t. &0 <= t /\ t < (tc:num->real) ((D:num->num) j) /\
                      x IN topspace(rfs_top_at ((hs:num->(A)rfs_history) (D j)) t) /\
                      inv(r pow 2) <= rfs_vscalar (rfs_view (hs (D j))) t x
                      ==> p3_canon_at (rfs_view (hs (D j))) C eps x t` ASSUME_TAC THENL
   [UNDISCH_TAC `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q
                         tc` THEN
    REWRITE_TAC[p3n_seq] THEN DISCH_THEN(MP_TAC o SPEC `(D:num->num) j`) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (Q:num->real) ((D:num->num) j) /\ inv(r pow 2) <= Q (D j)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE ((Phi:num->real^3->A) ((D:num->num) j)) {x | p3_std_dist g0 x < &m + &1}
        ==> p3_vrm (rfs_view ((hs:num->(A)rfs_history) (D j)))
                   ((ts:num->real) (D j) + b0 / (Q:num->real) (D j)) y
            <= (K0 + &1) * Q (D j)` ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "b1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K0 + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "C1" (MP_TAC o SPECL [`(hs:num->(A)rfs_history) ((D:num->num) j)`; `C:real`;
    `eps:real`; `r:real`; `(tc:num->real) ((D:num->num) j)`; `g0:real^3->real^3^3`;
    `(Phi:num->real^3->A) ((D:num->num) j)`; `(ts:num->real) ((D:num->num) j)`;
    `(Q:num->real) ((D:num->num) j)`; `m:num`; `b0:real`; `Kb:real`; `K0 + &1`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* Goodness at a level L' below the window end bw and below L1, the end of *)
(* the closeness of the core to the model G (P3N_RUN): for every ball m the *)
(* ball m + ms persists while s < min Tf (min bw L1) (P3N_BIG_PERSIST with  *)
(* the curvature from the window, the metric bound P3N_EXT_METRIC and the  *)
(* shell closeness), hence so does the ball m (P3N_PERSIST_SUB), with the  *)
(* curvature bound Kx.                                                      *)

let P3N_EXT_GOOD = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?epsb. &0 < epsb /\
         !eps. &0 < eps /\ eps <= epsb
           ==> ?dd0. &0 < dd0 /\
               !C hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc (D:num->num)
                (G:real->real^3->real^3^3) ms th d0 m0 dd Kx bw L1 L'.
                 p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
                 p3_modulus md /\ p3_std_initial g0 A0 /\
                 (!m n. m < n ==> D m < D n) /\ p3_std_flow g0 (&1) G /\
                 0 < ms /\ &0 < th /\ th < &1 /\
                 inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= &ms /\ &0 < dd /\ dd <= dd0 /\
                 (!t x. &0 <= t /\ t <= th /\
                        d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                        ==> lck_dist2 (rfs_kreg eps)
                              (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x
                            < dd pow 2) /\
                 &0 <= Kx /\
                 (!m. ?N. !j s.
                    N <= j /\ &0 <= s /\ s <= bw /\ ts (D j) + s / Q (D j) < tc (D j) /\
                    rfs_persists (rfs_view (hs (D j)))
                      (IMAGE (Phi (D j)) {x | p3_std_dist g0 x < &m + &1})
                      (ts (D j)) (ts (D j) + s / Q (D j))
                    ==> !y. y IN IMAGE (Phi (D j)) {x | p3_std_dist g0 x < &m + &1}
                            ==> p3_vrm (rfs_view (hs (D j))) (ts (D j) + s / Q (D j)) y
                                <= Kx * Q (D j)) /\
                 (?N. !j s y. N <= j /\ &0 <= s /\ s < p3n_tf g0 hs Phi ts Q tc ms th (D j) /\
                              s < bw /\ s < L1 /\ p3_std_dist g0 y < m0
                              ==> lck_dist2 (rfs_kreg eps) (G s)
                                    (p3n_cfl (hs (D j)) (Phi (D j)) (ts (D j)) (Q (D j)) s) y
                                  < dd pow 2) /\
                 &0 <= L' /\ L' < bw /\ L' < L1
                 ==> p3n_good g0 hs Phi ts Q (p3n_tf g0 hs Phi ts Q tc ms th) D L'`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "hreg") THEN
  X_CHOOSE_THEN `epsb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BP")) P3N_BIG_PERSIST THEN
  EXISTS_TAC `epsb:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "BP" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BP2"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC
      (map (fun i -> el i cs) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;15;18;19;20]) THEN
    LABEL_TAC "shell" (el 14 cs) THEN LABEL_TAC "curv" (el 16 cs) THEN
    X_CHOOSE_THEN `Ncl:num` (LABEL_TAC "cl") (el 17 cs)) THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 < &ms` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; REAL_OF_NUM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)`) THEN
    MESON_TAC[p3_std_flow; p3_partial_std];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s. &0 <= s /\ s < p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th n
          ==> rfs_persists (rfs_view (hs n)) (IMAGE (Phi n) {x | p3_std_dist g0 x < &ms})
                           (ts n) (ts n + s / Q n) /\
              ts n + s / Q n < tc n /\ s < th`
  (LABEL_TAC "tff") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P3N_TF_FACTS THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`; `k:num->num`;
      `i:num->num`; `xi:num->real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p3n_good] THEN EXISTS_TAC `Kx:real` THEN X_GEN_TAC `m:num` THEN
  ABBREV_TAC `M = m + ms:num` THEN
  SUBGOAL_THEN `m0 <= &M + &1 /\ &ms <= &M + &1 /\ &m + &1 <= &M + &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&0 <= &m` MP_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!R. &0 < R ==> open {x:real^3 | p3_std_dist g0 x < R} /\
                                ~({x:real^3 | p3_std_dist g0 x < R} = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `R:real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] P3N_STD_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `vec 0:real^3` THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "curv" (X_CHOOSE_THEN `NcM:num` (LABEL_TAC "cM") o SPEC `M:num`) THEN
  USE_THEN "curv" (X_CHOOSE_THEN `Ncm:num` (LABEL_TAC "cm") o SPEC `m:num`) THEN
  USE_THEN "hreg" (MP_TAC o MATCH_MP P3N_EXT_METRIC) THEN
  DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
    `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`; `D:num->num`;
    `M:num`; `Kx:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `LM:real` (X_CHOOSE_THEN `Nm:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "met")))) THEN
  USE_THEN "BP2" (MP_TAC o SPECL [`&6 * max Kx (&0)`;
                                  `max LM (p3s_rad_rinv g0 (&M + &1))`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BP3"))) THEN
  MP_TAC(SPEC `dl1:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ndl:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`] P3N_SEQ_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&M + &1`) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `Np:num` (LABEL_TAC "par"))] THEN
  EXISTS_TAC `NcM + Ncm + Nm + Ncl + Ndl + Np:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j <= (D:num->num) j` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `n = (D:num->num) j` THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `n:num`] P3N_SEQ_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `n:num` (REWRITE_RULE[p3n_seq] (ASSUME
    `p3n_seq (C,eps,hf,md,g0,A0,r) rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc`))) THEN
  STRIP_TAC THEN
  ABBREV_TAC `h = p3_hscale hf ((rp:num->real->real) n) ((dl:num->real->real) n)
                            ((ts:num->real) n)` THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view ((hs:num->(A)rfs_history) n))` ASSUME_TAC THENL
   [USE_THEN "hreg" (MATCH_MP_TAC o REWRITE_RULE[P2C_HISTORY_REGULAR_STATEMENT]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!jj. k n < jj /\ jj <= hs_count ((hs:num->(A)rfs_history) n)
         ==> rfs_surgery_ok (hs n) C eps ((dl:num->real->real) n)
               (p3_hscale hf ((rp:num->real->real) n) (dl n)) jj /\
             &0 < dl n (hs_time (hs n) jj) /\ dl n (hs_time (hs n) jj) <= dl1`
  ASSUME_TAC THENL
   [X_GEN_TAC `jj:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `ts n < hs_time ((hs:num->(A)rfs_history) n) jj` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `(ts:num->real) n`)) THEN
      MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) ((rp:num->real->real) n,(dl:num->real->real) n)
                   ((hs:num->(A)rfs_history) n)` THEN
    REWRITE_TAC[p3_struct] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `jj:num` o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "rfs_surgery_ok" with Failure _ -> false))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `hs_time ((hs:num->(A)rfs_history) n) jj` o check (fun th ->
        is_forall(concl th) && not (is_imp(snd(dest_forall(concl th))) = false) &&
        can (find_term (fun t -> try fst(dest_const t) = "real_lt" with Failure _ -> false))
            (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dl:num->real->real) n (ts n)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`(ts:num->real) n`;
                                      `hs_time ((hs:num->(A)rfs_history) n) jj`] o
          check (fun th -> length(fst(strip_forall(concl th))) = 2 &&
            can (find_term (fun t -> t = `(dl:num->real->real) n`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&Ndl)` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop (rfs_view ((hs:num->(A)rfs_history) n)) (ts n))
                  (rfs_vatlas (rfs_view (hs n)) (ts n)) {x | p3_std_dist g0 x < &M + &1}
                  ((Phi:num->real^3->A) n)` ASSUME_TAC THENL
   [USE_THEN "par" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `se = min (p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th n) (min bw L1)` THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s < se
        ==> rfs_persists (rfs_view ((hs:num->(A)rfs_history) n))
              (IMAGE ((Phi:num->real^3->A) n) {x | p3_std_dist g0 x < &ms})
              (ts n) (ts n + s / (Q:num->real) n)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "tff" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the hypotheses of P3N_BIG_PERSIST on (0, se) *)
  SUBGOAL_THEN
   `!s. &0 < s /\ s < se /\
        rfs_persists (rfs_view ((hs:num->(A)rfs_history) n))
          (IMAGE ((Phi:num->real^3->A) n) {x | p3_std_dist g0 x < &M + &1})
          (ts n) (ts n + s / (Q:num->real) n)
        ==> metric_field (:real^3) ((G:real->real^3->real^3^3) s) /\ &0 <= s /\ s < &1 /\
            (!y. p3_std_dist g0 y < m0
                 ==> lck_dist2 (rfs_kreg eps) (G s) (p3n_cfl (hs n) (Phi n) (ts n) (Q n) s) y
                     < dd pow 2) /\
            (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                 ==> lck_dist2 (rfs_kreg eps)
                       (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) (G s) x < dd pow 2) /\
            (!y. p3_std_dist g0 y < &M + &1
                 ==> mfd_scalar (rfs_vatlas (rfs_view (hs n)) (ts n + s / Q n))
                                (rfs_vmetric (rfs_view (hs n)) (ts n + s / Q n)) (Phi n y)
                     <= (&6 * max Kx (&0)) * Q n /\
                     norm y <= max LM (p3s_rad_rinv g0 (&M + &1)) /\
                     (!w. w dot (p3n_cfl (hs n) (Phi n) (ts n) (Q n) s y ** w) <=
                          max LM (p3s_rad_rinv g0 (&M + &1)) * (w dot w)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s < p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th n /\
                  s < bw /\ s < L1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "tff" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
    SUBGOAL_THEN `s < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!s' z. &0 <= s' /\ s' <= s /\
             z IN IMAGE ((Phi:num->real^3->A) n) {x | p3_std_dist g0 x < &M + &1}
             ==> p3_vrm (rfs_view ((hs:num->(A)rfs_history) n))
                        (ts n + s' / (Q:num->real) n) z <= Kx * Q n`
    (LABEL_TAC "vb") THENL
     [MAP_EVERY X_GEN_TAC [`s':real`; `z:A`] THEN STRIP_TAC THEN
      USE_THEN "tff" (MP_TAC o SPECL [`n:num`; `s':real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "cM" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o
                     SPECL [`j:num`; `s':real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
          MAP_EVERY EXISTS_TAC [`(ts:num->real) n`; `(ts:num->real) n + s / (Q:num->real) n`] THEN
          ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_LADD] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "cl" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o
                     SPECL [`j:num`; `s:real`; `y:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "shell" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `((Phi:num->real^3->A) n y) IN
                    IMAGE (Phi n) {x | p3_std_dist g0 x < &M + &1}` ASSUME_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `p3_vrm (rfs_view ((hs:num->(A)rfs_history) n)) (ts n + s / (Q:num->real) n)
               ((Phi:num->real^3->A) n y) <= Kx * Q n /\
        Phi n y IN topspace(rfs_vtop (rfs_view (hs n)) (ts n + s / Q n))`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "vb" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
          MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) n)`;
                         `IMAGE ((Phi:num->real^3->A) n) {x | p3_std_dist g0 x < &M + &1}`;
                         `(ts:num->real) n`; `(ts:num->real) n + s / (Q:num->real) n`;
                         `(ts:num->real) n + s / (Q:num->real) n`] P2CV_PERSISTS_AT) THEN
          ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_ADDR] THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
          STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC P3N_SCAL_FROM_VRM THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        SUBGOAL_THEN `(y:real^3) IN ball(vec 0,p3s_rad_rinv g0 (&M + &1))` MP_TAC THENL
         [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&M + &1`] P3N_STD_BALL) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC];
        X_GEN_TAC `w:real^3` THEN
        USE_THEN "met" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o
                        SPECL [`j:num`; `s:real`; `y:real^3`; `w:real^3`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s < se
        ==> rfs_persists (rfs_view ((hs:num->(A)rfs_history) n))
              (IMAGE ((Phi:num->real^3->A) n) {x | p3_std_dist g0 x < &M + &1})
              (ts n) (ts n + s / (Q:num->real) n)`
  (LABEL_TAC "bigp") THENL
   [USE_THEN "BP3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`C:real`; `eps:real`; `(dl:num->real->real) n`;
      `p3_hscale hf ((rp:num->real->real) n) (dl n)`; `(k:num->num) n`; `A0:real`; `h:real`;
      `m0:real`; `&ms`; `d0:real`; `dd:real`; `G:real->real^3->real^3^3`; `\s:real. s`;
      `&0`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; P2CV_DIV_LZERO; REAL_ADD_RID; P3N_PERSISTS_REFL];
    ALL_TAC] THEN
  (* goodness of the ball m at L' *)
  REWRITE_TAC[p3n_gat] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s < se` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "tff" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_persists (rfs_view ((hs:num->(A)rfs_history) n))
                  (IMAGE ((Phi:num->real^3->A) n) {x | p3_std_dist g0 x < &m + &1})
                  (ts n) (ts n + s / (Q:num->real) n)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) n)`; `euclidean:(real^3)topology`;
                   `open_set_atlas (:real^3)`; `{x:real^3 | p3_std_dist g0 x < &M + &1}`;
                   `(Phi:num->real^3->A) n`; `(ts:num->real) n`; `(Q:num->real) n`; `s:real`;
                   `{x:real^3 | p3_std_dist g0 x < &m + &1}`] P3N_PERSIST_SUB) THEN
    REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3N_ONE_FROM_PARAM THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open" with Failure _ -> false))
            (concl th))) THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      USE_THEN "bigp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM OPEN_IN] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&m + &1` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open" with Failure _ -> false))
            (concl th))) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "cm" (MP_TAC o REWRITE_RULE[ASSUME `(D:num->num) j = n`] o
                 SPECL [`j:num`; `s:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]; SIMP_TAC[]]);;

(* The extension step of Lemma 16.8: if the cap sequence is good below a  *)
(* level L < th and its persistence times stay eventually above every      *)
(* b < L, an eventual subsequence is good up to some L' > L.  The model G  *)
(* at L (P3N_LIMIT_OR_START), its sectional bound Ks on [0, th], the base  *)
(* b0 = max 0 (L - wl/2) with the Lemma 11.2 window wl for the base bound  *)
(* (Ks + 1) Q, the curvature over [0, b0 + wl] (P3N_EXT_CURV), closeness   *)
(* of the core up to L + lam (P3N_RUN) and goodness at L' (P3N_EXT_GOOD).  *)

let P3N_EXTEND = prove
 (`!u:A->bool.
     P2C_PROP_5_14_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_STD_EXTEND_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_LEMMA_11_2_STATEMENT u
     ==> ?eps1. &0 < eps1 /\
         !eps. &0 < eps /\ eps <= eps1
           ==> ?dd0. &0 < dd0 /\
               !C hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc
                (D:num->num) ms mr th d0 m0 dd L.
                 p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ &1 < C /\
                 p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\ &0 < r /\
                 (!m n. m < n ==> D m < D n) /\ &0 < th /\ th < &1 /\
                 inv eps < d0 /\ d0 + inv eps < m0 /\ &0 < dd /\ dd <= dd0 /\ ms = mr + 3 /\
                 m0 <= &ms /\
                 cball(vec 0,p3s_rad_rinv g0 m0 + &2) SUBSET
                 {x | p3_std_dist g0 x < &mr + &1} /\
                 (!G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t <= th /\
                          d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                          ==> lck_dist2 (rfs_kreg eps)
                                (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x
                              < dd pow 2) /\
                 &0 <= L /\ L < th /\
                 (!b. &0 <= b /\ b < L
                      ==> p3n_good g0 hs Phi ts Q (p3n_tf g0 hs Phi ts Q tc ms th) D b) /\
                 (!b. b < L ==> ?N. !j. N <= j ==> b < p3n_tf g0 hs Phi ts Q tc ms th (D j))
                 ==> ?D':num->num L'.
                       p3n_esub D' D /\ L < L' /\ L' <= th /\
                       p3n_good g0 hs Phi ts Q (p3n_tf g0 hs Phi ts Q tc ms th) D' L'`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "route" (end_itlist CONJ [el 0 cs; el 1 cs; el 2 cs; el 3 cs]) THEN
    LABEL_TAC "hreg" (el 1 cs) THEN LABEL_TAC "l112" (el 4 cs)) THEN
  USE_THEN "hreg" (fun hr -> USE_THEN "l112" (fun l2 ->
    X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EC"))
      (MATCH_MP P3N_EXT_CURV (CONJ hr l2)))) THEN
  USE_THEN "hreg" (X_CHOOSE_THEN `epsb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EG")) o
                   MATCH_MP P3N_EXT_GOOD) THEN
  EXISTS_TAC `min eps0 epsb` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  USE_THEN "EG" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EG2"))) THEN
  EXISTS_TAC `dd0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC
      (map (fun i -> el i cs) [0;1;2;3;4;5;6;7;8;9;10;11;12;14;15;17;18]) THEN
    MP_TAC (el 13 cs) THEN
    LABEL_TAC "shell" (el 16 cs) THEN LABEL_TAC "good" (el 19 cs) THEN
    LABEL_TAC "below" (el 20 cs)) THEN
  DISCH_THEN(fun th -> SUBGOAL_THEN `0 < (ms:num) /\ &(mr + 2) + &1 = &ms` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[th; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC]) THEN
  SUBGOAL_THEN `!n. n <= (D:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 < m0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the model flow at L along a subsequence *)
  USE_THEN "route" (MP_TAC o MATCH_MP P3N_LIMIT_OR_START) THEN
  DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
    `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`;
    `D:num->num`; `p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `G:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `p3n_close_below g0 (hs:num->(A)rfs_history) Phi ts Q
                  (\j. (D:num->num) ((sub:num->num) j)) L (G:real->real^3->real^3^3)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\j. (D:num->num) ((sub:num->num) j)) = D o sub` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (D:num->num) ((sub:num->num) m) < D (sub n)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `!m n. m < n ==> (D:num->num) m < D n`) THEN
    MP_TAC(ASSUME `!m n. m < n ==> (sub:num->num) m < sub n`) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)`) THEN
    MESON_TAC[p3_std_flow; p3_partial_std];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!b. &0 <= b /\ b < L
         ==> p3n_good g0 (hs:num->(A)rfs_history) Phi ts Q (p3n_tf g0 hs Phi ts Q tc ms th)
                      (\j. (D:num->num) ((sub:num->num) j)) b) /\
    (!b. b < L ==> ?N. !j. N <= j ==> b < p3n_tf g0 hs Phi ts Q tc ms th (D (sub j)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `b:real` THEN STRIP_TAC THEN MATCH_MP_TAC P3N_GOOD_INHERIT THEN
      EXISTS_TAC `D:num->num` THEN CONJ_TAC THENL
       [USE_THEN "good" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`D:num->num`; `sub:num->num`] P3N_ESUB_O) THEN
        ASM_REWRITE_TAC[o_DEF]];
      X_GEN_TAC `b:real` THEN DISCH_TAC THEN
      USE_THEN "below" (MP_TAC o C MP (ASSUME `b < L`) o SPEC `b:real`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the constants *)
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `G:real->real^3->real^3^3`; `th:real`] P3N_STD_SEC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ks:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sec"))) THEN
  ABBREV_TAC `wl = inv(&16 * max C (&2) * (&6 * (Ks + &1) + &1))` THEN
  SUBGOAL_THEN `&0 < wl` ASSUME_TAC THENL
   [EXPAND_TAC "wl" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `b0 = max (&0) (L - wl / &2)` THEN
  SUBGOAL_THEN `&0 <= b0 /\ b0 <= L /\ L <= b0 + wl / &2 /\ b0 < &1 /\ b0 <= th`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "b0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b0 < L \/ b0 = &0` ASSUME_TAC THENL
   [EXPAND_TAC "b0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y u v. ~collinear {vec 0,u,v}
                        ==> abs(lsectional ((G:real->real^3->real^3^3) b0) y u v) <= Ks`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the curvature over the window *)
  USE_THEN "EC" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
    `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`;
    `\j. (D:num->num) ((sub:num->num) j)`; `G:real->real^3->real^3^3`; `ms:num`; `th:real`;
    `L:real`; `b0:real`; `Ks:real`]) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kx:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))) THEN
  (* facts on the persistence times *)
  SUBGOAL_THEN
   `!n s. &0 <= s /\ s < p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th n
          ==> rfs_persists (rfs_view (hs n)) (IMAGE (Phi n) {x | p3_std_dist g0 x < &ms})
                           (ts n) (ts n + s / Q n) /\
              ts n + s / Q n < tc n /\ s < th`
  (LABEL_TAC "tff") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P3N_TF_FACTS THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`; `k:num->num`;
      `i:num->num`; `xi:num->real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `ms:num`; `th:real`] P3N_TF_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Npos:num` (LABEL_TAC "pos")) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `ms:num`; `th:real`] P3N_TF_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the radius of the closeness ball *)
  ABBREV_TAC `R = p3s_rad_rinv g0 m0` THEN
  SUBGOAL_THEN `&0 <= R /\ {x:real^3 | p3_std_dist g0 x < m0} SUBSET cball(vec 0,R)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m0:real`] P3N_STD_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BALL_SUBSET_CBALL] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m0:real`] P3S_RINV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the window run of the core up to L + lam *)
  USE_THEN "hreg" (MP_TAC o MATCH_MP P3N_RUN) THEN
  DISCH_THEN(MP_TAC o BETA_RULE o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
    `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
    `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
    `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
    `tc:num->real`; `\j. (D:num->num) ((sub:num->num) j)`; `G:real->real^3->real^3^3`;
    `L:real`; `\n. min (p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th n) (b0 + wl)`;
    `mr:num`; `R:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC(REAL_ARITH `a <= th /\ th < &1 ==> min a b <= &1`) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `b:real` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
       [USE_THEN "below" (MP_TAC o C MP (ASSUME `b < L`) o SPEC `b:real`) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN
          ASM_REWRITE_TAC[];
          ASM_REAL_ARITH_TAC];
        EXISTS_TAC `Npos:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
         [USE_THEN "pos" MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
          EXISTS_TAC `(sub:num->num) j` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
          ASM_REAL_ARITH_TAC]];
      EXISTS_TAC `Kx:real` THEN
      USE_THEN "curv" (X_CHOOSE_THEN `Nc:num` (LABEL_TAC "c2") o SPEC `mr + 2:num`) THEN
      EXISTS_TAC `Nc:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[p3n_gat; REAL_LT_MIN] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "tff" (MP_TAC o SPECL [`(D:num->num) ((sub:num->num) j)`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "c2" (MP_TAC o SPECL [`j:num`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "run"))) THEN
  SUBGOAL_THEN `&0 < dd pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "run" (MP_TAC o C MP (ASSUME `&0 < dd pow 2`) o
                  SPECL [`rfs_kreg eps`; `dd pow 2`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "close")))) THEN
  SUBGOAL_THEN `!n. n <= (J:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the new level and the subsequence *)
  ABBREV_TAC `L' = min th (L + min (wl / &4) (lam / &2))` THEN
  SUBGOAL_THEN `L < L' /\ L' <= th /\ &0 <= L' /\ L' < b0 + wl /\ L' < L + lam`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "L'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\j. (D:num->num) ((sub:num->num) ((J:num->num) j))`; `L':real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`D:num->num`; `\j. (sub:num->num) ((J:num->num) j)`] P3N_ESUB_O) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ASSUME `!m n. m < n ==> (sub:num->num) m < sub n`) THEN
    MP_TAC(ASSUME `!m n. m < n ==> (J:num->num) m < J n`) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (D:num->num) ((sub:num->num) ((J:num->num) m)) < D (sub (J n))`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `!m n. m < n ==> (D:num->num) m < D n`) THEN
    MP_TAC(ASSUME `!m n. m < n ==> (sub:num->num) m < sub n`) THEN
    MP_TAC(ASSUME `!m n. m < n ==> (J:num->num) m < J n`) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t x. &0 <= t /\ t <= th /\
                      d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                      ==> lck_dist2 (rfs_kreg eps)
                            (mpullback (p3_std_nc g0 A0) (cylinder_flow t))
                            ((G:real->real^3->real^3^3) t) x < dd pow 2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "shell" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ?N. !j s.
      N <= j /\ &0 <= s /\ s <= b0 + wl /\
      (ts:num->real) ((D:num->num) ((sub:num->num) ((J:num->num) j))) +
        s / (Q:num->real) (D (sub (J j))) < (tc:num->real) (D (sub (J j))) /\
      rfs_persists (rfs_view ((hs:num->(A)rfs_history) (D (sub (J j)))))
        (IMAGE ((Phi:num->real^3->A) (D (sub (J j)))) {x | p3_std_dist g0 x < &m + &1})
        (ts (D (sub (J j)))) (ts (D (sub (J j))) + s / Q (D (sub (J j))))
      ==> !y. y IN IMAGE (Phi (D (sub (J j)))) {x | p3_std_dist g0 x < &m + &1}
              ==> p3_vrm (rfs_view (hs (D (sub (J j))))) (ts (D (sub (J j))) + s / Q (D (sub (J j))))
                         y <= Kx * Q (D (sub (J j)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN USE_THEN "curv" (X_CHOOSE_TAC `N:num` o SPEC `m:num`) THEN
    EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`j:num`; `s:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `N:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?N. !j s y. N <= j /\ &0 <= s /\
                s < p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th
                      ((D:num->num) ((sub:num->num) ((J:num->num) j))) /\
                s < b0 + wl /\ s < L + lam /\ p3_std_dist g0 y < m0
                ==> lck_dist2 (rfs_kreg eps) ((G:real->real^3->real^3^3) s)
                      (p3n_cfl (hs (D (sub (J j)))) ((Phi:num->real^3->A) (D (sub (J j))))
                               ((ts:num->real) (D (sub (J j)))) ((Q:num->real) (D (sub (J j))))
                               s) y
                    < dd pow 2` ASSUME_TAC THENL
   [EXISTS_TAC `N1:num` THEN MAP_EVERY X_GEN_TAC [`j:num`; `s:real`; `y:real^3`] THEN
    STRIP_TAC THEN USE_THEN "close" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    UNDISCH_TAC `{x:real^3 | p3_std_dist g0 x < m0} SUBSET cball(vec 0,R)` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "EG2" (MP_TAC o BETA_RULE o SPECL [`C:real`; `hf:real->real->real`;
    `md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
    `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
    `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
    `tc:num->real`; `\j. (D:num->num) ((sub:num->num) ((J:num->num) j))`;
    `G:real->real^3->real^3^3`; `ms:num`; `th:real`; `d0:real`; `m0:real`; `dd:real`;
    `Kx:real`; `b0 + wl`; `L + lam`; `L':real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* ========================================================================= *)
(* Lemma 16.8 in sequence form.  P3N_FINISH2: the output of                  *)
(* P3N_ENDPT / P3N_TOP (a subsequence, a standard flow G, goodness and     *)
(* closeness on a ball before min Tf theta) gives the conclusion of Prop    *)
(* 16.5 for some history (P3N_FINISH).  P3N_SEQ_CONCL: for every cap       *)
(* sequence (p3n_seq) some history satisfies the conclusion: saturation of *)
(* goodness (level L), the persistence level T* of the core ball, and the   *)
(* three cases T* < L (P3N_ENDPT), L = th <= T* (P3N_TOP) and T* >= L with  *)
(* L < th (P3N_EXTEND contradicts the maximality of L).                     *)
(* ========================================================================= *)

let P3N_FINISH2 = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?epsd. &0 < epsd /\
         !eps. &0 < eps /\ eps <= epsd
           ==> ?dd0. &0 < dd0 /\
               !C hf md g0 A0 r rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc
                A theta dcl th ms d0 m0 dd R.
                 p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc /\ p3_hfun C hf /\
                 p3_modulus md /\ p3_std_initial g0 A0 /\
                 &0 < A /\ A < &ms /\ &0 < theta /\ theta < th /\ th < &1 /\ &0 < dcl /\
                 inv eps < d0 /\ d0 + inv eps < m0 /\ m0 <= &ms /\ &0 < dd /\ dd <= dd0 /\
                 (!G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t <= th /\
                          d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                          ==> lck_dist2 (rfs_kreg eps)
                                (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x
                              < dd pow 2) /\
                 (!y. p3_std_dist g0 y < A ==> y IN cball(vec 0,R)) /\
                 (!y. p3_std_dist g0 y < m0 ==> y IN cball(vec 0,R)) /\
                 (?D':num->num G.
                    (!m n. m < n ==> D' m < D' n) /\ p3_std_flow g0 (&1) G /\
                    (?Kc. !m. ?N. !j. N <= j
                        ==> p3n_gat g0 (hs (D' j)) (Phi (D' j)) (ts (D' j)) (Q (D' j))
                              (min (p3n_tf g0 hs Phi ts Q tc ms th (D' j)) theta) Kc m (&1)) /\
                    (!kk ep. &0 < ep
                        ==> ?N. !j s y. N <= j /\ &0 <= s /\
                                    s < min (p3n_tf g0 hs Phi ts Q tc ms th (D' j)) theta /\
                                    y IN cball(vec 0,R)
                                    ==> lck_dist2 kk (G s)
                                          (p3n_cfl (hs (D' j)) (Phi (D' j)) (ts (D' j))
                                                   (Q (D' j)) s) y < ep))
                 ==> ?n G. p3_std_flow g0 (&1) G /\
                           p3n_concl g0 A theta dcl (hs n) (k n) (Phi n) (ts n)
                                     (p3_hscale hf (rp n) (dl n) (ts n)) (tc n) G`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3N_FINISH) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `epsd:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  USE_THEN "F" (MP_TAC o C MP (ASSUME `&0 < eps /\ eps <= epsd`) o SPEC `eps:real`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `dd0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F2")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast(butlast(butlast cs)))) THEN
    LABEL_TAC "shell" (el (length cs - 4) cs) THEN
    LABEL_TAC "inA" (el (length cs - 3) cs) THEN LABEL_TAC "inm" (el (length cs - 2) cs) THEN
    X_CHOOSE_THEN `D':num->num` (X_CHOOSE_THEN `G:real->real^3->real^3^3`
      (fun th2 -> let ds = CONJUNCTS th2 in
         ASSUME_TAC (el 0 ds) THEN ASSUME_TAC (el 1 ds) THEN
         ASSUME_TAC (el 2 ds) THEN LABEL_TAC "cl" (el 3 ds))) (last cs)) THEN
  USE_THEN "F2" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
    `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`; `D':num->num`;
    `G:real->real^3->real^3^3`; `A:real`; `theta:real`; `dcl:real`; `th:real`; `ms:num`;
    `d0:real`; `m0:real`; `dd:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "shell" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "cl" (MP_TAC o SPECL [`rfs_kreg eps`; `dd pow 2`]) THEN
      ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "inm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "cl" (MP_TAC o SPECL [`rfs_kreg dcl`; `dcl pow 2 / &4`]) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "inA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `G:real->real^3->real^3^3`] THEN ASM_REWRITE_TAC[]]);;

let P3N_SEQ_CONCL = prove
 (`!u:A->bool.
     P2C_PROP_5_14_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_STD_EXTEND_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_LEMMA_11_2_STATEMENT u /\
     P2_PROP_12_7_STATEMENT
     ==> ?eps2. &0 < eps2 /\
         !C eps hf md g0 A0 r A dcl theta rp dl (hs:num->(A)rfs_history) k i Phi xi ts Q tc.
           &1 < C /\ &0 < eps /\ eps <= eps2 /\ p3_hfun C hf /\ p3_modulus md /\
           p3_std_initial g0 A0 /\ &0 < r /\ &0 < A /\ &0 < dcl /\ &0 < theta /\ theta < &1 /\
           p3n_seq (C,eps,hf,md,g0,A0,r) rp dl hs k i Phi xi ts Q tc
           ==> ?n G. p3_std_flow g0 (&1) G /\
                     p3n_concl g0 A theta dcl (hs n) (k n) (Phi n) (ts n)
                               (p3_hscale hf (rp n) (dl n) (ts n)) (tc n) G`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "r4" (end_itlist CONJ [el 0 cs; el 1 cs; el 2 cs; el 3 cs]) THEN
    LABEL_TAC "r5" (end_itlist CONJ [el 0 cs; el 1 cs; el 2 cs; el 3 cs; el 4 cs]) THEN
    LABEL_TAC "hreg" (el 1 cs) THEN LABEL_TAC "r127" (el 5 cs)) THEN
  USE_THEN "hreg" (X_CHOOSE_THEN `epsf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fin")) o
                   MATCH_MP P3N_FINISH2) THEN
  USE_THEN "r5" (X_CHOOSE_THEN `epse:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "xtd")) o
                 MATCH_MP P3N_EXTEND) THEN
  EXISTS_TAC `min epsf epse` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "fin" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ddf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fin2"))) THEN
  USE_THEN "xtd" (MP_TAC o SPEC `eps:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dde:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "xtd2"))) THEN
  (* the constants *)
  ABBREV_TAC `th = (&1 + theta) / &2` THEN
  SUBGOAL_THEN `theta < th /\ th < &1 /\ &0 < th` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `dd = min (min ddf dde) eps` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= ddf /\ dd <= dde /\ dd <= eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "r127" (MP_TAC o MATCH_MP P3N_SHELL_CLOSE) THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `th:real`; `eps:real`; `dd:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh"))) THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 < A0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3S_A0_POS THEN EXISTS_TAC `g0:real^3->real^3^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `d0 = A1 + inv eps + &1` THEN
  ABBREV_TAC `m0 = d0 + inv eps + &1` THEN
  SUBGOAL_THEN `inv eps < d0 /\ d0 + inv eps < m0 /\ A1 + inv eps <= d0 /\ &0 < m0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m0"; "d0"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t <= th /\
            d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
            ==> lck_dist2 (rfs_kreg eps) (mpullback (p3_std_nc g0 A0) (cylinder_flow t))
                          (G t) x < dd pow 2`
  (LABEL_TAC "shell") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sh" MATCH_MP_TAC THEN EXISTS_TAC `d0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the radii *)
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`;
                `cball(vec 0:real^3,p3s_rad_rinv g0 m0 + &2)`] P3N_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `R2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R2"))) THEN
  MP_TAC(SPEC `R2 + A + m0` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `mr:num`) THEN
  SUBGOAL_THEN `cball(vec 0:real^3,p3s_rad_rinv g0 m0 + &2) SUBSET
                {x | p3_std_dist g0 x < &mr + &1}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `R2:real` THEN CONJ_TAC THENL
     [USE_THEN "R2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `ms = mr + 3:num` THEN
  SUBGOAL_THEN `m0 <= &ms /\ A < &ms /\ 0 < ms` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ms" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD; ARITH_RULE `0 < mr + 3:num`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Am = max A m0` THEN
  SUBGOAL_THEN `&0 < Am /\ A <= Am /\ m0 <= Am` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Am" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `R = p3s_rad_rinv g0 Am` THEN
  SUBGOAL_THEN `&0 <= R /\ !y:real^3. p3_std_dist g0 y < Am ==> y IN cball(vec 0,R)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `Am:real`] P3S_RINV) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN {x | p3_std_dist g0 x < Am}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `Am:real`] P3N_STD_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y:real^3. p3_std_dist g0 y < A ==> y IN cball(vec 0,R)) /\
                (!y:real^3. p3_std_dist g0 y < m0 ==> y IN cball(vec 0,R))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* saturation of goodness *)
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `hs:num->(A)rfs_history`; `Phi:num->real^3->A`;
                 `ts:num->real`; `Q:num->real`;
                 `p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th`; `th:real`;
                 `I:num->num`] P3N_GOOD_SATURATE) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; REWRITE_TAC[I_O_ID]] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:num->num` (X_CHOOSE_THEN `L:real` (fun th ->
    let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC [el 0 cs; el 1 cs; el 2 cs] THEN
    LABEL_TAC "good" (el 3 cs) THEN LABEL_TAC "max" (el 4 cs)))) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`;
                 `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`;
                 `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`;
                 `tc:num->real`; `ms:num`; `th:real`] P3N_TF_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the persistence level T* *)
  MP_TAC(ISPECL [`\s:num->num. \b:real. ?N. !j. N <= j
                     ==> b < p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th (s j)`;
                 `th:real`; `D:num->num`] P3N_TSUP_FACTS) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `tstar = p3n_tsup (\s:num->num. \b:real. ?N. !j. N <= j
                        ==> b < p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th (s j))
                      th D` THEN
  BETA_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN ASSUME_TAC (el 1 cs) THEN
    LABEL_TAC "tsup" (el 2 cs) THEN LABEL_TAC "tsdown" (el 3 cs)) THEN
  SUBGOAL_THEN
   `!b. b < tstar
        ==> ?N. !j. N <= j
                    ==> b < p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th ((D:num->num) j)`
  (LABEL_TAC "bts") THENL
   [X_GEN_TAC `b:real` THEN DISCH_TAC THEN ASM_CASES_TAC `&0 <= b` THENL
     [USE_THEN "tsdown" MP_TAC THEN ANTS_TAC THENL
       [MAP_EVERY X_GEN_TAC [`b1:real`; `b2:real`] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `N:num`) ASSUME_TAC) THEN
        EXISTS_TAC `N:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `b1:real` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `N:num`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `0` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b N. tstar < b
          ==> ?j. N <= j /\
                  p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th ((D:num->num) j) <= b`
  (LABEL_TAC "io") THENL
   [MAP_EVERY X_GEN_TAC [`b:real`; `N:num`] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`;
                                         REAL_NOT_LE]) THEN
    SUBGOAL_THEN `b < th` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `p3n_tf g0 (hs:num->(A)rfs_history) Phi ts Q tc ms th ((D:num->num) N)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `N:num`)) (concl th))) THEN
        REWRITE_TAC[LE_REFL];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "tsup" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `tstar < L` THENL
   [(* case T* < L: the endpoint T* *)
    USE_THEN "fin2" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
      `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
      `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`; `A:real`;
      `theta:real`; `dcl:real`; `th:real`; `ms:num`; `d0:real`; `m0:real`; `dd:real`;
      `R:real`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "r4" (MP_TAC o MATCH_MP P3N_ENDPT) THEN
    DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
      `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
      `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`; `D:num->num`;
      `ms:num`; `th:real`; `theta:real`; `tstar:real`; `L:real`; `R:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `L:real = th` THENL
   [(* case L = th <= T*: the top *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "fin2" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
      `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
      `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`; `A:real`;
      `theta:real`; `dcl:real`; `th:real`; `ms:num`; `d0:real`; `m0:real`; `dd:real`;
      `R:real`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "r4" (MP_TAC o MATCH_MP P3N_TOP) THEN
    DISCH_THEN(MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
      `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
      `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`; `D:num->num`;
      `ms:num`; `th:real`; `theta:real`; `R:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        X_GEN_TAC `b:real` THEN DISCH_TAC THEN USE_THEN "bts" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* case T* >= L, L < th: the extension contradicts the maximality of L *)
  USE_THEN "xtd2" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `rp:num->real->real`; `dl:num->real->real`;
    `hs:num->(A)rfs_history`; `k:num->num`; `i:num->num`; `Phi:num->real^3->A`;
    `xi:num->real^3->real^3`; `ts:num->real`; `Q:num->real`; `tc:num->real`; `D:num->num`;
    `ms:num`; `mr:num`; `th:real`; `d0:real`; `m0:real`; `dd:real`; `L:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `b:real` THEN DISCH_TAC THEN USE_THEN "bts" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D':num->num` (X_CHOOSE_THEN `L':real` STRIP_ASSUME_TAC)) THEN
  USE_THEN "max" (MP_TAC o SPECL [`D':num->num`; `L':real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `L' <= L ==> ~(L < L')`)) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* MT Prop 16.5 with the cutoff tc, from the sequence form P3N_SEQ_CONCL by  *)
(* contradiction: if no d0 works, choose for d0 = 1/(n+1) a history          *)
(* violating the conclusion; these form a cap sequence (p3n_seq) for which   *)
(* P3N_SEQ_CONCL gives a history satisfying it.  The statement is the body   *)
(* of P3_PROP_16_5_STATEMENT (bound variable dd2 written dcl).               *)
(* ========================================================================= *)

let P3N_PROP_16_5_TC = prove
 (`!u:A->bool.
     P2C_PROP_5_14_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u /\
     P2_STD_EXTEND_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_LEMMA_11_2_STATEMENT u /\
     P2_PROP_12_7_STATEMENT
     ==> ?eps165. &0 < eps165 /\
         !C eps hf md g0 A0 r A dcl theta.
           &1 < C /\ &0 < eps /\ eps <= eps165 /\
           p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           &0 < r /\ &0 < A /\ &0 < dcl /\ &0 < theta /\ theta < &1
           ==> ?d0. &0 < d0 /\
                 !rp dl (hs:(A)rfs_history) k i Phi xi ts h tc.
                    p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ tc <= rfs_horizon hs /\
                    (!t x. &0 <= t /\ t < tc /\ x IN topspace(rfs_top_at hs t) /\
                           inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                           ==> p3_canon_at (rfs_view hs) C eps x t) /\
                    1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
                    ts = hs_time hs k /\ ts < tc /\ h = p3_hscale hf rp dl ts /\
                    p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i Phi xi /\
                    dl ts <= d0 /\ rp ts <= eps
                    ==> ?G. p3_std_flow g0 (&1) G /\
                        (p3_view_close
                          (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                         {s | &0 <= s /\ s < &1} G)
                          (&0) (&1) {x | p3_std_dist g0 x < A}
                          (rfs_view hs) ts (inv(h pow 2)) Phi
                          {s | &0 <= s /\ s < theta /\ ts + s * h pow 2 <= tc /\
                               ts + s * h pow 2 < rfs_horizon hs} dcl \/
                        ?k'. k < k' /\ k' <= hs_count hs /\ hs_time hs k' <= tc /\
                             hs_time hs k' < ts + theta * h pow 2 /\
                             p3_view_close
                               (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                              {s | &0 <= s /\ s < &1} G)
                               (&0) (&1) {x | p3_std_dist g0 x < A}
                               (rfs_view hs) ts (inv(h pow 2)) Phi
                               {s | &0 <= s /\ ts + s * h pow 2 < hs_time hs k'} dcl /\
                             DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < A})
                                      (topspace(hs_top hs k')))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3N_SEQ_CONCL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps2:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SC")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[SKOLEM_THM] o
             REWRITE_RULE[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`; NOT_FORALL_THM; NOT_IMP] o
             GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `rp:num->real->real` (X_CHOOSE_THEN `dl:num->real->real`
    (X_CHOOSE_THEN `hs:num->(A)rfs_history` (X_CHOOSE_THEN `k:num->num`
    (X_CHOOSE_THEN `i:num->num` (X_CHOOSE_THEN `Phi:num->real^3->A`
    (X_CHOOSE_THEN `xi:num->real^3->real^3` (X_CHOOSE_THEN `ts:num->real`
    (X_CHOOSE_THEN `h:num->real` (X_CHOOSE_THEN `tc:num->real` (LABEL_TAC "cx"))))))))))) THEN
  USE_THEN "SC" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `r:real`; `A:real`; `dcl:real`; `theta:real`;
    `rp:num->real->real`; `dl:num->real->real`; `hs:num->(A)rfs_history`; `k:num->num`;
    `i:num->num`; `Phi:num->real^3->A`; `xi:num->real^3->real^3`; `ts:num->real`;
    `\n. inv((h:num->real) n pow 2)`; `tc:num->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[p3n_seq] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "cx" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      MAP_EVERY ASSUME_TAC (map (fun i -> el i cs) [0;1;2;3;4;5;7;9;10;11]) THEN
      ASSUME_TAC (SYM (el 6 cs)) THEN ASSUME_TAC (SYM (el 8 cs))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `G:real->real^3->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[p3n_concl])))) THEN
  USE_THEN "cx" (MP_TAC o SPEC `n:num`) THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MP_TAC (SPEC `G:real->real^3->real^3^3` (REWRITE_RULE[NOT_EXISTS_THM] (last cs))) THEN
    SUBST1_TAC (SYM (el 8 cs))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* ========================================================================= *)
(* The route theorem for Prop 16.5 (P3_PROP_16_5_ROUTE_STATEMENT).           *)
(* ========================================================================= *)

let P3N_PROP_16_5_ROUTE = prove
 (`!u:A->bool. P3_PROP_16_5_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_16_5_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  REWRITE_TAC[P3_PROP_16_5_STATEMENT] THEN
  MP_TAC(ISPEC `u:A->bool` P3N_PROP_16_5_TC) THEN ASM_REWRITE_TAC[]);;

