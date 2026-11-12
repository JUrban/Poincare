(* ========================================================================= *)
(* Unit pc_p3_c172v: MT Lemma 17.2 for the                                  *)
(* canonv neighbourhoods (strong canonical neighbourhoods whose C-component *)
(* alternative carries the volume clause p3_comp_vol, KL 69.1 (c)).  The   *)
(* first-bad-time argument needs the canonv condition to be open forward in *)
(* time: the volume clause persists on boxes of a slab (curvature bound on  *)
(* compact time intervals, the metric comparison of RFU_FLOW_EQUIV, volume  *)
(* comparison), the static neighbourhoods persist with their type, and the  *)
(* neck case is part D, as for the plain form.  The c172a first-bad-time    *)
(* machinery is restated for p3_canonv_at.                                  *)
(*                                                                         *)
(* Numeric margin of the volume clause.                                    *)
(* ========================================================================= *)

needs "src/pc_p3_c172x.ml";;
needs "src/pc_p3_c17curv.ml";;
needs "src/pc_rf_unique_a14.ml";;

prioritize_real();;
type_invention_error := true;;

let P3H_CUBE_LOW = prove
 (`!t. &0 <= t /\ t <= &1 ==> &1 - &3 * t <= (&1 - t) pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (t * t) * (&3 - t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(&1 - t) pow 3 = &1 - &3 * t + (t * t) * (&3 - t) /\ &0 <= (t * t) * (&3 - t)
    ==> &1 - &3 * t <= (&1 - t) pow 3`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3H_VOL_MARGIN_LOW = prove
 (`!v R C. &0 < R /\ &0 < C /\ inv C * inv(sqrt R) pow 3 < v
     ==> ?t. &0 < t /\ t <= &1 / &10 /\
             !dl a. &0 <= dl /\ dl <= t /\ &0 <= a /\ a <= t * R
                    ==> (&1 + dl) * sqrt(&1 + dl) * (inv C * inv(sqrt(R - a)) pow 3) < v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt R /\ &0 < inv C` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < v` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv C * inv(sqrt R) pow 3` THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv C < v * sqrt R pow 3` ASSUME_TAC THENL
   [UNDISCH_TAC `inv C * inv(sqrt R) pow 3 < v` THEN
    REWRITE_TAC[REAL_POW_INV; GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT];
    ALL_TAC] THEN
  ABBREV_TAC `M = inv C pow 2` THEN
  ABBREV_TAC `N = v pow 2 * R pow 3` THEN
  SUBGOAL_THEN `M < N /\ &0 <= M` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN EXPAND_TAC "N" THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `v pow 2 * R pow 3 = (v * sqrt R pow 3) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ARITH_RULE `6 = 2 * 3`; GSYM REAL_POW_POW] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t. &0 < t /\ t <= &1 / &10 /\ t * (&4 * M + &3 * N) < N - M`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &8 * (N + M) + &1 /\ &0 < N - M` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `min (&1 / &10) ((N - M) / (&8 * (N + M) + &1))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    CONJ_TAC THENL [CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_DIV]]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(N - M) / (&8 * (N + M) + &1) * (&4 * M + &3 * N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a / b * c = (a * c) / b`] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`dl:real`; `a:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t * R <= &1 / &10 * R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) * R <= R - a /\ &0 < R - a /\ &0 <= (&1 - t) * R`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(R - a) /\ &0 < &1 + dl /\ &0 <= sqrt(&1 + dl)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + dl) * sqrt(&1 + dl) * (inv C * inv(sqrt(R - a)) pow 3) =
                ((&1 + dl) * sqrt(&1 + dl) * inv C) / sqrt(R - a) pow 3` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT] THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + dl) * sqrt(&1 + dl) * inv C) pow 2 = (&1 + dl) pow 3 * M /\
                (v * sqrt(R - a) pow 3) pow 2 = v pow 2 * (R - a) pow 3`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `6 = 2 * 3`; GSYM REAL_POW_POW] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + dl) pow 3 <= &1 + &4 * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &4 * dl` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BC_CUBE_BOUND THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - &3 * t) * R pow 3 <= (R - a) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((&1 - t) * R) pow 3` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN MATCH_MP_TAC P3H_CUBE_LOW THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 + &4 * t) * M` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `v pow 2 * (&1 - &3 * t) * R pow 3` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `t * (&4 * M + &3 * N) < N - M` THEN EXPAND_TAC "N" THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]);;

(* ========================================================================= *)
(* The scalar curvature stays above a strict lower bound on a                *)
(* box (twin of P3H_SCALAR_BOX), the volume of a compact set at later times *)
(* of a slab, and the persistence of the volume clause on a box.            *)
(* ========================================================================= *)

let P3H_SCALAR_BOX_GT = prove
 (`!(hs:(A)rfs_history) k ts x c.
     rfs_history_ok hs /\ k <= hs_count hs /\
     hs_time hs k <= ts /\ ts < hs_time hs (k + 1) /\ x IN topspace(hs_top hs k) /\
     c < mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x
     ==> ?N d. open_in (hs_top hs k) N /\ x IN N /\ &0 < d /\
               !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N
                     ==> c < mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `top = hs_top (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `atlas = hs_atlas (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `g = hs_metric (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `b = hs_time (hs:(A)rfs_history) (k + 1)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ts:real`;
                 `b:real`; `g:real->A->real^3^3`] RFA_MFD_SCALAR_CONTINUOUS_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `hs_time (hs:(A)rfs_history) k`; `b:real`; `g:real->A->real^3^3`;
                     `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC RFA_RICCI_FLOW_FROM_EXT_AT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `hs_time (hs:(A)rfs_history) k`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_map; SUBTOPOLOGY_TOPSPACE] THEN
  DISCH_THEN(MP_TAC o SPEC `{r:real | c < r}` o CONJUNCT2) THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; REWRITE_RULE[real_gt] REAL_OPEN_HALFSPACE_GT] THEN
  REWRITE_TAC[OPEN_IN_PROD_TOPOLOGY_ALT] THEN
  DISCH_THEN(MP_TAC o SPECL [`ts:real`; `x:A`]) THEN
  REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real->bool` (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_SUBTOPOLOGY] o check (fun th ->
    can (find_term (fun t -> t = `u:real->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open_in euclideanreal (w:real->bool)` THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `ts:real`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`v:A->bool`; `e:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `(u:real->bool) CROSS (v:A->bool)`)) (concl th))) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:real->bool) = w INTER {t | ts <= t /\ t < b}` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* The volume of a compact set at later times of a slab: at least           *)
(* v0 / (1 + dl)^(3/2) for s in [ts, ts + d) (metric comparison from the    *)
(* curvature bound on [ts, (ts + T_(k+1))/2], RFU_FLOW_EQUIV).               *)

let P3H_VOL_BOX = prove
 (`!(hs:(A)rfs_history) k ts U v0 dl.
     rfs_history_ok hs /\ k <= hs_count hs /\
     hs_time hs k <= ts /\ ts < hs_time hs (k + 1) /\
     compact_in (hs_top hs k) U /\
     mfd_has_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k ts) U v0 /\ &0 < dl
     ==> ?d. &0 < d /\
             !s. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1)
                 ==> ?v. mfd_has_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k s) U v /\
                         v0 <= (&1 + dl) * sqrt(&1 + dl) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `top = hs_top (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `atlas = hs_atlas (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `g = hs_metric (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `b = hs_time (hs:(A)rfs_history) (k + 1)` THEN
  SUBGOAL_THEN `ricci_flow_from (top:A topology,atlas) ts b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`hs_time (hs:(A)rfs_history) k`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ts:real`; `b:real`;
                 `(ts + b) / &2`; `g:real->A->real^3^3`] P3H_RF_RM_BOUND_COMPACT_TIME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC (INST_TYPE [`:3`,`:N`] RFU_FLOW_EQUIV) THEN
  ABBREV_TAC `K = abs B` THEN
  SUBGOAL_THEN `&0 <= K /\ &0 <= C0 * K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. &0 < m /\ m <= &1 /\ m <= dl` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1) dl` THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * (C0 * K) + &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ d <= (b - ts) / &2 /\ (&4 * (C0 * K) + &4) * d <= m`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min ((b - ts) / &2) (m / (&4 * (C0 * K) + &4))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    CONJ_TAC THENL [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_DIV]]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&4 * (C0 * K) + &4) * (m / (&4 * (C0 * K) + &4))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exp(&2 * (C0 * K) * d) <= &1 + dl` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (C0 * K) * d` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * (C0 * K) * d <= m / &2` ASSUME_TAC THENL
     [UNDISCH_TAC `(&4 * (C0 * K) + &4) * d <= m` THEN UNDISCH_TAC `&0 < d` THEN
      UNDISCH_TAC `&0 <= (C0 * K) * d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * (&2 * (C0 * K) * d)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 <= (C0 * K) * d` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `&2 * (C0 * K) * d <= m / &2` THEN UNDISCH_TAC `m <= &1` THEN
        REAL_ARITH_TAC];
      UNDISCH_TAC `&2 * (C0 * K) * d <= m / &2` THEN UNDISCH_TAC `m <= dl` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `ts:real`; `b:real`; `g:real->A->real^3^3`; `ts + d`; `K:real`] o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "exp"))
                                          (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`t:real`; `z:A`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "K" THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(ts + d) - ts = d`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) ts) /\
                riemannian_metric atlas (g s)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ts:real`;
                   `b:real`; `g:real->A->real^3^3`; `ts:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ts:real`;
                   `b:real`; `g:real->A->real^3^3`; `s:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) s`; `U:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_COMPARE_QF THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `(g:real->A->real^3^3) ts`; `(g:real->A->real^3^3) s`; `U:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:A`; `w:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `compact_in top (U:A->bool)` THEN REWRITE_TAC[compact_in] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 <= w dot ((g:real->A->real^3^3) s y ** w)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) s`; `y:A`] GEOG_G_SYM_POS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `compact_in top (U:A->bool)` THEN
      REWRITE_TAC[compact_in] THEN ASM SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&2 * (C0 * K) * d) * (w dot ((g:real->A->real^3^3) s y ** w))` THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `&2 * (C0 * K) * d` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
    UNDISCH_TAC `exp(--(&2 * (C0 * K) * d)) * (w dot ((g:real->A->real^3^3) ts y ** w)) <=
                 w dot (g s y ** w)` THEN
    REWRITE_TAC[REAL_EXP_NEG] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(&2 * (C0 * K) * d) *
                (inv(exp(&2 * (C0 * K) * d)) * (w dot ((g:real->A->real^3^3) ts y ** w)))` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

let P3H_INV_SQRT_CUBE_MONO = prove
 (`!r1 r2. &0 < r1 /\ r1 <= r2 ==> inv(sqrt r2) pow 3 <= inv(sqrt r1) pow 3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]]);;

let P3H_COMP_VOL_BOX = prove
 (`!(hs:(A)rfs_history) k ts x U C.
     rfs_history_ok hs /\ k <= hs_count hs /\
     hs_time hs k <= ts /\ ts < hs_time hs (k + 1) /\ x IN topspace(hs_top hs k) /\
     &0 < C /\ &0 < mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x /\
     compact_in (hs_top hs k) U /\
     (?v. mfd_has_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k ts) U v /\
          inv C * inv(sqrt(mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x)) pow 3 < v)
     ==> ?N d. open_in (hs_top hs k) N /\ x IN N /\ &0 < d /\
               !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N
                     ==> ?v. mfd_has_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k s) U v /\
                             inv C * inv(sqrt(mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y))
                                     pow 3 < v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC))))))))) THEN
  ABBREV_TAC `R0 = mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k ts) x` THEN
  MP_TAC(SPECL [`v0:real`; `R0:real`; `C:real`] P3H_VOL_MARGIN_LOW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MG")))) THEN
  SUBGOAL_THEN `&0 < t * R0` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`; `x:A`; `R0 - t * R0`]
                P3H_SCALAR_BOX_GT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SB")))))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`; `U:A->bool`; `v0:real`; `t:real`]
                P3H_VOL_BOX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "VB"))) THEN
  MAP_EVERY EXISTS_TAC [`N:A->bool`; `min d1 d2`] THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  REMOVE_THEN "VB" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vs:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `vs:real` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Ry = mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k s) y` THEN
  SUBGOAL_THEN `R0 - t * R0 < Ry` ASSUME_TAC THENL
   [EXPAND_TAC "Ry" THEN REMOVE_THEN "SB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?a. &0 <= a /\ a <= t * R0 /\ R0 - a <= Ry /\ &0 < R0 - a` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `R0 <= Ry` THENL
     [EXISTS_TAC `&0` THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `R0 - Ry` THEN
      SUBGOAL_THEN `t * R0 <= &1 / &10 * R0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "MG" (MP_TAC o SPECL [`t:real`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (&1 + t) * sqrt(&1 + t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `inv C * inv(sqrt(R0 - a)) pow 3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC P3H_INV_SQRT_CUBE_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + t) * sqrt(&1 + t)) * (inv C * inv(sqrt(R0 - a)) pow 3) <
                ((&1 + t) * sqrt(&1 + t)) * vs` MP_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `v0:real` THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ]]);;

(* ========================================================================= *)
(* Static neighbourhoods persist with their type (the proof of              *)
(* P3H_STATIC_PERSIST, pc_p3_c172b, with a type-preserving conclusion), and *)
(* the static canonv neighbourhoods are open forward in time.               *)
(* ========================================================================= *)

let P3H_STATIC_PERSIST3 = prove
 (`?eps0. &0 < eps0 /\ eps0 <= &1 / &8 /\
     !top atlas (g:real->A->real^3^3) a b ts C eps x U.
       hausdorff_space top /\ compact_space top /\ ricci_flow_from (top,atlas) a b g /\
       a <= ts /\ ts < b /\ &1 < C /\ &0 < eps /\ eps <= eps0 /\
       &0 < mfd_scalar atlas (g ts) x
       ==> ((?Y. rfs_cap (top,atlas) (g ts) C eps U Y /\ x IN Y)
            ==> ?N eta. open_in top N /\ x IN N /\ N SUBSET U /\ &0 < eta /\
                        !s y. ts <= s /\ s < ts + eta /\ s < b /\ y IN N
                              ==> ?Y. rfs_cap (top,atlas) (g s) C eps U Y /\ y IN Y) /\
           ((x IN U /\ rfs_c_component (top,atlas) (g ts) C U)
            ==> ?N eta. open_in top N /\ x IN N /\ N SUBSET U /\ &0 < eta /\
                        !s y. ts <= s /\ s < ts + eta /\ s < b /\ y IN N
                              ==> y IN U /\ rfs_c_component (top,atlas) (g s) C U) /\
           ((x IN U /\ rfs_round_component (top,atlas) (g ts) eps U)
            ==> ?N eta. open_in top N /\ x IN N /\ N SUBSET U /\ &0 < eta /\
                        !s y. ts <= s /\ s < ts + eta /\ s < b /\ y IN N
                              ==> y IN U /\ rfs_round_component (top,atlas) (g s) eps U)`,
  MP_TAC(ISPECL [`(:A)`; `(:A)`] P2B_PROP_9_79_OPEN_TYPED) THEN
  REWRITE_TAC[P2B_PROP_9_79_OPEN_TYPED_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "cap"))))
    (CONJUNCTS_THEN2 (LABEL_TAC "ccomp") (LABEL_TAC "round")))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) ts)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `ts:real`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. ts <= s /\ s < b
                    ==> riemannian_metric atlas ((g:real->A->real^3^3) s) /\
                        mfd_complete (top,atlas) (g s)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `s:real`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BL_COMPACT_COMPLETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = mfd_scalar atlas ((g:real->A->real^3^3) ts) x` THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THENL
   [(* cap *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) ts`; `C:real`; `eps:real`; `U:A->bool`;
                   `Y:A->bool`] APX_CAP_CORE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_cap]; ALL_TAC] THEN
    USE_THEN "cap" (MP_TAC o SPECL [`C:real`; `eps:real`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) ts`; `x:A`;
      `U:A->bool`; `Y:A->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `ts:real`; `Q:real`;
                   `U:A->bool`; `delta:real`] P3H_SLAB_MCLOSE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`Y:A->bool`; `eta:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[P2B_CAP_CORE_SUBSET]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    EXISTS_TAC `Y:A->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `(g:real->A->real^3^3) s`; `\x:A. x`; `\x:A. x`] o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
    REWRITE_TAC[IMAGE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MFD_DIFFEO_ID];
    (* C-component *)
    SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`]
                    P3H_MFD_COMPONENT_OPEN) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[rfs_c_component]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(U:A->bool) IN connected_components_of top` ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_c_component]; ALL_TAC] THEN
    USE_THEN "ccomp" (MP_TAC o SPECL [`C:real`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) ts`; `x:A`;
      `U:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `ts:real`; `Q:real`;
                   `U:A->bool`; `delta:real`] P3H_SLAB_MCLOSE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `eta:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `(g:real->A->real^3^3) s`; `\x:A. x`; `\x:A. x`] o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
    REWRITE_TAC[IMAGE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MFD_DIFFEO_ID];
    (* round component *)
    SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`]
                    P3H_MFD_COMPONENT_OPEN) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[rfs_round_component]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(U:A->bool) IN connected_components_of top` ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_round_component]; ALL_TAC] THEN
    USE_THEN "round" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) ts`; `x:A`;
      `U:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `ts:real`; `Q:real`;
                   `U:A->bool`; `delta:real`] P3H_SLAB_MCLOSE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `eta:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `(g:real->A->real^3^3) s`; `\x:A. x`; `\x:A. x`] o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
    REWRITE_TAC[IMAGE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MFD_DIFFEO_ID]]);;

let P3H_OPEN_STATIC_HIST_V = prove
 (`?eps0. &0 < eps0 /\
     !(hs:(A)rfs_history) C eps k ts x U.
       rfs_history_ok hs /\ k <= hs_count hs /\
       hs_time hs k <= ts /\ ts < hs_time hs (k + 1) /\
       &1 < C /\ &0 < eps /\ eps <= eps0 /\
       &0 < mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x /\
       ((?Y. rfs_cap (hs_top hs k,hs_atlas hs k) (hs_metric hs k ts) C eps U Y /\ x IN Y) \/
        (x IN U /\ rfs_c_component (hs_top hs k,hs_atlas hs k) (hs_metric hs k ts) C U /\
         (?v. mfd_has_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k ts) U v /\
              inv C * inv(sqrt(mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x)) pow 3 < v)) \/
        (x IN U /\ rfs_round_component (hs_top hs k,hs_atlas hs k) (hs_metric hs k ts) eps U))
       ==> ?N d. open_in (hs_top hs k) N /\ x IN N /\ &0 < d /\
                 !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N
                       ==> p3_canonv_at (rfs_view hs) C eps y s`,
  MP_TAC(INST_TYPE [`:A`,`:A`] P3H_STATIC_PERSIST3) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pers")))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "pers" (MP_TAC o SPECL
    [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
     `hs_metric (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) k`;
     `hs_time (hs:(A)rfs_history) (k + 1)`; `ts:real`; `C:real`; `eps:real`; `x:A`;
     `U:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PC") (CONJUNCTS_THEN2 (LABEL_TAC "PK")
    (LABEL_TAC "PR"))) THEN
  SUBGOAL_THEN
   `!s. hs_time hs k <= s /\ s < hs_time (hs:(A)rfs_history) (k + 1)
        ==> rfs_top_at hs s = hs_top hs k /\ rfs_atlas_at hs s = hs_atlas hs k /\
            rfs_metric_at hs s = hs_metric hs k s`
  (LABEL_TAC "SL") THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) o
    check (is_disj o concl)) THENL
   [REMOVE_THEN "PC" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N:A->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "SL" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[p3_canonv_at; p3_strong_canonv] THEN EXISTS_TAC `U:A->bool` THEN
    DISJ2_TAC THEN DISJ1_TAC THEN
    ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "PK" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N0:A->bool` (X_CHOOSE_THEN `d0:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K0"))))))) THEN
    SUBGOAL_THEN `compact_in (hs_top (hs:(A)rfs_history) k) U` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_c_component (hs_top hs k,hs_atlas hs k)
                     (hs_metric (hs:(A)rfs_history) k ts) C U` THEN
      SIMP_TAC[rfs_c_component];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:A) IN topspace(hs_top (hs:(A)rfs_history) k) /\ &0 < C` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `compact_in (hs_top (hs:(A)rfs_history) k) U` THEN
        UNDISCH_TAC `(x:A) IN U` THEN REWRITE_TAC[compact_in] THEN SET_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`; `x:A`; `U:A->bool`; `C:real`]
                  P3H_COMP_VOL_BOX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:A->bool` (X_CHOOSE_THEN `d1:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "V1")))))) THEN
    MAP_EVERY EXISTS_TAC [`N0 INTER N1:A->bool`; `min d0 d1`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER; REAL_LT_MIN] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "SL" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[p3_canonv_at; p3_strong_canonv; p3_comp_vol] THEN EXISTS_TAC `U:A->bool` THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [USE_THEN "K0" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "V1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    REMOVE_THEN "PR" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N:A->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "SL" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[p3_canonv_at; p3_strong_canonv] THEN EXISTS_TAC `U:A->bool` THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The first bad time for the canonv assumption (the c172a                  *)
(* machinery restated for p3_canonv_at; P3H_SCALAR_BOX is reused), with the *)
(* truncation equivalence for p3_strong_canonv.                             *)
(* ========================================================================= *)

let P3H_STRONG_CANONV_TRUNC_EQ = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t U tau.
     t < tau
     ==> (p3_strong_canonv (rfs_trunc V tau) C eps x t U <=>
          p3_strong_canonv V C eps x t U)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `e:real^3->A` (ISPECL
    [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `eps:real`; `x:A`; `t:real`; `e:real^3->A`; `tau:real`] P3E_STRONG_NECK_TRUNC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[p3_strong_canonv; p3_comp_vol] THEN ASM_SIMP_TAC[P3E_VIEW_TRUNC_AT]);;

let p3h_badv = new_definition
 `p3h_badv (hs:(A)rfs_history) (C:real) (eps:real) (rp:real->real) (t:real) <=>
    ?x. &0 <= t /\ x IN topspace(rfs_top_at hs t) /\
        inv(rp t pow 2) <= rfs_vscalar (rfs_view hs) t x /\
        ~p3_canonv_at (rfs_view hs) C eps x t`;;

let P3H_CANONV_BAD = prove
 (`!(hs:(A)rfs_history) C eps rp.
     p3_canonv_assumption (rfs_view hs) C eps rp <=> !t. ~p3h_badv hs C eps rp t`,
  REWRITE_TAC[p3_canonv_assumption; p3h_badv] THEN
  REWRITE_TAC[rfs_view; rfs_vtop] THEN MESON_TAC[]);;

let P3H_TRUNC_CANONV_BAD = prove
 (`!(hs:(A)rfs_history) C eps rp tau.
     p3_canonv_assumption (rfs_trunc (rfs_view hs) tau) C eps rp <=>
     !t. t < tau ==> ~p3h_badv hs C eps rp t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_canonv_assumption; p3h_badv] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN
    ASM_SIMP_TAC[P3E_VIEW_TRUNC_AT] THEN REWRITE_TAC[p3_canonv_at] THEN
    ASM_SIMP_TAC[P3H_STRONG_CANONV_TRUNC_EQ] THEN
    UNDISCH_TAC `~p3_canonv_at (rfs_view (hs:(A)rfs_history)) C eps x t` THEN
    REWRITE_TAC[p3_canonv_at; rfs_view; rfs_vtop] THEN
    UNDISCH_TAC `(x:A) IN topspace(rfs_top_at hs t)` THEN REWRITE_TAC[rfs_view; rfs_vtop] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t < tau` THENL
   [ALL_TAC;
    UNDISCH_TAC `(x:A) IN topspace(rfs_vtop (rfs_trunc (rfs_view hs) tau) t)` THEN
    REWRITE_TAC[rfs_view; rfs_trunc; rfs_vtop] THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  UNDISCH_TAC `(x:A) IN topspace(rfs_vtop (rfs_trunc (rfs_view hs) tau) t)` THEN
  UNDISCH_TAC `inv(rp t pow 2) <= rfs_vscalar (rfs_trunc (rfs_view (hs:(A)rfs_history)) tau) t x` THEN
  ASM_SIMP_TAC[P3E_VIEW_TRUNC_AT] THEN REWRITE_TAC[p3_canonv_at] THEN
  ASM_SIMP_TAC[P3H_STRONG_CANONV_TRUNC_EQ] THEN REWRITE_TAC[rfs_view; rfs_vtop] THEN
  MESON_TAC[]);;

let P3H_BADV_LIVE = prove
 (`!(hs:(A)rfs_history) C eps rp t.
     p3h_badv hs C eps rp t ==> &0 <= t /\ t < rfs_horizon hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3h_badv; rfs_top_at; rfs_live; rfs_horizon] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]);;

let P3H_GOOD_BOX_V = prove
 (`!(hs:(A)rfs_history) C eps rp r' ts k.
     rfs_history_ok hs /\ k <= hs_count hs /\
     hs_time hs k <= ts /\ ts < hs_time hs (k + 1) /\ &0 <= ts /\
     (!t. ts <= t /\ t < hs_time hs (k + 1) ==> rp t = r') /\
     (!x. x IN topspace(hs_top hs k) /\
          inv(r' pow 2) <= mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x
          ==> ?N d. open_in (hs_top hs k) N /\ x IN N /\ &0 < d /\
                    !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N /\
                          inv(r' pow 2) <= mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y
                          ==> p3_canonv_at (rfs_view hs) C eps y s)
     ==> ?d. &0 < d /\ !t. ts <= t /\ t < ts + d ==> ~p3h_badv hs C eps rp t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN topspace(hs_top hs k)
        ==> ?N d. open_in (hs_top (hs:(A)rfs_history) k) N /\ x IN N /\ &0 < d /\
                  !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N /\
                        inv(r' pow 2) <= mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y
                        ==> p3_canonv_at (rfs_view hs) C eps y s`
  MP_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `inv(r' pow 2) <= mfd_scalar (hs_atlas hs k)
                                     (hs_metric (hs:(A)rfs_history) k ts) x` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canonv_at")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k ts) x <
                  inv(r' pow 2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`; `x:A`; `inv(r' pow 2)`]
                  P3H_SCALAR_BOX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N:A->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:A`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `N:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A->A->bool` (X_CHOOSE_TAC `d:A->real`)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `compact_space (hs_top (hs:(A)rfs_history) k)` THEN
  REWRITE_TAC[compact_space; compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (N:A->A->bool) (topspace(hs_top (hs:(A)rfs_history) k))` o
             CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> (a /\ b) /\ c`] THEN
  REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:A->bool` (X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `dd = inf ((hs_time (hs:(A)rfs_history) (k + 1) - ts) INSERT IMAGE (d:A->real) Fs)` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= hs_time (hs:(A)rfs_history) (k + 1) - ts /\
                (!x. x IN Fs ==> dd <= (d:A->real) x)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN
    MP_TAC(ISPEC `(hs_time (hs:(A)rfs_history) (k + 1) - ts) INSERT IMAGE (d:A->real) Fs`
                 INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY; FORALL_IN_INSERT;
                 FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      is_const t && fst(dest_const t) = "INSERT")) (concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "IN")) THEN
    REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:A) IN topspace(hs_top (hs:(A)rfs_history) k)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `dd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[p3h_badv; NOT_EXISTS_THM] THEN
  X_GEN_TAC `y:A` THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `t:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[rfs_view; rfs_vscalar] THEN
  SUBGOAL_THEN `(rp:real->real) t = r'` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?x:A. x IN Fs /\ (y:A) IN (N:A->A->bool) x` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(hs_top (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `N:A->A->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canonv_at")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `y:A`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[rfs_view] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `ts + dd` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> ts + a <= ts + b`) THEN ASM_SIMP_TAC[]);;

let P3H_FIRST_BAD_TIME_V = prove
 (`!(hs:(A)rfs_history) C eps rp r' T0.
     rfs_history_ok hs /\ &0 <= T0 /\
     p3_canonv_assumption (rfs_trunc (rfs_view hs) T0) C eps rp /\
     ~p3_canonv_assumption (rfs_view hs) C eps rp /\
     (!t. T0 <= t /\ t < rfs_horizon hs ==> rp t = r') /\
     (!ts x. T0 <= ts /\ ts < rfs_horizon hs /\
             p3_canonv_assumption (rfs_trunc (rfs_view hs) ts) C eps rp /\
             x IN topspace(rfs_top_at hs ts) /\
             inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
             p3_canonv_at (rfs_view hs) C eps x ts
             ==> ?N d. open_in (rfs_top_at hs ts) N /\ x IN N /\ &0 < d /\
                       !s y. ts <= s /\ s < ts + d /\ y IN N /\
                             y IN topspace(rfs_top_at hs s) /\
                             inv(r' pow 2) <= rfs_vscalar (rfs_view hs) s y
                             ==> p3_canonv_at (rfs_view hs) C eps y s)
     ==> ?ts x. T0 <= ts /\ ts < rfs_horizon hs /\
                p3_canonv_assumption (rfs_trunc (rfs_view hs) ts) C eps rp /\
                x IN topspace(rfs_top_at hs ts) /\
                inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
                ~p3_canonv_at (rfs_view hs) C eps x ts`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "const") (LABEL_TAC "open")))))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P3H_TRUNC_CANONV_BAD] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_trunc")) (concl th))) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[P3H_CANONV_BAD] o check (is_neg o concl)) THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN DISCH_THEN(X_CHOOSE_TAC `t0:real`) THEN
  ABBREV_TAC `B = {t | p3h_badv (hs:(A)rfs_history) C eps rp t}` THEN
  SUBGOAL_THEN `~(B:real->bool = {}) /\ (!t. t IN B ==> T0 <= t)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[REAL_NOT_LT]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `B:real->bool` INF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `ts = inf (B:real->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `T0 <= ts /\ ts < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `t0:real` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ASM_MESON_TAC[P3H_BADV_LIVE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_canonv_assumption (rfs_trunc (rfs_view (hs:(A)rfs_history)) ts)
                  C eps rp` ASSUME_TAC THENL
   [REWRITE_TAC[P3H_TRUNC_CANONV_BAD] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `ts <= t:real` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `B:real->bool`)) (concl th) &&
        can (find_term (fun t -> t = `ts:real`)) (concl th) &&
        not (can (find_term (fun t -> is_var t && fst(dest_var t) = "b")) (concl th)))) THEN
      EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `p3h_badv (hs:(A)rfs_history) C eps rp ts` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3h_badv]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`ts:real`; `x:A`] THEN
    REMOVE_THEN "const" (MP_TAC o SPEC `ts:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) ts` THEN STRIP_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k + 1) <= rfs_horizon hs` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_horizon] THEN MATCH_MP_TAC APX_HS_TIME_LE THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ts /\
                (!t. ts <= t /\ t < hs_time (hs:(A)rfs_history) (k + 1) ==> (rp:real->real) t = r')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "const" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `rp:real->real`; `r':real`;
                 `ts:real`; `k:num`] P3H_GOOD_BOX_V) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "open" (MP_TAC o SPECL [`ts:real`; `x:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[rfs_view; rfs_vscalar] THEN
      MP_TAC(ASSUME `~p3h_badv (hs:(A)rfs_history) C eps rp ts`) THEN
      REWRITE_TAC[p3h_badv; NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      SUBGOAL_THEN `(rp:real->real) ts = r'` SUBST1_TAC THENL
       [USE_THEN "const" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[rfs_view; rfs_vscalar];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N:A->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `N:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[rfs_view; rfs_vscalar] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `N:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `ts + d0` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `B:real->bool`)) (concl th) &&
    can (find_term (fun t -> is_var t && fst(dest_var t) = "b")) (concl th))) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  X_GEN_TAC `t:real` THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `d0:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `B:real->bool`)) (concl th) &&
    can (find_term (fun t -> t = `ts:real`)) (concl th) &&
    not (can (find_term (fun t -> is_var t && fst(dest_var t) = "b")) (concl th)))) THEN
  EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `~(t:real = ts)` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The canonv condition is open forward in time at points of a               *)
(* history (canonv form of P3H_OPEN_HIST), and MT Lemma 17.2 (canonv) from   *)
(* history regularity and the part D statement.                              *)
(* ========================================================================= *)

let P3H_OPEN_HIST_V = prove
 (`?eps0. &0 < eps0 /\
     !(hs:(A)rfs_history) C eps ts x.
       rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\
       &1 < C /\ &0 < eps /\ eps <= eps0 /\
       &0 <= ts /\ ts < rfs_horizon hs /\ x IN topspace(rfs_top_at hs ts) /\
       &0 < rfs_vscalar (rfs_view hs) ts x /\
       p3_canonv_at (rfs_view hs) C eps x ts /\
       (!e p1. rfs_strong_neck (rfs_view hs) eps x ts e /\ &0 < p1 /\ p1 < &1 /\
               ~(?eta0. &0 < eta0 /\
                        rfs_persists (rfs_view hs) (IMAGE e (rfs_neck_dom (eps / p1)))
                          (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0) ts)
               ==> ?U Y. rfs_cap (rfs_top_at hs ts,rfs_atlas_at hs ts)
                                 (rfs_metric_at hs ts) C eps U Y /\ x IN Y)
       ==> ?N d. open_in (rfs_top_at hs ts) N /\ x IN N /\ &0 < d /\
                 !s y. ts <= s /\ s < ts + d /\ y IN N
                       ==> p3_canonv_at (rfs_view hs) C eps y s`,
  MP_TAC(INST_TYPE [`:A`,`:A`] P3H_OPEN_STATIC_HIST_V) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  EXISTS_TAC `min e0 (&1 / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))))))))))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts:real`] RFS_SLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) ts` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`] APX_RFS_SLAB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar (hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k ts) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
    ASM_REWRITE_TAC[P2B9_RFS_VSCALAR; P2C_RFS_VIEW_PARTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!U. ((?Y. rfs_cap (rfs_top_at hs ts,rfs_atlas_at hs ts)
                       (rfs_metric_at (hs:(A)rfs_history) ts) C eps U Y /\ x IN Y) \/
         (x IN U /\ rfs_c_component (rfs_top_at hs ts,rfs_atlas_at hs ts)
                                    (rfs_metric_at hs ts) C U /\
          (?v. mfd_has_volume (rfs_top_at hs ts,rfs_atlas_at hs ts) (rfs_metric_at hs ts) U v /\
               inv C * inv(sqrt(mfd_scalar (rfs_atlas_at hs ts) (rfs_metric_at hs ts) x))
                       pow 3 < v)) \/
         (x IN U /\ rfs_round_component (rfs_top_at hs ts,rfs_atlas_at hs ts)
                                        (rfs_metric_at hs ts) eps U))
        ==> ?N d. open_in (rfs_top_at hs ts) N /\ x IN N /\ &0 < d /\
                  !s y. ts <= s /\ s < ts + d /\ y IN N
                        ==> p3_canonv_at (rfs_view hs) C eps y s`
  (LABEL_TAC "stat") THENL
   [X_GEN_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "st" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `k:num`;
                                   `ts:real`; `x:A`; `U:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N:A->bool`; `min d (hs_time (hs:(A)rfs_history) (k + 1) - ts)`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `U:A->bool` o REWRITE_RULE[p3_canonv_at] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canonv_at")) (concl th) &&
    not (is_forall (concl th)))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[rfs_view] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_strong_canonv"))
      (concl th))) THEN
  REWRITE_TAC[p3_strong_canonv; p3_comp_vol; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
  STRIP_TAC THENL
   [ALL_TAC;
    USE_THEN "stat" MATCH_MP_TAC THEN EXISTS_TAC `U:A->bool` THEN DISJ1_TAC THEN
    EXISTS_TAC `Y:A->bool` THEN ASM_REWRITE_TAC[];
    USE_THEN "stat" MATCH_MP_TAC THEN EXISTS_TAC `U:A->bool` THEN DISJ2_TAC THEN DISJ1_TAC THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    EXISTS_TAC `v:real` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "stat" MATCH_MP_TAC THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `rfs_strong_neck (rfs_view (hs:(A)rfs_history)) eps x ts e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfs_view]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `eps:real`; `ts:real`; `x:A`; `e:real^3->A`]
                P3H_NECK_OPEN_HIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk")))) THEN
  ASM_CASES_TAC
   `?eta0. &0 < eta0 /\
           rfs_persists (rfs_view (hs:(A)rfs_history)) (IMAGE e (rfs_neck_dom (eps / p1)))
             (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0) ts` THENL
   [USE_THEN "nk" (MP_TAC o C MP (ASSUME
      `?eta0. &0 < eta0 /\
              rfs_persists (rfs_view (hs:(A)rfs_history)) (IMAGE e (rfs_neck_dom (eps / p1)))
                (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0) ts`)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:A->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:A`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck"))
        (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `e':real^3->A` o CONJUNCT2) THEN
    REWRITE_TAC[p3_canonv_at; p3_strong_canonv] THEN
    EXISTS_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN DISJ1_TAC THEN
    EXISTS_TAC `e':real^3->A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "D" (MP_TAC o SPECL [`e:real^3->A`; `p1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC)) THEN
  USE_THEN "stat" MATCH_MP_TAC THEN EXISTS_TAC `U':A->bool` THEN DISJ1_TAC THEN
  EXISTS_TAC `Y:A->bool` THEN ASM_REWRITE_TAC[]);;

let P3H_LEMMA_17_2_FROM_D_V = prove
 (`!u:A->bool. P2C_HISTORY_REGULAR_STATEMENT u /\ P3H_PART_D_STATEMENT u
               ==> P3_LEMMA_17_2_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3H_PART_D_STATEMENT; P3_LEMMA_17_2_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "reg")
    (X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] P3H_OPEN_HIST_V) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "OP"))) THEN
  EXISTS_TAC `min eps0 eps1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `g0:real^3->real^3^3`; `A0:real`] THEN STRIP_TAC THEN
  USE_THEN "D" (MP_TAC o SPECL [`eps:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `hf:real->real->real`; `md:real->real`] THEN STRIP_TAC THEN
  USE_THEN "D1" (MP_TAC o SPECL [`C:real`; `hf:real->real->real`; `md:real->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "D2")] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `r':real`] THEN
  STRIP_TAC THEN
  USE_THEN "D2" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`;
                                 `r':real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D3"))) THEN
  EXISTS_TAC `dlt:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`;
                       `hs:(A)rfs_history`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p3_step_hyp] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_step_hyp")) (concl th) &&
    not (is_forall (concl th)))) THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_struct]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [USE_THEN "reg" (MP_TAC o REWRITE_RULE[P2C_HISTORY_REGULAR_STATEMENT]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p3_T i` ASSUME_TAC THENL
   [REWRITE_TAC[p3_T] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC P3H_FIRST_BAD_TIME_V THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[p3_stepf] THEN
    SUBGOAL_THEN `p3_step t = SUC i` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(ARITH_RULE `a <= b /\ b <= a ==> a = b:num`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3_STEP_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P3_STEP_GE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`ts:real`; `x:A`] THEN STRIP_TAC THEN
  USE_THEN "OP" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `ts:real`;
                                 `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT];
      REPEAT STRIP_TAC THEN USE_THEN "D3" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`;
                            `e:real^3->A`; `p1:real`] THEN
      ASM_SIMP_TAC[P3_CANONV_ASSUMPTION_IMP]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:A->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

