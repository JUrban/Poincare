(* ========================================================================= *)
(* Unit pc_p3_c17vgen: generic volume facts for MT Lemma                    *)
(* 17.12: the volume budget across events (each event costs a fixed amount *)
(* per neck, the volume grows at most like exp(6 t) on each slab), C^0      *)
(* closeness gives quadratic-form and volume comparison.                    *)
(*                                                                         *)
(* The volume budget (real arithmetic over the events).                    *)
(* ========================================================================= *)

needs "src/pc_grg_area.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_rfs_history.ml";;

prioritize_real();;
type_invention_error := true;;

(* With W k = exp(-6 tm k) V k the budget telescopes:                       *)
(* W n + v exp(-6 Tb) sum m <= W 0.                                         *)

let P3H_VOLUME_BUDGET = prove
 (`!(V:num->real) (tm:num->real) (m:num->num) v Tb n.
        &0 < v /\ tm 0 = &0 /\
        (!k. k <= n ==> &0 <= V k /\ tm k <= Tb) /\
        (!k. 1 <= k /\ k <= n
             ==> V k <= exp(&6 * (tm k - tm(k - 1))) * V(k - 1) - &(m k) * v)
        ==> &(nsum(1..n) m) * v <= V 0 * exp(&6 * Tb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. j <= n
        ==> exp(--(&6 * tm j)) * (V:num->real) j +
            v * exp(--(&6 * Tb)) * &(nsum(1..j) m) <= V 0`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `~(1 = 0)`] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `SUC j <= n` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC j`; GSYM REAL_OF_NUM_ADD] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC j` o
      check (fun th -> can (find_term ((=) `exp`)) (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `SUC j <= n` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `SUC j - 1 = j`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(tm:num->real) (SUC j) <= Tb` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `exp(--(&6 * tm(SUC j))) * (V:num->real)(SUC j) <=
      exp(--(&6 * tm j)) * V j - exp(--(&6 * tm(SUC j))) * &(m(SUC j)) * v`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `exp(--(&6 * tm(SUC j))) *
                  (exp(&6 * ((tm:num->real)(SUC j) - tm j)) * (V:num->real) j -
                   &(m(SUC j)) * v)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
      SUBGOAL_THEN
       `exp(--(&6 * (tm:num->real)(SUC j))) * exp(&6 * (tm(SUC j) - tm j)) =
        exp(--(&6 * tm j))`
      ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_SUB_LDISTRIB] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
      ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `v * exp(--(&6 * Tb)) * &(m(SUC j)) <=
      exp(--(&6 * (tm:num->real)(SUC j))) * &(m(SUC j)) * v`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `exp(--(&6 * Tb)) <= exp(--(&6 * (tm:num->real)(SUC j)))`
      ASSUME_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        UNDISCH_TAC `(tm:num->real) (SUC j) <= Tb` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &(m(SUC j):num) * v` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MP_TAC(ISPECL [`&(m(SUC j):num) * v`; `exp(--(&6 * Tb))`;
                     `exp(--(&6 * (tm:num->real)(SUC j)))`] REAL_LE_LMUL) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
     `exp(--(&6 * tm j)) * (V:num->real) j + v * exp(--(&6 * Tb)) * &(nsum(1..j) m) <=
      V 0` THEN
    UNDISCH_TAC
     `exp(--(&6 * tm(SUC j))) * (V:num->real)(SUC j) <=
      exp(--(&6 * tm j)) * V j - exp(--(&6 * tm(SUC j))) * &(m(SUC j)) * v` THEN
    UNDISCH_TAC
     `v * exp(--(&6 * Tb)) * &(m(SUC j)) <=
      exp(--(&6 * (tm:num->real)(SUC j))) * &(m(SUC j)) * v` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= exp(--(&6 * tm(n:num))) * (V:num->real) n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_EXP_POS_LE; LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `v * exp(--(&6 * Tb)) * &(nsum(1..n) m) <= (V:num->real) 0` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < v * exp(--(&6 * Tb))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&6 * Tb) * exp(--(&6 * Tb)) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `&(nsum(1..n) m) * v = (v * exp(--(&6 * Tb)) * &(nsum(1..n) m)) * exp(&6 * Tb)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `exp(&6 * Tb) * exp(--(&6 * Tb)) = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]);;

(* ========================================================================= *)
(* C^0 closeness (lck_dist2 of any order) gives two-sided                   *)
(* quadratic-form bounds.                                                   *)
(* ========================================================================= *)

let P3H_LCK_QF = prove
 (`!k s (G0:real^N->real^N^N) G y d.
        metric_field s G0 /\ metric_field s G /\ y IN s /\ lck_dist2 k G0 G y <= d
        ==> !w. w dot (G y ** w) <= (&1 + sqrt d) * (w dot (G0 y ** w)) /\
                (&1 - sqrt d) * (w dot (G0 y ** w)) <= w dot (G y ** w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `w:real^N`] LCK_DIST_C0) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= w dot ((G0:real^N->real^N^N) y ** w)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_NONNEG THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (G0:real^N->real^N^N) G y) <= sqrt d` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(lck_dist2 k (G0:real^N->real^N^N) G y) * (w dot (G0 y ** w)) <=
    sqrt d * (w dot (G0 y ** w))`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Near the event time, on a compact subset of Omega, volumes                *)
(* for the limit metric are at most (1 + e) times the volumes for the slab  *)
(* metric (C^0 part of rfs_limit_metric).                                   *)
(* ========================================================================= *)

let P3H_LAM_BOUND = prove
 (`!q. &0 < q /\ q <= &1 / &4
       ==> &1 <= inv(&1 - q) /\ inv(&1 - q) * sqrt(inv(&1 - q)) <= &1 + &5 * q`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= inv(&1 - q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(&1 - q) <= &1 + &2 * q` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(&1 - q) * (&1 - q) = &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&1 - q) <= inv(&3 / &4)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `q * inv(&1 - q) <= q * inv(&3 / &4)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
    UNDISCH_TAC `inv(&1 - q) * (&1 - q) = &1` THEN
    UNDISCH_TAC `q * inv(&1 - q) <= q * &4 / &3` THEN
    UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(inv(&1 - q)) <= inv(&1 - q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + &2 * q) * (&1 + &2 * q)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&4 * q * q <= q ==> (&1 + &2 * q) * (&1 + &2 * q) <= &1 + &5 * q`) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= q * (&1 - &4 * q) ==> &4 * q * q <= q`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let P3H_LIMIT_VOLUME_COMPARE = prove
 (`!top atlas a Om ts (g:real->A->real^3^3) gl K e.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas gl /\ a < ts /\
        (!t. a <= t /\ t < ts ==> riemannian_metric atlas (g t)) /\
        rfs_limit_metric (top,atlas) Om ts g gl /\
        compact_in top K /\ K SUBSET Om /\ &0 < e
        ==> ?d. &0 < d /\ d <= ts - a /\
                !t S v v'. ts - d < t /\ t < ts /\ S SUBSET K /\
                           mfd_has_volume (top,atlas) gl S v /\
                           mfd_has_volume (top,atlas) (g t) S v'
                           ==> v <= (&1 + e) * v'`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = min (&1 / &4) (e / &8)` THEN
  SUBGOAL_THEN `&0 < q /\ q <= &1 / &4 /\ &5 * q <= e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(q pow 2) = q` ASSUME_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `lam = inv(&1 - q)` THEN
  SUBGOAL_THEN `&1 <= lam /\ lam * sqrt lam <= &1 + e` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `q:real` P3H_LAM_BOUND) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_limit_metric (top,atlas) (Om:A->bool) ts (g:real->A->real^3^3) gl` THEN
  REWRITE_TAC[rfs_limit_metric] THEN
  DISCH_THEN(MP_TAC o SPECL [`K:A->bool`; `0`; `q pow 2`] o CONJUNCT2) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d0 (ts - a)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `S:A->bool`; `v:real`; `v':real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * sqrt lam * v'` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_COMPARE_QF THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `gl:A->real^3^3`; `(g:real->A->real^3^3) t`; `S:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`0`; `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                                (FST(chart_at atlas y))`;
                   `metric_local (atlas:((A->bool)#(A->real^3))->bool)
                                 (chart_at atlas (y:A)) (gl:A->real^3^3)`;
                   `metric_local (atlas:((A->bool)#(A->real^3))->bool)
                                 (chart_at atlas (y:A)) ((g:real->A->real^3^3) t)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)) y`;
                   `q pow 2`] P3H_LCK_QF) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlas (gl:A->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) t)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `w:real^3`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `gl:A->real^3^3`; `y:A`] METRIC_LOCAL_AT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `y:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `lam * (&1 - q) = &1` ASSUME_TAC THENL
     [EXPAND_TAC "lam" THEN MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `X = w dot ((gl:A->real^3^3) y ** w)` THEN
    ABBREV_TAC `Y = w dot ((g:real->A->real^3^3) t y ** w)` THEN
    SUBGOAL_THEN `lam * ((&1 - q) * X) = X` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
    MP_TAC(ISPECL [`lam:real`; `(&1 - q) * X`; `Y:real`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MFD_HAS_VOLUME_POS_LE) THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `(g:real->A->real^3^3) t`; `S:A->bool`] THEN
    ASM_REWRITE_TAC[]]);;

