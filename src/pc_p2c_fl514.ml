(* ========================================================================= *)
(* Unit pc_p2c_fl514 (Part 2C, flowlim route): MT Prop 5.14, that is         *)
(* P2C_PROP_5_14_STATEMENT.  The hypotheses of the statement give p2cv_hyp   *)
(* (conjunct 5 of p2c_regular_view is p2cz_from_smooth); after a thinning of *)
(* the sequence that dominates the persistence thresholds of every region W  *)
(* k over a countable cofinal family of compact intervals of J, the setting  *)
(* P2CQ_SETTING and the assembly P2CA_ASSEMBLY give a subsequence and a      *)
(* limit Ricci flow g on J with g 0 = g0, and the flow limit                 *)
(* p2c_flow_limit_with (diffeo clause by P2CV_PHI_DIFFEO, lck clause by      *)
(* P2CV_P_CHART and LCK_DIST2_LOCAL).  Smoothness from time 0: in every      *)
(* chart the limit is near every point the local limit of a context of       *)
(* pc_p2c_flconv (P2CR_IDENT), so P2CB_UPTO_CTX of pc_p2c_flfrom extends it  *)
(* past time 0 (P2CR_FROM).                                                  *)
(* ========================================================================= *)

needs "src/pc_p2c_flseq.ml";;
needs "src/pc_p2c_flfrom.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* From the hypotheses of Prop 5.14 to p2cv_hyp, reindexing of              *)
(* the sequence, domination of a double sequence of thresholds by a strictly *)
(* increasing sequence, and a countable cofinal family of compact intervals. *)
(* ------------------------------------------------------------------------- *)

let P2CR_REGULAR_FROM_SMOOTH = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     p2c_regular_view V ==> p2cz_from_smooth V`,
  REWRITE_TAC[p2c_regular_view; p2cz_from_smooth] THEN MESON_TAC[]);;

let P2CR_HYP = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A).
     is_realinterval J /\ (&0) IN J /\
     (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
     (!n. p2c_regular_view (V n)) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!m a b. real_interval[a,b] SUBSET J
              ==> ?CM N. !n. N <= n
                       ==> (!s. a <= s /\ s <= b
                                ==> IMAGE (phi n) (W m) SUBSET
                                    topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                           rfs_persists (V n) (IMAGE (phi n) (W m))
                                        (t n + a / Q n) (t n + b / Q n) /\
                           !s y. a <= s /\ s <= b /\ y IN IMAGE (phi n) (W m)
                                 ==> p3_vrm (V n) (t n + s / Q n) y <= CM * Q n)
     ==> p2cv_hyp V x t Q J (top,atlas) g0 xl W phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2cv_hyp] THEN
  ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH]);;

let P2CR_P_REINDEX = prove
 (`!V t Q (atlas:((B->bool)#(B->real^3))->bool) (phi:num->B->A) (r:num->num) n.
     p2cv_P (V o r) (t o r) (Q o r) atlas (phi o r) n = p2cv_P V t Q atlas phi (r n)`,
  REWRITE_TAC[p2cv_P; o_THM]);;

let P2CR_HYP_REINDEX = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) r.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ (!n. n <= r n)
     ==> p2cv_hyp (V o r) (x o r) (t o r) (Q o r) J (top,atlas) g0 xl W (phi o r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r")) THEN
  SUBGOAL_THEN
   `!k. ?psi. mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                ((W:num->B->bool) k)
                (rfs_vtop ((V:num->p2cvv3) (r k)) (t (r k)))
                (rfs_vatlas (V (r k)) (t (r k)))
                (IMAGE ((phi:num->B->A) (r k)) (W k)) (phi (r k)) psi`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2CV_ONE_DIFFEO THEN EXISTS_TAC `(Q:num->real) ((r:num->num) k)` THEN
    MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `p2cv_hyp V x t Q J (top,atlas) (g0:B->real^3^3) xl W (phi:num->B->A)` THEN
  REWRITE_TAC[p2cv_hyp; p2c_slice_limit_with; o_THM] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (CONJ (ASSUME `compact_in top (K:B->bool)`)
                                      (ASSUME `&0 < eta`)) o
                  SPECL [`K:B->bool`; `m:num`; `eta:real`]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
    DISCH_THEN(LABEL_TAC "k0") THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ASM_SIMP_TAC[];
      USE_THEN "k0" (MP_TAC o SPEC `(r:num->num) k`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "r" (ACCEPT_TAC o SPEC `k:num`);
        SIMP_TAC[]]];
    MAP_EVERY X_GEN_TAC [`m:num`; `a:real`; `b:real`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `real_interval[a,b] SUBSET J`) o
                  SPECL [`m:num`; `a:real`; `b:real`]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `CM:real` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_THEN(LABEL_TAC "N") THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N" MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "r" (ACCEPT_TAC o SPEC `n:num`)]);;

let P2CR_DOMINATE = prove
 (`!f:num->num->num. ?r. (!m n. m < n ==> r m < r n) /\
                         (!i j k. i <= k /\ j <= k ==> f i j <= r k)`,
  GEN_TAC THEN
  EXISTS_TAC `\k. k + nsum(0..k) (\i. nsum(0..k) (\j. (f:num->num->num) i j))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `\m n. m + nsum(0..m) (\i. nsum(0..m) (\j. (f:num->num->num) i j)) <
                        n + nsum(0..n) (\i. nsum(0..n) (\j. f i j))`
                 TRANSITIVE_STEPWISE_LT_EQ) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC(ARITH_RULE `x <= y ==> n + x < SUC n + y`) THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `nsum(0..n) (\i. nsum(0..SUC n) (\j. (f:num->num->num) i j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[NSUM_CLAUSES_NUMSEG; LE_0] THEN ARITH_TAC;
      REWRITE_TAC[NSUM_CLAUSES_NUMSEG; LE_0] THEN ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `k:num`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= k + y`) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `nsum(0..k) (\j. (f:num->num->num) i j)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\j. (f:num->num->num) i j`; `nsum(0..k) (\j. (f:num->num->num) i j)`;
                     `0..k`] NSUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; LE_REFL; IN_NUMSEG; LE_0] THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`\i. nsum(0..k) (\j. (f:num->num->num) i j)`;
                     `nsum(0..k) (\i. nsum(0..k) (\j. (f:num->num->num) i j))`;
                     `0..k`] NSUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; LE_REFL; IN_NUMSEG; LE_0] THEN ASM_SIMP_TAC[]]]);;

let P2CR_INTERVALS = prove
 (`!J. is_realinterval J /\ (&0) IN J
       ==> ?(al:num->real) (be:num->real).
              (!j. al j <= &0 /\ &0 <= be j /\ real_interval[al j,be j] SUBSET J) /\
              (!a b. a <= b /\ real_interval[a,b] SUBSET J
                     ==> ?j. al j <= a /\ b <= be j)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `J = {&0}` THENL
   [MAP_EVERY EXISTS_TAC [`\j:num. &0`; `\j:num. &0`] THEN REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_SING] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_SING] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `a:real`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `J:real->bool` P2CA_INTERVALS) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* One member of the sequence over a persisting interval: the               *)
(* slices are smooth manifolds, and lck distances to the chart form of the   *)
(* rescaled pulled back metric (P2CV_P_CHART) at points of the region.      *)
(* ------------------------------------------------------------------------- *)

let P2CR_SLICE_MFD = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a0 b0 s.
     p2cv_one V (top,atlas) Wb f t0 q /\
     rfs_persists V (IMAGE f Wb) (t0 + a0 / q) (t0 + b0 / q) /\
     a0 <= &0 /\ &0 <= b0 /\ a0 <= s /\ s <= b0 /\ (&0 <= s \/ a0 < s)
     ==> smooth_manifold_atlas (rfs_vtop V (t0 + s / q)) (rfs_vatlas V (t0 + s / q))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `IMAGE (f:B->A) Wb`; `t0 + a0 / q`; `t0 + b0 / q`; `t0 + s / q`]
                P2CV_PERSISTS_AT) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LT_LADD; REAL_LE_LADD] THEN
  ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC);;

let P2CR_LCK_CHART = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a0 b0 s G m y.
     p2cv_one V (top,atlas) Wb f t0 q /\
     rfs_persists V (IMAGE f Wb) (t0 + a0 / q) (t0 + b0 / q) /\
     a0 <= &0 /\ &0 <= b0 /\ a0 <= s /\ s <= b0 /\ (&0 <= s \/ a0 < s) /\ y IN Wb
     ==> lck_dist2 m G (metric_local atlas (chart_at atlas y) (p2cv_pb V t0 q atlas f s))
                   (SND(chart_at atlas y) y) =
         lck_dist2 m G (\z. q %% rfs_pullback (rfs_vatlas V (t0 + s / q))
                                   (f o chart_inv (chart_at atlas y))
                                   (rfs_vmetric V (t0 + s / q)) z)
                   (SND(chart_at atlas y) y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`; `a0:real`; `b0:real`; `s:real`]
                P2CV_PHI_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  MP_TAC(ISPECL [`V:p2cvv3`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Wb:B->bool`; `f:B->A`; `t0:real`; `q:real`; `a0:real`; `b0:real`; `s:real`]
                P2CR_SLICE_MFD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                    (FST(chart_at atlas y) INTER Wb)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CV_P_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `Wb:B->bool`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The thinning of the sequence (P2CR_THIN), the flow limit of               *)
(* a dominated subsequence (P2CR_FLOW_LIMIT) and Prop 5.14 without the       *)
(* smoothness from time 0 (P2CR_CORE).                                       *)
(* ------------------------------------------------------------------------- *)

let P2CR_THIN = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) (al:num->real) be.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     (!j. al j <= &0 /\ &0 <= be j /\ real_interval[al j,be j] SUBSET J)
     ==> ?r. (!m n. m < n ==> r m < r n) /\
             !i j n. i <= n /\ j <= n
                     ==> !k. r n <= k
                             ==> rfs_persists (V k) (IMAGE (phi k) (W i))
                                              (t k + al j / Q k) (t k + be j / Q k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o last o CONJUNCTS o MATCH_MP P2CV_HYP_BASIC) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i j. ?N. !k. N <= k
                  ==> rfs_persists ((V:num->p2cvv3) k) (IMAGE ((phi:num->B->A) k) ((W:num->B->bool) i))
                                   (t k + (al:num->real) j / Q k) (t k + (be:num->real) j / Q k)`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `(al:num->real) j`; `(be:num->real) j`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `CM:real` (X_CHOOSE_THEN `N:num` ASSUME_TAC)) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num->num->num` (LABEL_TAC "N")) THEN
  MP_TAC(SPEC `N:num->num->num` P2CR_DOMINATE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dom")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `n:num`] THEN STRIP_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(r:num->num) n` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "dom" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2CR_FLOW_LIMIT = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) (al:num->real) be R g.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     (!j. al j <= &0 /\ &0 <= be j /\ real_interval[al j,be j] SUBSET J) /\
     (!a b. a <= b /\ real_interval[a,b] SUBSET J ==> ?j. al j <= a /\ b <= be j) /\
     (!n. n <= R n) /\
     (!i j k. i <= k /\ j <= k
              ==> rfs_persists (V (R k)) (IMAGE (phi (R k)) (W i))
                               (t (R k) + al j / Q (R k)) (t (R k) + be j / Q (R k))) /\
     (!a b K m e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 m (metric_local atlas (chart_at atlas y) (g s))
                                        (metric_local atlas (chart_at atlas y)
                                           (p2cv_P V t Q atlas phi (R n) s))
                                        (SND(chart_at atlas y) y) < e)
     ==> p2c_flow_limit_with (\n. V (R n)) (x o R) (t o R) (Q o R) J (top,atlas) g xl W
                             (phi o R)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cof") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (LABEL_TAC "lck")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  REWRITE_TAC[p2c_flow_limit_with; o_THM] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `K:B->bool`; `m:num`; `eta:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?m0. !k. m0 <= k ==> (K:B->bool) SUBSET (W:num->B->bool) k`
  (X_CHOOSE_THEN `m0:num` (LABEL_TAC "m0")) THENL
   [MP_TAC(ISPECL [`top:B topology`; `W:num->B->bool`; `K:B->bool`] P2CA_COMPACT_IN_W) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m0:num` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(W:num->B->bool) m0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a <= b` THENL
   [ALL_TAC;
    EXISTS_TAC `m0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "m0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC]] THEN
  MP_TAC(ISPECL [`J:real->bool`; `a:real`; `b:real`] P2CQ_WORKING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  USE_THEN "cof" (MP_TAC o SPECL [`a':real`; `b':real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "lck" (MP_TAC o SPECL [`a:real`; `b:real`; `K:B->bool`; `m:num`; `eta:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  EXISTS_TAC `m0 + j + N1:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(K:B->bool) SUBSET (W:num->B->bool) k` ASSUME_TAC THENL
   [USE_THEN "m0" MATCH_MP_TAC THEN UNDISCH_TAC `m0 + j + N1 <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k <= (R:num->num) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2cv_one ((V:num->p2cvv3) (R k)) (top,atlas) ((W:num->B->bool) k)
             ((phi:num->B->A) (R k)) (t (R k)) (Q (R k))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_persists ((V:num->p2cvv3) (R k)) (IMAGE ((phi:num->B->A) (R k)) ((W:num->B->bool) k))
                 (t (R k) + (al:num->real) j / Q (R k)) (t (R k) + (be:num->real) j / Q (R k))`
  ASSUME_TAC THENL
   [USE_THEN "per" MATCH_MP_TAC THEN UNDISCH_TAC `m0 + j + N1 <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s <= b
        ==> (al:num->real) j <= &0 /\ &0 <= (be:num->real) j /\ al j <= s /\ s <= be j /\
            (&0 <= s \/ al j < s)`
  (LABEL_TAC "sj") THENL
   [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "sj" (MP_TAC o C MP (ASSUME `a <= s /\ s <= b`) o SPEC `s:real`) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC P2CV_PHI_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`(al:num->real) j`; `(be:num->real) j`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    USE_THEN "sj" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
    SUBGOAL_THEN `(y:B) IN (W:num->B->bool) k` ASSUME_TAC THENL
     [UNDISCH_TAC `(K:B->bool) SUBSET (W:num->B->bool) k` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:num->p2cvv3) ((R:num->num) k)`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) k`;
                   `(phi:num->B->A) ((R:num->num) k)`; `(t:num->real) ((R:num->num) k)`;
                   `(Q:num->real) ((R:num->num) k)`;
                   `(al:num->real) j`; `(be:num->real) j`; `s:real`;
                   `metric_local atlas (chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B))
                                 ((g:real->B->real^3^3) s)`; `m:num`; `y:B`] P2CR_LCK_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[GSYM P2CV_P_PB] THEN USE_THEN "N1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `m0 + j + N1 <= k:num` THEN ARITH_TAC]);;

let P2CR_CORE = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A).
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi
     ==> ?sub g. p3_subseq sub /\ g (&0) = g0 /\
                 p2c_flow_limit_with (\n. V (sub n)) (x o sub) (t o sub) (Q o sub) J
                                     (top,atlas) g xl W (phi o sub) /\
                 (!s. s IN J ==> riemannian_metric atlas (g s)) /\
                 (!a b. a < b /\ real_interval[a,b] SUBSET J
                        ==> ricci_flow_on (top,atlas) a b g) /\
                 (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                              ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                              ==> lck_dist2 k
                                                    (metric_local atlas (chart_at atlas y) (g s))
                                                    (metric_local atlas (chart_at atlas y)
                                                       (p2cv_P V t Q atlas phi (sub n) s))
                                                    (SND(chart_at atlas y) y) < e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MP_TAC(SPEC `J:real->bool` P2CR_INTERVALS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:num->real` (X_CHOOSE_THEN `be:num->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cof")))) THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `al:num->real`; `be:num->real`] P2CR_THIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (CONJUNCTS_THEN2 (LABEL_TAC "rmono") (LABEL_TAC "thin"))) THEN
  SUBGOAL_THEN `!n. n <= (r:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN USE_THEN "rmono" ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (r:num->num) m <= r n` (LABEL_TAC "rle") THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `m:num = n` THEN ASM_REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC LT_IMP_LE THEN USE_THEN "rmono" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `r:num->num`]
                P2CR_HYP_REINDEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(V:num->p2cvv3) o (r:num->num)`; `(x:num->A) o (r:num->num)`;
                 `(t:num->real) o (r:num->num)`; `(Q:num->real) o (r:num->num)`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `(phi:num->B->A) o (r:num->num)`]
                P2CQ_SETTING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP P2CA_ASSEMBLY) THEN
  REWRITE_TAC[P2CR_P_REINDEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub0:num->num` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "smono") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lck"))))))) THEN
  SUBGOAL_THEN `!n. n <= (sub0:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN USE_THEN "smono" ACCEPT_TAC; ALL_TAC] THEN
  EXISTS_TAC `(r:num->num) o (sub0:num->num)` THEN EXISTS_TAC `g:real->B->real^3^3` THEN
  SUBGOAL_THEN
   `p2c_flow_limit_with (\n. (V:num->p2cvv3) (((r:num->num) o (sub0:num->num)) n))
                        ((x:num->A) o r o sub0) ((t:num->real) o r o sub0)
                        ((Q:num->real) o r o sub0) J (top,atlas) (g:real->B->real^3^3) xl W
                        ((phi:num->B->A) o r o sub0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CR_FLOW_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`g0:B->real^3^3`; `al:num->real`; `be:num->real`] THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `(sub0:num->num) n` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `k:num`] THEN STRIP_TAC THEN
      USE_THEN "thin" (MATCH_MP_TAC o C MP (CONJ (ASSUME `i <= k:num`) (ASSUME `j <= k:num`)) o
                       SPECL [`i:num`; `j:num`; `k:num`]) THEN
      USE_THEN "rle" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p3_subseq] THEN CONJ_TAC THENL
   [REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN USE_THEN "rmono" MATCH_MP_TAC THEN
    USE_THEN "smono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN USE_THEN "lck" ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness from time 0.  Chart transfer of lck                            *)
(* convergence (P2CR_LCK_CHART_C), the hypotheses p2ca_seqhyp for the       *)
(* subsequence (P2CR_SEQHYP_SUB), the limit in a chart is the local limit of *)
(* the Arzela-Ascoli context of the subsequence (P2CR_IDENT, by              *)
(* P2CB_LCK_LIM_UNIQUE), the extension past time 0 in every chart           *)
(* (P2CR_CHART_UPTO, by P2CB_UPTO_CTX) and ricci_flow_from (P2CR_FROM).     *)
(* ------------------------------------------------------------------------- *)

let P2CR_RIEM_FIELD = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) c O.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
     open_in top O
     ==> metric_field (IMAGE (SND c) (FST c INTER O)) (metric_local atlas c g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    SET_TAC[]]);;

let P2CR_LCK_CHART_C = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (Ps:num->real->B->real^3^3) g Wm c a b x k.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ open_in top Wm /\
     x IN FST c /\ x IN Wm /\
     (!s. a <= s /\ s <= b ==> riemannian_metric atlas (g s)) /\
     (!c' n s. c' IN atlas /\ a <= s /\ s <= b
               ==> metric_field (IMAGE (SND c') (FST c' INTER Wm))
                                (metric_local atlas c' (Ps n s))) /\
     (!e. &0 < e
          ==> ?N. !n s. N <= n /\ a <= s /\ s <= b
                        ==> lck_dist2 k (metric_local atlas (chart_at atlas x) (g s))
                                        (metric_local atlas (chart_at atlas x) (Ps n s))
                                        (SND(chart_at atlas x) x) < e)
     ==> !e. &0 < e
             ==> ?N. !n s. N <= n /\ a <= s /\ s <= b
                           ==> lck_dist2 k (metric_local atlas c (g s))
                                           (metric_local atlas c (Ps n s)) (SND c x) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 (LABEL_TAC "mf")
    (LABEL_TAC "lck")))))))) THEN
  SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "lck" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_THEN(LABEL_TAC "N") THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `(Ps:num->real->B->real^3^3) n s`;
                 `c:(B->bool)#(B->real^3)`;
                 `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`;
                 `Wm:B->bool`; `x:B`; `k:num`] P2CA_LCK_CHART_INDEP_C) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CR_RIEM_FIELD THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2CR_SEQHYP_SUB = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m a b sub.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ p3_subseq sub /\
     a <= &0 /\ &0 <= b /\ a < b /\ real_interval[a,b] SUBSET J
     ==> ?N. !c. c IN atlas
                 ==> p2ca_seqhyp (IMAGE (SND c) (FST c INTER W m)) a b
                       (\n s. metric_local atlas c (p2cv_P V t Q atlas phi (sub (N + n)) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `m:num`; `a:real`; `b:real`] P2CQ_SEQHYP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
  USE_THEN "N" (MP_TAC o C MP (ASSUME `(c:(B->bool)#(B->real^3)) IN atlas`) o
                SPEC `c:(B->bool)#(B->real^3)`) THEN
  DISCH_THEN(MP_TAC o SPEC `\n. (sub:num->num) (N + n) - N` o MATCH_MP P2CA_SEQHYP_REINDEX) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN
  SUBGOAL_THEN `N + (sub:num->num) (N + n) - N = sub (N + n)` (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `N + n:num` (MATCH_MP MONOTONE_BIGGER
    (REWRITE_RULE[p3_subseq] (ASSUME `p3_subseq (sub:num->num)`)))) THEN
  ARITH_TAC);;

let P2CR_IDENT = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) sub g m b N c FF ee cc rr sub' H.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (g s))
                                        (metric_local atlas (chart_at atlas y)
                                           (p2cv_P V t Q atlas phi (sub n) s))
                                        (SND(chart_at atlas y) y) < e) /\
     real_interval[&0,b] SUBSET J /\ c IN atlas /\
     (!c'. c' IN atlas
           ==> p2ca_seqhyp (IMAGE (SND c') (FST c' INTER W m)) (&0) b
                 (\n s. metric_local atlas c' (p2cv_P V t Q atlas phi (sub (N + n)) s))) /\
     p2cm_ctx (IMAGE (SND c) (FST c INTER W m)) (&0) b
              (\n s. metric_local atlas c (p2cv_P V t Q atlas phi (sub (N + n)) s))
              FF ee cc rr sub' H
     ==> !s0 y. &0 <= s0 /\ s0 <= b /\ y IN IMAGE (SND c) (FST c INTER W m)
                ==> metric_local atlas c (g s0) y =
                    p2cm_lim (\n s. metric_local atlas c
                                      (p2cv_P V t Q atlas phi (sub (N + n)) s))
                             sub' s0 y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "riem")
    (CONJUNCTS_THEN2 (LABEL_TAC "lck") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sh") (LABEL_TAC "ctx"))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. n <= (sub':num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN
    USE_THEN "ctx" (MP_TAC o REWRITE_RULE[p2cm_ctx]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?xc:B. xc IN FST(c:(B->bool)#(B->real^3)) /\ xc IN (W:num->B->bool) m /\
                       SND c xc = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3)))
                                     (FST c INTER (W:num->B->bool) m)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xc:B) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `(W:num->B->bool) m` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= b ==> s IN J` (LABEL_TAC "inJ") THENL
   [UNDISCH_TAC `real_interval[&0,b] SUBSET J` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= b
        ==> riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) ((g:real->B->real^3^3) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "riem" MATCH_MP_TAC THEN USE_THEN "inJ" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c' n s. c' IN atlas /\ &0 <= s /\ s <= b
             ==> metric_field (IMAGE (SND c') (FST c' INTER (W:num->B->bool) m))
                   (metric_local atlas c'
                      (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s))`
  (LABEL_TAC "mfall") THENL
   [MAP_EVERY X_GEN_TAC [`c':(B->bool)#(B->real^3)`; `n:num`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "sh" (MP_TAC o C MP (ASSUME `(c':(B->bool)#(B->real^3)) IN atlas`) o
                   SPEC `c':(B->bool)#(B->real^3)`) THEN
    REWRITE_TAC[p2ca_seqhyp] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `s:real`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N1. !n s. N1 <= n /\ &0 <= s /\ s <= b
                       ==> lck_dist2 0
                             (metric_local atlas (chart_at atlas (xc:B)) ((g:real->B->real^3^3) s))
                             (metric_local atlas (chart_at atlas xc)
                                (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s))
                             (SND(chart_at atlas xc) xc) < e`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "lck" (MP_TAC o SPECL [`&0`; `b:real`; `{xc:B}`; `0`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_IN_SING]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN EXISTS_TAC `N1:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN
    UNDISCH_TAC `N1 <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\n s. p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s`;
                 `g:real->B->real^3^3`; `(W:num->B->bool) m`; `c:(B->bool)#(B->real^3)`;
                 `&0`; `b:real`; `xc:B`; `0`] P2CR_LCK_CHART_C) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "lc")] THEN
  MATCH_MP_TAC P2CB_LCK_LIM_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`;
    `\n. metric_local atlas (c:(B->bool)#(B->real^3))
           (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + (sub':num->num) n)) s0)`;
    `0`] THEN
  REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CR_RIEM_FIELD THEN EXISTS_TAC `top:B topology` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2CM_CTX_METRIC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`;
                          `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
                          `cc:num->real^3`; `rr:num->real`;
                          `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "mfall" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "lc" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN EXISTS_TAC `N2:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `y = SND(c:(B->bool)#(B->real^3)) (xc:B)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`;
                   `&0`; `b:real`;
                   `\n s. metric_local atlas (c:(B->bool)#(B->real^3))
                            (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s)`;
                   `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
                   `cc:num->real^3`; `rr:num->real`; `sub':num->num`;
                   `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`;
                   `{y:real^3}`; `0`; `e:real`] P2CM_CTX_LCK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[IN_SING] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s0:real`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[]]);;

let P2CR_CHART_UPTO = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) sub g b c.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ p3_subseq sub /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top,atlas) a b g) /\
     (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (g s))
                                        (metric_local atlas (chart_at atlas y)
                                           (p2cv_P V t Q atlas phi (sub n) s))
                                        (SND(chart_at atlas y) y) < e) /\
     &0 < b /\ real_interval[&0,b] SUBSET J /\ c IN atlas
     ==> pde_upto (&0) b (IMAGE (SND c) (FST c))
                  (\s y. vectorize(metric_local atlas c (g s) y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 (LABEL_TAC "rf")
    (CONJUNCTS_THEN2 (LABEL_TAC "lck") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`&0`; `b:real`; `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`;
                 `\s y. metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) s) y`]
                P2CB_UPTO_CTX) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "rf" (MP_TAC o C MP (CONJ (ASSUME `&0 < b`) (ASSUME `real_interval[&0,b] SUBSET J`)) o
                   SPECL [`&0`; `b:real`]) THEN
    REWRITE_TAC[ricci_flow_on] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(B->bool)#(B->real^3)` o CONJUNCT1 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?z0:B. z0 IN FST(c:(B->bool)#(B->real^3)) /\ SND c z0 = y0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. (z0:B) IN (W:num->B->bool) m` (X_CHOOSE_TAC `m:num`) THENL
   [UNDISCH_TAC `UNIONS {(W:num->B->bool) k | k IN (:num)} = topspace top` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `z0:B`) THEN
    SUBGOAL_THEN `(z0:B) IN topspace top` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `FST(c:(B->bool)#(B->real^3)) SUBSET topspace top` THEN
      UNDISCH_TAC `(z0:B) IN FST(c:(B->bool)#(B->real^3))` THEN SET_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `m:num`; `&0`; `b:real`; `sub:num->num`] P2CR_SEQHYP_SUB) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "sh")) THEN
  ABBREV_TAC `Vm = IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)` THEN
  SUBGOAL_THEN `open (Vm:real^3->bool) /\ (y0:real^3) IN Vm /\
                Vm SUBSET IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Vm" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `z0:B` THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Vm:real^3->bool`; `&0`; `b:real`;
                 `\n s. metric_local atlas (c:(B->bool)#(B->real^3))
                          (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s)`]
                P2CB_CTX_SEQHYP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Vm" THEN
    USE_THEN "sh" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
                       `cc:num->real^3`; `rr:num->real`; `sub':num->num`;
                       `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`Vm:real^3->bool`;
    `\n s. metric_local atlas (c:(B->bool)#(B->real^3))
             (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s)`;
    `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
    `cc:num->real^3`; `rr:num->real`; `sub':num->num`;
    `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "Vm" THEN
  MATCH_MP_TAC P2CR_IDENT THEN
  MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `top:B topology`; `g0:B->real^3^3`;
                        `xl:B`; `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`;
                        `ee:num->real`; `cc:num->real^3`; `rr:num->real`;
                        `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
  ASM_REWRITE_TAC[]);;

let P2CR_FROM = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) sub g b.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ p3_subseq sub /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top,atlas) a b g) /\
     (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (g s))
                                        (metric_local atlas (chart_at atlas y)
                                           (p2cv_P V t Q atlas phi (sub n) s))
                                        (SND(chart_at atlas y) y) < e) /\
     &0 < b /\ real_interval[&0,b] SUBSET J
     ==> ricci_flow_from (top,atlas) (&0) b g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 (LABEL_TAC "rf")
    (CONJUNCTS_THEN2 (LABEL_TAC "lck") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  REWRITE_TAC[ricci_flow_from] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                   `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                   `sub:num->num`; `g:real->B->real^3^3`; `b:real`;
                   `c:(B->bool)#(B->real^3)`] P2CR_CHART_UPTO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[pde_upto]]]);;

(* ------------------------------------------------------------------------- *)
(* MT Prop 5.14 (P2C_PROP_5_14_STATEMENT of unit pc_p3_iface, with the       *)
(* smoothness from time 0).                                                  *)
(* ------------------------------------------------------------------------- *)

let P2CR_PROP_5_14 = prove
 (`!u:A->bool w:B->bool. P2C_PROP_5_14_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2C_PROP_5_14_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                       `J:real->bool`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                       `W:num->B->bool`; `phi:num->B->A`] THEN
  DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2CR_HYP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2CR_CORE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sub:num->num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real->B->real^3^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2CR_FROM THEN
  MAP_EVERY EXISTS_TAC [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                        `J:real->bool`; `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`;
                        `phi:num->B->A`; `sub:num->num`] THEN
  ASM_REWRITE_TAC[]);;

