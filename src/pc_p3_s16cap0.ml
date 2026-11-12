(* ========================================================================= *)
(* Unit pc_p3_s16cap0 (Part 3 proofs; MT Ch 16, for Prop 16.5): MT Cor 16.7, *)
(* the time-0 slice limit at the tips of the surgery caps (P3N_SLICE0), with *)
(* helpers on the balls of the standard initial metric (P3N_STD_BALL,        *)
(* P3N_STD_WBALLS) and the views of a history at event times.                *)
(* ========================================================================= *)

needs "src/pc_p3_s13thm.ml";;
needs "src/pc_p3_s14glue.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* MT Cor 16.7 in the explicit form of Prop 5.14: for                       *)
(* surgery caps with control dl_n -> 0 (dl_n <= 1/(n+1)), the rescaled     *)
(* slices at the surgery times, pulled back by the cap maps Phi_n, converge *)
(* to the standard initial metric g0 in every C^m on compact sets, over the *)
(* exhaustion by the balls d < m + 1 (P3N_SLICE0).                          *)
(* ========================================================================= *)

let P3N_EUCL_ATLAS = prove
 (`hausdorff_space (euclidean:(real^3)topology) /\
   smooth_manifold_atlas euclidean (open_set_atlas (:real^3))`,
  REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN] THEN
  MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV] THEN
  MESON_TAC[SUBTOPOLOGY_TOPSPACE; TOPSPACE_EUCLIDEAN]);;

let P3N_STD_BALL = prove
 (`!g0 A0 m. p3_std_initial g0 A0 /\ &0 < m
             ==> {x:real^3 | p3_std_dist g0 x < m} = ball(vec 0,p3s_rad_rinv g0 m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0] THEN X_GEN_TAC `x:real^3` THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`;
                `p3s_rad_rinv g0 m`] P3S_RHO_LT_EQ) THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]);;

let P3N_STD_WBALLS = prove
 (`!g0 A0. p3_std_initial g0 A0
     ==> (!m. open {x:real^3 | p3_std_dist g0 x < &m + &1} /\
              vec 0 IN {x:real^3 | p3_std_dist g0 x < &m + &1} /\
              compact(closure {x:real^3 | p3_std_dist g0 x < &m + &1}) /\
              closure {x:real^3 | p3_std_dist g0 x < &m + &1} SUBSET
              {x:real^3 | p3_std_dist g0 x < &(SUC m) + &1}) /\
         UNIONS {{x:real^3 | p3_std_dist g0 x < &m + &1} | m IN (:num)} = (:real^3)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&m + &1`] P3N_STD_BALL) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&(SUC m) + &1`] P3N_STD_BALL) THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < &m + &1`] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&m + &1`] P3S_RINV_FACTS) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&(SUC m) + &1`] P3S_RINV_FACTS) THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < &m + &1`] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; CLOSURE_BALL; COMPACT_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN X_GEN_TAC `x:real^3` THEN
    MATCH_MP_TAC(REAL_ARITH `b < c ==> x <= b ==> x < c`) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 (&m + &1)`;
                  `p3s_rad_rinv g0 (&(SUC m) + &1)`] P3S_RHO_LT_EQ) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNIV; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    MP_TAC(SPEC `p3_std_dist g0 (x:real^3)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `{x:real^3 | p3_std_dist g0 x < &n + &1}` THEN
    CONJ_TAC THENL [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

let P3N_VIEW_AT_EVENT = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs
     ==> rfs_vtop (rfs_view hs) (hs_time hs k) = hs_top hs k /\
         rfs_vatlas (rfs_view hs) (hs_time hs k) = hs_atlas hs k /\
         rfs_vmetric (rfs_view hs) (hs_time hs k) = hs_metric hs k (hs_time hs k) /\
         smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
         riemannian_metric (hs_atlas hs k) (hs_metric hs k (hs_time hs k))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3S_STAGE_FACTS) THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k` o
    check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `hs_metric (hs:(A)rfs_history) k`)) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ricci_flow_from (hs_top hs k,hs_atlas hs k) (hs_time hs k)
                 (hs_time hs (k + 1)) (hs_metric (hs:(A)rfs_history) k)` THEN
  SIMP_TAC[ricci_flow_from]);;

let P3N_OPEN_UNIV_LOCAL = prove
 (`!(g:real^3->real^3^3) y.
     chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x. x)) /\
     metric_local (open_set_atlas (:real^3)) (chart_at (open_set_atlas (:real^3)) y) g = g /\
     chart_inv (chart_at (open_set_atlas (:real^3)) y) = (\x. x) /\
     SND(chart_at (open_set_atlas (:real^3)) y) y = y`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x. x))` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
    MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    REWRITE_TAC[FUN_EQ_THM; chart_inv; IN_UNIV] THEN MESON_TAC[]]);;

let P3N_INV_GE = prove
 (`!x n. &0 < x /\ x <= inv(&n + &1) ==> &n + &1 <= inv x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&n + &1 = inv(inv(&n + &1))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]);;

let P3N_SLICE0 = prove
 (`!md g0 A0 (hs:num->(A)rfs_history) (k:num->num) (i:num->num) (dl:num->real->real)
    (hh:num->real->real) (Phi:num->real^3->A) (xi:num->real^3->real^3).
     p3_modulus md /\ p3_std_initial g0 A0 /\
     (!n. rfs_history_ok (hs n) /\ 1 <= k n /\ k n <= hs_count (hs n) /\
          &0 < dl n (hs_time (hs n) (k n)) /\ dl n (hs_time (hs n) (k n)) <= inv(&n + &1) /\
          &0 < hh n (hs_time (hs n) (k n)) /\
          p3_cap_param (md,g0,A0) (dl n,hh n) (hs n) (k n) (i n) (Phi n) (xi n))
     ==> p2c_slice_limit_with (\n. rfs_view (hs n)) (\n. Phi n (vec 0))
           (\n. hs_time (hs n) (k n)) (\n. inv(hh n (hs_time (hs n) (k n)) pow 2))
           (euclidean,open_set_atlas (:real^3)) g0 (vec 0)
           (\m. {x | p3_std_dist g0 x < &m + &1}) Phi`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_UNIV] o MATCH_MP P3N_STD_WBALLS) THEN
  REWRITE_TAC[p2c_slice_limit_with; P3N_EUCL_ATLAS; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
  REWRITE_TAC[OPEN_IN_EUCLIDEAN; EUCLIDEAN_CLOSURE_OF; COMPACT_IN_EUCLIDEAN] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[p3_std_initial];
    GEN_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `n:num` THEN
    USE_THEN "H" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[p3_cap_param; mfd_param] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`(hs:num->(A)rfs_history) n`; `(k:num->num) n`] P3N_VIEW_AT_EVENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `e':A->real^3` THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC
     [`{x:real^3 | --(inv((dl:num->real->real) n
                         (hs_time ((hs:num->(A)rfs_history) n) ((k:num->num) n)))) <
                   A0 + &4 - p3_std_dist g0 x}`;
      `IMAGE ((Phi:num->real^3->A) n)
         {x:real^3 | --(inv((dl:num->real->real) n
                         (hs_time ((hs:num->(A)rfs_history) n) ((k:num->num) n)))) <
                     A0 + &4 - p3_std_dist g0 x}`] THEN
    ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`(dl:num->real->real) n (hs_time ((hs:num->(A)rfs_history) n) ((k:num->num) n))`;
                  `n:num`] P3N_INV_GE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:real^3->bool`; `m:num`; `eta:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `DK = p3s_rad_rho g0 B` THEN
  SUBGOAL_THEN `(!y:real^3. y IN K ==> p3_std_dist g0 y <= DK) /\ &0 <= DK`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "DK" THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_ROT_DIST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`; `B:real`]
             P3S_RHO_LT_EQ) THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&0`; `B:real`] P3S_RHO_LT_EQ) THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; P3S_RHO_0]];
    ALL_TAC] THEN
  ABBREV_TAC `dd = min (inv(DK + &1)) (min (inv(&m + &2)) (sqrt eta / &2))` THEN
  SUBGOAL_THEN `&0 < dd /\ dd < inv(&m + &1) /\ dd pow 2 < eta /\ DK + &1 <= inv dd`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt eta /\ sqrt eta pow 2 = eta` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < dd` ASSUME_TAC THENL
     [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LT_INV) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&m + &2)` THEN CONJ_TAC THENL
       [EXPAND_TAC "dd" THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV2 THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(sqrt eta / &2) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        EXPAND_TAC "dd" THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_POW_DIV] THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `DK + &1 = inv(inv(DK + &1))` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "dd" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < md(dd:real)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_modulus]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `DK:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&N1 <= &n /\ DK <= &n` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N2` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `DK:real` THEN ASM_SIMP_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[P3N_OPEN_UNIV_LOCAL; o_DEF; ETA_AX] THEN
  USE_THEN "H" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[p3_cap_param] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(hs:num->(A)rfs_history) n`; `(k:num->num) n`] P3N_VIEW_AT_EVENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `ts = hs_time ((hs:num->(A)rfs_history) n) ((k:num->num) n)` THEN
  MP_TAC(SPECL [`(dl:num->real->real) n ts`; `n:num`] P3N_INV_GE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(dl:num->real->real) n ts <= md(dd:real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N1)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [UNDISCH_TAC `~(N1 = 0)` THEN ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dd:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_close_on" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[rfs_close_on; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CL"))) THEN
  SUBGOAL_THEN `p3_std_dist g0 (y:real^3) < inv dd /\
                --(inv((dl:num->real->real) n ts)) < A0 + &4 - p3_std_dist g0 y`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `p3_std_dist g0 (y:real^3) <= DK` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg dd) g0
     (\z. inv((hh:num->real->real) n ts pow 2) %%
          rfs_pullback (hs_atlas ((hs:num->(A)rfs_history) n) ((k:num->num) n))
            ((Phi:num->real^3->A) n) (hs_metric (hs n) (k n) ts) z) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN
    EXISTS_TAC `{x:real^3 | --(inv((dl:num->real->real) n ts)) < A0 + &4 - p3_std_dist g0 x}` THEN
    ASM_SIMP_TAC[P3S_KREG_GE; IN_ELIM_THM] THEN
    SUBGOAL_THEN `open {x:real^3 | --(inv((dl:num->real->real) n ts)) <
                                   A0 + &4 - p3_std_dist g0 x}` ASSUME_TAC THENL
     [MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 < a ==> --x < a + &4`) THEN
      ASM_SIMP_TAC[REAL_LT_INV];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; ETA_AX; REAL_LT_INV_EQ; REAL_POW_LT] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `hs_top ((hs:num->(A)rfs_history) n) ((k:num->num) n)` THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
     [REMOVE_THEN "CL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

