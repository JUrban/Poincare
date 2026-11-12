(* ========================================================================= *)
(* Unit pc_rf_mequiv: two-sided exponential metric bounds on an open set     *)
(* where abs Rm is bounded along a Ricci flow (RFA_METRIC_EQUIV on the       *)
(* restricted manifold, transported back through the chart Jacobian of the   *)
(* restriction).  A separate unit, so that users need not load pc_p2c_sing   *)
(* (the names keep its prefix): SNGL_QF_NONNEG, SNGL_RESTRICT_QF,            *)
(* SNGL_METRIC_EQUIV_LOCAL.  pc_p2c_sing loads this unit.  Dependencies:     *)
(* P2CF_RFF_RESTRICT (pc_p2c_fview), P2AP_MFD_RICCI_ABS (pc_p2a_par),        *)
(* RFA_METRIC_EQUIV (pc_rfa_shi), RFA_METRIC_LOCAL_QFORM (pc_rfa_r1), the    *)
(* MFDR_ restriction lemmas (pc_mfd_restrict).                               *)
(* ========================================================================= *)

needs "src/pc_p2c_fview.ml";;
needs "src/pc_p2a_par.ml";;
needs "src/pc_rfa_r1.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The quadratic form of a metric is nonnegative; the                        *)
(* restricted metric is the metric read through an onto chart Jacobian;     *)
(* metric equivalence on an open set where abs Rm is bounded.               *)
(* ------------------------------------------------------------------------- *)

let SNGL_QF_NONNEG = prove
 (`!top atlas (g:A->real^N^N) x v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> &0 <= v dot (g x ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[RIEMANNIAN_METRIC_POS]);;

let SNGL_RESTRICT_QF = prove
 (`!top atlas (W:A->bool) x.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     open_in top W /\ x IN W
     ==> ?J:real^N->real^N.
           (!w. ?v. J v = w) /\
           !(g:A->real^N^N) v.
             v dot (restrict_metric atlas W g x ** v) = (J v) dot (g x ** J v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `x:A`] MFDR_RESTRICT_JAC_ISO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Kj:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `chart_jac (chart_at (restrict_atlas atlas W) x)
                        (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) (x:A)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:A->real^N^N`; `v:real^N`] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `g:A->real^N^N`; `x:A`] MFDR_RESTRICT_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool)`;
                 `(U:A->bool) INTER W`; `phi:A->real^N`] CHART_INV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool)`; `x:A`]
                  PDE_CHART_AT_FACTS) THEN
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `linear(chart_jac ((U:A->bool) INTER W,phi:A->real^N)
                                 (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[restrict_metric] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RFA_METRIC_LOCAL_QFORM] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let SNGL_METRIC_EQUIV_LOCAL = prove
 (`!top atlas (g:real->A->real^N^N) a b W K.
     ricci_flow_from (top,atlas) a b g /\ open_in top W /\ &0 <= K /\
     (!t x. a <= t /\ t < b /\ x IN W ==> mfd_rm_norm atlas (g t) x <= K)
     ==> !t x v. a <= t /\ t < b /\ x IN W
                 ==> exp(--(&2 * (&(dimindex(:N) - 1) * K) * (t - a))) *
                     (v dot (g a x ** v)) <= v dot (g t x ** v) /\
                     v dot (g t x ** v) <=
                     exp(&2 * (&(dimindex(:N) - 1) * K) * (t - a)) * (v dot (g a x ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
                (!t. a <= t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^N^N) t))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_from (top,atlas) a b (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = a` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool)`;
                 `a:real`; `b:real`; `\t. restrict_metric atlas W ((g:real->A->real^N^N) t)`;
                 `&(dimindex(:N) - 1) * K`] RFA_METRIC_EQUIV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC P2CF_RFF_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `v:real^N`] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `(g:real->A->real^N^N) t`] RIEMANNIAN_METRIC_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `(g:real->A->real^N^N) t`; `x:A`] MFD_RM_NORM_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool)`;
                   `restrict_metric atlas W ((g:real->A->real^N^N) t)`; `x:A`; `v:real^N`]
                  P2AP_MFD_RICCI_ABS) THEN
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; RIEMANNIAN_METRIC_RESTRICT;
                 TOPSPACE_SUBTOPOLOGY; IN_INTER; MFD_RM_NORM_RESTRICT] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SNGL_QF_NONNEG THEN
      MAP_EVERY EXISTS_TAC [`subtopology top (W:A->bool)`;
                            `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`] THEN
      ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY; IN_INTER]];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(LABEL_TAC "eq") THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `w:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `x:A`] SNGL_RESTRICT_QF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^N->real^N` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^N` o SPEC `w:real^N`) THEN
  USE_THEN "eq" (MP_TAC o SPECL [`t:real`; `x:A`; `v:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ASM_REWRITE_TAC[]]);;

