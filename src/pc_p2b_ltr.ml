(* ========================================================================= *)
(* Unit pc_p2b_ltr (Part 2B): the limit transfer of MT's proof of Cor 9.95   *)
(* (P2B_LIMIT_TRANSFER, history form; P2B_LIMIT_TRANSFER_VIEW, view form)    *)
(* and the extension of strong necks of kappa-solutions                      *)
(* (P2B_KSOL_NECK_EXTEND_Q).  The route is P2BL_LIMIT_TRANSFER_FROM_PARTS.   *)
(*                                                                           *)
(* Contents:                                                                 *)
(* - the type-preserving open form P2B_PROP_9_79_OPEN_TYPED_STATEMENT and    *)
(*   its proof;                                                              *)
(* - flow limits give diffeomorphisms and closeness on compact sets          *)
(*   (P2BL_FLOW_LIMIT_CLOSE, P2BL_STATIC_DATA);                              *)
(* - compact closures of necks and caps in complete slices, images of        *)
(*   compact components, slices of histories, the kappa-solution view, the   *)
(*   slice condition p2bl_vslices;                                           *)
(* - the four cases (general views), P2BL_LIMIT_TRANSFER_FROM_PARTS and      *)
(*   P2BL_LIMIT_TRANSFER_VIEW_FROM_PARTS;                                    *)
(* - smoothness and continuity of the C^k distance between time slices;      *)
(* - the tube lemma on compact sets and the extension arithmetic;            *)
(* - P2B_KSOL_NECK_EXTEND_Q (strong necks of kappa-solutions extend);        *)
(* - the main theorems P2B_LIMIT_TRANSFER and P2B_LIMIT_TRANSFER_VIEW.       *)
(* ========================================================================= *)

needs "src/pc_p2b_cap.ml";;
needs "src/pc_p2b_cscale.ml";;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_rf_unique.ml";;

prioritize_real();;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The four alternatives of a canonical neighbourhood keep their type under  *)
(* the open transfer of Prop 9.79 (P2B_PROP_9_79_OPEN_TYPED_STATEMENT).      *)
(* ------------------------------------------------------------------------- *)

let P2B_PROP_9_79_OPEN_TYPED_STATEMENT = new_definition
 `P2B_PROP_9_79_OPEN_TYPED_STATEMENT (u:A->bool) (w:B->bool) <=>
    (!eps top atlas (g:A->real^3^3) x e.
       &0 < eps /\ eps < &1 / &4 /\ riemannian_metric atlas g /\
       rfs_neck (top,atlas) g eps x e
       ==> ?delta. &0 < delta /\
             !top' atlas' (g':B->real^3^3) psi psi'.
                smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
                mfd_diffeo top atlas (IMAGE e (rfs_neck_dom eps)) top' atlas'
                           (IMAGE psi (IMAGE e (rfs_neck_dom eps))) psi psi' /\
                rfs_mclose (rfs_kreg delta) delta atlas (IMAGE e (rfs_neck_dom eps))
                  (\y. mfd_scalar atlas g x %% g y)
                  (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                ==> rfs_neck (top',atlas') g' eps (psi x) (psi o e)) /\
    (?eps0. &0 < eps0 /\ eps0 <= &1 / &8 /\
       !C eps top atlas (g:A->real^3^3) x U Y.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
         rfs_cap (top,atlas) g C eps U Y /\ x IN Y /\
         compact_in top (top closure_of U)
         ==> ?delta. &0 < delta /\
               !top' atlas' (g':B->real^3^3) psi psi'.
                  hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
                  riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
                  mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
                  rfs_mclose (rfs_kreg delta) delta atlas U
                    (\y. mfd_scalar atlas g x %% g y)
                    (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                  ==> rfs_cap (top',atlas') g' C eps (IMAGE psi U) (IMAGE psi Y)) /\
    (!C top atlas (g:A->real^3^3) x U.
       &1 < C /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
       rfs_c_component (top,atlas) g C U /\ x IN U
       ==> ?delta. &0 < delta /\
             !top' atlas' (g':B->real^3^3) psi psi'.
                smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
                mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
                IMAGE psi U IN connected_components_of top' /\
                rfs_mclose (rfs_kreg delta) delta atlas U
                  (\y. mfd_scalar atlas g x %% g y)
                  (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                ==> rfs_c_component (top',atlas') g' C (IMAGE psi U)) /\
    (!eps top atlas (g:A->real^3^3) x U.
       &0 < eps /\ eps <= &1 / &2 /\
       smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
       rfs_round_component (top,atlas) g eps U /\ x IN U /\ &0 < mfd_scalar atlas g x
       ==> ?delta. &0 < delta /\
             !top' atlas' (g':B->real^3^3) psi psi'.
                smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
                mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
                IMAGE psi U IN connected_components_of top' /\
                rfs_mclose (rfs_kreg delta) delta atlas U
                  (\y. mfd_scalar atlas g x %% g y)
                  (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                ==> rfs_round_component (top',atlas') g' eps (IMAGE psi U))`;;

let P2B_PROP_9_79_OPEN_TYPED = prove
 (`!(u:A->bool) (w:B->bool). P2B_PROP_9_79_OPEN_TYPED_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_PROP_9_79_OPEN_TYPED_STATEMENT] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_ACCEPT_TAC P2B9S_OPEN_NECK;
    MATCH_ACCEPT_TAC (MP P2BC_OPEN_CAP P2B_REQ_LRG_DERIV);
    MATCH_ACCEPT_TAC (MP P2B9S_OPEN_CCOMP P2B_REQ_LRG_DERIV);
    MATCH_ACCEPT_TAC P2B9S_OPEN_ROUND]);;

(* ------------------------------------------------------------------------- *)
(* The neck extension with eps < 1/4 (the bound of NECK_OPEN; the base       *)
(* change LRG_CK_BASE_CHANGE needs closeness <= 1/4).  The routes use this   *)
(* form instead of P2B_KSOL_NECK_EXTEND_STATEMENT of pc_p2b_defs.            *)
(* ------------------------------------------------------------------------- *)

let P2B_KSOL_NECK_EXTEND_Q_STATEMENT = new_definition
 `P2B_KSOL_NECK_EXTEND_Q_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) eps x e.
       p2b_kappa_solution kappa (top,atlas) g /\ &0 < eps /\ eps < &1 / &4 /\
       rfs_strong_neck (p2b_kview (top,atlas) g) eps x (&0) e
       ==> ?a. &1 < a /\ rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0) a e`;;

(* ------------------------------------------------------------------------- *)
(* From p3_flow_limit to the closeness forms of the open transfers: the      *)
(* chart form of pullback metrics, the pointwise conversion with rescaling,  *)
(* uniform closeness on compact sets over a time interval, and the static    *)
(* data at time 0 (views whose nonempty slices are smooth Riemannian).       *)
(* ------------------------------------------------------------------------- *)

let P2BL_PB_CHART = prove
 (`!top atlas top' atlas' W W' (f:A->B) f' (g':B->real^N^N) c z.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas W top' atlas' W' f f' /\ c IN atlas /\
     z IN IMAGE (SND c) (FST c INTER W)
     ==> metric_local atlas c (mfd_pullback_metric atlas atlas' f g') z =
         rfs_pullback atlas' (f o chart_inv c) g' z`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`;
    `f:A->B`; `f':B->A`; `g':B->real^N^N`; `U:A->bool`; `phi:A->real^N`; `z:real^N`] THEN
  REWRITE_TAC[FST; SND; IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(f:A->B) x IN W'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:A->B) W SUBSET W'` THEN UNDISCH_TAC `(x:A) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    UNDISCH_TAC `(f:A->B) x IN W'` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `(f:A->B) x`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `f':B->A`; `g':B->real^N^N`; `U:A->bool`; `phi:A->real^N`;
                 `FST(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x))`;
                 `SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x))`;
                 `W:A->bool`; `W':B->bool`; `x:A`] P2B9S_PB_LOCAL_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rfs_pullback; o_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`] CHART_INV) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[o_ASSOC]);;

let P2BL_LCK_CHART_CONVERT = prove
 (`!top atlas top' atlas' W W' (f:A->B) f' (g:A->real^N^N) (g':B->real^N^N) R Q m y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas W top' atlas' W' f f' /\ y IN W /\ &0 < R /\ &0 < Q
     ==> lck_dist2 m (metric_local atlas (chart_at atlas y) (\z. R %% g z))
                     (metric_local atlas (chart_at atlas y)
                        (\z. (R * Q) %% mfd_pullback_metric atlas atlas' f g' z))
                     (SND(chart_at atlas y) y)
         <= (&1 + inv R) pow m *
            lck_dist2 m (metric_local atlas (chart_at atlas y) g)
                        (\z. Q %% rfs_pullback atlas' (f o chart_inv (chart_at atlas y)) g' z)
                        (SND(chart_at atlas y) y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (W':B->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) W top'
                   (atlas':((B->bool)#(B->real^N))->bool) W' (f:A->B) f'` THEN
    SIMP_TAC[mfd_diffeo];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ (f:A->B) y IN topspace top'` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    MP_TAC(ISPECL [`top':B topology`; `W':B->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:A->B) W SUBSET W'` THEN UNDISCH_TAC `(y:A) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `(f:A->B) y`]
                CHART_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) y` THEN
  ABBREV_TAC `c' = chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) y)` THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`; `W:A->bool`; `f:A->B`]
                MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = IMAGE (SND (c:(A->bool)#(A->real^N)))
                    {x | x IN FST c INTER W /\ (f:A->B) x IN FST (c':(B->bool)#(B->real^N))}` THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) y IN s /\
                s SUBSET IMAGE (SND c) (FST c INTER W) /\
                s SUBSET IMAGE (SND c) (FST c)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    CONJ_TAC THENL [EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field s (metric_local atlas c (g:A->real^N^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) s (chart_inv c)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  MFD_PARAM_CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (chart_inv (c:(A->bool)#(A->real^N))) s SUBSET W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `s SUBSET IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE; IN_INTER] THEN
    DISCH_TAC THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field s
                  (\z. Q %% rfs_pullback atlas' ((f:A->B) o chart_inv c) (g':B->real^N^N) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `W:A->bool`; `W':B->bool`; `f':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  SUBGOAL_THEN
   `lck_dist2 m (\z. R %% metric_local atlas c (g:A->real^N^N) z)
      (\z. (R * Q) %% metric_local atlas c (mfd_pullback_metric atlas atlas' (f:A->B)
                                                (g':B->real^N^N)) z)
      (SND (c:(A->bool)#(A->real^N)) y) =
    lck_dist2 m (\z. R %% metric_local atlas c g z)
      (\z. R %% (\w. Q %% rfs_pullback atlas' (f o chart_inv c) g' w) z)
      (SND c y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC P2BL_PB_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `W:A->bool`; `W':B->bool`;
                          `f':B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2B9S_LCK_SCALE_LE THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2BL_FLOW_LIMIT_CLOSE = prove
 (`!V x t Q (top:B topology) atlas g xl Tl.
     p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) x t Q (top,atlas) g xl Tl /\
     (!k s. ~(topspace(rfs_vtop (V k) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V k) s) (rfs_vatlas (V k) s) /\
                riemannian_metric (rfs_vatlas (V k) s) (rfs_vmetric (V k) s))
     ==> ?phi. (!k. phi k xl = x k) /\
           !K U a0 delta R.
             compact_in top K /\ open_in top U /\ U SUBSET K /\ --Tl < a0 /\ a0 <= &0 /\
             &0 < delta /\ &0 < R
             ==> ?k0. !k. k0 <= k
                    ==> !s. a0 <= s /\ s <= &0
                            ==> (?psi. mfd_diffeo top atlas U
                                         (rfs_vtop (V k) (t k + s / Q k))
                                         (rfs_vatlas (V k) (t k + s / Q k))
                                         (IMAGE (phi k) U) (phi k) psi) /\
                                rfs_mclose (rfs_kreg delta) delta atlas U
                                  (\y. R %% g s y)
                                  (\y. (R * Q k) %%
                                       mfd_pullback_metric atlas
                                         (rfs_vatlas (V k) (t k + s / Q k)) (phi k)
                                         (rfs_vmetric (V k) (t k + s / Q k)) y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "slices")) THEN
  REWRITE_TAC[p3_flow_limit] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "close" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "diffeo" o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "flow" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th))) THEN
  EXISTS_TAC `phi:num->B->A` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `U:B->bool`; `a0:real`; `delta:real`; `R:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `m = rfs_kreg delta` THEN
  SUBGOAL_THEN `&0 < (&1 + inv R) pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `R:real` REAL_LT_INV) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "close" (MP_TAC o SPECL [`K:B->bool`; `m:num`;
                                       `delta pow 2 / (&2 * (&1 + inv R) pow m)`; `a0:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  USE_THEN "diffeo" (MP_TAC o SPECL [`k:num`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  SUBGOAL_THEN `(U:B->bool) SUBSET W(k:num)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) U (rfs_vtop ((V:num->(real->A topology)#
                                    (real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k))
      (rfs_vatlas (V k) (t k + s / Q k)) (IMAGE ((phi:num->B->A) k) U) (phi k) psi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [EXISTS_TAC `psi:A->B` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s)` ASSUME_TAC THENL
   [ASM_CASES_TAC `s = &0` THENL
     [USE_THEN "flow" (MP_TAC o SPEC `(a0 - Tl) / &2`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[rfs_flow_upto];
      USE_THEN "flow" (MP_TAC o SPEC `(a0 - Tl) / &2`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN
      DISCH_THEN(MP_TAC o el 2 o CONJUNCTS o CONJUNCT1) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `delta pow 2 / &2` THEN CONJ_TAC THENL
   [MP_TAC(SPEC `delta:real` REAL_POW_2) THEN
    SUBGOAL_THEN `&0 < delta pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#
                                    (real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k))
                          (rfs_vatlas (V k) (t k + s / Q k)) /\
    riemannian_metric (rfs_vatlas (V k) (t k + s / Q k)) (rfs_vmetric (V k) (t k + s / Q k))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "slices" MATCH_MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `(phi:num->B->A) k y` THEN
    UNDISCH_TAC
     `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) U
        (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) k) (t k + s / Q k))
        (rfs_vatlas (V k) (t k + s / Q k)) (IMAGE ((phi:num->B->A) k) U) (phi k) psi` THEN
    REWRITE_TAC[mfd_diffeo] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + inv R) pow m *
              lck_dist2 m (metric_local atlas (chart_at atlas y) ((g:real->B->real^3^3) s))
                (\z. Q k %%
                     rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#
                                    (real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k))
                                  ((phi:num->B->A) k o chart_inv (chart_at atlas y))
                                  (rfs_vmetric (V k) (t k + s / Q k)) z)
                (SND(chart_at atlas y) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BL_LCK_CHART_CONVERT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`;
                          `rfs_vtop ((V:num->(real->A topology)#
                                    (real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)`;
                          `U:B->bool`; `IMAGE ((phi:num->B->A) k) U`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPECL [`s:real`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + inv R) pow m * delta pow 2 / (&2 * (&1 + inv R) pow m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < (&1 + inv R) pow m` THEN CONV_TAC REAL_FIELD]);;

(* The static data of a flow limit at time 0, for the slices t n of views
   whose nonempty slices are smooth Riemannian: diffeomorphisms of an open U
   with compact closure, and closeness of R g(0) to R Q_n times the pullback
   by phi_n of the metric of V_n at t_n. *)

let P2BL_STATIC_DATA = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl K U delta R.
     (!k s. ~(topspace(rfs_vtop (V k) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V k) s) (rfs_vatlas (V k) s) /\
                riemannian_metric (rfs_vatlas (V k) s) (rfs_vmetric (V k) s)) /\
     (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top,atlas) g xl Tl) /\
     compact_in top K /\ open_in top U /\ U SUBSET K /\ &0 < delta /\ &0 < R
     ==> ?phi k0. (!n. phi n xl = x n) /\ (!n. &0 < Q n) /\
                  !n. k0 <= n
                      ==> (?psi. mfd_diffeo top atlas U
                                   (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n))
                                   (IMAGE (phi n) U) (phi n) psi) /\
                          rfs_mclose (rfs_kreg delta) delta atlas U
                            (\y. R %% g (&0) y)
                            (\y. R %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                       (\z. Q n %% rfs_vmetric (V n) (t n) z) y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o SPEC `&1`)
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[REAL_LT_01] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3_flow_limit]) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `Q:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `&1`] P2BL_FLOW_LIMIT_CLOSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->B->A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPECL [`K:B->bool`; `U:B->bool`; `&0`; `delta:real`; `R:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`phi:num->B->A`; `k0:num`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[P2B9S_PB_CMUL; MATRIX_CMUL_ASSOC; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Compact closures (bounded sets of complete manifolds, necks, caps),       *)
(* images of compact components, slices of histories, kappa-solutions and    *)
(* their views, and the slice condition p2bl_vslices.                        *)
(* ------------------------------------------------------------------------- *)

let P2BL_BOUNDED_CLOSURE_COMPACT = prove
 (`!top atlas (g:A->real^N^N) x S D.
     hausdorff_space top /\ mfd_complete (top,atlas) g /\ x IN topspace top /\
     (!y. y IN S ==> mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y <= D)
     ==> compact_in top (top closure_of S)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact_in top (mfd_cball (top,atlas) (g:A->real^N^N) x D)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_complete]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) x D` THEN
  ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
  ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN
  REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let P2BL_NECK_CLOSURE_COMPACT = prove
 (`!top atlas (g:A->real^3^3) eps x e.
     hausdorff_space top /\ riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     rfs_neck (top,atlas) g eps x e /\ eps < &1
     ==> compact_in top (top closure_of IMAGE e (rfs_neck_dom eps))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2BL_BOUNDED_CLOSURE_COMPACT) THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`;
    `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
     (inv eps + sqrt(&2) * pi)`] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y0:real^3`; `y:real^3`]
                APX_NECK_DIST_UPPER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
              (abs(apx_sval y0 - apx_sval y) + sqrt(&2) * pi)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs a <= b ==> a + c <= b + c`) THEN
  SUBGOAL_THEN `apx_sval y0 = &0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]; ALL_TAC] THEN
  UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
  REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN REAL_ARITH_TAC);;

let P2BL_CAP_CLOSURE_COMPACT = prove
 (`!top atlas (g:A->real^3^3) C eps U Y x.
     hausdorff_space top /\ riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     rfs_cap (top,atlas) g C eps U Y /\ x IN Y
     ==> compact_in top (top closure_of U)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B_CAP_CORE_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_CAP_JOINABLE) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_cap]) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist_in")) (concl th) &&
    not (is_forall (concl th)))) THEN
  REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2BL_BOUNDED_CLOSURE_COMPACT) THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`;
                        `dd:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U (x:A) y` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_IMP]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) U x y` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[rfs_cap];
    FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`x:A`; `y:A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let P2BL_COMPONENT_IMAGE = prove
 (`!top atlas top' atlas' (U:A->bool) (f:A->B) f'.
     hausdorff_space top' /\ U IN connected_components_of top /\ compact_in top U /\
     mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) U
                top' (atlas':((B->bool)#(B->real^N))->bool) (IMAGE f U) f f'
     ==> IMAGE f U IN connected_components_of top'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_CLOPEN_COMPONENT THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology top (U:A->bool)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    ASM_MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENTS_OF];
    ASM_MESON_TAC[mfd_diffeo];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology top (U:A->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF]]);;

let P2BL_VIEW_TRIPLE = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     V = (rfs_vtop V,rfs_vatlas V,rfs_vmetric V)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2BL_COMPACT_COMPLETE = prove
 (`!top atlas (g:A->real^N^N).
     compact_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
     ==> mfd_complete (top,atlas) g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_complete] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED]);;

let P2BL_ROUND_SCALAR_POS = prove
 (`!top atlas (g:A->real^3^3) eps U x.
     &0 < eps /\ eps <= &1 / &40 /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ rfs_round_component (top,atlas) g eps U /\ x IN U
     ==> &0 < mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `rfs_round_component (top,atlas) (g:A->real^3^3) eps U` THEN
    REWRITE_TAC[rfs_round_component] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN U` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `U:A->bool`; `x:A`] APX_ROUND_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`u1:real^3`; `v1:real^3`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u1:real^3`; `v1:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < mfd_sectional atlas (g:A->real^3^3) x u1 v1 / q` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]]);;

let P2BL_KSOL_FACTS = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\
         (!s. s <= &0 ==> riemannian_metric atlas (g s)) /\
         mfd_complete (top,atlas) (g (&0)) /\
         (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL [ASM_SIMP_TAC[rfs_flow_upto]; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN
  DISCH_THEN(MP_TAC o el 2 o CONJUNCTS o CONJUNCT1) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2BL_KVIEW_REGULAR = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> p2c_regular_view (p2b_kview (top,atlas) g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  REWRITE_TAC[p2b_kview] THEN MATCH_MP_TAC P2CF_FLOW_VIEW_REGULAR_GEN THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `b <= &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `b = &0` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a:real`; `&0`] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto"))
          (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]]];
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `b <= &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2CF_RFO_FROM THEN MAP_EVERY EXISTS_TAC [`a - &1`; `&0`] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a - &1` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto"))
        (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]]]);;

let P2BL_HIST_SLICE_FACTS = prove
 (`!(hs:(A)rfs_history) t x c.
     rfs_history_ok hs /\ x IN topspace(rfs_top_at hs t) /\ &0 < c
     ==> hausdorff_space (rfs_vtop (rfs_view hs) t) /\
         smooth_manifold_atlas (rfs_vtop (rfs_view hs) t) (rfs_vatlas (rfs_view hs) t) /\
         riemannian_metric (rfs_vatlas (rfs_view hs) t) (rfs_vmetric (rfs_view hs) t) /\
         riemannian_metric (rfs_vatlas (rfs_view hs) t)
                           (\y. c %% rfs_vmetric (rfs_view hs) t y) /\
         mfd_complete (rfs_vtop (rfs_view hs) t,rfs_vatlas (rfs_view hs) t)
                      (\y. c %% rfs_vmetric (rfs_view hs) t y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `t:real`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas (rfs_view hs) t)
                  (\y. c %% rfs_vmetric (rfs_view (hs:(A)rfs_history)) t y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vatlas (rfs_view (hs:(A)rfs_history)) t`;
                   `rfs_vmetric (rfs_view (hs:(A)rfs_history)) t`; `c:real`]
                  RIEMANNIAN_METRIC_CMUL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rfs_vtop (rfs_view hs) t = rfs_top_at (hs:(A)rfs_history) t`
  SUBST1_TAC THENL [REWRITE_TAC[rfs_view; rfs_vtop]; ALL_TAC] THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `t:real`; `x:A`] P2B_HS_SLICE_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BL_COMPACT_COMPLETE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `smooth_manifold_atlas (rfs_vtop (rfs_view hs) t)
                   (rfs_vatlas (rfs_view (hs:(A)rfs_history)) t)` THEN
    REWRITE_TAC[rfs_view; rfs_vtop]] THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `t:real`; `x:A`] P2B_HS_SLICE_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
  DISCH_THEN(MP_TAC o SPEC `rfs_slab (hs:(A)rfs_history) t` o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* The slice condition used by the case lemmas below: nonempty slices are
   Hausdorff smooth Riemannian, and the base slices contain x n and are
   complete.  It holds for history views (P2BL_HIST_VSLICES) and for regular
   views with complete base slices (P2BL_REGULAR_VSLICES). *)

let p2bl_vslices = new_definition
 `p2bl_vslices (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) (x:num->A) (t:num->real) <=>
    (!k s. ~(topspace(rfs_vtop (V k) s) = {})
           ==> hausdorff_space (rfs_vtop (V k) s) /\
               smooth_manifold_atlas (rfs_vtop (V k) s) (rfs_vatlas (V k) s) /\
               riemannian_metric (rfs_vatlas (V k) s) (rfs_vmetric (V k) s)) /\
    (!k. x k IN topspace(rfs_vtop (V k) (t k)) /\
         mfd_complete (rfs_vtop (V k) (t k),rfs_vatlas (V k) (t k)) (rfs_vmetric (V k) (t k)))`;;

let P2BL_VSLICES_SLICES = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t.
     p2bl_vslices V x t
     ==> !k s. ~(topspace(rfs_vtop (V k) s) = {})
               ==> smooth_manifold_atlas (rfs_vtop (V k) s) (rfs_vatlas (V k) s) /\
                   riemannian_metric (rfs_vatlas (V k) s) (rfs_vmetric (V k) s)`,
  REWRITE_TAC[p2bl_vslices] THEN MESON_TAC[]);;

let P2BL_VSLICE_FACTS = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t n c.
     p2bl_vslices V x t /\ &0 < c
     ==> hausdorff_space (rfs_vtop (V n) (t n)) /\
         smooth_manifold_atlas (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n)) /\
         riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
         riemannian_metric (rfs_vatlas (V n) (t n)) (\y. c %% rfs_vmetric (V n) (t n) y) /\
         mfd_complete (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                      (\y. c %% rfs_vmetric (V n) (t n) y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bl_vslices] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) n) (t n)) /\
    smooth_manifold_atlas (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n)) /\
    riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) n) (t n)`; `c:real`]
                RIEMANNIAN_METRIC_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) n) (t n)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) n) (t n)`; `c:real`]
                MFD_COMPLETE_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let P2BL_HIST_VSLICES = prove
 (`!(hs:num->(A)rfs_history) x t.
     (!n. rfs_history_ok (hs n) /\ x n IN topspace(rfs_top_at (hs n) (t n)))
     ==> p2bl_vslices (\n. rfs_view (hs n)) x t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bl_vslices] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `y:A`) THEN
    MP_TAC(SPECL [`(hs:num->(A)rfs_history) k`; `s:real`; `y:A`; `&1`]
                 P2BL_HIST_SLICE_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01] THEN
      UNDISCH_TAC `(y:A) IN topspace(rfs_vtop (rfs_view ((hs:num->(A)rfs_history) k)) s)` THEN
      REWRITE_TAC[rfs_view; rfs_vtop];
      SIMP_TAC[]];
    X_GEN_TAC `k:num` THEN
    MP_TAC(SPECL [`(hs:num->(A)rfs_history) k`; `(t:num->real) k`; `(x:num->A) k`; `&1`]
                 P2BL_HIST_SLICE_FACTS) THEN
    ASM_REWRITE_TAC[REAL_LT_01; MATRIX_CMUL_LID; ETA_AX] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `!n. rfs_history_ok ((hs:num->(A)rfs_history) n) /\
                     (x:num->A) n IN topspace(rfs_top_at (hs n) ((t:num->real) n))` THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[rfs_view; rfs_vtop] THEN SIMP_TAC[]]);;

let P2BL_REGULAR_VSLICES = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t.
     (!n. p2c_regular_view (V n) /\ x n IN topspace(rfs_vtop (V n) (t n)) /\
          mfd_complete (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)))
     ==> p2bl_vslices V x t`,
  REWRITE_TAC[p2bl_vslices; p2c_regular_view] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The four alternatives of the limit's canonical neighbourhood, for views   *)
(* with the slice condition p2bl_vslices: caps, C-components and round       *)
(* components through the typed open transfer and scale invariance           *)
(* (pc_p2b_cscale); necks through NECK_OPEN (strong necks, from an evolving  *)
(* neck of length a > 1) or NECK_OPEN_L (necks of length L, from length L +  *)
(* 1), in P2BL_NECK_LIMIT for a general target predicate P.  Then            *)
(* P2BL_LIMIT_TRANSFER_FROM_PARTS (history form) and                         *)
(* P2BL_LIMIT_TRANSFER_VIEW_FROM_PARTS (view form).                          *)
(* ------------------------------------------------------------------------- *)

let P2BL_CAP_LIMIT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl kappa C eps U Y.
     p2bl_vslices V x t /\
     (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top,atlas) g xl Tl) /\
     p2b_kappa_solution kappa (top,atlas) g /\
     rfs_cap (top,atlas) (g (&0)) C eps U Y /\ xl IN Y /\
     (?delta. &0 < delta /\
        !top' atlas' (g':A->real^3^3) psi psi'.
           hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
           riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
           mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
           rfs_mclose (rfs_kreg delta) delta atlas U
             (\y. mfd_scalar atlas (g (&0)) xl %% g (&0) y)
             (\y. mfd_scalar atlas (g (&0)) xl %% mfd_pullback_metric atlas atlas' psi g' y)
           ==> rfs_cap (top',atlas') g' C eps (IMAGE psi U) (IMAGE psi Y))
     ==> ?N. !n. N <= n
                 ==> ?U' Y'. rfs_cap (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                                     (rfs_vmetric (V n) (t n)) C eps U' Y' /\ x n IN Y'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")))))))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BL_VSLICES_SLICES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B_CAP_CORE_SUBSET) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_CAP_RATIO) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (U:B->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_cap]) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `top closure_of (U:B->bool)`; `U:B->bool`;
                 `delta:real`; `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl`]
                P2BL_STATIC_DATA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BL_CAP_CLOSURE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) (&0)`;
                            `C:real`; `eps:real`; `Y:B->bool`; `xl:B`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->B->A` (X_CHOOSE_THEN `k0:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_mclose")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `n:num`; `(Q:num->real) n`] P2BL_VSLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "D" (MP_TAC o SPECL
   [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
    `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
    `\z. (Q:num->real) n %% rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) z`;
    `(phi:num->B->A) n`; `psi:A->B`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                 `C:real`; `eps:real`; `IMAGE ((phi:num->B->A) n) U`;
                 `IMAGE ((phi:num->B->A) n) Y`; `(Q:num->real) n`] P2BCS_CAP_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE ((phi:num->B->A) n) U`; `IMAGE ((phi:num->B->A) n) Y`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:num->A) n = (phi:num->B->A) n xl` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let P2BL_CCOMP_LIMIT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl kappa C U.
     p2bl_vslices V x t /\
     (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top,atlas) g xl Tl) /\
     p2b_kappa_solution kappa (top,atlas) g /\
     rfs_c_component (top,atlas) (g (&0)) C U /\ xl IN U /\
     (?delta. &0 < delta /\
        !top' atlas' (g':A->real^3^3) psi psi'.
           smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
           mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
           IMAGE psi U IN connected_components_of top' /\
           rfs_mclose (rfs_kreg delta) delta atlas U
             (\y. mfd_scalar atlas (g (&0)) xl %% g (&0) y)
             (\y. mfd_scalar atlas (g (&0)) xl %% mfd_pullback_metric atlas atlas' psi g' y)
           ==> rfs_c_component (top',atlas') g' C (IMAGE psi U))
     ==> ?N. !n. N <= n
                 ==> ?U'. x n IN U' /\
                          rfs_c_component (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                                          (rfs_vmetric (V n) (t n)) C U'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")))))))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BL_VSLICES_SLICES) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `C:real`; `U:B->bool`; `xl:B`]
                P2B_C_COMPONENT_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:B->bool) IN connected_components_of top /\ compact_in top U /\
                open_in top U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_c_component (top,atlas) ((g:real->B->real^3^3) (&0)) C U` THEN
    REWRITE_TAC[rfs_c_component] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] APX_COMPONENT_OPEN) THEN
    EXISTS_TAC `atlas:((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `U:B->bool`; `U:B->bool`;
                 `delta:real`; `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl`]
                P2BL_STATIC_DATA) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->B->A` (X_CHOOSE_THEN `k0:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_mclose")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `n:num`; `(Q:num->real) n`] P2BL_VSLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE ((phi:num->B->A) n) U IN
                connected_components_of (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2BL_COMPONENT_IMAGE) THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
      `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "D" (MP_TAC o SPECL
   [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
    `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
    `\z. (Q:num->real) n %% rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) z`;
    `(phi:num->B->A) n`; `psi:A->B`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                 `C:real`; `IMAGE ((phi:num->B->A) n) U`; `(Q:num->real) n`]
                P2BCS_CCOMP_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE ((phi:num->B->A) n) U` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:num->A) n = (phi:num->B->A) n xl` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let P2BL_ROUND_LIMIT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl kappa eps U.
     p2bl_vslices V x t /\
     (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top,atlas) g xl Tl) /\
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < eps /\ eps <= &1 / &40 /\
     rfs_round_component (top,atlas) (g (&0)) eps U /\ xl IN U /\
     (?delta. &0 < delta /\
        !top' atlas' (g':A->real^3^3) psi psi'.
           smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
           mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
           IMAGE psi U IN connected_components_of top' /\
           rfs_mclose (rfs_kreg delta) delta atlas U
             (\y. mfd_scalar atlas (g (&0)) xl %% g (&0) y)
             (\y. mfd_scalar atlas (g (&0)) xl %% mfd_pullback_metric atlas atlas' psi g' y)
           ==> rfs_round_component (top',atlas') g' eps (IMAGE psi U))
     ==> ?N. !n. N <= n
                 ==> ?U'. x n IN U' /\
                          rfs_round_component (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                                              (rfs_vmetric (V n) (t n)) eps U'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")))))))))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BL_VSLICES_SLICES) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BL_ROUND_SCALAR_POS THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `eps:real`; `U:B->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:B->bool) IN connected_components_of top /\ compact_in top U /\
                open_in top U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_round_component (top,atlas) ((g:real->B->real^3^3) (&0)) eps U` THEN
    REWRITE_TAC[rfs_round_component] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] APX_COMPONENT_OPEN) THEN
    EXISTS_TAC `atlas:((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `U:B->bool`; `U:B->bool`;
                 `delta:real`; `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl`]
                P2BL_STATIC_DATA) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->B->A` (X_CHOOSE_THEN `k0:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_mclose")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `n:num`; `(Q:num->real) n`] P2BL_VSLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE ((phi:num->B->A) n) U IN
                connected_components_of (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2BL_COMPONENT_IMAGE) THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
      `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "D" (MP_TAC o SPECL
   [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
    `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
    `\z. (Q:num->real) n %% rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) z`;
    `(phi:num->B->A) n`; `psi:A->B`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                 `eps:real`; `IMAGE ((phi:num->B->A) n) U`; `(Q:num->real) n`]
                P2BCS_ROUND_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE ((phi:num->B->A) n) U` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:num->A) n = (phi:num->B->A) n xl` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let P2BL_KVIEW_ACCESS = prove
 (`!top atlas (g:real->B->real^3^3) s x.
     rfs_vatlas (p2b_kview (top,atlas) g) s = atlas /\
     rfs_vmetric (p2b_kview (top,atlas) g) s = g s /\
     (s <= &0 ==> rfs_vtop (p2b_kview (top,atlas) g) s = top) /\
     rfs_vscalar (p2b_kview (top,atlas) g) s x = mfd_scalar atlas (g s) x`,
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar;
              IN_ELIM_THM] THEN
  SIMP_TAC[]);;

let P2BL_KVIEW_NECK0 = prove
 (`!top atlas (g:real->B->real^3^3) eps x a e.
     rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0) a e
     ==> rfs_neck (top,atlas) (g (&0)) eps x e /\ &0 < a`,
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_evolving_neck; IN_ELIM_THM; REAL_LE_REFL] THEN
  SIMP_TAC[]);;

let P2BL_NECK_LIMIT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl kappa eps a e
    (P:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->real->A->bool).
     p2bl_vslices V x t /\
     (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top,atlas) g xl Tl) /\
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < eps /\ eps < &1 /\
     rfs_evolving_neck (p2b_kview (top,atlas) g) eps xl (&0) a e /\
     (?delta. &0 < delta /\
        !V' t' Q' psi.
          (!s. --a < s /\ s <= &0
               ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                         (rfs_vatlas V' (t' + s / Q')) /\
                   riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                     (rfs_vmetric V' (t' + s / Q'))) /\
          p3_view_close (p2b_kview (top,atlas) g) (&0)
            (rfs_vscalar (p2b_kview (top,atlas) g) (&0) xl) (IMAGE e (rfs_neck_dom eps))
            (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) t' Q' psi {s | --a < s /\ s <= &0} delta
          ==> P V' t' (psi xl))
     ==> ?N. !n. N <= n ==> P (V n) (t n) (x n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim")
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NO"))))))))) THEN
  FIRST_ASSUM(LABEL_TAC "sl" o MATCH_MP P2BL_VSLICES_SLICES) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KVIEW_NECK0) THEN
  ABBREV_TAC `R = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (e:real^3->B) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_neck" with Failure _ -> false)) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->B`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (top closure_of IMAGE (e:real^3->B) (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BL_NECK_CLOSURE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`;
                          `(g:real->B->real^3^3) (&0)`; `xl:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "lim" (MP_TAC o SPEC `a / R + &1`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3_flow_limit]) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `Q:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `a / R + &1`] P2BL_FLOW_LIMIT_CLOSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->B->A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPECL [`top closure_of IMAGE (e:real^3->B) (rfs_neck_dom eps)`;
                             `IMAGE (e:real^3->B) (rfs_neck_dom eps)`;
                             `--(a / R)`; `delta:real`; `R:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_NEG_LE0] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  SUBGOAL_THEN `(xl:B) IN IMAGE (e:real^3->B) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_neck" with Failure _ -> false)) THEN
    STRIP_TAC THEN MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s. k0 <= n /\ --a < s /\ s <= &0
          ==> smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / (R * Q n)))
                                    (rfs_vatlas (V n) (t n + s / (R * Q n))) /\
              riemannian_metric (rfs_vatlas (V n) (t n + s / (R * Q n)))
                                (rfs_vmetric (V n) (t n + s / (R * Q n)))`
  (LABEL_TAC "slk") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:num->real) n + s / (R * Q n) = t n + (s / R) / Q n` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 < (Q:num->real) n` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    USE_THEN "sl" MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(phi:num->B->A) n xl` THEN
    USE_THEN "k0" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s / R`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
        REWRITE_TAC[REAL_ARITH `--(s / R) = --s / R`] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `psi:A->B` MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[mfd_diffeo] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
    MATCH_MP_TAC(SET_RULE `(a:A) IN s ==> s SUBSET t ==> a IN t`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REMOVE_THEN "NO" (MP_TAC o SPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
                                    `(t:num->real) n`; `R * (Q:num->real) n`;
                                    `(phi:num->B->A) n`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "slk" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[p3_view_close; P2BL_KVIEW_ACCESS] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 + s / R <= &0 /\ --(a / R) <= &0 + s / R` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ADD_LID] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
        REWRITE_TAC[GSYM real_div; REAL_ARITH `--(s / R) = --s / R`] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[P2BL_KVIEW_ACCESS] THEN
    SUBGOAL_THEN `(t:num->real) n + s / (R * Q n) = t n + (&0 + s / R) / Q n` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ADD_LID] THEN
      SUBGOAL_THEN `&0 < (Q:num->real) n` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    USE_THEN "k0" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `&0 + s / R`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let P2BL_CANON_AT_PARTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) C eps x t.
     (?e. rfs_strong_neck V eps x t e) \/
     (?U Y. rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps U Y /\ x IN Y) \/
     (?U. x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U) \/
     (?U. x IN U /\
          rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps U)
     ==> p3_canon_at V C eps x t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p3_canon_at] THEN
  ONCE_REWRITE_TAC[P2BL_VIEW_TRIPLE] THEN REWRITE_TAC[rfs_strong_canonical] THEN
  ONCE_REWRITE_TAC[GSYM P2BL_VIEW_TRIPLE] THEN ASM_MESON_TAC[]);;

let P2BL_LIMIT_TRANSFER_FROM_PARTS = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_PROP_9_79_OPEN_TYPED_STATEMENT w u /\ P2B_NECK_OPEN_STATEMENT w u /\
     P2B_KSOL_NECK_EXTEND_Q_STATEMENT w
     ==> P2B_LIMIT_TRANSFER_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B_PROP_9_79_OPEN_TYPED_STATEMENT; P2B_NECK_OPEN_STATEMENT;
              P2B_KSOL_NECK_EXTEND_Q_STATEMENT; P2B_LIMIT_TRANSFER_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps0c:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TC"))))
      (CONJUNCTS_THEN2 (LABEL_TAC "TCC") (LABEL_TAC "TR"))))
    (CONJUNCTS_THEN2 (LABEL_TAC "NO") (LABEL_TAC "NE"))) THEN
  EXISTS_TAC `min eps0c (&1 / &40)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:num->(A)rfs_history`; `x:num->A`;
                       `t:num->real`; `Q:num->real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `xl:B`; `kappa:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `p2bl_vslices (\n. rfs_view ((hs:num->(A)rfs_history) n)) x t` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BL_HIST_VSLICES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SIMP_RULE[P2BL_KVIEW_ACCESS; REAL_LE_REFL] o
    REWRITE_RULE[GSYM P2BL_VIEW_TRIPLE] o REWRITE_RULE[rfs_strong_canonical] o
    ONCE_REWRITE_RULE[P2BL_VIEW_TRIPLE] o REWRITE_RULE[p3_canon_at] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p3_canon_at"
                     with Failure _ -> false)) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:B->bool` (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC)) THENL
   [(* strong neck *)
    REMOVE_THEN "NE" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                      `atlas:((B->bool)#(B->real^3))->bool`;
                                      `g:real->B->real^3^3`; `eps:real`; `xl:B`;
                                      `e:real^3->B`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `eps:real`; `a:real`; `e:real^3->B`;
                   `\(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t':real) (z:A).
                      ?e'. rfs_strong_neck V' eps z t' (e':real^3->A)`] P2BL_NECK_LIMIT) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "NO" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BL_CANON_AT_PARTS THEN ASM_REWRITE_TAC[];
    (* cap *)
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `C:real`; `eps:real`; `U:B->bool`; `Y:B->bool`]
                  P2BL_CAP_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "TC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BL_CAP_CLOSURE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`;
                            `(g:real->B->real^3^3) (&0)`; `C:real`; `eps:real`;
                            `Y:B->bool`; `xl:B`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    BETA_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BL_CANON_AT_PARTS THEN ASM_REWRITE_TAC[];
    (* C-component *)
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `C:real`; `U:B->bool`] P2BL_CCOMP_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "TCC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    BETA_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BL_CANON_AT_PARTS THEN ASM_REWRITE_TAC[];
    (* round component *)
    MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `eps:real`; `U:B->bool`] P2BL_ROUND_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "TR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC P2BL_ROUND_SCALAR_POS THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `eps:real`; `U:B->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    BETA_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BL_CANON_AT_PARTS THEN ASM_REWRITE_TAC[]]);;

let P2BL_LIMIT_TRANSFER_VIEW_FROM_PARTS = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_PROP_9_79_OPEN_TYPED_STATEMENT w u /\ P2B_NECK_OPEN_L_STATEMENT w u
     ==> P2B_LIMIT_TRANSFER_VIEW_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B_PROP_9_79_OPEN_TYPED_STATEMENT; P2B_NECK_OPEN_L_STATEMENT;
              P2B_LIMIT_TRANSFER_VIEW_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps0c:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TC"))))
      (CONJUNCTS_THEN2 (LABEL_TAC "TCC") (LABEL_TAC "TR"))))
    (LABEL_TAC "NO")) THEN
  EXISTS_TAC `min eps0c (&1 / &40)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `L:real`; `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`;
                       `t:num->real`; `Q:num->real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `xl:B`; `kappa:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `p2bl_vslices (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BL_REGULAR_VSLICES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SIMP_RULE[P2BL_KVIEW_ACCESS; REAL_LE_REFL] o
    REWRITE_RULE[p2b_canon_L] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p2b_canon_L"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[p2b_canon_L] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [(* evolving neck of length L + 1 *)
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `eps:real`; `L + &1`; `e:real^3->B`;
                   `\(V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t':real) (z:A).
                      ?e'. rfs_evolving_neck V' eps z t' L (e':real^3->A)`] P2BL_NECK_LIMIT) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "NO" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MESON_TAC[];
    (* cap *)
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `C:real`; `eps:real`; `U:B->bool`; `Y:B->bool`]
                  P2BL_CAP_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "TC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BL_CAP_CLOSURE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`;
                            `(g:real->B->real^3^3) (&0)`; `C:real`; `eps:real`;
                            `Y:B->bool`; `xl:B`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MESON_TAC[];
    (* C-component *)
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `C:real`; `U:B->bool`] P2BL_CCOMP_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "TCC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MESON_TAC[];
    (* round component *)
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                   `kappa:real`; `eps:real`; `U:B->bool`] P2BL_ROUND_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "TR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC P2BL_ROUND_SCALAR_POS THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `eps:real`; `U:B->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The C^k distance between two time slices of a Ricci flow: joint           *)
(* smoothness in a chart (P2BL_LCK_FAMILY_SMOOTH), smooth chart families,    *)
(* independence of the chart near a point (P2BL_LCK_CHART_INDEP), the zero   *)
(* distance of a metric to itself, and joint continuity in time and point    *)
(* (P2BL_LCK_CHART_CONTINUOUS, P2BL_LCK_SLICES_CONTINUOUS).                  *)
(* ------------------------------------------------------------------------- *)

let P2BL_LCK_FAMILY_SMOOTH = prove
 (`!k U ta tb (G0:real->real^N->real^N^N) G.
     lrg_lsmooth U ta tb G0 /\ lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lck_dist2 k (G0 (drop(fstcart z))) (G (drop(fstcart z))) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP LRG_LSMOOTH_BASIC
    (ASSUME `lrg_lsmooth U ta tb (G0:real->real^N->real^N^N)`)) THEN
  MP_TAC(MATCH_MP LRG_LSMOOTH_BASIC
    (ASSUME `lrg_lsmooth U ta tb (G:real->real^N->real^N^N)`)) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lck_dist2] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC RFU_LSMOOTH_LTNORM2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `u:num->real^N` THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `ta:real`; `tb:real`; `G0:real->real^N->real^N^N`;
                 `\s. rfu_hh ((G:real->real^N->real^N^N) s) (G0 s)`]
                RFA_LSMOOTH_LNABLA_ITER) THEN
  REWRITE_TAC[rfu_hh] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `(G0:real->real^N->real^N^N) s`;
                     `(G:real->real^N->real^N^N) s`] LRG_LMETRIC2_DIFF_FIELD) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `v:num->real^N` THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`;
                     `G:real->real^N->real^N^N`; `G0:real->real^N->real^N^N`]
                    RFU_LSMOOTH_TENSORS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `v:num->real^N`) THEN
      REWRITE_TAC[rfu_hh]];
    DISCH_THEN(MP_TAC o SPECL [`l:num`; `u:num->real^N`]) THEN REWRITE_TAC[]]);;

let P2BL_LSMOOTH_CMUL = prove
 (`!U a b (G:real->real^N->real^N^N) c.
     lrg_lsmooth U a b G /\ &0 < c ==> lrg_lsmooth U a b (\t z. c %% G t z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lrg_lsmooth] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTORIZE_CMUL] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_SIMP_TAC[ETA_AX];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]]);;

let P2BL_LSMOOTH_CONST = prove
 (`!U a b (G:real^N->real^N^N).
     metric_field U G /\ a < b ==> lrg_lsmooth U a b (\t. G)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrg_lsmooth] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                                ((G:real^N->real^N^N) (sndcart z))) =
    (vectorize o G) o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                SNDCART_PASTECART] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART]]);;

let P2BL_FLOW_CHART_LSMOOTH = prove
 (`!top atlas (g:real->A->real^N^N) a b c R.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas /\ &0 < R
     ==> lrg_lsmooth (IMAGE (SND c) (FST c)) a b
                     (\t. metric_local atlas c (\y. R %% g t y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[METRIC_LOCAL_CMUL] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t)`;
                 `R:real`] P2BL_LSMOOTH_CMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LRICCI_FLOW_LSMOOTH THEN
    MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ETA_AX]]);;

let P2BL_FLOW_CHART_CONST = prove
 (`!top atlas (g:real->A->real^N^N) a b c R s0.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas /\ &0 < R /\ a < s0 /\ s0 < b
     ==> lrg_lsmooth (IMAGE (SND c) (FST c)) a b
                     (\t. metric_local atlas c (\y. R %% g s0 y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BL_LSMOOTH_CONST THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `(g:real->A->real^N^N) s0`] RIEMANNIAN_METRIC_OVERLAP) THEN
  ASM_SIMP_TAC[PAIR; INTER_IDEMPOT]);;

let P2BL_LCK_CHART_INDEP = prove
 (`!top atlas (g0:A->real^N^N) g c1 c2 p k.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     riemannian_metric atlas g /\ c1 IN atlas /\ c2 IN atlas /\
     p IN FST c1 /\ p IN FST c2
     ==> lck_dist2 k (metric_local atlas c1 g0) (metric_local atlas c1 g) (SND c1 p) =
         lck_dist2 k (metric_local atlas c2 g0) (metric_local atlas c2 g) (SND c2 p)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `g0:A->real^N^N`; `g:A->real^N^N`; `U1:A->bool`; `phi1:A->real^N`;
    `U2:A->bool`; `phi2:A->real^N`; `p:A`; `k:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(U1:A->bool,phi1:A->real^N)`; `(U2:A->bool,phi2:A->real^N)`]
                GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!h:A->real^N^N. riemannian_metric atlas h
       ==> !z. z IN IMAGE phi1 (U1 INTER U2)
               ==> metric_local atlas (U1,phi1) h z =
                   mpullback (chart_trans (U1,phi1) (U2,phi2))
                             (metric_local atlas (U2,phi2) h) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) = false &&
      can (find_term ((=) `z:real^N`)) (concl th))) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi1:A->real^N) p IN IMAGE phi1 (U1 INTER U2)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lck_dist2 k (mpullback (chart_trans (U1,phi1) (U2,phi2))
                           (metric_local atlas (U2:A->bool,phi2:A->real^N) (g0:A->real^N^N)))
                (mpullback (chart_trans (U1,phi1) (U2,phi2))
                           (metric_local atlas (U2,phi2) (g:A->real^N^N)))
                ((phi1:A->real^N) p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `IMAGE (phi1:A->real^N) (U1 INTER U2)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi2:A->real^N) p = chart_trans (U1,phi1) (U2,phi2) (phi1 p)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
  EXISTS_TAC `IMAGE (phi2:A->real^N) (U1 INTER U2)` THEN
  EXISTS_TAC `IMAGE (phi1:A->real^N) (U1 INTER U2)` THEN
  EXISTS_TAC `chart_trans (U2:A->bool,phi2:A->real^N) (U1,phi1)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (phi2:A->real^N) (U1 INTER U2) = IMAGE phi2 (U2 INTER U1)`
  SUBST1_TAC THENL [REWRITE_TAC[INTER_COMM]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `phi1:A->real^N`] THEN ASM_REWRITE_TAC[]);;

let P2BL_LNABLA_ITER_ZERO = prove
 (`!k l (G:real^N->real^N^N). lnabla_iter k l G (\x u. &0) = (\x u. &0)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[lnabla_iter] THEN
  REWRITE_TAC[FUN_EQ_THM; LRG_LNABLA_ZERO]);;

let P2BL_LCK_DIST2_REFL = prove
 (`!k (G:real^N->real^N^N) y. lck_dist2 k G G y = &0`,
  REWRITE_TAC[lck_dist2; REAL_SUB_REFL] THEN
  REWRITE_TAC[ETA_AX; GSYM(REWRITE_CONV[ETA_AX] `\x:real^N u:num->real^N. &0`)] THEN
  REWRITE_TAC[P2BL_LNABLA_ITER_ZERO; ltnorm2; REAL_MUL_LZERO; SUM_0]);;

let P2BL_LCK_CHART_CONTINUOUS = prove
 (`!top atlas (g:real->A->real^N^N) a b R s0 k c.
     ricci_flow_on (top,atlas) a b g /\ &0 < R /\ a < s0 /\ s0 < b /\ c IN atlas
     ==> continuous_map
           (subtopology
             (prod_topology (subtopology euclideanreal {t | a < t /\ t < b}) top)
             {z | z IN topspace(prod_topology (subtopology euclideanreal
                                                 {t | a < t /\ t < b}) top) /\
                  SND z IN FST c},
            euclideanreal)
           (\z. lck_dist2 k (metric_local atlas (chart_at atlas (SND z)) (\y. R %% g s0 y))
                            (metric_local atlas (chart_at atlas (SND z))
                                          (\y. R %% g (FST z) y))
                            (SND(chart_at atlas (SND z)) (SND z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  MP_TAC(ISPECL [`k:num`; `V:real^N->bool`; `a:real`; `b:real`;
                 `\t:real. metric_local atlas (c:(A->bool)#(A->real^N))
                             (\y. R %% (g:real->A->real^N^N) s0 y)`;
                 `\t:real. metric_local atlas (c:(A->bool)#(A->real^N))
                             (\y. R %% (g:real->A->real^N^N) t y)`]
                P2BL_LCK_FAMILY_SMOOTH) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "V" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BL_FLOW_CHART_CONST THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BL_FLOW_CHART_LSMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  SUBGOAL_THEN
   `continuous_map
     (subtopology euclidean (interval(lift a,lift b) PCROSS (V:real^N->bool)), euclideanreal)
     (\w. lck_dist2 k (metric_local atlas (c:(A->bool)#(A->real^N))
                         (\y. R %% (g:real->A->real^N^N) s0 y))
                      (metric_local atlas c (\y. R %% g (drop(fstcart w)) y)) (sndcart w))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC
   `(\w. lck_dist2 k (metric_local atlas (c:(A->bool)#(A->real^N))
                        (\y. R %% (g:real->A->real^N^N) s0 y))
                     (metric_local atlas c (\y. R %% g (drop(fstcart w)) y)) (sndcart w)) o
    (\z:real#A. pastecart (lift(FST z)) (SND c (SND z)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY; IN_INTER; IN_ELIM_THM;
                FORALL_PAIR_THM; IN_CROSS; TOPSPACE_EUCLIDEANREAL; IN_UNIV;
                o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BL_LCK_CHART_INDEP THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (interval(lift a,lift b) PCROSS (V:real^N->bool))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND;
                TOPSPACE_EUCLIDEANREAL; IN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(\z:real#A. pastecart (lift(FST z)) (SND(c:(A->bool)#(A->real^N)) (SND z))) =
    (\(x,y). pastecart x y) o (\z. lift(FST z),SND c (SND z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM; FST; SND]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (euclidean:(real^1)topology) (euclidean:(real^N)topology)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PASTECART; CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[CONTINUOUS_MAP_LIFT; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MP_TAC(ISPECL [`subtopology euclideanreal {t | a < t /\ t < b}`;
                   `top:A topology`] CONTINUOUS_MAP_FST) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (top:A topology) (FST(c:(A->bool)#(A->real^N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                  IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND] THEN
      SIMP_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
           SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP
                                 (last(CONJUNCTS th)))) THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX] THEN SIMP_TAC[]]);;

let P2BL_LCK_SLICES_CONTINUOUS = prove
 (`!top atlas (g:real->A->real^N^N) a b R s0 k.
     ricci_flow_on (top,atlas) a b g /\ &0 < R /\ a < s0 /\ s0 < b
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a < t /\ t < b}) top,
            euclideanreal)
           (\z. lck_dist2 k (metric_local atlas (chart_at atlas (SND z)) (\y. R %% g s0 y))
                            (metric_local atlas (chart_at atlas (SND z))
                                          (\y. R %% g (FST z) y))
                            (SND(chart_at atlas (SND z)) (SND z)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on] o CONJUNCT1) THEN
  MATCH_MP_TAC(INST_TYPE [`:real#A`,`:A`; `:real`,`:B`;
                          `:(A->bool)#(A->real^N)`,`:K`] PASTING_LEMMA) THEN
  MAP_EVERY EXISTS_TAC
   [`\c:(A->bool)#(A->real^N). \z:real#A.
       lck_dist2 k (metric_local atlas (chart_at atlas (SND z)) (\y. R %% (g:real->A->real^N^N) s0 y))
                   (metric_local atlas (chart_at atlas (SND z)) (\y. R %% g (FST z) y))
                   (SND(chart_at atlas (SND z)) (SND z))`;
    `\c:(A->bool)#(A->real^N).
       {z:real#A | z IN topspace(prod_topology
                                   (subtopology euclideanreal {t | a < t /\ t < b}) top) /\
                   SND z IN FST c}`;
    `atlas:((A->bool)#(A->real^N))->bool`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P2BL_LCK_CHART_CONTINUOUS THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; IN_CROSS; IN_INTER;
                IN_ELIM_THM] THEN
    STRIP_TAC THEN
    EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[IN_ELIM_THM; IN_CROSS; IN_INTER; TOPSPACE_PROD_TOPOLOGY;
             TOPSPACE_SUBTOPOLOGY; FST; SND] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The tube lemma: on a compact set the time slices near s0 stay C^k close   *)
(* to the slice at s0 (P2BL_SLICES_TUBE); the arithmetic of the extension    *)
(* step (P2BL_EXT_ARITH); pointwise continuity at a fixed point with varying *)
(* base slice (P2BL_SLICE_PT_CONT).                                          *)
(* ------------------------------------------------------------------------- *)

let P2BL_SLICES_TUBE = prove
 (`!top atlas (g:real->A->real^N^N) a b R s0 k K th.
     ricci_flow_on (top,atlas) a b g /\ &0 < R /\ a < s0 /\ s0 < b /\
     compact_in top K /\ &0 < th
     ==> ?eta. &0 < eta /\
               !s p. abs(s - s0) < eta /\ p IN K
                     ==> lck_dist2 k (metric_local atlas (chart_at atlas p)
                                                   (\y. R %% g s0 y))
                                     (metric_local atlas (chart_at atlas p)
                                                   (\y. R %% g s y))
                                     (SND(chart_at atlas p) p) < th`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `K:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  ABBREV_TAC
   `L = \s p. lck_dist2 k (metric_local atlas (chart_at atlas p)
                                        (\y. R %% (g:real->A->real^N^N) s0 y))
                          (metric_local atlas (chart_at atlas p) (\y. R %% g s y))
                          (SND(chart_at atlas p) (p:A))` THEN
  SUBGOAL_THEN
   `continuous_map (prod_topology (subtopology euclideanreal {t | a < t /\ t < b})
                                  (subtopology top (K:A->bool)),
                    euclideanreal)
                   (\z. (L:real->A->real) (FST z) (SND z))`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ONCE_REWRITE_TAC[CONJUNCT2 PROD_TOPOLOGY_SUBTOPOLOGY] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MATCH_MP_TAC P2BL_LCK_SLICES_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclideanreal {t | a < t /\ t < b}`; `top:A topology`;
                 `K:A->bool`; `L:real->A->real`] RFA_SUP_COMPACT_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM RFA_REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP; real_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `s0:real`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `th:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sup(IMAGE ((L:real->A->real) s0) K) = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE ((L:real->A->real) s0) K = {&0}` SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[P2BL_LCK_DIST2_REFL] THEN ASM SET_TAC[];
      REWRITE_TAC[SUP_SING]];
    ALL_TAC] THEN
  EXISTS_TAC `min d (min (s0 - a) (b - s0))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `p:A`] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclideanreal {t | a < t /\ t < b}`; `top:A topology`;
                 `K:A->bool`; `L:real->A->real`; `s:real`] RFA_SUP_COMPACT_ATTAINED) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV;
                  IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs(sup(IMAGE ((L:real->A->real) s) K)) < th` THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN REAL_ARITH_TAC);;

let P2BL_EXT_ARITH = prove
 (`!n Sd Sd' M.
     &0 <= Sd /\ Sd < Sd' /\ &0 <= M
     ==> ?h. &0 < h /\ h <= &1 / &2 /\
             !x th. &0 <= x /\ x <= h /\ &0 <= th /\ th <= h pow 2
                    ==> (&1 + x) pow n * (Sd + sqrt(M * th) + &2 * x) <= Sd'`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `C = sqrt M + &2` THEN
  SUBGOAL_THEN `&2 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MP_TAC(SPEC `M:real` SQRT_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B = C * (&1 + &n) + &2 * &n * Sd + &1` THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SUBGOAL_THEN `&0 <= C * (&1 + &n) /\ &0 <= &2 * &n * Sd` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &2) (min (inv(&2 * (&n + &1))) ((Sd' - Sd) / B))` THEN
  ABBREV_TAC `h = min (&1 / &2) (min (inv(&2 * (&n + &1))) ((Sd' - Sd) / B))` THEN
  SUBGOAL_THEN `&0 < h /\ h <= &1 / &2 /\ h <= inv(&2 * (&n + &1)) /\ h <= (Sd' - Sd) / B`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real`; `th:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&n * h <= inv(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n * inv(&2 * (&n + &1))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &2 * (&n + &1)`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + x) pow n <= &1 + &2 * &n * h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + h) pow n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2B9_POW_BOUND THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(M * th) <= sqrt M * h` ASSUME_TAC THENL
   [REWRITE_TAC[SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + &2 * &n * h) * (Sd + C * h)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      MP_TAC(SPEC `M * th:real` SQRT_POS_LE) THEN
      ASM_SIMP_TAC[REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * B <= Sd' - Sd` ASSUME_TAC THENL
   [UNDISCH_TAC `h <= (Sd' - Sd) / B` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ;
      REAL_ARITH `&1 <= B ==> &0 < B`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &n * C * h * h <= &n * C * h` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * &n * C * h * h = (&n * C * h) * (&2 * h)` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `h * B <= Sd' - Sd` THEN EXPAND_TAC "B" THEN
  UNDISCH_TAC `&2 * &n * C * h * h <= &n * C * h` THEN
  SUBGOAL_THEN `&0 <= h * &2 * &n * Sd` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < h` THEN REAL_ARITH_TAC);;

let P2BL_ML_FIELD = prove
 (`!top atlas (h:A->real^N^N) c R.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\ c IN atlas /\ &0 < R
     ==> metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (\y. R %% h y))`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p1:A->bool`; `p2:A->real^N`; `p1:A->bool`; `p2:A->real^N`;
                 `h:A->real^N^N`] RIEMANNIAN_METRIC_OVERLAP) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT]);;

let P2BL_SLICE_PT_CONT = prove
 (`!top atlas (g:real->A->real^N^N) a b R s0 k p th.
     ricci_flow_on (top,atlas) a b g /\ &0 < R /\ a < s0 /\ s0 < b /\
     p IN topspace top /\ &0 < th
     ==> ?eta. &0 < eta /\
           !s. abs(s - s0) < eta
               ==> lck_dist2 k (metric_local atlas (chart_at atlas p) (\y. R %% g s y))
                               (metric_local atlas (chart_at atlas p) (\y. R %% g s0 y))
                               (SND(chart_at atlas p) p) < th`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`;
                 `\t:real. metric_local atlas (c:(A->bool)#(A->real^N))
                             (\y. R %% (g:real->A->real^N^N) t y)`;
                 `\t:real. metric_local atlas (c:(A->bool)#(A->real^N))
                             (\y. R %% (g:real->A->real^N^N) s0 y)`]
                P2BL_LCK_FAMILY_SMOOTH) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2BL_FLOW_CHART_LSMOOTH THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BL_FLOW_CHART_CONST THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_PCROSS; OPEN_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC
    `pastecart (lift s0) (SND(c:(A->bool)#(A->real^N)) (p:A))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `th:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (min (s0 - a) (b - s0))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `pastecart (lift s) (SND(c:(A->bool)#(A->real^N)) (p:A))`) THEN
  REWRITE_TAC[DIST_PASTECART_CANCEL; DIST_LIFT; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP; P2BL_LCK_DIST2_REFL; DIST_0; NORM_LIFT] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (metric_local atlas (c:(A->bool)#(A->real^N))
                                  (\y. R %% (g:real->A->real^N^N) s y))
                     (metric_local atlas c (\y. R %% g s0 y)) (SND c (p:A))`
  MP_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]]] THEN
    MATCH_MP_TAC P2BL_ML_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DIST_LIFT; REAL_SUB_RZERO] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Strong necks of kappa-solutions extend to evolving necks of some length a *)
(* > 1 (P2B_KSOL_NECK_EXTEND_Q): the evolving neck condition in the          *)
(* kappa-solution view, pullbacks along the neck chart, transfer of cylinder *)
(* closeness from s1 to s2 by base change (needs closeness at most 1/4,      *)
(* hence eps < 1/4), the endpoint s = -1, and the extension over (-a,-1] by  *)
(* the tube lemma.                                                           *)
(* ------------------------------------------------------------------------- *)

let P2BL_KVIEW_EVOLVING_NECK = prove
 (`!top atlas (g:real->B->real^3^3) eps x len e.
     rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0) len e <=>
     rfs_neck (top,atlas) (g (&0)) eps x e /\ &0 < len /\
     rfs_close_fam (rfs_kreg eps) eps {s | --len < s /\ s <= &0} (rfs_neck_dom eps)
       cylinder_flow
       (\s y. mfd_scalar atlas (g (&0)) x %%
              rfs_pullback atlas e (g (s / mfd_scalar atlas (g (&0)) x)) y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_evolving_neck; rfs_persists; IN_ELIM_THM;
              REAL_LE_REFL; REAL_ADD_LID] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->B`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BL_NECK_PB_FACTS = prove
 (`!top atlas (g:real->B->real^3^3) eps x e R s1 s2 k y.
     rfs_neck (top,atlas) (g (&0)) eps x e /\ riemannian_metric atlas (g s1) /\
     riemannian_metric atlas (g s2) /\ &0 < R /\ y IN rfs_neck_dom eps
     ==> metric_field (rfs_neck_dom eps) (\z. R %% rfs_pullback atlas e (g s1) z) /\
         lck_dist2 k (\z. R %% rfs_pullback atlas e (g s1) z)
                     (\z. R %% rfs_pullback atlas e (g s2) z) y =
         lck_dist2 k (metric_local atlas (chart_at atlas (e y)) (\w. R %% g s1 w))
                     (metric_local atlas (chart_at atlas (e y)) (\w. R %% g s2 w))
                     (SND(chart_at atlas (e y)) (e y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM P2B9_RFS_PULLBACK_CMUL] THEN
  MATCH_MP_TAC P2B9_LCK_PARAM THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `rfs_neck_dom eps`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let P2BL_CYL_TRANSFER = prove
 (`!k M t (G1:real^3->real^3^3) G2 s1 s2 y d1 th.
     (!s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k G0 G1 y <= &1 / &4
         ==> lck_dist2 k G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k G1 G2 y) /\
     &0 <= M /\ t SUBSET ((:real^3) DELETE vec 0) /\
     metric_field t G1 /\ metric_field t G2 /\ y IN t /\
     s1 <= &0 /\ s2 <= &0 /\ abs(s2 - s1) <= &1 / &2 /\
     lck_dist2 k (cylinder_flow s1) G1 y <= d1 /\ d1 <= &1 / &4 /\
     lck_dist2 k G1 G2 y <= th
     ==> sqrt(lck_dist2 k (cylinder_flow s2) G2 y) <=
         (&1 + abs(s2 - s1)) pow (k + 2) * (sqrt d1 + sqrt(M * th) + &2 * abs(s2 - s1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open(t:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field t (cylinder_flow s1)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (G1:real^3->real^3^3) G2 y` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 k (cylinder_flow s1) (\z. cylinder_flow s1 z + G2 z - G1 z) y <= M * th`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M * lck_dist2 k (G1:real^3->real^3^3) G2 y` THEN CONJ_TAC THENL
     [REMOVE_THEN "base" MATCH_MP_TAC THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(lck_dist2 k (cylinder_flow s1) (G2:real^3->real^3^3) y) <=
    sqrt d1 + sqrt(M * th)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 k (cylinder_flow s1) (G1:real^3->real^3^3) y) +
                sqrt(lck_dist2 k (cylinder_flow s1) (\z. cylinder_flow s1 z + G2 z - G1 z) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_TRIANGLE THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + abs(s2 - s1)) pow (k + 2) *
              (sqrt(lck_dist2 k (cylinder_flow s1) (G2:real^3->real^3^3) y) +
               &2 * abs(s2 - s1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2B9_CYL_BASE2 THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let P2BL_NECK_DOM_NZ = prove
 (`!eps. rfs_neck_dom eps SUBSET ((:real^3) DELETE vec 0)`,
  REWRITE_TAC[SUBSET; APX_SLAB_NECK_DOM; APX_SLAB_SVAL; IN_DELETE; IN_UNIV] THEN
  MESON_TAC[]);;

let P2BL_NECK_ENDPOINT = prove
 (`!top atlas (g:real->B->real^3^3) kappa eps x e d1 y.
     p2b_kappa_solution kappa (top,atlas) g /\ &0 < eps /\ eps < &1 / &4 /\
     rfs_neck (top,atlas) (g (&0)) eps x e /\ d1 < eps pow 2 /\
     (!s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom eps
            ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                  (\z. mfd_scalar atlas (g (&0)) x %%
                       rfs_pullback atlas e (g (s / mfd_scalar atlas (g (&0)) x)) z) y
                <= d1) /\
     y IN rfs_neck_dom eps
     ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (--(&1)))
           (\z. mfd_scalar atlas (g (&0)) x %%
                rfs_pullback atlas e (g (--(&1) / mfd_scalar atlas (g (&0)) x)) z) y
         <= d1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cl") ASSUME_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  ABBREV_TAC `R = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x` THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `G = \s z. R %% rfs_pullback atlas (e:real^3->B) ((g:real->B->real^3^3) (s / R)) z` THEN
  SUBGOAL_THEN `!s. s <= &0 ==> metric_field (rfs_neck_dom eps) ((G:real->real^3->real^3^3) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `eps:real`; `x:B`; `e:real^3->B`; `R:real`;
                   `s / R`; `s / R`; `k:num`; `y:real^3`] P2BL_NECK_PB_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 k (cylinder_flow (&0)) ((G:real->real^3->real^3^3) (&0)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_SIMP_TAC[REAL_LE_REFL; APX_NECK_CYL_FIELD_GEN; REAL_LT_01];
      USE_THEN "cl" (fun th -> MP_TAC(MP (SPECL [`&0`; `y:real^3`] th)
        (CONJ (REAL_ARITH `--(&1) < &0`) (CONJ (SPEC `&0` REAL_LE_REFL)
          (ASSUME `(y:real^3) IN rfs_neck_dom eps`))))) THEN
      EXPAND_TAC "G" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `k:num` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT] P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (--(&2) / R) (&0) (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `--(&2) / R` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto"))
        (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LT0] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV] THEN REAL_ARITH_TAC;
      SIMP_TAC[rfs_flow_upto]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!th. &0 < th
         ==> sqrt(lck_dist2 k (cylinder_flow (--(&1)))
                    ((G:real->real^3->real^3^3) (--(&1))) y) <= sqrt d1 + th`
  (LABEL_TAC "epsb") THENL
   [X_GEN_TAC `th:real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`k + 2`; `sqrt d1`; `sqrt d1 + th`; `M:real`] P2BL_EXT_ARITH) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ar")))) THEN
    SUBGOAL_THEN `(e:real^3->B) y IN topspace top` ASSUME_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->B`] GRGD_PARAM_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `--(&2) / R`; `&0`; `R:real`; `--(&1) / R`;
                   `k:num`; `(e:real^3->B) y`; `h pow 2`] P2BL_SLICE_PT_CONT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
      SUBGOAL_THEN `&0 < inv R` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pc"))) THEN
    ABBREV_TAC `s = --(&1) + min h (eta * R) / &2` THEN
    SUBGOAL_THEN `&0 < min h (eta * R) /\ min h (eta * R) <= h /\
                  min h (eta * R) <= eta * R`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_MUL; REAL_MIN_LE; REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `--(&1) < s /\ s <= &0 /\ abs(--(&1) - s) <= h /\
                  abs(--(&1) - s) <= &1 / &2 /\ abs(s / R - --(&1) / R) < eta`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB; REAL_ABS_MUL] THEN
        ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < R ==> abs R = R`] THEN
        REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `L = lck_dist2 k ((G:real->real^3->real^3^3) s) (G (--(&1))) y` THEN
    SUBGOAL_THEN `&0 <= L /\ L <= h pow 2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field"))
            (concl th) && is_forall(concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "G" THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:real->B->real^3^3`; `eps:real`; `x:B`; `e:real^3->B`; `R:real`;
                     `s / R`; `--(&1) / R`; `k:num`; `y:real^3`] P2BL_NECK_PB_FACTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
        REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "pc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `metric_field (rfs_neck_dom eps) ((G:real->real^3->real^3^3) s) /\
                  metric_field (rfs_neck_dom eps) ((G:real->real^3->real^3^3) (--(&1))) /\
                  lck_dist2 k (cylinder_flow s) ((G:real->real^3->real^3^3) s) y <= d1 /\
                  d1 <= &1 / &4 /\ --(&1) <= &0`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field"))
            (concl th) && is_forall(concl th))) THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field"))
            (concl th) && is_forall(concl th))) THEN REAL_ARITH_TAC;
        USE_THEN "cl" (fun th -> MP_TAC(MP (SPECL [`s:real`; `y:real^3`] th)
          (CONJ (ASSUME `--(&1) < s`) (CONJ (ASSUME `s <= &0`)
            (ASSUME `(y:real^3) IN rfs_neck_dom eps`))))) THEN
        EXPAND_TAC "G" THEN SIMP_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &4) pow 2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          CONV_TAC REAL_RAT_REDUCE_CONV];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `M:real`; `rfs_neck_dom eps`;
                   `(G:real->real^3->real^3^3) s`; `(G:real->real^3->real^3^3) (--(&1))`;
                   `s:real`; `--(&1)`; `y:real^3`; `d1:real`; `L:real`]
                  P2BL_CYL_TRANSFER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[P2BL_NECK_DOM_NZ; REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + abs(--(&1) - s)) pow (k + 2) *
                (sqrt d1 + sqrt(M * L) + &2 * abs(--(&1) - s))` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ar" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow (--(&1)))
                     ((G:real->real^3->real^3^3) (--(&1))) y) <= sqrt d1`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "epsb" (MP_TAC o SPEC
      `(sqrt(lck_dist2 k (cylinder_flow (--(&1)))
                       ((G:real->real^3->real^3^3) (--(&1))) y) - sqrt d1) / &2`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_MONO_LE_EQ] THEN EXPAND_TAC "G" THEN SIMP_TAC[]);;

let P2B_KSOL_NECK_EXTEND_Q = prove
 (`!w:B->bool. P2B_KSOL_NECK_EXTEND_Q_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_KSOL_NECK_EXTEND_Q_STATEMENT; rfs_strong_neck; P2BL_KVIEW_EVOLVING_NECK] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `eps:real`; `x:B`; `e:real^3->B`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_fam")) (concl th))) THEN
  REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))) THEN
  SUBGOAL_THEN
   `!s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom eps
          ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                (\z. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x %%
                     rfs_pullback atlas (e:real^3->B)
                       (g (s / mfd_scalar atlas (g (&0)) x)) z) y <= d1`
  (LABEL_TAC "cl2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN rfs_neck_dom eps
        ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (--(&1)))
              (\z. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x %%
                   rfs_pullback atlas (e:real^3->B)
                     (g (--(&1) / mfd_scalar atlas (g (&0)) x)) z) y <= d1`
  (LABEL_TAC "endp") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BL_NECK_ENDPOINT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `kappa:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x` THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= &0 ==> s / R <= &0 /\ riemannian_metric atlas ((g:real->B->real^3^3) (s / R))`
  (LABEL_TAC "sc") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s / R <= &0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `G = \s z. R %% rfs_pullback atlas (e:real^3->B) ((g:real->B->real^3^3) (s / R)) z` THEN
  SUBGOAL_THEN `!s. s <= &0 ==> metric_field (rfs_neck_dom eps) ((G:real->real^3->real^3^3) s)`
  (LABEL_TAC "mf") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `eps:real`; `x:B`; `e:real^3->B`; `R:real`;
                   `s / R`; `s / R`; `k:num`; `basis 1:real^3`] P2BL_NECK_PB_FACTS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN
      DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(basis 1:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 k (cylinder_flow (&0)) ((G:real->real^3->real^3^3) (&0)) (basis 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_SIMP_TAC[REAL_LE_REFL; APX_NECK_CYL_FIELD_GEN; REAL_LT_01];
      EXPAND_TAC "G" THEN USE_THEN "cl2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d = (d1 + eps pow 2) / &2` THEN
  SUBGOAL_THEN `d1 < d /\ d < eps pow 2 /\ sqrt d1 < sqrt d /\ &0 <= sqrt d1 /\
                d1 <= &1 / &4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `d1 < d /\ d < eps pow 2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[SQRT_MONO_LT_EQ] THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &4) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(SPEC `k:num` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT] P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  MP_TAC(SPECL [`k + 2`; `sqrt d1`; `sqrt d`; `M:real`] P2BL_EXT_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ar")))) THEN
  SUBGOAL_THEN `IMAGE (e:real^3->B) (rfs_neck_dom eps) SUBSET topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->B`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (top closure_of IMAGE (e:real^3->B) (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `eps:real`; `x:B`; `e:real^3->B`]
                  P2BL_NECK_CLOSURE_COMPACT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (--(&2) / R) (&0) (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `--(&2) / R` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto"))
        (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LT0] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV] THEN REAL_ARITH_TAC;
      SIMP_TAC[rfs_flow_upto]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `--(&2) / R`; `&0`; `R:real`; `--(&1) / R`;
                 `k:num`; `top closure_of IMAGE (e:real^3->B) (rfs_neck_dom eps)`;
                 `h pow 2`] P2BL_SLICES_TUBE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
    SUBGOAL_THEN `&0 < inv R` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tube"))) THEN
  SUBGOAL_THEN `&0 < min h (eta * R) /\ min h (eta * R) <= h /\
                min h (eta * R) <= eta * R`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_MUL; REAL_MIN_LE; REAL_LE_REFL]; ALL_TAC] THEN
  EXISTS_TAC `&1 + min h (eta * R) / &2` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `--(&1) < t` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d1:real` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "cl2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. R %% rfs_pullback atlas (e:real^3->B) ((g:real->B->real^3^3) (t / R)) z) =
                (G:real->real^3->real^3^3) t` SUBST1_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(t - --(&1)) <= h /\ abs(t - --(&1)) <= &1 / &2 /\
                abs(t / R - --(&1) / R) < eta /\ --(&1) <= &0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB; REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < R ==> abs R = R`] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) ((G:real->real^3->real^3^3) (--(&1))) /\
                metric_field (rfs_neck_dom eps) ((G:real->real^3->real^3^3) t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 k (cylinder_flow (--(&1))) ((G:real->real^3->real^3^3) (--(&1))) y
                <= d1`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN USE_THEN "endp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = lck_dist2 k ((G:real->real^3->real^3^3) (--(&1))) (G t) y` THEN
  SUBGOAL_THEN `&0 <= L /\ L <= h pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `eps:real`; `x:B`; `e:real^3->B`; `R:real`;
                   `--(&1) / R`; `t / R`; `k:num`; `y:real^3`] P2BL_NECK_PB_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "sc" (MP_TAC o SPEC `--(&1)`); USE_THEN "sc" (MP_TAC o SPEC `t:real`)] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "tube" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `IMAGE (e:real^3->B) (rfs_neck_dom eps)`]
                  CLOSURE_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE `(a:B) IN s ==> s SUBSET t ==> a IN t`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `M:real`; `rfs_neck_dom eps`;
                 `(G:real->real^3->real^3^3) (--(&1))`; `(G:real->real^3->real^3^3) t`;
                 `--(&1)`; `t:real`; `y:real^3`; `d1:real`; `L:real`]
                P2BL_CYL_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2BL_NECK_DOM_NZ; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow t) ((G:real->real^3->real^3^3) t) y) <= sqrt d`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + abs(t - --(&1))) pow (k + 2) *
                (sqrt d1 + sqrt(M * L) + &2 * abs(t - --(&1)))` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ar" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    REWRITE_TAC[SQRT_MONO_LE_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorems P2B_LIMIT_TRANSFER (history form) and                   *)
(* P2B_LIMIT_TRANSFER_VIEW (view form).                                      *)
(* ------------------------------------------------------------------------- *)

let P2B_LIMIT_TRANSFER = prove
 (`!(u:A->bool) (w:B->bool). P2B_LIMIT_TRANSFER_STATEMENT u w`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2BL_LIMIT_TRANSFER_FROM_PARTS THEN
  REWRITE_TAC[P2B_PROP_9_79_OPEN_TYPED; P2B_NECK_OPEN; P2B_KSOL_NECK_EXTEND_Q]);;

let P2B_LIMIT_TRANSFER_VIEW = prove
 (`!(u:A->bool) (w:B->bool). P2B_LIMIT_TRANSFER_VIEW_STATEMENT u w`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2BL_LIMIT_TRANSFER_VIEW_FROM_PARTS THEN
  REWRITE_TAC[P2B_PROP_9_79_OPEN_TYPED; P2B_NECK_OPEN_L]);;

