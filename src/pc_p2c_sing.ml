(* ========================================================================= *)
(* Unit pc_p2c_sing (Part 2C): MT Lemma 11.21 (p. 280-281; Thm 11.19 (1),    *)
(* (2)) in route form, P2C_LEMMA_11_21_ROUTE_STATEMENT of pc_p2c_iface, and  *)
(* general tools on limit metrics at the horizon of a history (properness of *)
(* the scalar curvature of ANY limit metric, pointwise convergence of the    *)
(* scalar curvature), used also by pc_p2c_sing2 (Lemma 11.23 MAXEXT).        *)
(*                                                                           *)
(* Route: Lemma 11.2 in history form from the route hypotheses              *)
(* (P2C_LEMMA_11_2_FROM_DB) and its open-set window form P3N_L112_WINDOW of *)
(* pc_p3_s16end; pinching gives abs Rm bounds (P3N_PINCH_RM); Shi (route    *)
(* hypothesis P2_THM_3_28) on balls of later times inside the bounded       *)
(* region (LIM_CURVES_STAY); Hamilton's chart jet bounds (RFA_R1_CHART_FROM)*)
(* on restricted manifolds (P2CF_RFF_RESTRICT); the C^0 limit from the      *)
(* Lipschitz bound P3N_LIP_ENTRY; smooth limits and C^k convergence from    *)
(* P2CS_JET_SUBSEQ, P2CI_CINF_FROM_BOUNDS and P2CI_LCK_COMPACT.              *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_lim_close.ml";;
needs "src/pc_p2c_cgcinf.ml";;
needs "src/pc_rfa_r1.ml";;
needs "src/pc_p3_s16end.ml";;
needs "src/pc_p3e_limscal.ml";;
needs "src/pc_rf_mequiv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The hypotheses of Lemma 11.21 as one predicate (sngl_hyp),                *)
(* the forward window form and the backward form of Lemma 11.2 for a fixed   *)
(* history (sngl_fwd, sngl_bwd; obtained from the route hypotheses below),  *)
(* and the last slab of a history: its slices, persistence of open sets and  *)
(* the scalar curvature there.                                              *)
(* ------------------------------------------------------------------------- *)

let sngl_hyp = new_definition
 `sngl_hyp (hs:(A)rfs_history) (C:real) (eps:real) (r0:real) <=>
    &1 < C /\ &0 < eps /\ rfs_history_ok hs /\ &0 < r0 /\
    rfs_pinched (rfs_view hs) /\
    (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
           inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
           ==> p3_canon_at (rfs_view hs) C eps x t)`;;

let sngl_fwd = new_definition
 `sngl_fwd (hs:(A)rfs_history) (C:real) (r0:real) <=>
    !B t0 t1 D.
      &0 <= t0 /\ t0 < t1 /\ t1 < rfs_horizon hs /\
      open_in (rfs_top_at hs t0) B /\ rfs_persists (rfs_view hs) B t0 t1 /\ &0 <= D /\
      (!z. z IN B ==> rfs_vscalar (rfs_view hs) t0 z <= D) /\
      t1 - t0 <= inv(&16 * max C (&2) * (D + inv(r0 pow 2)))
      ==> !s z. t0 <= s /\ s <= t1 /\ z IN B
                ==> rfs_vscalar (rfs_view hs) s z <= &2 * (D + inv(r0 pow 2))`;;

let sngl_bwd = new_definition
 `sngl_bwd (hs:(A)rfs_history) (C:real) (r0:real) <=>
    !z t0 t' r'.
      &0 <= t' /\ t' < t0 /\ t0 < rfs_horizon hs /\
      z IN topspace(rfs_top_at hs t0) /\ &0 < r' /\
      r' <= inv(&2 * max C (&2) *
                sqrt(max (rfs_vscalar (rfs_view hs) t0 z) (inv(r0 pow 2)))) /\
      t0 - t' <= inv(&16 * max C (&2) *
                     (max (&0) (rfs_vscalar (rfs_view hs) t0 z) + inv(r0 pow 2))) /\
      rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) t0 z r') t' t0
      ==> !s. t' < s /\ s <= t0
              ==> rfs_vscalar (rfs_view hs) s z <=
                  &2 * (max (&0) (rfs_vscalar (rfs_view hs) t0 z) + inv(r0 pow 2))`;;

(* The last slab [T_n, T) of a history: its slices are the last stage.       *)

let SNGL_LAST_SLAB = prove
 (`!hs:(A)rfs_history t.
     rfs_history_ok hs /\ hs_time hs (hs_count hs) <= t /\ t < rfs_horizon hs
     ==> rfs_slab hs t = hs_count hs`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_slab] THEN
  MATCH_MP_TAC (INST_TYPE [`:num`,`:A`] SELECT_UNIQUE) THEN X_GEN_TAC `k:num` THEN BETA_TAC THEN
  EQ_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k + 1`; `hs_count(hs:(A)rfs_history)`]
                  APX_HS_TIME_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
    UNDISCH_TAC `t < rfs_horizon(hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_horizon]]);;

let SNGL_LAST_VIEW = prove
 (`!hs:(A)rfs_history t.
     rfs_history_ok hs /\ hs_time hs (hs_count hs) <= t /\ t < rfs_horizon hs
     ==> rfs_top_at hs t = hs_top hs (hs_count hs) /\
         rfs_atlas_at hs t = hs_atlas hs (hs_count hs) /\
         rfs_metric_at hs t = hs_metric hs (hs_count hs) t /\
         rfs_vtop (rfs_view hs) t = hs_top hs (hs_count hs) /\
         rfs_vatlas (rfs_view hs) t = hs_atlas hs (hs_count hs) /\
         rfs_vmetric (rfs_view hs) t = hs_metric hs (hs_count hs) t /\
         (!z. rfs_vscalar (rfs_view hs) t z =
              mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) t) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_live (hs:(A)rfs_history) t` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_live] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`] APX_HS_TIME_POS) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= n + 1`] THEN
    UNDISCH_TAC `t < rfs_horizon(hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_horizon] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] SNGL_LAST_SLAB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_metric_at; rfs_view; rfs_vtop;
                  rfs_vatlas; rfs_vmetric; rfs_vscalar]);;

(* The last stage: compact Hausdorff manifold with a Ricci flow from T_n.    *)

let SNGL_LAST_STAGE = prove
 (`!hs:(A)rfs_history.
     rfs_history_ok hs
     ==> hausdorff_space (hs_top hs (hs_count hs)) /\
         smooth_manifold_atlas (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
         compact_space (hs_top hs (hs_count hs)) /\
         ricci_flow_from (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                         (hs_time hs (hs_count hs)) (rfs_horizon hs)
                         (hs_metric hs (hs_count hs)) /\
         hs_time hs (hs_count hs) < rfs_horizon hs /\
         (!t. hs_time hs (hs_count hs) <= t /\ t < rfs_horizon hs
              ==> riemannian_metric (hs_atlas hs (hs_count hs))
                                    (hs_metric hs (hs_count hs) t))`,
  GEN_TAC THEN REWRITE_TAC[rfs_history_ok; rfs_horizon] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tm")
    (CONJUNCTS_THEN2 (LABEL_TAC "st") (LABEL_TAC "ev")))) THEN
  REMOVE_THEN "st" (MP_TAC o SPEC `hs_count(hs:(A)rfs_history)`) THEN
  REMOVE_THEN "tm" (MP_TAC o SPEC `hs_count(hs:(A)rfs_history)`) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  ASM_CASES_TAC `t = hs_time hs (hs_count(hs:(A)rfs_history))` THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Open sets of the last stage persist over every window inside [T_n, T).   *)

let SNGL_LAST_PERSISTS = prove
 (`!hs:(A)rfs_history B a b.
     rfs_history_ok hs /\ open_in (hs_top hs (hs_count hs)) B /\
     hs_time hs (hs_count hs) <= a /\ b < rfs_horizon hs
     ==> rfs_persists (rfs_view hs) B a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_view; rfs_persists] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] SNGL_LAST_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* sngl_fwd and sngl_bwd from Lemma 11.2.  The forward window                *)
(* form is P3N_L112_WINDOW of pc_p3_s16end; the backward form is the ball    *)
(* form P2C_LEMMA_11_2_STATEMENT at the centre, with C replaced by max C 2   *)
(* (P2B_CANON_MONO_C).  P2_LEMMA_11_2_STATEMENT has the same body as         *)
(* P2C_LEMMA_11_2_STATEMENT.                                                 *)
(* ------------------------------------------------------------------------- *)

let SNGL_P2_L112 = prove
 (`!u:A->bool. P2C_LEMMA_11_2_STATEMENT u ==> P2_LEMMA_11_2_STATEMENT u`,
  REWRITE_TAC[P2C_LEMMA_11_2_STATEMENT; P2_LEMMA_11_2_STATEMENT]);;

let SNGL_FWD_FROM = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !(hs:(A)rfs_history) C eps r0.
             sngl_hyp hs C eps r0 /\ eps <= eps0 /\ p2c_regular_view (rfs_view hs)
             ==> sngl_fwd hs C r0`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3N_L112_WINDOW) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`] THEN
  REWRITE_TAC[sngl_hyp; sngl_fwd] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`B:A->bool`; `t0:real`; `t1:real`; `D:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "W" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`;
                                   `B:A->bool`; `t0:real`; `t1:real`; `D:real`]) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `open_in (rfs_top_at (hs:(A)rfs_history) t0) B` THEN
    REWRITE_TAC[rfs_view; rfs_vtop]]);;

(* Nonempty slices of a regular view are manifolds with Riemannian metrics. *)

let SNGL_REGULAR_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x.
     p2c_regular_view V /\ x IN topspace(rfs_vtop V t)
     ==> hausdorff_space (rfs_vtop V t) /\
         smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
         riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_regular_view] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let SNGL_BWD_FROM = prove
 (`!u:A->bool.
     P2C_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !(hs:(A)rfs_history) C eps r0.
             sngl_hyp hs C eps r0 /\ eps <= eps0 /\ p2c_regular_view (rfs_view hs)
             ==> sngl_bwd hs C r0`,
  GEN_TAC THEN REWRITE_TAC[P2C_LEMMA_11_2_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`] THEN
  REWRITE_TAC[sngl_hyp; sngl_bwd] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`z:A`; `t0:real`; `t':real`; `r':real`] THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `min t0 t' = t' /\ max t0 t' = t0 /\ abs(t' - t0) = t0 - t'`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "L" (MP_TAC o SPECL [`hs:(A)rfs_history`; `max C (&2)`; `eps:real`; `r0:real`;
                                   `z:A`; `t0:real`; `t':real`; `r':real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `t:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `u:A->bool` P2B_CANON_MONO_C) THEN
    REWRITE_TAC[P2B_CANON_MONO_C_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_view(hs:(A)rfs_history)`; `t:real`; `x:A`] SNGL_REGULAR_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_view; rfs_vtop] THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `z:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`rfs_view(hs:(A)rfs_history)`; `t0:real`; `z:A`] SNGL_REGULAR_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_view; rfs_vtop] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_vball; rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Omega is open (MT p. 280, first paragraph of the proof):                 *)
(* a point of Omega has an open neighbourhood B in the last stage and a     *)
(* time t0 after which R is bounded on B (forward Lemma 11.2 on the open    *)
(* set {R(., t0) < D}).                                                      *)
(* ------------------------------------------------------------------------- *)

let SNGL_SCALAR_SUBLEVEL_OPEN = prove
 (`!top atlas (g:A->real^3^3) D.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
     ==> open_in top {z | z IN topspace top /\ mfd_scalar atlas g z < D}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`]
                MFD_SCALAR_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3)`; `top:A topology`; `euclideanreal`;
                 `{y:real | y < D}`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT; IN_ELIM_THM]);;

let SNGL_OMEGA_LOCAL = prove
 (`!(hs:(A)rfs_history) C eps r0 x.
     sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\ x IN p3_omega hs
     ==> ?B t0 Q. open_in (hs_top hs (hs_count hs)) B /\ x IN B /\
                  hs_time hs (hs_count hs) <= t0 /\ t0 < rfs_horizon hs /\ &0 <= Q /\
                  !s z. t0 <= s /\ s < rfs_horizon hs /\ z IN B
                        ==> mfd_scalar (hs_atlas hs (hs_count hs))
                                       (hs_metric hs (hs_count hs) s) z <= Q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sngl_hyp] THEN STRIP_TAC THEN
  ABBREV_TAC `top = hs_top hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `atlas = hs_atlas hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `g = hs_metric hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Tn = hs_time hs (hs_count(hs:(A)rfs_history))` THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:A) IN p3_omega hs` THEN ASM_REWRITE_TAC[p3_omega; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Bx:real` (LABEL_TAC "om"))) THEN
  ABBREV_TAC `D = max (&0) Bx + &1` THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL [EXPAND_TAC "D" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(r0 pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_POW_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D + inv(r0 pow 2)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `dl = inv(&16 * max C (&2) * (D + inv(r0 pow 2)))` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_ADD THEN ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT];
    ALL_TAC] THEN
  REMOVE_THEN "om" (MP_TAC o SPEC `max Tn (rfs_horizon(hs:(A)rfs_history) - dl)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= t0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`] APX_HS_TIME_POS) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= n + 1`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t0:real`] SNGL_LAST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `BB = {z | z IN topspace top /\ mfd_scalar atlas ((g:real->A->real^3^3) t0) z < D}` THEN
  SUBGOAL_THEN `open_in top (BB:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "BB" THEN ASM_SIMP_TAC[SNGL_SCALAR_SUBLEVEL_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN BB` ASSUME_TAC THENL
   [EXPAND_TAC "BB" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`BB:A->bool`; `t0:real`; `&2 * (D + inv(r0 pow 2))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->A->real^3^3) t0) z < D` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN BB` THEN EXPAND_TAC "BB" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real = t0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] SNGL_LAST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_persists (rfs_view hs) (BB:A->bool) t0 s` ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_LAST_PERSISTS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `sngl_fwd (hs:(A)rfs_history) C r0` THEN REWRITE_TAC[sngl_fwd] THEN
  DISCH_THEN(MP_TAC o SPECL [`BB:A->bool`; `t0:real`; `s:real`; `D:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    X_GEN_TAC `y:A` THEN EXPAND_TAC "BB" THEN SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `z:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let SNGL_OMEGA_OPEN = prove
 (`!(hs:(A)rfs_history) C eps r0.
     sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0
     ==> open_in (hs_top hs (hs_count hs)) (p3_omega hs)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `x:A`]
                SNGL_OMEGA_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:A->bool` (X_CHOOSE_THEN `t0:real`
    (X_CHOOSE_THEN `Q:real` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `B:A->bool` THEN ASM_REWRITE_TAC[SUBSET; p3_omega; IN_ELIM_THM] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `Q:real` THEN X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(max t1 t0 + rfs_horizon(hs:(A)rfs_history)) / &2` THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tools for the limit metric.  Pinching bounds abs Rm where R               *)
(* is bounded above (P3N_PINCH_RM and R >= -6 / (4t + 1)); a Ricci flow     *)
(* smooth from a0 is smooth up to every b < b0 (rfs_flow_upto); the pullback *)
(* by the identity in the same atlas; balls of a later metric inside a ball *)
(* of an earlier one (LIM_CURVES_STAY with the identity).                    *)
(* ------------------------------------------------------------------------- *)

let SNGL_RM_PINCH = prove
 (`!(hs:(A)rfs_history) C eps r0 s z Q.
     sngl_hyp hs C eps r0 /\ hs_time hs (hs_count hs) <= s /\ s < rfs_horizon hs /\
     z IN topspace(hs_top hs (hs_count hs)) /\
     mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) s) z <= Q
     ==> mfd_rm_norm (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) s) z <=
         &2 * max Q (&6) + &2 * exp(&4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sngl_hyp] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] SNGL_LAST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`] APX_HS_TIME_POS) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= n + 1`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (hs_atlas hs (hs_count hs))
                  (hs_metric hs (hs_count(hs:(A)rfs_history)) s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_pinched_at (hs_atlas hs (hs_count hs))
                  (hs_metric hs (hs_count(hs:(A)rfs_history)) s) s z` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_pinched (rfs_view(hs:(A)rfs_history))` THEN
    REWRITE_TAC[rfs_view; rfs_pinched] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real`; `z:A`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`; `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                 `hs_metric hs (hs_count(hs:(A)rfs_history)) s`; `s:real`; `z:A`]
                P3N_PINCH_RM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `--(&6) <= mfd_scalar (hs_atlas hs (hs_count hs))
                           (hs_metric hs (hs_count(hs:(A)rfs_history)) s) z` MP_TAC THENL
   [UNDISCH_TAC `rfs_pinched_at (hs_atlas hs (hs_count hs))
                   (hs_metric hs (hs_count(hs:(A)rfs_history)) s) s z` THEN
    REWRITE_TAC[rfs_pinched_at] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `&6 / (&4 * s + &1) <= &6` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= s ==> &0 < &4 * s + &1`] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let SNGL_FROM_UPTO = prove
 (`!top atlas (g:real->A->real^3^3) a0 b0 a b.
     ricci_flow_from (top,atlas) a0 b0 g /\ a0 <= a /\ a < b /\ b < b0
     ==> rfs_flow_upto (top,atlas) a b g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_flow_upto] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a0:real`; `b0:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `ricci_flow_on (top,atlas) a0 b0 (g:real->A->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  UNDISCH_TAC `ricci_flow_on (top,atlas) a0 b0 (g:real->A->real^3^3)` THEN
  REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
  EXISTS_TAC `(b0 - b) / &2` THEN
  EXISTS_TAC `\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                  (metric_local atlas c ((g:real->A->real^3^3) (drop(fstcart z))) (sndcart z))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a0,lift b0) PCROSS IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]);;

let SNGL_PULLBACK_ID = prove
 (`!top atlas (g:A->real^N^N) z.
     smooth_manifold_atlas top atlas /\ z IN topspace top
     ==> mfd_pullback_metric atlas atlas (\x. x) g z = g z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_pullback_metric] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`]
                PDE_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas (z:A))
                           (g:A->real^N^N) (SND(chart_at atlas z) z)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[METRIC_LOCAL_AT]] THEN
  MATCH_MP_TAC P2CF_MPULLBACK_LOCAL_ID THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                    (FST(chart_at atlas z))` THEN
  ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`] CHART_INV) THEN
  ASM_REWRITE_TAC[PAIR] THEN ASM_SIMP_TAC[]);;

let SNGL_BALL_LATER = prove
 (`!top atlas (g0:A->real^N^N) g1 U x rho mu.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g0 /\ riemannian_metric atlas g1 /\ open_in top U /\
     compact_in top (top closure_of mfd_ball (top,atlas) g0 x rho) /\
     top closure_of mfd_ball (top,atlas) g0 x rho SUBSET U /\ &0 < mu /\
     (!z v. z IN U ==> mu * (v dot (g0 z ** v)) <= v dot (g1 z ** v))
     ==> !y0. y0 IN mfd_ball (top,atlas) g0 x (rho / &2)
              ==> mfd_ball (top,atlas) g1 y0 (sqrt mu * rho / &2) SUBSET
                  mfd_ball (top,atlas) g0 x rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y0:A` THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g1:A->real^N^N`;
                 `y0:A`; `y:A`; `sqrt mu * rho / &2`] P2C_BALL_CURVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g0:A->real^N^N`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g1:A->real^N^N`;
                 `U:A->bool`; `U:A->bool`; `\x:A. x`; `\x:A. x`; `x:A`; `y0:A`;
                 `rho:real`; `rho / &2`; `mu:real`; `gamma:real->A`] LIM_CURVES_STAY) THEN
  ASM_SIMP_TAC[MFD_DIFFEO_ID; IMAGE_ID] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g1:A->real^N^N`; `z:A`] SNGL_PULLBACK_ID) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `mfd_length atlas (g1:A->real^N^N) gamma (&0) (&1) < sqrt mu * rho / &2` THEN
      REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* SNGL_QF_NONNEG, SNGL_RESTRICT_QF and SNGL_METRIC_EQUIV_LOCAL (metric      *)
(* equivalence on an open set where abs Rm is bounded) are in the unit       *)
(* pc_rf_mequiv, loaded above.                                               *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Shi's bounds near a point of a region of bounded scalar                   *)
(* curvature.  If R <= Q on B0 x [t0, Th) then, on a smaller ball B1 around   *)
(* x and after t1 = (t0 + Th) / 2, every abs(nabla^l Rm)^2 is bounded         *)
(* uniformly in time (route hypothesis P2_THM_3_28 on the balls at the       *)
(* times b, which stay inside B0 by SNGL_BALL_LATER).                        *)
(* ------------------------------------------------------------------------- *)

let SNGL_SMALL_BALL = prove
 (`!top atlas (g:A->real^N^N) W x.
     hausdorff_space top /\ compact_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ open_in top W /\ x IN W
     ==> ?rho. &0 < rho /\ mfd_ball (top,atlas) g x rho SUBSET W /\
               compact_in top (top closure_of mfd_ball (top,atlas) g x rho) /\
               top closure_of mfd_ball (top,atlas) g x rho SUBSET W`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `W:A->bool`; `x:A`] MFD_BALL_NEIGHBOURHOOD_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r / &2` THEN
  SUBGOAL_THEN `top closure_of mfd_ball (top,atlas) (g:A->real^N^N) x (r / &2) SUBSET
                mfd_cball (top,atlas) g x (r / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_cball (top,atlas) (g:A->real^N^N) x (r / &2) SUBSET
                mfd_ball (top,atlas) g x r` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) x r` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ASM SET_TAC[]]);;

let SNGL_SHI_BOUNDS = prove
 (`!(u:A->bool) (hs:(A)rfs_history) C eps r0 B0 t0 Q x.
     P2_THM_3_28_STATEMENT u /\ sngl_hyp hs C eps r0 /\
     open_in (hs_top hs (hs_count hs)) B0 /\ x IN B0 /\
     hs_time hs (hs_count hs) <= t0 /\ t0 < rfs_horizon hs /\
     (!s z. t0 <= s /\ s < rfs_horizon hs /\ z IN B0
            ==> mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) s) z <= Q)
     ==> ?B1 t1. open_in (hs_top hs (hs_count hs)) B1 /\ x IN B1 /\ B1 SUBSET B0 /\
                 t0 < t1 /\ t1 < rfs_horizon hs /\
                 !l. ?Cl. !b y. t1 <= b /\ b < rfs_horizon hs /\ y IN B1
                                ==> rfa_rmd2 l (hs_atlas hs (hs_count hs))
                                               (hs_metric hs (hs_count hs) b) y <= Cl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sngl_hyp]) THEN
  ABBREV_TAC `top = hs_top hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `atlas = hs_atlas hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `g = hs_metric hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Tn = hs_time hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Th = rfs_horizon(hs:(A)rfs_history)` THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `K = &2 * max Q (&6) + &2 * exp(&4)` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. z IN B0 ==> z IN topspace top` (LABEL_TAC "tsp") THENL
   [UNDISCH_TAC `open_in top (B0:A->bool)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN REWRITE_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s z. t0 <= s /\ s < Th /\ z IN B0
                      ==> mfd_rm_norm atlas ((g:real->A->real^3^3) s) z <= K`
  (LABEL_TAC "rm") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K" THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `s:real`; `z:A`;
                   `Q:real`] SNGL_RM_PINCH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [USE_THEN "tsp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `mu = exp(--(&2 * (&(dimindex(:3) - 1) * K) * (Th - t0)))` THEN
  SUBGOAL_THEN `&0 < mu` ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!b z v. t0 <= b /\ b < Th /\ z IN B0
                        ==> mu * (v dot ((g:real->A->real^3^3) t0 z ** v)) <=
                            v dot (g b z ** v)` (LABEL_TAC "cmp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `t0:real`; `Th:real`; `B0:A->bool`; `K:real`]
                  SNGL_METRIC_EQUIV_LOCAL) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PDE_RFF_RESTRICT THEN
        MAP_EVERY EXISTS_TAC [`Tn:real`; `Th:real`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`b:real`; `z:A`; `v:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [EXPAND_TAC "mu" THEN REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SNGL_QF_NONNEG THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "tsp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t0`; `B0:A->bool`; `x:A`] SNGL_SMALL_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `tau = (Th - t0) / &2` THEN
  ABBREV_TAC `r = sqrt mu * rho / &2` THEN
  SUBGOAL_THEN `&0 < tau /\ &0 < r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "tau" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_HALF];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`mfd_ball (top,atlas) ((g:real->A->real^3^3) t0) x (rho / &2)`;
                        `t0 + tau`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[MFD_BALL_OPEN];
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THEN
    TRY(USE_THEN "tsp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) ((g:real->A->real^3^3) t0) x rho` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN
  UNDISCH_TAC `P2_THM_3_28_STATEMENT (u:A->bool)` THEN REWRITE_TAC[P2_THM_3_28_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `K:real`; `r:real`; `tau:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "shi")) THEN
  EXISTS_TAC `Cl:real` THEN MAP_EVERY X_GEN_TAC [`b:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t0`; `(g:real->A->real^3^3) b`; `B0:A->bool`;
                 `x:A`; `rho:real`; `mu:real`] SNGL_BALL_LATER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "cmp" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "shi" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `b - tau`; `b:real`; `g:real->A->real^3^3`; `y:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `b - (b - tau) = tau`; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SNGL_FROM_UPTO THEN MAP_EVERY EXISTS_TAC [`Tn:real`; `Th:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(g:real->A->real^3^3) t0`; `x:A`; `rho / &2`] MFD_BALL_OPEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      MAP_EVERY X_GEN_TAC [`t:real`; `z:A`] THEN STRIP_TAC THEN
      USE_THEN "rm" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(z:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) b) y r` THEN
      UNDISCH_TAC `mfd_ball (top,atlas) ((g:real->A->real^3^3) b) y r SUBSET
                   mfd_ball (top,atlas) (g t0) x rho` THEN
      UNDISCH_TAC `mfd_ball (top,atlas) ((g:real->A->real^3^3) t0) x rho SUBSET B0` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:A`) THEN REWRITE_TAC[rfa_rmd2] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`; `x:A`; `rho / &2`] MFD_BALL_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Limits at the right end of a time interval.  A Lipschitz                  *)
(* real function on (a,b) has a limit at b with the rate c (b - t)           *)
(* (t -> f t + c t is nondecreasing and bounded); the same entrywise for     *)
(* matrix families with a uniform Lipschitz bound; jet norms from bounds on *)
(* the iterated partials.                                                    *)
(* ------------------------------------------------------------------------- *)

let SNGL_LIP_LIMIT = prove
 (`!(f:real->real) a b c.
     a < b /\ &0 <= c /\
     (!t1 t2. a < t1 /\ t1 <= t2 /\ t2 < b ==> abs(f t2 - f t1) <= c * (t2 - t1))
     ==> ?l. !t. a < t /\ t < b ==> abs(f t - l) <= c * (b - t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (\t. (f:real->real) t + c * t) {t | a < t /\ t < b}` THEN
  SUBGOAL_THEN `!t s. a < t /\ t < b /\ a < s /\ s < b
                      ==> (f:real->real) s + c * s <= f t + c * t + &2 * c * (b - t)`
  (LABEL_TAC "ub") THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `s <= t` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `t:real`]) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= &2 * c * (b - t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&2 * c * (s - t) <= &2 * c * (b - t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(S:real->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(a + b) / &2` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> (f:real->real) t + c * t <= sup S /\
                                      sup S <= f t + c * t + &2 * c * (b - t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
       [EXISTS_TAC `(f:real->real) t + c * t + &2 * c * (b - t)` THEN
        EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "ub" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
        EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "ub" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `sup S - c * b` THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SNGL_ENTRY_LIMITS = prove
 (`!(G:real->real^M->real^N^N) S a b c.
     a < b /\ &0 <= c /\
     (!t1 t2 y p q. a < t1 /\ t1 <= t2 /\ t2 < b /\ y IN S /\
                    1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                    ==> abs(G t2 y$p$q - G t1 y$p$q) <= c * (t2 - t1))
     ==> ?Gl. !t y p q. a < t /\ t < b /\ y IN S /\
                        1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                        ==> abs(G t y$p$q - (Gl:real^M->real^N^N) y$p$q) <= c * (b - t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y p q. ?l. y IN S /\ 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                ==> !t. a < t /\ t < b
                        ==> abs((G:real->real^M->real^N^N) t y$p$q - l) <= c * (b - t)`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^M`; `p:num`; `q:num`] THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC SNGL_LIP_LIMIT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real^M->num->num->real`) THEN
  EXISTS_TAC `\y:real^M. (lambda p q. L y p q):real^N^N` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA]);;

let SNGL_JETN_BOUND = prove
 (`!m (f:real^M->real^N) y B.
     (!l. l IN pde_index_lists m (:M) ==> norm(iterated_partial l f y) <= B)
     ==> pde_jetn m f y <= &(CARD(pde_index_lists m (:M))) * B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE]);;

(* ------------------------------------------------------------------------- *)
(* The Euclidean core of the limit metric.  For a local Ricci                *)
(* flow G on [a,b) in an open V of R^N whose jets of every order are bounded *)
(* on cball(c0, 2r), uniformly equivalent to the Euclidean metric there and  *)
(* with abs(Rm)^2 bounded, the metrics converge as t -> b: entrywise with   *)
(* the rate c (b - t) (Lipschitz in time, P3N_LIP_ENTRY), to a metric field *)
(* Gl on ball(c0, r) (smoothness from P2CS_JET_SUBSEQ), and in lck_dist2 of  *)
(* every order on cball(c0, r / 2) (P2CI_LCK_COMPACT along sequences).      *)
(* ------------------------------------------------------------------------- *)

let SNGL_QF_ENTRY_DIFF = prove
 (`!(A:real^N^N) B e v.
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> abs(A$p$q - B$p$q) <= e)
     ==> abs(v dot (A ** v) - v dot (B ** v)) <=
         &(dimindex(:N)) * &(dimindex(:N)) * e * (v dot v)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM DOT_RSUB; GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(v:real^N) * norm((A - B:real^N^N) ** v)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(v:real^N) * ((&(dimindex(:N)) * &(dimindex(:N)) * e) * norm v)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `onorm(\x. (A - B:real^N^N) ** x) * norm(v:real^N)` THEN CONJ_TAC THENL
     [MP_TAC(MATCH_MP ONORM (ISPEC `A - B:real^N^N` MATRIX_VECTOR_MUL_LINEAR)) THEN
      SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC ONORM_LE_MATRIX_COMPONENT THEN
      ASM_SIMP_TAC[MATRIX_SUB_COMPONENT]];
    REWRITE_TAC[GSYM NORM_POW_2] THEN REAL_ARITH_TAC]);;

(* A real number bounded by k (b - t) for all t in (a,b) is <= 0.          *)

let SNGL_SMALL_LE = prove
 (`!x k a b. a < b /\ (!t. a < t /\ t < b ==> x <= k * (b - t)) ==> x <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `h = min ((b - a) / &2) (x / (abs k + &1))` THEN
  SUBGOAL_THEN `&0 < h /\ h <= (b - a) / &2 /\ h <= x / (abs k + &1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b - h`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `b - (b - h) = h`] THEN
  SUBGOAL_THEN `k * h <= abs k * h /\ (abs k + &1) * h <= x` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 < abs k + &1`]];
    REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC]);;

let SNGL_LL_RATE = prove
 (`!V a b (G:real->real^N->real^N^N) S L D.
     lricci_flow V a b G /\ S SUBSET V /\ &0 <= L /\ &0 <= D /\
     (!t y v. a <= t /\ t < b /\ y IN S ==> v dot (G t y ** v) <= L * (v dot v)) /\
     (!t y. a <= t /\ t < b /\ y IN S ==> lrm_deriv_norm2 0 (G t) y <= D)
     ==> ?Gl. !t y p q. a < t /\ t < b /\ y IN S /\
                        1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                        ==> abs(G t y$p$q - (Gl:real^N->real^N^N) y$p$q) <=
                            (&8 * &(dimindex(:N)) * sqrt D * L) * (b - t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SNGL_ENTRY_LIMITS THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `lricci_flow V a b (G:real->real^N->real^N^N)` THEN
    SIMP_TAC[lricci_flow];
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P3N_LIP_ENTRY THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Times approaching b from inside (a,b). *)

let SNGL_SEQ_TIMES = prove
 (`!a b. a < b
         ==> (!n. a < b - (b - a) / (&n + &2) /\ b - (b - a) / (&n + &2) < b) /\
             (!e. &0 < e ==> ?N. !n. N <= n ==> (b - a) / (&n + &2) < e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN SUBGOAL_THEN `&0 < (b - a) / (&n + &2) /\ (b - a) / (&n + &2) < b - a` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &2`] THEN
        SUBGOAL_THEN `&0 <= (b - a) * &n` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      REAL_ARITH_TAC];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `(b - a) / e` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &2`] THEN
    UNDISCH_TAC `(b - a) / e <= &N` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&N * e <= &n * e` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE];
      ASM_REAL_ARITH_TAC]]);;

(* Smoothness of the entrywise limit: P2CS_JET_SUBSEQ along the times       *)
(* s_n = b - (b - a) / (n + 2) gives a smooth limit of a subsequence, which  *)
(* agrees with Gl (both are limits of the same matrices).                    *)

let SNGL_LL_SMOOTH = prove
 (`!(G:real->real^N->real^N^N) Gl a b c0 r c.
     a < b /\ &0 < r /\ &0 <= c /\
     (!t. a < t /\ t < b
          ==> smooth_map_on (ball(c0,&2 * r))
                ((vectorize:real^N^N->real^(N,N)finite_prod) o G t)) /\
     (!m. ?B. !t l y. a < t /\ t < b /\ l IN pde_index_lists m (:N) /\ y IN ball(c0,&2 * r)
                      ==> norm(iterated_partial l
                                 ((vectorize:real^N^N->real^(N,N)finite_prod) o G t) y) <= B) /\
     (!t y p q. a < t /\ t < b /\ y IN ball(c0,&2 * r) /\
                1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                ==> abs(G t y$p$q - Gl y$p$q) <= c * (b - t))
     ==> smooth_map_on (ball(c0,r)) ((vectorize:real^N^N->real^(N,N)finite_prod) o Gl)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sm")
   (CONJUNCTS_THEN2 (LABEL_TAC "jet") (LABEL_TAC "rate")))))) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] SNGL_SEQ_TIMES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (LABEL_TAC "sz")) THEN
  MP_TAC(ISPECL
   [`\(i:num) (n:num). (vectorize:real^N^N->real^(N,N)finite_prod) o
                       (G:real->real^N->real^N^N) (b - (b - a) / (&n + &2))`;
    `\i:num. ball(c0:real^N,&2 * r)`; `\i:num. (c0:real^N)`; `\i:num. r:real`]
   P2CS_JET_SUBSEQ) THEN
  REWRITE_TAC[NUM_COUNTABLE; OPEN_BALL] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
      USE_THEN "sm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `m:num` THEN
      USE_THEN "jet" (X_CHOOSE_TAC `B:real` o SPEC `m:num`) THEN
      EXISTS_TAC `&(CARD(pde_index_lists m (:N))) * B` THEN EXISTS_TAC `0` THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SNGL_JETN_BOUND THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN
    `H:num->real^N->real^(N,N)finite_prod` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `[]:num list`)) THEN
  REWRITE_TAC[ALL; iterated_partial] THEN DISCH_THEN(LABEL_TAC "hc") THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `(H:num->real^N->real^(N,N)finite_prod) 0` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `e = norm((H:num->real^N->real^(N,N)finite_prod) 0 y -
                       (vectorize:real^N^N->real^(N,N)finite_prod) (Gl y))` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "hc" (MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_HALF]; DISCH_THEN(X_CHOOSE_THEN `K1:num` (LABEL_TAC "k1"))] THEN
  ABBREV_TAC `M = &(dimindex(:N) * dimindex(:N)) * c + &1` THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  USE_THEN "sz" (MP_TAC o SPEC `e / &2 / M`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF]; DISCH_THEN(X_CHOOSE_TAC `K2:num`)] THEN
  ABBREV_TAC `n = (K1:num) + K2` THEN
  SUBGOAL_THEN `K2 <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN CONJ_TAC THENL
     [EXPAND_TAC "n" THEN ARITH_TAC;
      MP_TAC(SPEC `sub:num->num` MONOTONE_BIGGER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `d = (b - a) / (&((sub:num->num) n) + &2)` THEN
  SUBGOAL_THEN `&0 < d /\ d * M < e / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_LT_DIV THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN EXPAND_TAC "d" THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "k1" (MP_TAC o SPECL [`n:num`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `norm((vectorize:real^N^N->real^(N,N)finite_prod)
           ((G:real->real^N->real^N^N) (b - d) y) - vectorize(Gl y)) <
    e / &2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&(dimindex(:N) * dimindex(:N)) * (c * d)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3N_VEC_C0 THEN MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
      USE_THEN "rate" (MP_TAC o SPECL [`b - d`; `y:real^N`; `p:num`; `q:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [EXPAND_TAC "d" THEN USE_THEN "st" (MP_TAC o SPEC `(sub:num->num) n`) THEN
          SIMP_TAC[];
          UNDISCH_TAC `(y:real^N) IN ball(c0,r)` THEN REWRITE_TAC[IN_BALL] THEN
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_ARITH `b - (b - d) = d`]];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d * M` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `norm((vectorize:real^N^N->real^(N,N)finite_prod)
                  ((G:real->real^N->real^N^N) (b - d) y) -
                (H:num->real^N->real^(N,N)finite_prod) 0 y) < e / &2` THEN
  UNDISCH_TAC `norm((H:num->real^N->real^(N,N)finite_prod) 0 y -
                    (vectorize:real^N^N->real^(N,N)finite_prod) (Gl y)) = e` THEN
  CONV_TAC NORM_ARITH);;

(* The limit is a metric field: symmetric and positive definite as a limit  *)
(* of metrics uniformly equivalent to the Euclidean metric.                  *)

let SNGL_LL_FIELD = prove
 (`!(G:real->real^N->real^N^N) Gl a b c0 r c L.
     a < b /\ &0 < r /\ &0 <= c /\ &0 < L /\
     smooth_map_on (ball(c0,r)) ((vectorize:real^N^N->real^(N,N)finite_prod) o Gl) /\
     (!t y. a < t /\ t < b /\ y IN ball(c0,r) ==> transp(G t y) = G t y) /\
     (!t y v. a < t /\ t < b /\ y IN ball(c0,r)
              ==> norm v pow 2 <= L * (v dot (G t y ** v))) /\
     (!t y p q. a < t /\ t < b /\ y IN ball(c0,r) /\
                1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                ==> abs(G t y$p$q - Gl y$p$q) <= c * (b - t))
     ==> metric_field (ball(c0,r)) Gl`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sym")
   (CONJUNCTS_THEN2 (LABEL_TAC "low") (LABEL_TAC "rate")))))))) THEN
  ASM_REWRITE_TAC[metric_field; OPEN_BALL] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [SIMP_TAC[CART_EQ; TRANSP_COMPONENT] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &0 /\ --x <= &0 ==> x = &0`) THEN
    CONJ_TAC THEN
    (MATCH_MP_TAC SNGL_SMALL_LE THEN
     MAP_EVERY EXISTS_TAC [`&2 * c`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `t:real` THEN STRIP_TAC THEN
     USE_THEN "rate" (MP_TAC o SPECL [`t:real`; `y:real^N`; `p:num`; `q:num`]) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     USE_THEN "rate" (MP_TAC o SPECL [`t:real`; `y:real^N`; `q:num`; `p:num`]) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     USE_THEN "sym" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN(MP_TAC o AP_TERM `\M:real^N^N. M$p$q`) THEN
     ASM_SIMP_TAC[TRANSP_COMPONENT] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(v:real^N) pow 2 <= L * (v dot ((Gl:real^N->real^N^N) y ** v))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `--x <= &0 ==> &0 <= x`) THEN
    MATCH_MP_TAC SNGL_SMALL_LE THEN
    MAP_EVERY EXISTS_TAC [`L * &(dimindex(:N)) * &(dimindex(:N)) * c * ((v:real^N) dot v)`;
                          `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "low" (MP_TAC o SPECL [`t:real`; `y:real^N`; `v:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`(G:real->real^N->real^N^N) t y`; `(Gl:real^N->real^N^N) y`;
                   `c * (b - t)`; `v:real^N`] SNGL_QF_ENTRY_DIFF) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "rate" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    SUBGOAL_THEN
     `L * (v dot ((G:real->real^N->real^N^N) t y ** v) - v dot ((Gl:real^N->real^N^N) y ** v))
      <= L * (&(dimindex(:N)) * &(dimindex(:N)) * (c * (b - t)) * (v dot v))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L * (v dot ((Gl:real^N->real^N^N) y ** v))` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_MUL_EQ]]);;

(* C^m convergence on cball(c0, r / 2), by contradiction along a sequence    *)
(* of times (P2CI_LCK_COMPACT).                                              *)

let SNGL_LL_LCK = prove
 (`!(G:real->real^N->real^N^N) Gl a b c0 r c.
     a < b /\ &0 < r /\ &0 <= c /\ metric_field (ball(c0,r)) Gl /\
     (!t. a < t /\ t < b
          ==> smooth_map_on (ball(c0,&2 * r))
                ((vectorize:real^N^N->real^(N,N)finite_prod) o G t)) /\
     (!m. ?B. !t l y. a < t /\ t < b /\ l IN pde_index_lists m (:N) /\ y IN ball(c0,&2 * r)
                      ==> norm(iterated_partial l
                                 ((vectorize:real^N^N->real^(N,N)finite_prod) o G t) y) <= B) /\
     (!t y p q. a < t /\ t < b /\ y IN ball(c0,&2 * r) /\
                1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                ==> abs(G t y$p$q - Gl y$p$q) <= c * (b - t))
     ==> !m e. &0 < e
               ==> ?d. &0 < d /\
                       !t y. b - d < t /\ t < b /\ y IN cball(c0,r / &2)
                             ==> lck_dist2 m Gl (G t) y < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sm")
   (CONJUNCTS_THEN2 (LABEL_TAC "jet") (LABEL_TAC "rate"))))))) THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `e:real`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`] SNGL_SEQ_TIMES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (LABEL_TAC "sz")) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_THEN(LABEL_TAC "neg") THEN
  SUBGOAL_THEN
   `!n:num. ?t y. b - (b - a) / (&n + &2) < t /\ t < b /\ y IN cball(c0,r / &2) /\
                  e <= lck_dist2 m Gl ((G:real->real^N->real^N^N) t) y`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 < (b - a) / (&n + &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "neg" (MP_TAC o SPEC `(b - a) / (&n + &2)` o
                    GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:num->real` (X_CHOOSE_THEN `yy:num->real^N` (LABEL_TAC "seq"))) THEN
  SUBGOAL_THEN `!n. a < (tt:num->real) n /\ tt n < b` (LABEL_TAC "tab") THENL
   [GEN_TAC THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    USE_THEN "st" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. b - (tt:num->real) n < (b - a) / (&n + &2)` (LABEL_TAC "td") THENL
   [GEN_TAC THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(c0:real^N,r)`; `Gl:real^N->real^N^N`;
                 `\n. (G:real->real^N->real^N^N) ((tt:num->real) n)`;
                 `cball(c0:real^N,r / &2)`] P2CI_LCK_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `ball(z:real^N,r / &2) SUBSET ball(c0,r) /\
                  ball(z:real^N,r / &2) SUBSET ball(c0,&2 * r)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL] THEN
      UNDISCH_TAC `dist(c0:real^N,z) <= r / &2` THEN UNDISCH_TAC `&0 < r` THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    REWRITE_TAC[p2ci_near] THEN EXISTS_TAC `r / &2` THEN REWRITE_TAC[o_THM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(c0:real^N,&2 * r)` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "sm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(c0:real^N,r)` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `metric_field (ball(c0:real^N,r)) Gl` THEN
      SIMP_TAC[metric_field];
      X_GEN_TAC `k:num` THEN
      USE_THEN "jet" (X_CHOOSE_TAC `B:real` o SPEC `k:num`) THEN
      EXISTS_TAC `&(CARD(pde_index_lists k (:N))) * B` THEN EXISTS_TAC `0` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC SNGL_JETN_BOUND THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^N) IN ball(z,r / &2)` THEN
      UNDISCH_TAC `ball(z:real^N,r / &2) SUBSET ball(c0,&2 * r)` THEN SET_TAC[];
      X_GEN_TAC `e1:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < &(dimindex(:N) * dimindex(:N)) * c + &1` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
        ALL_TAC] THEN
      USE_THEN "sz" (MP_TAC o SPEC `e1 / (&(dimindex(:N) * dimindex(:N)) * c + &1)`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
      EXISTS_TAC `N1:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `&(dimindex(:N) * dimindex(:N)) * (c * (b - (tt:num->real) n))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P3N_VEC_C0 THEN MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
        STRIP_TAC THEN USE_THEN "rate" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^N) IN ball(z,r / &2)` THEN
        UNDISCH_TAC `ball(z:real^N,r / &2) SUBSET ball(c0,&2 * r)` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "tab" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      USE_THEN "td" (ASSUME_TAC o SPEC `n:num`) THEN
      USE_THEN "n1" (MP_TAC o SPEC `n:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `(b - (tt:num->real) n) * (&(dimindex(:N) * dimindex(:N)) * c + &1) < e1`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `((b - a) / (&n + &2)) * (&(dimindex(:N) * dimindex(:N)) * c + &1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= b - (tt:num->real) n` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `e:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (MP_TAC o SPECL [`N0:num`; `(yy:num->real^N) N0`])) THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `N0:num`) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ASM_REAL_ARITH_TAC);;

(* The Euclidean core. *)

let SNGL_LOCAL_LIMIT = prove
 (`!V a b (G:real->real^N->real^N^N) c0 r.
     lricci_flow V a b G /\ (!t. a <= t /\ t < b ==> metric_field V (G t)) /\
     &0 < r /\ cball(c0,&2 * r) SUBSET V /\
     (!m. ?B. !t l y. a <= t /\ t < b /\ l IN pde_index_lists m (:N) /\
                      y IN cball(c0,&2 * r)
                      ==> norm(iterated_partial l
                                 ((vectorize:real^N^N->real^(N,N)finite_prod) o G t) y) <= B) /\
     (?L. &0 < L /\
          !t y v. a <= t /\ t < b /\ y IN cball(c0,&2 * r)
                  ==> norm v pow 2 <= L * (v dot (G t y ** v)) /\
                      v dot (G t y ** v) <= L * (v dot v)) /\
     (?D. &0 <= D /\
          !t y. a <= t /\ t < b /\ y IN cball(c0,&2 * r) ==> lrm_deriv_norm2 0 (G t) y <= D)
     ==> ?Gl c. &0 <= c /\ metric_field (ball(c0,r)) Gl /\
                (!t y p q. a < t /\ t < b /\ y IN ball(c0,&2 * r) /\
                           1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                           ==> abs(G t y$p$q - Gl y$p$q) <= c * (b - t)) /\
                (!m e. &0 < e
                       ==> ?d. &0 < d /\
                               !t y. b - d < t /\ t < b /\ y IN cball(c0,r / &2)
                                     ==> lck_dist2 m Gl (G t) y < e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mf")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "jet") (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eqv")))
     (X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmd"))))))))) THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL
   [UNDISCH_TAC `lricci_flow V a b (G:real->real^N->real^N^N)` THEN SIMP_TAC[lricci_flow];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `cball(c0:real^N,&2 * r)`; `L:real`; `D:real`] SNGL_LL_RATE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [USE_THEN "eqv" (MP_TAC o SPECL [`t:real`; `y:real^N`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "rmd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Gl:real^N->real^N^N` (LABEL_TAC "rate0")) THEN
  ABBREV_TAC `c = &8 * &(dimindex(:N)) * sqrt D * L` THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(c0:real^N,&2 * r) SUBSET cball(c0,&2 * r) /\
                ball(c0:real^N,r) SUBSET ball(c0,&2 * r)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y p q. a < t /\ t < b /\ y IN ball(c0,&2 * r) /\
              1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> abs((G:real->real^N->real^N^N) t y$p$q - (Gl:real^N->real^N^N) y$p$q)
                  <= c * (b - t)`
  (LABEL_TAC "rate") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "rate0" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b
                    ==> smooth_map_on (ball(c0,&2 * r))
                          ((vectorize:real^N^N->real^(N,N)finite_prod) o
                           (G:real->real^N->real^N^N) t)` (LABEL_TAC "sm") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `V:real^N->bool` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "mf" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[metric_field]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ?B. !t l y. a < t /\ t < b /\ l IN pde_index_lists m (:N) /\ y IN ball(c0,&2 * r)
                    ==> norm(iterated_partial l
                               ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                (G:real->real^N->real^N^N) t) y) <= B`
  (LABEL_TAC "jet2") THENL
   [X_GEN_TAC `m:num` THEN USE_THEN "jet" (X_CHOOSE_TAC `B:real` o SPEC `m:num`) THEN
    EXISTS_TAC `B:real` THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(c0:real^N,r))
                  ((vectorize:real^N^N->real^(N,N)finite_prod) o (Gl:real^N->real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_LL_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`G:real->real^N->real^N^N`; `a:real`; `b:real`; `c:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "sm" ACCEPT_TAC; USE_THEN "jet2" ACCEPT_TAC; USE_THEN "rate" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (ball(c0,r)) (Gl:real^N->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_LL_FIELD THEN
    MAP_EVERY EXISTS_TAC [`G:real->real^N->real^N^N`; `a:real`; `b:real`; `c:real`;
                          `L:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "mf" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[metric_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2 o
                                                  CONJUNCT2) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN USE_THEN "eqv" (MP_TAC o SPECL [`t:real`; `y:real^N`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
                      SIMP_TAC[]];
      REPEAT STRIP_TAC THEN USE_THEN "rate" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Gl:real^N->real^N^N`; `c:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SNGL_LL_LCK THEN EXISTS_TAC `a:real` THEN EXISTS_TAC `c:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "sm" ACCEPT_TAC; USE_THEN "jet2" ACCEPT_TAC; USE_THEN "rate" ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A uniform constant over a compact set from local ones (for               *)
(* an antitone property), used to globalize the local convergence.          *)
(* ------------------------------------------------------------------------- *)

let SNGL_COMPACT_UNIFORM = prove
 (`!top (K:A->bool) (P:real->A->bool).
     compact_in top K /\
     (!x. x IN K ==> ?N d. open_in top N /\ x IN N /\ &0 < d /\ !y. y IN N ==> P d y) /\
     (!d d' y. &0 < d' /\ d' <= d /\ P d y ==> P d' y)
     ==> ?d. &0 < d /\ !y. y IN K ==> P d y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `NN:A->A->bool` (X_CHOOSE_THEN `dd:A->real` (LABEL_TAC "loc"))) THEN
  UNDISCH_TAC `compact_in top (K:A->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `IMAGE (NN:A->A->bool) K`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    CONJ_TAC THEN
    (X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     USE_THEN "loc" (MP_TAC o SPEC `x:A`) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
     ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`NN:A->A->bool`; `K:A->bool`; `V:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `S:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    UNDISCH_TAC `(K:A->bool) SUBSET UNIONS V` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; SUBSET_EMPTY; NOT_IN_EMPTY] THEN
    SIMP_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  EXISTS_TAC `inf(IMAGE (dd:A->real) S)` THEN
  ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL
     [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x:A. x IN S /\ (y:A) IN (NN:A->A->bool) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:A->bool) SUBSET UNIONS V` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(dd:A->real) x` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `z:A`) THEN ANTS_TAC THENL
     [ASM SET_TAC[]; SIMP_TAC[]];
    ASM_SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; EXISTS_IN_IMAGE] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The local limit at a point x of Omega, in a chart (U,phi)                 *)
(* of the last stage around x: on a Euclidean ball around phi x the chart    *)
(* metrics g(t) converge as t -> T entrywise to a metric field Gl, and in    *)
(* lck_dist2 of every order on a smaller closed ball.  Hamilton's chart jet  *)
(* bounds on the restricted manifold M1 = B1 (RFA_R1_CHART_FROM) feed the    *)
(* Euclidean core SNGL_LOCAL_LIMIT.                                          *)
(* ------------------------------------------------------------------------- *)

let SNGL_OMEGA_OF_BOUND = prove
 (`!(hs:(A)rfs_history) B t0 Q.
     open_in (hs_top hs (hs_count hs)) B /\
     hs_time hs (hs_count hs) <= t0 /\ t0 < rfs_horizon hs /\
     (!s z. t0 <= s /\ s < rfs_horizon hs /\ z IN B
            ==> mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) s) z <= Q)
     ==> B SUBSET p3_omega hs`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; p3_omega; IN_ELIM_THM] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `open_in (hs_top hs (hs_count(hs:(A)rfs_history))) B` THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `Q:real` THEN X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(max t1 t0 + rfs_horizon(hs:(A)rfs_history)) / &2` THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SNGL_RMD2_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) l x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ x IN W
     ==> rfa_rmd2 l (restrict_atlas atlas W) (restrict_metric atlas W g) x =
         rfa_rmd2 l atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `g:A->real^N^N`; `x:A`] MFDR_RESTRICT_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`l:num`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(U:A->bool,phi:A->real^N)`; `x:A`] RFA_RMD2_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[rfa_rmd2] THEN
  MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[]);;

(* A Ricci flow on [a,b) whose abs Rm and all abs(nabla^l Rm)^2 are bounded  *)
(* on an open set W converges as t -> b near every point of W, in a chart    *)
(* of the atlas: entrywise with a rate and in lck_dist2 of every order.      *)

let SNGL_FLOW_LOCAL_LIMIT = prove
 (`!top atlas (g:real->A->real^N^N) a b W x.
     ricci_flow_from (top,atlas) a b g /\ open_in top W /\ x IN W /\
     (?K. &0 <= K /\ !t z. a <= t /\ t < b /\ z IN W ==> mfd_rm_norm atlas (g t) z <= K) /\
     (!l. ?C. !t z. a <= t /\ t < b /\ z IN W ==> rfa_rmd2 l atlas (g t) z <= C)
     ==> ?U phi rho Gl c.
           (U,phi) IN atlas /\ x IN U /\ &0 < rho /\
           cball(phi x,&2 * rho) SUBSET IMAGE phi (U INTER W) /\
           metric_field (ball(phi x,rho)) Gl /\ &0 <= c /\
           (!t y p q. a < t /\ t < b /\ y IN ball(phi x,&2 * rho) /\
                      1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                      ==> abs(metric_local atlas (U,phi) (g t) y$p$q - Gl y$p$q)
                          <= c * (b - t)) /\
           (!m e. &0 < e
                  ==> ?d. &0 < d /\
                          !t y. b - d < t /\ t < b /\ y IN cball(phi x,rho / &2)
                                ==> lck_dist2 m Gl (metric_local atlas (U,phi) (g t)) y < e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))
     (LABEL_TAC "rmd"))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\ a < b /\
                (!t. a <= t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^N^N) t))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_from (top,atlas) a b (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = a` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `top1 = subtopology top (W:A->bool)` THEN
  ABBREV_TAC `atlas1 = restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W` THEN
  ABBREV_TAC `g1 = \t. restrict_metric atlas W ((g:real->A->real^N^N) t)` THEN
  SUBGOAL_THEN `ricci_flow_from (top1,atlas1) a b (g1:real->A->real^N^N)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["top1"; "atlas1"; "g1"] THEN
    MATCH_MP_TAC P2CF_RFF_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^N))->bool) /\
                topspace top1 = (W:A->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["top1"; "atlas1"] THEN
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY] THEN
    UNDISCH_TAC `open_in top (W:A->bool)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t < b ==> riemannian_metric atlas1 ((g1:real->A->real^N^N) t)`
  (LABEL_TAC "rie1") THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["atlas1"; "g1"] THEN BETA_TAC THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z v. a <= t /\ t < b /\ z IN topspace top1
            ==> abs(mfd_ricci atlas1 ((g1:real->A->real^N^N) t) z v v) <=
                (&(dimindex(:N) - 1) * K) * (v dot (g1 t z ** v))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "rie1" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                   `(g1:real->A->real^N^N) t`; `z:A`; `v:real^N`] P2AP_MFD_RICCI_ABS) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MAP_EVERY EXPAND_TAC ["atlas1"; "g1"] THEN BETA_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                     `(g:real->A->real^N^N) t`; `z:A`] MFD_RM_NORM_RESTRICT) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SNGL_QF_NONNEG THEN
      MAP_EVERY EXISTS_TAC [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. ?C. !t z. a <= t /\ t < b /\ z IN topspace top1
                             ==> rfa_rmd2 l atlas1 ((g1:real->A->real^N^N) t) z <= C`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num` THEN USE_THEN "rmd" (X_CHOOSE_TAC `Cl:real` o SPEC `l:num`) THEN
    EXISTS_TAC `Cl:real` THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["atlas1"; "g1"] THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `(g:real->A->real^N^N) t`; `l:num`; `z:A`] SNGL_RMD2_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `(g:real->A->real^N^N) a`; `x:A`] MFDR_RESTRICT_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `((U:A->bool) INTER W,phi:A->real^N) IN atlas1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `x:A`]
                  PDE_CHART_AT_FACTS) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "atlas1" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t y. a <= t /\ t < b /\ y IN IMAGE (phi:A->real^N) (U INTER W)
                      ==> metric_local atlas1 ((U:A->bool) INTER W,phi)
                                       ((g1:real->A->real^N^N) t) y =
                          metric_local atlas (U,phi) (g t) y` (LABEL_TAC "mlr") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["atlas1"; "g1"] THEN BETA_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `open(IMAGE (phi:A->real^N) (U INTER W))`) THEN
  REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^N) x`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho = e / &4` THEN
  SUBGOAL_THEN `&0 < rho /\ cball((phi:A->real^N) x,&2 * rho) SUBSET IMAGE phi (U INTER W) /\
                ball((phi:A->real^N) x,&2 * rho) SUBSET IMAGE phi (U INTER W) /\
                cball((phi:A->real^N) x,rho / &2) SUBSET IMAGE phi (U INTER W)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball((phi:A->real^N) x,e)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g1:real->A->real^N^N`; `&(dimindex(:N) - 1) * K`;
                 `((U:A->bool) INTER W,phi:A->real^N)`;
                 `cball((phi:A->real^N) x,&2 * rho)`] RFA_R1_CHART_BDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL; FST; SND] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bds"))) THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g1:real->A->real^N^N`; `&(dimindex(:N) - 1) * K`;
                 `((U:A->bool) INTER W,phi:A->real^N)`;
                 `cball((phi:A->real^N) x,&2 * rho)`] RFA_R1_CHART_FROM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL; FST; SND] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    DISCH_THEN(LABEL_TAC "jets")] THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g1:real->A->real^N^N`;
                 `((U:A->bool) INTER W,phi:A->real^N)`;
                 `cball((phi:A->real^N) x,&2 * rho)`] RFA_R1_CHART_RMD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[FST; SND]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `C0:real` o SPEC `0`) THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `a:real`; `b:real`;
                 `\t. metric_local atlas1 ((U:A->bool) INTER W,phi:A->real^N)
                                   ((g1:real->A->real^N^N) t)`;
                 `(phi:A->real^N) x`; `rho:real`] SNGL_LOCAL_LIMIT) THEN
  BETA_TAC THEN
  SUBGOAL_THEN `!t. a <= t /\ t < b
                    ==> metric_field (IMAGE (phi:A->real^N) (U INTER W))
                          (metric_local atlas1 ((U:A->bool) INTER W,phi)
                                        ((g1:real->A->real^N^N) t))` (LABEL_TAC "mf1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "rie1" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `((U:A->bool) INTER W,phi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `a:real`;
                     `b:real`; `g1:real->A->real^N^N`; `((U:A->bool) INTER W,phi:A->real^N)`]
                    LRG_RICCI_FLOW_ON_CHART) THEN
      REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ricci_flow_from (top1,atlas1) a b (g1:real->A->real^N^N)` THEN
      SIMP_TAC[ricci_flow_from];
      USE_THEN "mf1" ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `m:num` THEN USE_THEN "jets" (X_CHOOSE_TAC `Bc:real` o SPEC `m:num`) THEN
      EXISTS_TAC `Bc:real` THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Bc:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `L0 + &(dimindex(:N)) * &(dimindex(:N)) * L0 + &1` THEN
      SUBGOAL_THEN `&0 <= &(dimindex(:N)) * &(dimindex(:N)) * L0` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      USE_THEN "bds" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `&0 <= v dot (metric_local atlas1 ((U:A->bool) INTER W,phi:A->real^N)
                                   ((g1:real->A->real^N^N) t) y ** v)` ASSUME_TAC THENL
       [ASM_CASES_TAC `v:real^N = vec 0` THEN
        ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        USE_THEN "mf1" (MP_TAC o SPEC `t:real`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[metric_field] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2 o CONJUNCT2) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `(y:real^N) IN cball((phi:A->real^N) x,&2 * rho)` THEN
          UNDISCH_TAC `cball((phi:A->real^N) x,&2 * rho) SUBSET IMAGE phi (U INTER W)` THEN
          SET_TAC[];
          DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`metric_local atlas1 ((U:A->bool) INTER W,phi:A->real^N)
                                   ((g1:real->A->real^N^N) t) y`;
                     `mat 0:real^N^N`; `L0:real`; `v:real^N`] SNGL_QF_ENTRY_DIFF) THEN
      ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAT_COMPONENT; COND_ID; REAL_SUB_RZERO];
        REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO; DOT_RZERO; REAL_SUB_RZERO]] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (v:real^N) dot v` ASSUME_TAC THENL
       [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN DISCH_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `L0 * (v dot (metric_local atlas1 ((U:A->bool) INTER W,phi:A->real^N)
                                   ((g1:real->A->real^N^N) t) y ** v))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&(dimindex(:N)) * &(dimindex(:N)) * L0) * ((v:real^N) dot v)` THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `abs(v dot (metric_local atlas1 ((U:A->bool) INTER W,phi:A->real^N)
                                   ((g1:real->A->real^N^N) t) y ** v)) <=
                       &(dimindex(:N)) * &(dimindex(:N)) * L0 * ((v:real^N) dot v)` THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]];
      EXISTS_TAC `max C0 (&0)` THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
      REPEAT STRIP_TAC THEN DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Gl:real^N->real^N^N` (X_CHOOSE_THEN `c:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "rt") (LABEL_TAC "lk")))))) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`; `rho:real`; `Gl:real^N->real^N^N`;
                        `c:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "mlr" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^N) IN ball((phi:A->real^N) x,&2 * rho)` THEN
      UNDISCH_TAC `ball((phi:A->real^N) x,&2 * rho) SUBSET IMAGE phi (U INTER W)` THEN
      SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "rt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `e1:real`] THEN DISCH_TAC THEN
  USE_THEN "lk" (MP_TAC o SPECL [`m:num`; `e1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (b - a)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lck_dist2 m (Gl:real^N->real^N^N)
      (metric_local atlas (U,phi) ((g:real->A->real^N^N) t)) y =
    lck_dist2 m Gl (metric_local atlas1 ((U:A->bool) INTER W,phi) ((g1:real->A->real^N^N) t)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN cball((phi:A->real^N) x,rho / &2)` THEN
      UNDISCH_TAC `cball((phi:A->real^N) x,rho / &2) SUBSET IMAGE phi (U INTER W)` THEN
      SET_TAC[];
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "mlr" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The local limit at a point of Omega (MT p. 280, second paragraph). *)

let SNGL_LOCAL_AT = prove
 (`!(u:A->bool) (hs:(A)rfs_history) C eps r0 x.
     P2_THM_3_28_STATEMENT u /\ sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\
     x IN p3_omega hs
     ==> ?U phi rho Gl c t1.
           (U,phi) IN hs_atlas hs (hs_count hs) /\ x IN U /\ &0 < rho /\
           cball(phi x,&2 * rho) SUBSET IMAGE phi (U INTER p3_omega hs) /\
           metric_field (ball(phi x,rho)) Gl /\ &0 <= c /\ t1 < rfs_horizon hs /\
           (!t y p q. t1 < t /\ t < rfs_horizon hs /\ y IN ball(phi x,&2 * rho) /\
                      1 <= p /\ p <= dimindex(:3) /\ 1 <= q /\ q <= dimindex(:3)
                      ==> abs(metric_local (hs_atlas hs (hs_count hs)) (U,phi)
                                (hs_metric hs (hs_count hs) t) y$p$q - Gl y$p$q)
                          <= c * (rfs_horizon hs - t)) /\
           (!m e. &0 < e
                  ==> ?d. &0 < d /\
                          !t y. rfs_horizon hs - d < t /\ t < rfs_horizon hs /\
                                y IN cball(phi x,rho / &2)
                                ==> lck_dist2 m Gl
                                      (metric_local (hs_atlas hs (hs_count hs)) (U,phi)
                                         (hs_metric hs (hs_count hs) t)) y < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `x:A`]
                SNGL_OMEGA_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:A->bool` (X_CHOOSE_THEN `t0:real`
    (X_CHOOSE_THEN `Q:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`;
                 `B0:A->bool`; `t0:real`; `Q:real`; `x:A`] SNGL_SHI_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:A->bool` (X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(B0:A->bool) SUBSET p3_omega hs` ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_OMEGA_OF_BOUND THEN
    MAP_EVERY EXISTS_TAC [`t0:real`; `Q:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SNGL_LAST_STAGE o CONJUNCT1 o CONJUNCT2 o
              CONJUNCT2 o GEN_REWRITE_RULE I [sngl_hyp]) THEN
  MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                 `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                 `hs_metric hs (hs_count(hs:(A)rfs_history))`; `t1:real`;
                 `rfs_horizon(hs:(A)rfs_history)`; `B1:A->bool`; `x:A`]
                SNGL_FLOW_LOCAL_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RFF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`hs_time hs (hs_count(hs:(A)rfs_history))`;
                            `rfs_horizon(hs:(A)rfs_history)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `&2 * max Q (&6) + &2 * exp(&4)` THEN CONJ_TAC THENL
       [MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SNGL_RM_PINCH THEN
      MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `r0:real`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `open_in (hs_top hs (hs_count(hs:(A)rfs_history))) B1` THEN
        DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
        UNDISCH_TAC `(z:A) IN B1` THEN SET_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(z:A) IN B1` THEN UNDISCH_TAC `(B1:A->bool) SUBSET B0` THEN SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3`
    (X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `Gl:real^3->real^3^3`
    (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^3`; `rho:real`; `Gl:real^3->real^3^3`;
                        `c:real`; `t1:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER B1)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(B1:A->bool) SUBSET B0` THEN UNDISCH_TAC `(B0:A->bool) SUBSET p3_omega hs` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The limit metric gl = sngl_gl hs (entrywise limit at T of                 *)
(* the metric matrices in the preferred charts), its chart representations,  *)
(* and rfs_limit_metric (MT Lemma 11.21, C^infinity convergence on compact   *)
(* subsets of Omega).                                                        *)
(* ------------------------------------------------------------------------- *)

let sngl_gl = new_definition
 `sngl_gl (hs:(A)rfs_history) =
    \x:A. (lambda p q. @l. ((\t. hs_metric hs (hs_count hs) t x$p$q) ---> l)
                            (atreal (rfs_horizon hs) within {t | t < rfs_horizon hs})):real^3^3`;;

let SNGL_CONGR_ENTRY = prove
 (`!(J:real^N^N) (A:real^N^N) e p q.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> abs(A$i$j) <= e)
     ==> abs((transp J ** A ** J)$p$q) <=
         onorm(\x. transp J ** x) * (&(dimindex(:N)) * &(dimindex(:N)) * e) *
         onorm(\x. J ** x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `onorm(\x. (transp J ** A ** J:real^N^N) ** x)` THEN
  REWRITE_TAC[MATRIX_COMPONENT_LE_ONORM] THEN
  SUBGOAL_THEN `(\x. (transp J ** A ** J:real^N^N) ** x) =
                (\x. transp J ** x) o (\x. (A:real^N^N) ** x) o (\x. (J:real^N^N) ** x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIX_VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(\x. transp(J:real^N^N) ** x) /\ linear(\x. (A:real^N^N) ** x) /\
                linear(\x. (J:real^N^N) ** x)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `onorm(\x. transp(J:real^N^N) ** x) *
              onorm((\x. (A:real^N^N) ** x) o (\x. (J:real^N^N) ** x))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC ONORM_COMPOSE THEN ASM_SIMP_TAC[LINEAR_COMPOSE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[ONORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `onorm(\x. (A:real^N^N) ** x) * onorm(\x. (J:real^N^N) ** x)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC ONORM_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[ONORM_POS_LE] THEN
  MATCH_MP_TAC ONORM_LE_MATRIX_COMPONENT THEN ASM_REWRITE_TAC[]);;

(* A limit at T from the left given by an explicit rate, and the selected   *)
(* limit equals it.                                                          *)

let SNGL_LIMIT_SELECT = prove
 (`!(f:real->real) T0 L c t1.
     t1 < T0 /\ (!t. t1 < t /\ t < T0 ==> abs(f t - L) <= c * (T0 - t))
     ==> (f ---> L) (atreal T0 within {t | t < T0}) /\
         (@l. (f ---> l) (atreal T0 within {t | t < T0})) = L`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rate")) THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?x. t1 < x /\ x < T0 /\ abs(c) * (T0 - x) < e /\
                                   !d. &0 < d ==> ?y. t1 < y /\ y < T0 /\ T0 - y < d /\
                                                      abs(c) * (T0 - y) < e`
  (LABEL_TAC "pick") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!d. &0 < d ==> ?y. t1 < y /\ y < T0 /\ T0 - y < d /\ abs(c) * (T0 - y) < e`
    ASSUME_TAC THENL
     [X_GEN_TAC `d:real` THEN DISCH_TAC THEN
      EXISTS_TAC `T0 - min (min d (T0 - t1)) (e / (abs c + &1)) / &2` THEN
      SUBGOAL_THEN `&0 < min (min d (T0 - t1)) (e / (abs c + &1))` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `T0 - (T0 - h) = h`] THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC(REAL_ARITH `min (min d (T0 - t1)) (e / (abs c + &1)) <= T0 - t1`) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MP_TAC(REAL_ARITH `min (min d (T0 - t1)) (e / (abs c + &1)) <= d`) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ABBREV_TAC `h = min (min d (T0 - t1)) (e / (abs c + &1))` THEN
      SUBGOAL_THEN `h * (abs c + &1) <= e` MP_TAC THENL
       [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 < abs c + &1`] THEN
        EXPAND_TAC "h" THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= abs c * h` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f ---> L) (atreal T0 within {t | t < T0})` ASSUME_TAC THENL
   [REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `min (T0 - t1) (e / (abs c + &1))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `c * (T0 - y)` THEN CONJ_TAC THENL
     [USE_THEN "rate" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs c * (T0 - y)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs(y - T0) < e / (abs c + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs c + &1`] THEN
    SUBGOAL_THEN `&0 <= abs c * (T0 - y)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (INST_TYPE [`:real`,`:A`] SELECT_UNIQUE) THEN
  X_GEN_TAC `l:real` THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(l - L)) ==> l = L`) THEN DISCH_TAC THEN
  UNDISCH_TAC `(f ---> l) (atreal T0 within {t | t < T0})` THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `abs(l - L) / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "pick" (MP_TAC o SPEC `abs(l - L) / &2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `d:real`))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "rate" (MP_TAC o SPEC `y:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `c * (T0 - y) <= abs c * (T0 - y)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SNGL_CHART_CONGR = prove
 (`!top atlas (g:A->real^N^N) c x.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
     ==> metric_local atlas c g (SND c x) =
         transp(matrix(chart_jac c (chart_at atlas x) x)) ** g x **
         matrix(chart_jac c (chart_at atlas x) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[metric_local] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                CHART_INV) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* Entry bounds for a congruence of a difference. *)

let SNGL_CONGR_DIFF = prove
 (`!(J:real^N^N) (A:real^N^N) B e p q.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> abs(A$i$j - B$i$j) <= e)
     ==> abs((transp J ** A ** J)$p$q - (transp J ** B ** J)$p$q) <=
         onorm(\x. transp J ** x) * (&(dimindex(:N)) * &(dimindex(:N)) * e) *
         onorm(\x. J ** x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(transp J ** A ** J:real^N^N)$p$q - (transp J ** B ** J)$p$q =
                (transp J ** (A - B) ** J)$p$q` SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB] THEN
    SIMP_TAC[MATRIX_SUB_COMPONENT];
    ALL_TAC] THEN
  MATCH_MP_TAC SNGL_CONGR_ENTRY THEN ASM_SIMP_TAC[MATRIX_SUB_COMPONENT]);;

(* The preferred chart at x against another chart (U,phi) at x. *)

let SNGL_JAC_AT = prove
 (`!top atlas (h:A->real^N^N) U phi x.
     smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ x IN U
     ==> h x = transp(matrix(chart_jac (chart_at atlas x) (U,phi) x)) **
               metric_local atlas (U,phi) h (phi x) **
               matrix(chart_jac (chart_at atlas x) (U,phi) x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    UNDISCH_TAC `(x:A) IN U` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                PDE_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `U:A->bool`; `phi:A->real^N`; `h:A->real^N^N`; `x:A`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(GSYM METRIC_LOCAL_AT) THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

let SNGL_GL_ENTRY = prove
 (`!(hs:(A)rfs_history) x p q.
     1 <= p /\ p <= dimindex(:3) /\ 1 <= q /\ q <= dimindex(:3)
     ==> sngl_gl hs x$p$q =
         @l. ((\t. hs_metric hs (hs_count hs) t x$p$q) ---> l)
               (atreal (rfs_horizon hs) within {t | t < rfs_horizon hs})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sngl_gl] THEN ASM_SIMP_TAC[LAMBDA_BETA]);;

let SNGL_GL_PREF_RATE = prove
 (`!(u:A->bool) (hs:(A)rfs_history) C eps r0 x.
     P2_THM_3_28_STATEMENT u /\ sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\
     x IN p3_omega hs
     ==> ?c1 t1. t1 < rfs_horizon hs /\
                 !t p q. t1 < t /\ t < rfs_horizon hs /\
                         1 <= p /\ p <= dimindex(:3) /\ 1 <= q /\ q <= dimindex(:3)
                         ==> abs(hs_metric hs (hs_count hs) t x$p$q - sngl_gl hs x$p$q)
                             <= c1 * (rfs_horizon hs - t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `x:A`]
                SNGL_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3`
    (X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `Gl:real^3->real^3^3`
    (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `t1:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rt") ASSUME_TAC)))))))))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (hs_top hs (hs_count hs))
                  (hs_atlas hs (hs_count(hs:(A)rfs_history)))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN
    UNDISCH_TAC `sngl_hyp (hs:(A)rfs_history) C eps r0` THEN SIMP_TAC[sngl_hyp];
    ALL_TAC] THEN
  ABBREV_TAC `J = matrix(chart_jac (chart_at (hs_atlas hs (hs_count(hs:(A)rfs_history))) x)
                                   (U,phi) (x:A))` THEN
  ABBREV_TAC `k1 = onorm(\x. transp(J:real^3^3) ** x) *
                   (&(dimindex(:3)) * &(dimindex(:3)) * c) * onorm(\x. (J:real^3^3) ** x)` THEN
  SUBGOAL_THEN
   `!t p q. t1 < t /\ t < rfs_horizon(hs:(A)rfs_history) /\
            1 <= p /\ p <= dimindex(:3) /\ 1 <= q /\ q <= dimindex(:3)
            ==> abs(hs_metric hs (hs_count hs) t (x:A)$p$q -
                    (transp(J:real^3^3) ** (Gl:real^3->real^3^3) (phi x) ** J)$p$q)
                <= k1 * (rfs_horizon hs - t)`
  (LABEL_TAC "rx") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                   `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                   `hs_metric hs (hs_count(hs:(A)rfs_history)) t`;
                   `U:A->bool`; `phi:A->real^3`; `x:A`] SNGL_JAC_AT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`J:real^3^3`;
                   `metric_local (hs_atlas hs (hs_count(hs:(A)rfs_history))) (U,phi)
                      (hs_metric hs (hs_count hs) t) (phi(x:A))`;
                   `(Gl:real^3->real^3^3) (phi(x:A))`;
                   `c * (rfs_horizon(hs:(A)rfs_history) - t)`;
                   `p:num`; `q:num`] SNGL_CONGR_DIFF) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "rt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "k1" THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k1:real`; `t1:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `x:A`; `p:num`; `q:num`] SNGL_GL_ENTRY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`\t. hs_metric hs (hs_count(hs:(A)rfs_history)) t (x:A)$p$q`;
                 `rfs_horizon(hs:(A)rfs_history)`;
                 `(transp(J:real^3^3) ** (Gl:real^3->real^3^3) (phi(x:A)) ** J)$p$q`;
                 `k1:real`; `t1:real`] SNGL_LIMIT_SELECT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "rx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  USE_THEN "rx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* gl in every chart: the entrywise rate in any chart, the                   *)
(* local chart identification with the core's limit, metric fields in all   *)
(* charts over Omega, uniform lck convergence on compact subsets of Omega,  *)
(* hence rfs_limit_metric.                                                   *)
(* ------------------------------------------------------------------------- *)

(* A Riemannian metric is a metric field in a chart over any open subset. *)

let SNGL_RIEM_FIELD_ON = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c O.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
     open_in top O
     ==> metric_field (IMAGE (SND c) (FST c INTER O)) (metric_local atlas c g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `O:A->bool`] MFDR_RESTRICT_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR];
      SET_TAC[]]]);;

let SNGL_GL_CHART_RATE = prove
 (`!(u:A->bool) (hs:(A)rfs_history) C eps r0 x c.
     P2_THM_3_28_STATEMENT u /\ sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\
     x IN p3_omega hs /\ c IN hs_atlas hs (hs_count hs) /\ x IN FST c
     ==> ?k t1. t1 < rfs_horizon hs /\
                !t p q. t1 < t /\ t < rfs_horizon hs /\
                        1 <= p /\ p <= dimindex(:3) /\ 1 <= q /\ q <= dimindex(:3)
                        ==> abs(metric_local (hs_atlas hs (hs_count hs)) c
                                  (hs_metric hs (hs_count hs) t) (SND c x)$p$q -
                                metric_local (hs_atlas hs (hs_count hs)) c (sngl_gl hs)
                                  (SND c x)$p$q) <= k * (rfs_horizon hs - t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `x:A`]
                SNGL_GL_PREF_RATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `t1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pr")))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (hs_top hs (hs_count hs))
                  (hs_atlas hs (hs_count(hs:(A)rfs_history)))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN
    UNDISCH_TAC `sngl_hyp (hs:(A)rfs_history) C eps r0` THEN SIMP_TAC[sngl_hyp];
    ALL_TAC] THEN
  ABBREV_TAC `Jc = matrix(chart_jac (c:(A->bool)#(A->real^3))
                     (chart_at (hs_atlas hs (hs_count(hs:(A)rfs_history))) x) (x:A))` THEN
  MAP_EVERY EXISTS_TAC
   [`onorm(\x. transp(Jc:real^3^3) ** x) * (&(dimindex(:3)) * &(dimindex(:3)) * c1) *
     onorm(\x. (Jc:real^3^3) ** x)`; `t1:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                 `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                 `hs_metric hs (hs_count(hs:(A)rfs_history)) t`; `c:(A->bool)#(A->real^3)`;
                 `x:A`] SNGL_CHART_CONGR) THEN
  MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                 `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                 `sngl_gl(hs:(A)rfs_history)`; `c:(A->bool)#(A->real^3)`;
                 `x:A`] SNGL_CHART_CONGR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`Jc:real^3^3`; `hs_metric hs (hs_count(hs:(A)rfs_history)) t (x:A)`;
                 `sngl_gl (hs:(A)rfs_history) (x:A)`;
                 `c1 * (rfs_horizon(hs:(A)rfs_history) - t)`; `p:num`; `q:num`]
                SNGL_CONGR_DIFF) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "pr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC);;

(* In the local chart of SNGL_LOCAL_AT the core's limit is metric_local of gl. *)

let SNGL_GL_LOCAL = prove
 (`!(u:A->bool) (hs:(A)rfs_history) C eps r0 x.
     P2_THM_3_28_STATEMENT u /\ sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\
     x IN p3_omega hs
     ==> ?U phi rho.
           (U,phi) IN hs_atlas hs (hs_count hs) /\ x IN U /\ &0 < rho /\
           cball(phi x,&2 * rho) SUBSET IMAGE phi (U INTER p3_omega hs) /\
           metric_field (ball(phi x,rho))
             (metric_local (hs_atlas hs (hs_count hs)) (U,phi) (sngl_gl hs)) /\
           (!m e. &0 < e
                  ==> ?d. &0 < d /\
                          !t y. rfs_horizon hs - d < t /\ t < rfs_horizon hs /\
                                y IN cball(phi x,rho / &2)
                                ==> lck_dist2 m
                                      (metric_local (hs_atlas hs (hs_count hs)) (U,phi)
                                         (sngl_gl hs))
                                      (metric_local (hs_atlas hs (hs_count hs)) (U,phi)
                                         (hs_metric hs (hs_count hs) t)) y < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `x:A`]
                SNGL_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3`
    (X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `Gl:real^3->real^3^3`
    (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `t1:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rt") (LABEL_TAC "lk"))))))))))))))) THEN
  SUBGOAL_THEN
   `!y. y IN ball((phi:A->real^3) x,&2 * rho)
        ==> metric_local (hs_atlas hs (hs_count hs)) (U,phi) (sngl_gl hs) y =
            (Gl:real^3->real^3^3) y` (LABEL_TAC "eq") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?w:A. w IN U /\ w IN p3_omega (hs:(A)rfs_history) /\ (y:real^3) = (phi:A->real^3) w`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `cball((phi:A->real^3) x,&2 * rho) SUBSET IMAGE phi (U INTER p3_omega hs)` THEN
      UNDISCH_TAC `(y:real^3) IN ball((phi:A->real^3) x,&2 * rho)` THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER; IN_BALL; IN_CBALL] THEN
      MESON_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `w:A`;
                   `(U:A->bool,phi:A->real^3)`] SNGL_GL_CHART_RATE) THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` (X_CHOOSE_THEN `t2:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cr")))) THEN
    SIMP_TAC[CART_EQ] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &0 /\ --x <= &0 ==> x = &0`) THEN
    CONJ_TAC THEN
    (MATCH_MP_TAC SNGL_SMALL_LE THEN
     MAP_EVERY EXISTS_TAC [`k + c`; `max t1 t2`; `rfs_horizon(hs:(A)rfs_history)`] THEN
     CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     X_GEN_TAC `t:real` THEN STRIP_TAC THEN
     USE_THEN "cr" (MP_TAC o SPECL [`t:real`; `p:num`; `q:num`]) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     USE_THEN "rt" (MP_TAC o SPECL [`t:real`; `(phi:A->real^3) w`; `p:num`; `q:num`]) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[REAL_ADD_RDISTRIB] THEN REAL_ARITH_TAC);
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^3`; `rho:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN EXISTS_TAC `Gl:real^3->real^3^3` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "eq" MATCH_MP_TAC THEN UNDISCH_TAC `(y:real^3) IN ball((phi:A->real^3) x,rho)` THEN
    REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `e:real`] THEN DISCH_TAC THEN
  USE_THEN "lk" (MP_TAC o SPECL [`m:num`; `e:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk2"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lck_dist2 m (metric_local (hs_atlas hs (hs_count hs)) (U,phi) (sngl_gl hs))
       (metric_local (hs_atlas hs (hs_count hs)) (U,phi) (hs_metric hs (hs_count hs) t)) y =
    lck_dist2 m (Gl:real^3->real^3^3)
       (metric_local (hs_atlas hs (hs_count(hs:(A)rfs_history))) (U,phi:A->real^3)
          (hs_metric hs (hs_count hs) t)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `ball((phi:A->real^3) x,&2 * rho)` THEN REWRITE_TAC[OPEN_BALL] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN cball((phi:A->real^3) x,rho / &2)` THEN
      REWRITE_TAC[IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN USE_THEN "eq" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    USE_THEN "lk2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* gl is a metric field in every chart over Omega. *)

let SNGL_GL_FIELD = prove
 (`!(u:A->bool) (hs:(A)rfs_history) C eps r0 c.
     P2_THM_3_28_STATEMENT u /\ sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\
     c IN hs_atlas hs (hs_count hs)
     ==> metric_field (IMAGE (SND c) (FST c INTER p3_omega hs))
           (metric_local (hs_atlas hs (hs_count hs)) c (sngl_gl hs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (hs_top hs (hs_count hs))
                  (hs_atlas hs (hs_count(hs:(A)rfs_history)))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN
    UNDISCH_TAC `sngl_hyp (hs:(A)rfs_history) C eps r0` THEN SIMP_TAC[sngl_hyp];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top hs (hs_count hs)) (p3_omega(hs:(A)rfs_history))` ASSUME_TAC
  THENL [MATCH_MP_TAC SNGL_OMEGA_OPEN THEN
         MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `r0:real`] THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                   `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                   `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`;
                   `p3_omega(hs:(A)rfs_history)`] MFDR_RESTRICT_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `z:A`]
                SNGL_GL_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3`
    (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                 `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                 `c:(A->bool)#(A->real^3)`; `(U:A->bool,phi:A->real^3)`;
                 `ball((phi:A->real^3) z,rho)`; `SND(c:(A->bool)#(A->real^3)) z`]
                P2CA_CHART_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; FST; SND] THEN
    MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                   `hs_atlas hs (hs_count(hs:(A)rfs_history))`;
                   `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`]
                  CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(MP_TAC o SPEC `z:A` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Oo:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `mpullback (chart_trans (c:(A->bool)#(A->real^3)) (U,phi))
                (metric_local (hs_atlas hs (hs_count(hs:(A)rfs_history))) (U,phi)
                   (sngl_gl hs))` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
  EXISTS_TAC `IMAGE (chart_trans (c:(A->bool)#(A->real^3)) (U,phi:A->real^3)) Oo` THEN
  EXISTS_TAC `chart_trans (U:A->bool,phi:A->real^3) (c:(A->bool)#(A->real^3))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `ball((phi:A->real^3) z,rho)` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `diffeomorphism_on Oo
                 (IMAGE (chart_trans (c:(A->bool)#(A->real^3)) (U,phi:A->real^3)) Oo)
                 (chart_trans c (U,phi)) (chart_trans (U,phi) c)` THEN
  SIMP_TAC[diffeomorphism_on]);;

(* Uniform C^k convergence on compact subsets of Omega. *)

let SNGL_GL_LCK = prove
 (`!(u:A->bool) (hs:(A)rfs_history) C eps r0 K k e.
     P2_THM_3_28_STATEMENT u /\ sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\
     compact_in (hs_top hs (hs_count hs)) K /\ K SUBSET p3_omega hs /\ &0 < e
     ==> ?d. &0 < d /\
             !t x. rfs_horizon hs - d < t /\ t < rfs_horizon hs /\ x IN K
                   ==> lck_dist2 k
                         (metric_local (hs_atlas hs (hs_count hs))
                            (chart_at (hs_atlas hs (hs_count hs)) x) (sngl_gl hs))
                         (metric_local (hs_atlas hs (hs_count hs))
                            (chart_at (hs_atlas hs (hs_count hs)) x)
                            (hs_metric hs (hs_count hs) t))
                         (SND(chart_at (hs_atlas hs (hs_count hs)) x) x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SNGL_LAST_STAGE o CONJUNCT1 o CONJUNCT2 o
              CONJUNCT2 o GEN_REWRITE_RULE I [sngl_hyp]) THEN
  SUBGOAL_THEN `open_in (hs_top hs (hs_count hs)) (p3_omega(hs:(A)rfs_history))` ASSUME_TAC
  THENL [MATCH_MP_TAC SNGL_OMEGA_OPEN THEN
         MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `r0:real`] THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
  ABBREV_TAC `top = hs_top hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `atlas = hs_atlas hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `g = hs_metric hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Om = p3_omega(hs:(A)rfs_history)` THEN
  ABBREV_TAC `Th = rfs_horizon(hs:(A)rfs_history)` THEN
  ABBREV_TAC `Tn = hs_time hs (hs_count(hs:(A)rfs_history))` THEN
  MP_TAC(ISPECL [`top:A topology`; `K:A->bool`;
                 `\d (x:A). !t. Th - d < t /\ t < Th
                               ==> lck_dist2 k
                                     (metric_local atlas (chart_at atlas x) (sngl_gl hs))
                                     (metric_local atlas (chart_at atlas x)
                                        ((g:real->A->real^3^3) t))
                                     (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x) x)
                                   < e`] SNGL_COMPACT_UNIFORM) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN Om` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:A) IN K` THEN UNDISCH_TAC `(K:A->bool) SUBSET Om` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `z:A`]
                  SNGL_GL_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3`
      (X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk"))))))))) THEN
    USE_THEN "lk" (MP_TAC o SPECL [`k:num`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk0"))) THEN
    EXISTS_TAC `{w:A | w IN U /\ (phi:A->real^3) w IN ball(phi z,rho / &2)} INTER Om` THEN
    EXISTS_TAC `min d0 (Th - Tn)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `w:A` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `Oz = {w':A | w' IN U /\ (phi:A->real^3) w' IN ball(phi z,rho)} INTER Om` THEN
    SUBGOAL_THEN `open_in top (Oz:A->bool) /\ (w:A) IN Oz` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Oz" THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN
        EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[OPEN_BALL];
        REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(phi:A->real^3) w IN ball(phi z,rho / &2)` THEN
        REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (phi:A->real^3) (U INTER Oz) SUBSET ball(phi z,rho)` ASSUME_TAC THENL
     [EXPAND_TAC "Oz" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `w:A`] PDE_CHART_AT_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `open_in top (Oz:A->bool)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN UNDISCH_TAC `(w:A) IN Oz` THEN
      SET_TAC[];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `sngl_gl(hs:(A)rfs_history)`; `(g:real->A->real^3^3) t`;
                   `chart_at (atlas:((A->bool)#(A->real^3))->bool) (w:A)`;
                   `(U:A->bool,phi:A->real^3)`; `Oz:A->bool`; `w:A`; `k:num`]
                  P2CA_LCK_CHART_INDEP_C) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball((phi:A->real^3) z,rho)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `(g:real->A->real^3^3) t`; `(U:A->bool,phi:A->real^3)`; `Oz:A->bool`]
                      SNGL_RIEM_FIELD_ON) THEN
        ASM_REWRITE_TAC[FST; SND]];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[SND] THEN USE_THEN "lk0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(phi:A->real^3) w IN ball(phi z,rho / &2)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SNGL_LIMIT_METRIC = prove
 (`!(u:A->bool) (hs:(A)rfs_history) C eps r0.
     P2_THM_3_28_STATEMENT u /\ sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0
     ==> rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
           (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) (sngl_gl hs)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_limit_metric] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SNGL_GL_FIELD THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `C:real`; `eps:real`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SNGL_GL_LCK THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `C:real`; `eps:real`; `r0:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The scalar curvature of a limit metric is continuous on                  *)
(* Omega (local chart independence), the uniform backward bound and the     *)
(* forward containment give properness, the pinching gives the lower bound, *)
(* and the headline Lemma 11.21.                                             *)
(* ------------------------------------------------------------------------- *)

(* Chart independence of the scalar curvature when the metric is a metric   *)
(* field near the point in the second chart only.                           *)

let SNGL_LSCALAR_CHART_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c c' (g:A->real^N^N) B x.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
     x IN FST c /\ x IN FST c' /\ open B /\ SND c' x IN B /\
     metric_field B (metric_local atlas c' g)
     ==> lscalar (metric_local atlas c g) (SND c x) =
         lscalar (metric_local atlas c' g) (SND c' x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`; `B:real^N->bool`;
                 `SND(c:(A->bool)#(A->real^N)) x`] P2CA_CHART_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Oo:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `chart_trans (c:(A->bool)#(A->real^N)) c' (SND c x) = SND c' x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                   `x:A`] CHART_TRANS_AT) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lscalar (mpullback (chart_trans (c:(A->bool)#(A->real^N)) c')
                       (metric_local atlas c' (g:A->real^N^N))) (SND c x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `Oo:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [SYM(ASSUME `chart_trans (c:(A->bool)#(A->real^N)) c' (SND c x) = SND c' x`)] THEN
  MATCH_MP_TAC LSCALAR_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (chart_trans (c:(A->bool)#(A->real^N)) c') Oo`;
                        `Oo:real^N->bool`; `chart_trans (c':(A->bool)#(A->real^N)) c`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `B:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `diffeomorphism_on Oo (IMAGE (chart_trans (c:(A->bool)#(A->real^N)) c') Oo)
                 (chart_trans c c') (chart_trans c' c)` THEN
  SIMP_TAC[diffeomorphism_on]);;

(* The scalar curvature of a metric that is a metric field in every chart  *)
(* over an open set Om is continuous on Om.                                 *)

let SNGL_SCALAR_CONT_ON = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Om (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ open_in top Om /\
     (!c. c IN atlas
          ==> metric_field (IMAGE (SND c) (FST c INTER Om)) (metric_local atlas c g))
     ==> continuous_map (subtopology top Om,euclideanreal) (mfd_scalar atlas g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mf"))) THEN
  MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) (U INTER Om))
                  (metric_local atlas (U,phi) (g:A->real^N^N))` ASSUME_TAC THENL
   [USE_THEN "mf" (MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
    REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `U INTER Om:A->bool` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `Om INTER U INTER Om = U INTER (Om:A->bool)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `\z:A. lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) (phi z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[mfd_scalar] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `open (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                  (FST(chart_at atlas z) INTER Om))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`;
                     `Om:A->bool`] MFDR_RESTRICT_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) z IN
      IMAGE (SND(chart_at atlas z)) (FST(chart_at atlas z) INTER Om)` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                          (FST(chart_at atlas z) INTER Om))
                   (metric_local atlas (chart_at atlas z) (g:A->real^N^N))` ASSUME_TAC THENL
     [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:A->bool,phi:A->real^N)`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`;
                   `g:A->real^N^N`;
                   `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                          (FST(chart_at atlas z) INTER Om)`; `z:A`]
                  SNGL_LSCALAR_CHART_LOCAL) THEN
    REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:A. lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) (phi z)) =
    (\y. lscalar (metric_local atlas (U,phi) g) y) o (phi:A->real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) (U INTER Om))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN EXISTS_TAC `U:A->bool` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      UNDISCH_TAC `homeomorphic_map (subtopology top U,
                                     subtopology euclidean (IMAGE (phi:A->real^N) U)) phi` THEN
      DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN
  ASM_REWRITE_TAC[]);;

(* The uniform backward bound: points of Omega with R_gl <= c have          *)
(* R <= 2 (max 0 (c + 1) + r0^-2) at the fixed time T - dt/2 (Lemma 11.2    *)
(* backward from a time near T where R < c + 1).                            *)

let SNGL_BWD_UNIFORM = prove
 (`!(hs:(A)rfs_history) C eps r0 gl c dt y.
     sngl_hyp hs C eps r0 /\ sngl_bwd hs C r0 /\
     open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     &0 < dt /\ dt <= rfs_horizon hs - hs_time hs (hs_count hs) /\
     dt <= inv(&16 * max C (&2) * (max (&0) (c + &1) + inv(r0 pow 2))) /\
     y IN p3_omega hs /\ mfd_scalar (hs_atlas hs (hs_count hs)) gl y <= c
     ==> mfd_scalar (hs_atlas hs (hs_count hs))
           (hs_metric hs (hs_count hs) (rfs_horizon hs - dt / &2)) y
         <= &2 * (max (&0) (c + &1) + inv(r0 pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sngl_hyp] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))))) THEN
  ABBREV_TAC `top = hs_top hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `atlas = hs_atlas hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `g = hs_metric hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Tn = hs_time hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Th = rfs_horizon(hs:(A)rfs_history)` THEN
  ABBREV_TAC `Om = p3_omega(hs:(A)rfs_history)` THEN
  SUBGOAL_THEN `&0 <= Tn` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`] APX_HS_TIME_POS) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= n + 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `open_in top (Om:A->bool)` THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(y:A) IN Om` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Om:A->bool`;
                 `Th:real`; `g:real->A->real^3^3`; `gl:A->real^3^3`; `y:A`]
                P3E_LIMIT_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `Th - Tn:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sc"))) THEN
  ABBREV_TAC `ty = Th - min (d / &2) (dt / &4)` THEN
  SUBGOAL_THEN `Th - dt / &2 < ty /\ ty < Th /\ Th - d < ty` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ty" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->A->real^3^3) ty) y < c + &1` ASSUME_TAC THENL
   [USE_THEN "sc" (MP_TAC o SPEC `ty:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `mfd_scalar atlas (gl:A->real^3^3) y <= c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(r0 pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ty:real`] SNGL_LAST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) ty)` ASSUME_TAC THENL
   [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Ry = mfd_scalar atlas ((g:real->A->real^3^3) ty) y` THEN
  ABBREV_TAC `rr = inv(&2 * max C (&2) * sqrt(max Ry (inv(r0 pow 2))))` THEN
  SUBGOAL_THEN `&0 < rr` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ty - (Th - &3 * dt / &4) <= inv(&16 * max C (&2) * (max (&0) Ry + inv(r0 pow 2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&16 * max C (&2) * (max (&0) (c + &1) + inv(r0 pow 2)))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) ty (y:A) rr) (Th - &3 * dt / &4) ty`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_LAST_PERSISTS THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[rfs_vball; rfs_view] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `sngl_bwd (hs:(A)rfs_history) C r0` THEN REWRITE_TAC[sngl_bwd] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:A`; `ty:real`; `Th - &3 * dt / &4`; `rr:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Th - dt / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Th - dt / &2`] SNGL_LAST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `Ry < c + &1` THEN REAL_ARITH_TAC);;

(* Forward containment: a closed sublevel set of R at a time t0 close to T  *)
(* lies in Omega (Lemma 11.2 forward on the open sublevel set).             *)

let SNGL_FWD_SUBLEVEL = prove
 (`!(hs:(A)rfs_history) C eps r0 t0 D.
     sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\ &0 <= D /\
     hs_time hs (hs_count hs) <= t0 /\ t0 < rfs_horizon hs /\
     rfs_horizon hs - t0 <= inv(&16 * max C (&2) * ((D + &1) + inv(r0 pow 2)))
     ==> {z | z IN topspace(hs_top hs (hs_count hs)) /\
              mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) t0) z <= D}
         SUBSET p3_omega hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sngl_hyp] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))))) THEN
  ABBREV_TAC `top = hs_top hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `atlas = hs_atlas hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `g = hs_metric hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Tn = hs_time hs (hs_count(hs:(A)rfs_history))` THEN
  SUBGOAL_THEN `&0 <= t0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`] APX_HS_TIME_POS) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= n + 1`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(r0 pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_POW_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t0:real`] SNGL_LAST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t0)` ASSUME_TAC THENL
   [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `BB = {z | z IN topspace top /\ mfd_scalar atlas ((g:real->A->real^3^3) t0) z < D + &1}` THEN
  SUBGOAL_THEN `open_in top (BB:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "BB" THEN ASM_SIMP_TAC[SNGL_SCALAR_SUBLEVEL_OPEN]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `BB:A->bool` THEN CONJ_TAC THENL
   [EXPAND_TAC "BB" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SNGL_OMEGA_OF_BOUND THEN
  MAP_EVERY EXISTS_TAC [`t0:real`; `&2 * ((D + &1) + inv(r0 pow 2))`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->A->real^3^3) t0) z < D + &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN BB` THEN EXPAND_TAC "BB" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real = t0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] SNGL_LAST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_persists (rfs_view hs) (BB:A->bool) t0 s` ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_LAST_PERSISTS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `sngl_fwd (hs:(A)rfs_history) C r0` THEN REWRITE_TAC[sngl_fwd] THEN
  DISCH_THEN(MP_TAC o SPECL [`BB:A->bool`; `t0:real`; `s:real`; `D + &1`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    X_GEN_TAC `y:A` THEN EXPAND_TAC "BB" THEN SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `z:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Properness: every sublevel set of R_gl in Omega is compact in the stage. *)

let SNGL_OMEGA_PROPER = prove
 (`!(hs:(A)rfs_history) C eps r0 gl c.
     sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\ sngl_bwd hs C r0 /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl
     ==> compact_in (hs_top hs (hs_count hs))
           {x | x IN p3_omega hs /\ mfd_scalar (hs_atlas hs (hs_count hs)) gl x <= c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (hs_top hs (hs_count hs)) (p3_omega(hs:(A)rfs_history))` ASSUME_TAC
  THENL [MATCH_MP_TAC SNGL_OMEGA_OPEN THEN
         MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `r0:real`] THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sngl_hyp]) THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))))) THEN
  ABBREV_TAC `top = hs_top hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `atlas = hs_atlas hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `g = hs_metric hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Om = p3_omega(hs:(A)rfs_history)` THEN
  ABBREV_TAC `Th = rfs_horizon(hs:(A)rfs_history)` THEN
  ABBREV_TAC `Tn = hs_time hs (hs_count(hs:(A)rfs_history))` THEN
  SUBGOAL_THEN `&0 < inv(r0 pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]; ALL_TAC] THEN
  ABBREV_TAC `cc = &2 * (max (&0) (c + &1) + inv(r0 pow 2))` THEN
  SUBGOAL_THEN `&0 <= cc` ASSUME_TAC THENL [EXPAND_TAC "cc" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `dt = min (inv(&16 * max C (&2) * (max (&0) (c + &1) + inv(r0 pow 2))))
             (min (Th - Tn) (inv(&16 * max C (&2) * ((cc + &1) + inv(r0 pow 2)))))` THEN
  SUBGOAL_THEN `&0 < dt` ASSUME_TAC THENL
   [EXPAND_TAC "dt" THEN REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dt <= Th - Tn /\
    dt <= inv(&16 * max C (&2) * (max (&0) (c + &1) + inv(r0 pow 2))) /\
    dt <= inv(&16 * max C (&2) * ((cc + &1) + inv(r0 pow 2)))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dt" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the closed sublevel set at time T - dt/2 lies in Omega *)
  SUBGOAL_THEN
   `{z | z IN topspace top /\
         mfd_scalar atlas ((g:real->A->real^3^3) (Th - dt / &2)) z <= cc} SUBSET Om`
  (LABEL_TAC "kom") THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`;
                   `Th - dt / &2`; `cc:real`] SNGL_FWD_SUBLEVEL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the sublevel set of R_gl lies in it *)
  SUBGOAL_THEN
   `{x | x IN Om /\ mfd_scalar atlas (gl:A->real^3^3) x <= c} SUBSET
    {z | z IN topspace top /\
         mfd_scalar atlas ((g:real->A->real^3^3) (Th - dt / &2)) z <= cc}`
  (LABEL_TAC "sk") THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `open_in top (Om:A->bool)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      UNDISCH_TAC `(y:A) IN Om` THEN SET_TAC[];
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `gl:A->real^3^3`;
                     `c:real`; `dt:real`; `y:A`] SNGL_BWD_UNIFORM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* the sublevel set of R_gl is closed in Omega *)
  SUBGOAL_THEN `continuous_map (subtopology top Om,euclideanreal)
                  (mfd_scalar atlas (gl:A->real^3^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_SCALAR_CONT_ON THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_limit_metric (top,atlas) (Om:A->bool) Th (g:real->A->real^3^3) gl` THEN
    REWRITE_TAC[rfs_limit_metric] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (Om:A->bool)`; `mfd_scalar atlas (gl:A->real^3^3)`]
                CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `c:real` o CONJUNCT2) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; CLOSED_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "feq"))) THEN
  MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{x | x IN Om /\ mfd_scalar atlas (gl:A->real^3^3) x <= c} =
    F0 INTER {z | z IN topspace top /\
                  mfd_scalar atlas ((g:real->A->real^3^3) (Th - dt / &2)) z <= cc}`
  SUBST1_TAC THENL
   [REMOVE_THEN "feq" MP_TAC THEN REMOVE_THEN "kom" MP_TAC THEN REMOVE_THEN "sk" MP_TAC THEN
    UNDISCH_TAC `open_in top (Om:A->bool)` THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_INTER THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `mfd_scalar atlas ((g:real->A->real^3^3) (Th - dt / &2))`]
                CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LE) THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal)
                  (mfd_scalar atlas ((g:real->A->real^3^3) (Th - dt / &2)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(ACCEPT_TAC o SPEC `cc:real` o CONJUNCT2));;

(* The pinching bound -6/(4t+1) moves by at most 24 per unit time.         *)

let SNGL_PINCH_BOUND_LIP = prove
 (`!s t. &0 <= s /\ s <= t
         ==> --(&6) / (&4 * t + &1) - &24 * (t - s) <= --(&6) / (&4 * s + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&24 * (t - s) = &6 * ((&4 * t + &1) - (&4 * s + &1))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &4 * s + &1 /\ &4 * s + &1 <= &4 * t + &1` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`&4 * s + &1`,`a:real`) THEN SPEC_TAC(`&4 * t + &1`,`b:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a /\ &0 < b /\ &1 <= a * b` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= a * b ==> &1 <= a * b`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
  SUBGOAL_THEN
   `--(&6) / a - (--(&6) / b - &6 * (b - a)) = (&6 * (b - a) * (a * b - &1)) / (a * b)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD
     `~(a = &0) /\ ~(b = &0)
      ==> --(&6) / a - (--(&6) / b - &6 * (b - a)) =
          (&6 * (b - a) * (a * b - &1)) / (a * b)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

(* The lower bound of R_gl on Omega from the pinching.                      *)

let SNGL_LOWER_BOUND = prove
 (`!(hs:(A)rfs_history) gl x.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     x IN p3_omega hs
     ==> --(&6) / (&4 * rfs_horizon hs + &1) <=
         mfd_scalar (hs_atlas hs (hs_count hs)) gl x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))))) THEN
  ABBREV_TAC `top = hs_top hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `atlas = hs_atlas hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `g = hs_metric hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Tn = hs_time hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Th = rfs_horizon(hs:(A)rfs_history)` THEN
  ABBREV_TAC `Om = p3_omega(hs:(A)rfs_history)` THEN
  SUBGOAL_THEN `&0 <= Tn` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`] APX_HS_TIME_POS) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= n + 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `open_in top (Om:A->bool)` THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(x:A) IN Om` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Om:A->bool`;
                 `Th:real`; `g:real->A->real^3^3`; `gl:A->real^3^3`; `x:A`]
                P3E_LIMIT_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `Th - Tn:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "sc") THEN
  MATCH_MP_TAC(REAL_ARITH `~(b < a) ==> a <= b`) THEN DISCH_TAC THEN
  ABBREV_TAC `e = (--(&6) / (&4 * Th + &1) - mfd_scalar atlas (gl:A->real^3^3) x) / &2` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "sc" (MP_TAC o SPEC `e:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sd"))) THEN
  ABBREV_TAC `t = Th - min (d / &2) (min (e / &48) ((Th - Tn) / &2))` THEN
  SUBGOAL_THEN `Th - d < t /\ t < Th /\ Tn < t /\ Th - t <= e / &48` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "sd" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `--(&6) / (&4 * t + &1) <= mfd_scalar atlas ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
    REWRITE_TAC[rfs_view; rfs_pinched] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`]) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] SNGL_LAST_VIEW) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[rfs_pinched_at] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&6) / (&4 * Th + &1) - &24 * (Th - t) <= --(&6) / (&4 * t + &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_PINCH_BOUND_LIP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Headline: Lemma 11.21 from the route hypotheses.                          *)
(* ------------------------------------------------------------------------- *)

let P2C_LEMMA_11_21_ROUTE = prove
 (`!u:A->bool. P2C_LEMMA_11_21_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_LEMMA_11_21_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `P2C_LEMMA_11_2_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_LEMMA_11_2_FROM_DB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `u:A->bool` SNGL_FWD_FROM) THEN
  ANTS_TAC THENL [MATCH_MP_TAC SNGL_P2_L112 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fw"))) THEN
  MP_TAC(ISPEC `u:A->bool` SNGL_BWD_FROM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bw"))) THEN
  REWRITE_TAC[P2C_LEMMA_11_21_STATEMENT] THEN EXISTS_TAC `min e1 e2` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `sngl_hyp (hs:(A)rfs_history) C eps r0` ASSUME_TAC THENL
   [REWRITE_TAC[sngl_hyp] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sngl_fwd (hs:(A)rfs_history) C r0` ASSUME_TAC THENL
   [USE_THEN "fw" MATCH_MP_TAC THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sngl_bwd (hs:(A)rfs_history) C r0` ASSUME_TAC THENL
   [USE_THEN "bw" MATCH_MP_TAC THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top hs (hs_count hs)) (p3_omega(hs:(A)rfs_history))` ASSUME_TAC
  THENL [MATCH_MP_TAC SNGL_OMEGA_OPEN THEN
         MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `r0:real`] THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
      (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs))
      (sngl_gl (hs:(A)rfs_history))` ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_LIMIT_METRIC THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `C:real`; `eps:real`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `sngl_gl (hs:(A)rfs_history)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SNGL_OMEGA_PROPER THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `r0:real`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SNGL_LOWER_BOUND THEN ASM_REWRITE_TAC[]]);;

