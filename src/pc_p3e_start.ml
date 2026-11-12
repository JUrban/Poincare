(* ========================================================================= *)
(* Unit pc_p3e_start: MT Claim 15.1 (the start of the construction, proof of *)
(* Cor 15.10) in route form: the curvature-time estimate PDE_CURVATURE_TIME, *)
(* the volume part of MT Prop 4.11 and MT Thm 4.32 on A + num#num#real^3     *)
(* give P3_START_STATEMENT (with b0 = min(c / T_1, 1 / C)).  The manifold is *)
(* moved from A to the history carrier by INL (unit pc_mfd_transport); the   *)
(* history has no event and horizon T_1; the canonical neighbourhood         *)
(* assumption is void (R < eps^-2) and noncollapsing is the volume bound of  *)
(* Prop 4.11.                                                                *)
(* ========================================================================= *)

needs "src/pc_mfd_transport.ml";;
needs "src/pc_p3_route.ml";;
needs "src/pc_p3_assembly.ml";;
needs "src/pc_rfa_pinch.ml";;
needs "src/pc_rf_unique_a14.ml";;
needs "src/pc_rfa_doubling.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Pointwise curvature facts (the least sectional curvature is               *)
(* at least minus the curvature norm; abs Rm <= 1 gives the pinching        *)
(* condition at time 0), step functions below their first value, and       *)
(* components of a simply connected space.                                   *)
(* ------------------------------------------------------------------------- *)

let P3E_SECMIN_GE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x.
     2 <= dimindex(:N) /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top
     ==> --(mfd_rm_norm atlas g x) <= mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sec_min] THEN MATCH_MP_TAC REAL_LE_INF THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`mfd_sectional (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x
                     (basis 1) (basis 2)`;
      `basis 1:real^N`; `basis 2:real^N`] THEN
    ASM_SIMP_TAC[RFA_NONCOLLINEAR_BASIS];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `abs s <= m ==> --m <= s`) THEN
    MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_NORM THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]]);;

let P3E_PINCHED_AT_0 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ mfd_rm_norm atlas g x <= &1
     ==> rfs_pinched_at atlas g (&0) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pinched_at] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] RFA_SCALAR_GE_6SECMIN) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] P3E_SECMIN_GE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  ABBREV_TAC `m = mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) g x` THEN
  ABBREV_TAC `R = mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) g x` THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID; LOG_1; REAL_DIV_1] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `log(--m) <= &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM LOG_1] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= --m * --log(--m)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= --m * --log(--m)` THEN REWRITE_TAC[REAL_MUL_RNEG] THEN
  ASM_REAL_ARITH_TAC);;

let P3E_STEPF_LE0 = prove
 (`!s t. p3_seq_ok s /\ &0 <= t ==> p3_stepf s t <= s 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3_stepf s (&0) = s 0` (fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THENL
   [REWRITE_TAC[p3_stepf] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `n <= 0 ==> n = 0`) THEN MATCH_MP_TAC P3_STEP_LE THEN
    REWRITE_TAC[P3_T_POS];
    MATCH_MP_TAC P3_STEPF_MONO THEN ASM_REWRITE_TAC[]]);;

let P3E_COMPONENTS_SC = prove
 (`!top:A topology. simply_connected_space top ==> rfs_components_sc top`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_components_sc] THEN
  SUBGOAL_THEN `connected_space (top:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLY_CONNECTED_SPACE_IMP_PATH_CONNECTED_SPACE;
                  PATH_CONNECTED_IMP_CONNECTED_SPACE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; IN_SING] THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]);;

(* ------------------------------------------------------------------------- *)
(* The history with no event, one stage (top,atlas) and the                  *)
(* flow G on [0,tz): its fields, its space-time view, rfs_history_ok, and    *)
(* the invariant p3_inv from pinching, a scalar curvature bound below the  *)
(* canonical neighbourhood threshold and a volume lower bound on balls      *)
(* (also the canonv assumption and p3_noncoll_all, the same way).           *)
(* ------------------------------------------------------------------------- *)

let P3E_HIST0_VIEW = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (G:real->B->real^3^3)
    (ev:num->(B)rfs_event) tz hs.
     hs = RfsHistory 0 (\k. if k = 0 then &0 else tz) (\k. top) (\k. atlas) (\k. G) ev
     ==> hs_count hs = 0 /\ hs_time hs 0 = &0 /\ hs_time hs 1 = tz /\
         (!k. hs_top hs k = top) /\ (!k. hs_atlas hs k = atlas) /\
         (!k. hs_metric hs k = G) /\ rfs_horizon hs = tz /\
         (!t. rfs_top_at hs t = if &0 <= t /\ t < tz then top else discrete_topology {}) /\
         (!t. rfs_atlas_at hs t = if &0 <= t /\ t < tz then atlas else {}) /\
         (!t. rfs_metric_at hs t = if &0 <= t /\ t < tz then G t else (\x. mat 1))`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[hs_count; hs_time; hs_top; hs_atlas; hs_metric; rfs_horizon;
              rfs_top_at; rfs_atlas_at; rfs_metric_at; rfs_live] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let P3E_HIST0_OK = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (G:real->B->real^3^3)
    (ev:num->(B)rfs_event) tz.
     &0 < tz /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     compact_space top /\ ricci_flow_from (top,atlas) (&0) tz G
     ==> rfs_history_ok
           (RfsHistory 0 (\k. if k = 0 then &0 else tz) (\k. top) (\k. atlas) (\k. G) ev)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_history_ok; hs_count; hs_time; hs_top; hs_atlas; hs_metric; hs_event] THEN
  REWRITE_TAC[LE; ARITH_RULE `~(1 <= k /\ k = 0)`; FORALL_UNWIND_THM2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let P3E_HIST0_INV = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (G:real->B->real^3^3)
    (ev:num->(B)rfs_event) tz b C eps hf md g0 A0 rs ks dd.
     &0 < tz /\ tz <= b /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     simply_connected_space top /\ mfd_orientable top atlas /\
     ricci_flow_from (top,atlas) (&0) b G /\ rfs_normalized (top,atlas) (G (&0)) /\
     p3_seq_ok rs /\ p3_seq_ok ks /\ p3_seq_ok dd /\ rs 0 = eps /\
     (!t x. &0 <= t /\ t < tz /\ x IN topspace top ==> rfs_pinched_at atlas (G t) t x) /\
     (!t x. &0 <= t /\ t < tz /\ x IN topspace top
            ==> mfd_scalar atlas (G t) x < inv(eps pow 2)) /\
     (!t x r. &0 <= t /\ t < tz /\ x IN topspace top /\ &0 < r /\ r <= eps
              ==> ?v. mfd_has_volume (top,atlas) (G t) (mfd_ball (top,atlas) (G t) x r) v /\
                      ks 0 * r pow 3 <= v)
     ==> p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd)
                (RfsHistory 0 (\k. if k = 0 then &0 else tz) (\k. top) (\k. atlas) (\k. G) ev)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `hs = RfsHistory 0 (\k. if k = 0 then &0 else tz) (\k:num. top)
                     (\k:num. atlas) (\k:num. G) (ev:num->(B)rfs_event)` THEN
  SUBGOAL_THEN `ricci_flow_from (top:B topology,atlas) (&0) tz (G:real->B->real^3^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(B)rfs_history)` ASSUME_TAC THENL
   [EXPAND_TAC "hs" THEN MATCH_MP_TAC P3E_HIST0_OK THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `G:real->B->real^3^3`; `ev:num->(B)rfs_event`; `tz:real`;
                 `hs:(B)rfs_history`] P3E_HIST0_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3_inv; p3_struct] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfs_view; rfs_pinched; rfs_canonical_assumption; rfs_noncollapsed;
              rfs_vball] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `~(1 <= k /\ k <= 0)`; LT] THEN
  ASM_SIMP_TAC[P3E_COMPONENTS_SC; P3_STEPF_POS; P3_STEPF_MONO] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN
    ASM_CASES_TAC `&0 <= t /\ t < tz` THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN
    ASM_CASES_TAC `&0 <= t /\ t < tz` THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < p3_stepf rs t /\ p3_stepf rs t <= eps` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[P3_STEPF_POS] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(rs:num->real) 0 = eps`)) THEN
      MATCH_MP_TAC P3E_STEPF_LE0 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(eps pow 2) <= inv(p3_stepf rs t pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas ((G:real->B->real^3^3) t) x < inv(eps pow 2)`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `r:real`] THEN
    ASM_CASES_TAC `&0 <= t /\ t < tz` THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:B`; `r:real`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> is_const tm && fst(dest_const tm) = "mfd_has_volume"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(ks:num->real) 0 * r pow 3` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE; P3E_STEPF_LE0];
    (* The canonical assumption with the volume clause, vacuous              *)
    (* as above (R < eps^-2 <= rp^-2 on [0,tz)).                            *)
    REWRITE_TAC[p3_canonv_assumption; rfs_vtop; rfs_vscalar] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN
    ASM_CASES_TAC `&0 <= t /\ t < tz` THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < p3_stepf rs t /\ p3_stepf rs t <= eps` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[P3_STEPF_POS] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(rs:num->real) 0 = eps`)) THEN
      MATCH_MP_TAC P3E_STEPF_LE0 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(eps pow 2) <= inv(p3_stepf rs t pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas ((G:real->B->real^3^3) t) x < inv(eps pow 2)`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    (* Noncollapsing without the positive-curvature exemption: the           *)
    (* volume bound of the hypothesis holds at every point.                  *)
    REWRITE_TAC[p3_noncoll_all; p3_noncoll_at; rfs_vtop; rfs_vatlas; rfs_vmetric;
                rfs_vball] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN
    ASM_CASES_TAC `&0 <= t /\ t < tz` THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:B`; `r:real`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> is_const tm && fst(dest_const tm) = "mfd_has_volume"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(ks:num->real) 0 * r pow 3` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE; P3E_STEPF_LE0]]);;

(* The zero-event history on INL points has the extra invariant.            *)

let P3E_EXTRA_HIST0 = prove
 (`!(top:(A+num#num#real^3)topology) (atlas:((A+num#num#real^3->bool)#
                                              (A+num#num#real^3->real^3))->bool)
    (G:real->A+num#num#real^3->real^3^3) (ev:num->(A+num#num#real^3)rfs_event) tz dl.
     topspace top SUBSET IMAGE INL (:A)
     ==> p3_extra dl
           (RfsHistory 0 (\k. if k = 0 then &0 else tz) (\k. top) (\k. atlas) (\k. G) ev)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_extra; hs_count; hs_top] THEN
  REWRITE_TAC[ARITH_RULE `~(1 <= k /\ k <= 0)`] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 15.1 in route form.  Constants: c, CC from                       *)
(* PDE_CURVATURE_TIME, T1 = p3_T 1, b0 = min(c / T1, 1 / CC) (so the flow    *)
(* exists past T1 with abs Rm <= CC b0 <= 1 on [0,T1]), kappa0 from Prop     *)
(* 4.11 at K = 1, tau = T1, eps2 = 1 / (CR + 1) with CR the constant of     *)
(* RFU_SCALAR_FROM_RMNORM (abs R <= CR when abs Rm <= 1).                  *)
(* ------------------------------------------------------------------------- *)

let P3E_START_ROUTE = prove
 (`!(u:A->bool). P3_START_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_START_ROUTE_STATEMENT; P3_START_STATEMENT] THEN
  REWRITE_TAC[PDE_CURVATURE_TIME_STATEMENT; P2_PROP_4_11_VOLUME_STATEMENT;
              P2_THM_4_32_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `CC:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pde")))))
    (CONJUNCTS_THEN2 (LABEL_TAC "vol") (LABEL_TAC "pinch"))) THEN
  ABBREV_TAC `T1 = p3_T 1` THEN
  SUBGOAL_THEN `&0 < T1` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN REWRITE_TAC[P3_T_POS]; ALL_TAC] THEN
  ABBREV_TAC `b0 = min (c / T1) (inv CC)` THEN
  SUBGOAL_THEN `&0 < b0 /\ b0 <= c / T1 /\ b0 <= inv CC` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b0" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `T1 <= c / b0 /\ CC * b0 <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC `b0 <= c / T1` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CC * inv CC` THEN
      ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                   REAL_LE_REFL]];
    ALL_TAC] THEN
  REMOVE_THEN "vol" (MP_TAC o SPECL [`&1`; `T1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vol"))) THEN
  X_CHOOSE_THEN `CR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "scal"))
    (INST_TYPE [`:3`,`:N`; `:A+num#num#real^3`,`:A`] RFU_SCALAR_FROM_RMNORM) THEN
  MAP_EVERY EXISTS_TAC [`kappa0:real`; `inv(CR + &1)`; `b0:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`; `rs:num->real`;
                       `ks:num->real`; `dd:num->real`] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`] THEN
  STRIP_TAC THEN
  (* transport to the history carrier *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `INL:A->A+num#num#real^3`; `OUTL:A+num#num#real^3->A`] MTR_MANIFOLD) THEN
  ASM_REWRITE_TAC[OUTL] THEN
  DISCH_THEN(X_CHOOSE_THEN `top':(A+num#num#real^3)topology`
    (X_CHOOSE_THEN `atlas':((A+num#num#real^3->bool)#(A+num#num#real^3->real^3))->bool`
      STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `topspace (top':(A+num#num#real^3)topology) = IMAGE INL (topspace top)`)) THEN
  SUBGOAL_THEN `hausdorff_space (top':(A+num#num#real^3)topology) /\ compact_space top' /\
                simply_connected_space top' /\
                mfd_orientable top'
                  (atlas':((A+num#num#real^3->bool)#(A+num#num#real^3->real^3))->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `g' = mfd_pullback_metric atlas' (atlas:((A->bool)#(A->real^3))->bool)
                     (OUTL:A+num#num#real^3->A) g` THEN
  SUBGOAL_THEN `!y. y IN topspace top' ==> mfd_rm_norm atlas' (g':A+num#num#real^3->real^3^3) y <= b0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A+num#num#real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x:A. x IN topspace top /\ (y:A+num#num#real^3) = INL x` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `top':(A+num#num#real^3)topology`;
                   `atlas':((A+num#num#real^3->bool)#(A+num#num#real^3->real^3))->bool`;
                   `g':A+num#num#real^3->real^3^3`;
                   `INL:A->A+num#num#real^3`; `OUTL:A+num#num#real^3->A`; `x:A`]
      MTR_ISOMETRY_RM_NORM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the flow on [0,b) *)
  REMOVE_THEN "pde" (MP_TAC o SPECL [`top':(A+num#num#real^3)topology`;
     `atlas':((A+num#num#real^3->bool)#(A+num#num#real^3->real^3))->bool`;
     `g':A+num#num#real^3->real^3^3`; `&0`; `b0:real`]) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH; REAL_ADD_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` (X_CHOOSE_THEN `G:real->A+num#num#real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `T1 < b /\ &0 < b` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < b ==> riemannian_metric atlas'
                     ((G:real->A+num#num#real^3->real^3^3) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `ricci_flow_from (top',atlas') (&0) b (G:real->A+num#num#real^3->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN
    ASM_CASES_TAC `s = &0` THENL
     [ASM_SIMP_TAC[];
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((G:real->A+num#num#real^3->real^3^3) (&0))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t x. &0 <= t /\ t <= T1 /\ x IN topspace top'
                      ==> mfd_rm_norm atlas' ((G:real->A+num#num#real^3->real^3^3) t) x <= &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CC * b0` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_isometry (top,atlas) (g:A->real^3^3) (top',atlas')
                  ((G:real->A+num#num#real^3->real^3^3) (&0)) INL OUTL`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MTR_ISOMETRY_CONG THEN
    EXISTS_TAC `g':A+num#num#real^3->real^3^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_normalized (top',atlas') ((G:real->A+num#num#real^3->real^3^3) (&0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MTR_ISOMETRY_NORMALIZED THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `INL:A->A+num#num#real^3`;
                          `OUTL:A+num#num#real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the history *)
  EXISTS_TAC `RfsHistory 0 (\k. if k = 0 then &0 else T1) (\k:num. top')
                (\k:num. atlas') (\k:num. G:real->A+num#num#real^3->real^3^3)
                (\k:num. ARB:(A+num#num#real^3)rfs_event)` THEN
  MAP_EVERY EXISTS_TAC [`INL:A->A+num#num#real^3`; `OUTL:A+num#num#real^3->A`] THEN
  MP_TAC(ISPECL [`top':(A+num#num#real^3)topology`;
                 `atlas':((A+num#num#real^3->bool)#(A+num#num#real^3->real^3))->bool`;
                 `G:real->A+num#num#real^3->real^3^3`;
                 `\k:num. ARB:(A+num#num#real^3)rfs_event`; `T1:real`;
                 `RfsHistory 0 (\k. if k = 0 then &0 else T1) (\k:num. top')
                    (\k:num. atlas') (\k:num. G:real->A+num#num#real^3->real^3^3)
                    (\k:num. ARB:(A+num#num#real^3)rfs_event)`] P3E_HIST0_VIEW) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[rfs_initial] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC P3E_EXTRA_HIST0 THEN
    UNDISCH_TAC `IMAGE INL (topspace top) = topspace (top':(A+num#num#real^3)topology)` THEN
    SET_TAC[]] THEN
  SUBGOAL_THEN `T1 <= b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P3E_HIST0_INV THEN EXISTS_TAC `b:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* pinching *)
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "pinch" (MP_TAC o SPECL [`top':(A+num#num#real^3)topology`;
       `atlas':((A+num#num#real^3->bool)#(A+num#num#real^3->real^3))->bool`;
       `&0`; `b:real`; `G:real->A+num#num#real^3->real^3^3`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
     [X_GEN_TAC `y:A+num#num#real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC P3E_PINCHED_AT_0 THEN EXISTS_TAC `top':(A+num#num#real^3)topology` THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    (* scalar curvature below the threshold *)
    REPEAT STRIP_TAC THEN
    USE_THEN "scal" (MP_TAC o SPECL [`top':(A+num#num#real^3)topology`;
       `atlas':((A+num#num#real^3->bool)#(A+num#num#real^3->real^3))->bool`;
       `(G:real->A+num#num#real^3->real^3^3) t`; `x:A+num#num#real^3`; `&1`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `CR < inv(eps pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(inv(CR + &1) pow 2)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_INV; REAL_INV_INV] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `CR + &1` THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      REAL_ARITH_TAC];
    (* volume lower bound *)
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "vol" (MP_TAC o SPECL [`top':(A+num#num#real^3)topology`;
       `atlas':((A+num#num#real^3->bool)#(A+num#num#real^3->real^3))->bool`;
       `b:real`; `G:real->A+num#num#real^3->real^3^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(CR + &1)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC]);;

