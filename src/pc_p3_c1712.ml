(* ========================================================================= *)
(* Unit pc_p3_c1712: MT Lemma 17.12 (surgery times do not accumulate) for   *)
(* histories whose cut necks have discarded, pairwise disjoint positive     *)
(* halves (P1, P2: p3h_plus_disc below; p3_extra contains them).            *)
(* Proof (MT p. 410, repaired): every event lowers the volume by at least   *)
(* hmin^3 per cut neck (n0 dyadic boxes of each discarded positive half     *)
(* against a cap of volume <= 2 h^3 Vol_g0), the volume grows at most like  *)
(* exp(6 t) on slabs (pinching), so the number of cut necks is bounded;    *)
(* every event discards a component of the cut manifold (plus caps, or     *)
(* slab maximality when no neck is cut), so the number of events is at     *)
(* most the number of initial components plus twice the number of necks.  *)
(*                                                                         *)
(* Definitions, arithmetic, slab volume growth.                            *)
(* ========================================================================= *)

needs "src/pc_p3_core.ml";;
needs "src/pc_p3_iface.ml";;
needs "src/pc_p3_c17curv.ml";;
needs "src/pc_p3_c17vol.ml";;

prioritize_real();;
type_invention_error := true;;

(* P1 and P2: at every event the positive halves of the cut necks are       *)
(* discarded and pairwise disjoint.                                         *)

let p3h_plus_disc = new_definition
 `p3h_plus_disc (dl:real->real) (hs:(A)rfs_history) <=>
    !k. 1 <= k /\ k <= hs_count hs
        ==> (!i. i IN ev_index(hs_event hs k)
                 ==> DISJOINT (IMAGE (ev_neck(hs_event hs k) i)
                                     {y | y IN rfs_neck_dom (dl(hs_time hs k)) /\ &1 < norm y})
                              (topspace(hs_top hs k))) /\
            (!i j. i IN ev_index(hs_event hs k) /\ j IN ev_index(hs_event hs k) /\ ~(i = j)
                   ==> DISJOINT (IMAGE (ev_neck(hs_event hs k) i)
                                       {y | y IN rfs_neck_dom (dl(hs_time hs k)) /\ &1 < norm y})
                                (IMAGE (ev_neck(hs_event hs k) j)
                                       {y | y IN rfs_neck_dom (dl(hs_time hs k)) /\ &1 < norm y}))`;;

(* The volume of stage k at the start of its slab. *)

let p3h_stage_vol = new_definition
 `p3h_stage_vol (hs:(A)rfs_history) (k:num) =
    mfd_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k (hs_time hs k))
               (topspace(hs_top hs k))`;;

let P3H_LE_EPS_LIMIT = prove
 (`!x y. &0 <= y /\ (!e. &0 < e ==> x <= (&1 + e) * y) ==> x <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x - y) / (&2 * (y + &1))`) THEN
  SUBGOAL_THEN `&0 < &2 * (y + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT] THEN
  SUBGOAL_THEN `(x - y) * y <= (x - y) * (y + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x - y) / (&2 * (y + &1)) * y <= (x - y) / &2` MP_TAC THENL
   [SUBGOAL_THEN `(x - y) / (&2 * (y + &1)) * y = ((x - y) * y) / (&2 * (y + &1)) /\
                  (x - y) / &2 = ((x - y) * (y + &1)) / (&2 * (y + &1))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [UNDISCH_TAC `&0 < &2 * (y + &1)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ASM_REAL_ARITH_TAC]);;

let P3H_EXP_POW2 = prove
 (`!n x. &n <= x ==> &2 pow n <= exp x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&n)` THEN
  ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MP_TAC(SPECL [`n:num`; `&1`] REAL_EXP_N) THEN REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

let P3H_DL_BOXES = prove
 (`!n0 dl. 1 <= n0 /\ &0 < dl /\ dl <= inv(&2 * &n0)
           ==> &2 pow n0 <= exp(inv(sqrt(&2) * dl))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_EXP_POW2 THEN
  SUBGOAL_THEN `&1 <= &n0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) <= &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 = sqrt(&2 pow 2)` (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * dl <= inv(&n0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * dl` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `dl <= inv(&2 * &n0)` THEN
    SUBGOAL_THEN `inv(&2 * &n0) = inv(&n0) / &2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&n0 = inv(inv(&n0))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]);;

let P3H_BOX_CAP_ARITH = prove
 (`!h n0 cv. &0 < h /\ &0 <= cv /\ &141 * (&1 + &2 * cv) <= &n0
             ==> h pow 3 <= &n0 * sqrt(inv(&3 * inv(h pow 2)) pow 3) / &27 -
                            &2 * h pow 3 * cv`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = sqrt(&27)` THEN
  SUBGOAL_THEN `&0 < s /\ s <= &141 / &27` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&141 / &27 = sqrt((&141 / &27) pow 2)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(inv(&3 * inv(h pow 2)) pow 3) = h pow 3 / s` SUBST1_TAC THENL
   [SUBGOAL_THEN `inv(&3 * inv(h pow 2)) pow 3 = (h pow 3) pow 2 / &27` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[SQRT_DIV] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &2 * cv) * (&27 * s) <= &n0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&141 * (&1 + &2 * cv)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&1 + &2 * cv) * (&27 * s) <= (&1 + &2 * cv) * &141` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &2 * cv <= &n0 / (&27 * s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &27`]; ALL_TAC] THEN
  SUBGOAL_THEN `h pow 3 * (&1 + &2 * cv) <= h pow 3 * (&n0 / (&27 * s))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&n0 * (h pow 3 / s) / &27 = h pow 3 * (&n0 / (&27 * s))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P3H_CAPVOL_POS = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> &0 <= p3h_capvol g0 A0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3h_capvol] THEN
  SUBGOAL_THEN `{x | &0 <= A0 + &4 - p3_std_dist g0 x} = {x | p3_std_dist g0 x <= A0 + &4}`
  SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S0 = {x | p3_std_dist g0 x <= A0 + &4}` THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `S0:real^3->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; COMPACT_IN_EUCLIDEAN] THEN EXPAND_TAC "S0" THEN
    MATCH_MP_TAC P3H_STD_REGION_COMPACT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `S0:real^3->bool`; `v:real`]
                MFD_HAS_VOLUME_VOLUME) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `S0:real^3->bool`; `v:real`]
                MFD_HAS_VOLUME_POS_LE) THEN
  ASM_REWRITE_TAC[GEOL_EUCLID_FACTS] THEN REAL_ARITH_TAC);;

(* Volume growth along a slab: R >= -6/(4t+1) >= -6 (pinching), so by the  *)
(* route input P2_VOLUME_GROWTH the volume grows at most like exp(6 t).     *)

let P3H_HIST_SLAB_GROWTH = prove
 (`!(u:A->bool) (hs:(A)rfs_history) k t.
     P2_VOLUME_GROWTH_STATEMENT u /\ rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     k <= hs_count hs /\ hs_time hs k <= t /\ t < hs_time hs (k + 1)
     ==> mfd_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k t) (topspace(hs_top hs k)) <=
         exp(&6 * (t - hs_time hs k)) * p3h_stage_vol hs k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= hs_time (hs:(A)rfs_history) k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `0`; `k:num`] APX_HS_TIME_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[rfs_history_ok];
    ALL_TAC] THEN
  ABBREV_TAC `top = hs_top (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `atlas = hs_atlas (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `g = hs_metric (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `a = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `b = hs_time (hs:(A)rfs_history) (k + 1)` THEN
  REWRITE_TAC[p3h_stage_vol] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `a:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) a`; `topspace top:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM compact_space]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v1:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `topspace top:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM compact_space]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v2:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) a`; `topspace top:A->bool`; `v1:real`]
                MFD_HAS_VOLUME_VOLUME) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `topspace top:A->bool`; `v2:real`]
                MFD_HAS_VOLUME_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2_VOLUME_GROWTH_STATEMENT] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "P2_VOLUME_GROWTH_STATEMENT"))
        (concl th))) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `a:real`; `b:real`; `g:real->A->real^3^3`; `&6`; `a:real`; `t:real`;
                             `v1:real`; `v2:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `x:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
  REWRITE_TAC[rfs_view; rfs_pinched] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `x:A`]) THEN ASM_REWRITE_TAC[rfs_pinched_at] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&6 / (&4 * s + &1) <= &6` MP_TAC THENL
   [SUBGOAL_THEN `&0 < &4 * s + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The data of one event of a structurally controlled history               *)
(* (p3_struct with p3h_plus_disc): n0 dyadic boxes in the positive half of  *)
(* each cut neck (a strong neck of the preview at the event time, whose     *)
(* slice is Omega with the limit metric), discarded and pairwise disjoint,  *)
(* and minus caps of volume <= 2 h^3 p3h_capvol g0 A0.                       *)
(* ========================================================================= *)

let P3H_PREVIEW_NECK = prove
 (`!(hs:(A)rfs_history) k d y ts e.
     hs_time hs k = ts /\ rfs_strong_neck (rfs_preview hs k) d y ts e
     ==> rfs_neck (subtopology (hs_top hs (k - 1)) (ev_omega(hs_event hs k)),
                   restrict_atlas (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k)))
                  (restrict_metric (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k))
                                   (ev_limit(hs_event hs k))) d y e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN
  ASM_REWRITE_TAC[rfs_strong_neck; rfs_preview; rfs_evolving_neck] THEN
  SIMP_TAC[]);;

let P3H_PREVIEW_SCALAR = prove
 (`!(hs:(A)rfs_history) k ts y.
     hs_time hs k = ts
     ==> rfs_vscalar (rfs_preview hs k) ts y =
     mfd_scalar (restrict_atlas (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k)))
                (restrict_metric (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k))
                                 (ev_limit(hs_event hs k))) y`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[rfs_preview; rfs_vscalar]);;

let P3H_HIST_EVENT_DATA = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k n0.
     p3_std_initial g0 A0 /\ p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
     p3h_plus_disc dl hs /\ 1 <= k /\ k <= hs_count hs /\
     dl(hs_time hs k) <= &1 / &2 /\ dl(hs_time hs k) <= md(inv(A0 + &5)) /\
     &2 pow n0 <= exp(inv(sqrt(&2) * dl(hs_time hs k))) /\
     &0 < p3_hscale hf rp dl (hs_time hs k)
     ==> ?Kp kv.
          (!i. i IN ev_index(hs_event hs k)
               ==> compact_in (hs_top hs (k - 1)) (Kp i) /\
                   Kp i SUBSET ev_omega(hs_event hs k) /\
                   DISJOINT (Kp i) (topspace(hs_top hs k)) /\
                   mfd_has_volume (subtopology (hs_top hs (k - 1)) (ev_omega(hs_event hs k)),
                                   restrict_atlas (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k)))
                                  (restrict_metric (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k))
                                                   (ev_limit(hs_event hs k)))
                                  (Kp i) (kv i) /\
                   &n0 * sqrt(inv(&3 * inv(p3_hscale hf rp dl (hs_time hs k) pow 2)) pow 3) / &27
                   <= kv i) /\
          (!i j. i IN ev_index(hs_event hs k) /\ j IN ev_index(hs_event hs k) /\ ~(i = j)
                 ==> DISJOINT (Kp i) (Kp j)) /\
          (!i. i IN ev_index(hs_event hs k)
               ==> ?v. mfd_has_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k (hs_time hs k))
                         (IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))) v /\
                       v <= &2 * p3_hscale hf rp dl (hs_time hs k) pow 3 * p3h_capvol g0 A0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_surgery_ok")) (concl th))) THEN
  ASM_REWRITE_TAC[rfs_surgery_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "necks") (K ALL_TAC))
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "caps"))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "times")
    (CONJUNCTS_THEN2 (LABEL_TAC "stages") (LABEL_TAC "events")))) THEN
  USE_THEN "events" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "stages" (MP_TAC o SPEC `k - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "stages" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= hs_time (hs:(A)rfs_history) k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `0`; `k:num`] APX_HS_TIME_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dl(hs_time (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (hs_atlas hs k)
                  (hs_metric (hs:(A)rfs_history) k (hs_time hs k))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `hs_time (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) (k + 1)`;
                   `hs_metric (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) k`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
     [USE_THEN "times" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `ev = hs_event (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `ts = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `h = p3_hscale hf rp dl ts` THEN
  ABBREV_TAC `Om = ev_omega (ev:(A)rfs_event)` THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) (k - 1)) Om /\
                rfs_limit_metric (hs_top hs (k - 1),hs_atlas hs (k - 1)) Om ts
                                 (hs_metric hs (k - 1)) (ev_limit ev)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1))
                   (hs_metric (hs:(A)rfs_history) (k - 1)) ts
                   (hs_top hs k,hs_atlas hs k) (hs_metric hs k) ev` THEN
    ASM_REWRITE_TAC[rfs_event_ok] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (subtopology (hs_top (hs:(A)rfs_history) (k - 1)) Om) /\
                riemannian_metric (restrict_atlas (hs_atlas hs (k - 1)) Om)
                  (restrict_metric (hs_atlas hs (k - 1)) Om (ev_limit (ev:(A)rfs_event)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
    MATCH_MP_TAC P3H_LIMIT_RESTRICT_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`; `ts:real`;
                          `hs_metric (hs:(A)rfs_history) (k - 1)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_plus_disc")) (concl th) = false &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)) o
    GEN_REWRITE_RULE I [p3h_plus_disc] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3h_plus_disc")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P1") (LABEL_TAC "P2")) THEN
  ABBREV_TAC `Kp = \i. UNIONS {IMAGE (ev_neck (ev:(A)rfs_event) i) (p3h_box j) | j | j < n0}` THEN
  ABBREV_TAC `P = \i. IMAGE (ev_neck (ev:(A)rfs_event) i)
                        {z | z IN rfs_neck_dom (dl(ts:real)) /\ &1 < norm z}` THEN
  SUBGOAL_THEN
   `!i. i IN ev_index ev
        ==> compact_in (hs_top (hs:(A)rfs_history) (k - 1)) ((Kp:num->A->bool) i) /\
            Kp i SUBSET Om /\ Kp i SUBSET (P:num->A->bool) i /\
            ?v. mfd_has_volume (subtopology (hs_top hs (k - 1)) Om,
                                restrict_atlas (hs_atlas hs (k - 1)) Om)
                               (restrict_metric (hs_atlas hs (k - 1)) Om (ev_limit ev))
                               (Kp i) v /\
                &n0 * sqrt(inv(&3 * inv(h pow 2)) pow 3) / &27 <= v`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "necks" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `dl(ts:real):real`; `y:A`; `ts:real`;
                   `ev_neck (ev:(A)rfs_event) i`] P3H_PREVIEW_NECK) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`; `y:A`] P3H_PREVIEW_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology (hs_top (hs:(A)rfs_history) (k - 1)) Om`;
                   `restrict_atlas (hs_atlas (hs:(A)rfs_history) (k - 1)) Om`;
                   `restrict_metric (hs_atlas (hs:(A)rfs_history) (k - 1)) Om
                                    (ev_limit (ev:(A)rfs_event))`;
                   `dl(ts:real):real`; `y:A`; `ev_neck (ev:(A)rfs_event) i`; `n0:num`]
                  P3H_NECK_PLUS_BOXES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Kp" THEN EXPAND_TAC "P" THEN BETA_TAC THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                                      SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `kv:num->real`) THEN
  MAP_EVERY EXISTS_TAC [`Kp:num->A->bool`; `kv:num->real`] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "P1" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(Kp:num->A->bool) i SUBSET (P:num->A->bool) i` THEN
    EXPAND_TAC "P" THEN EXPAND_TAC "ts" THEN BETA_TAC THEN SET_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "P2" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(Kp:num->A->bool) i SUBSET (P:num->A->bool) i` THEN
    UNDISCH_TAC `(Kp:num->A->bool) j SUBSET (P:num->A->bool) j` THEN
    EXPAND_TAC "P" THEN EXPAND_TAC "ts" THEN BETA_TAC THEN SET_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "caps" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[p3_cap_ok]] THEN
    DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->A` (X_CHOOSE_TAC `xi:real^3->real^3`)) THEN
    MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                   `p3_hscale hf rp dl`; `hs:(A)rfs_history`; `k:num`; `i:num`;
                   `Phi:real^3->A`; `xi:real^3->real^3`] P3H_CAP_VOLUME) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* One event lowers the stage volume (at the start of the                   *)
(* slab, grown by at most exp(6 dt) over the previous slab) by at least      *)
(* hmin^3 per cut neck.                                                      *)
(* ========================================================================= *)

let P3H_STAGE_VOL_HAS = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ k <= hs_count hs
     ==> mfd_has_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k (hs_time hs k))
                        (topspace(hs_top hs k)) (p3h_stage_vol hs k) /\
         &0 <= p3h_stage_vol hs k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_time (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) (k + 1)`;
                 `hs_metric (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) k`]
                RFA_RICCI_FLOW_FROM_METRIC) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`;
                 `topspace(hs_top (hs:(A)rfs_history) k)`] MFD_HAS_VOLUME_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM compact_space]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`;
                 `topspace(hs_top (hs:(A)rfs_history) k)`; `v:real`] MFD_HAS_VOLUME_VOLUME) THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`;
                 `topspace(hs_top (hs:(A)rfs_history) k)`; `v:real`] MFD_HAS_VOLUME_POS_LE) THEN
  ASM_REWRITE_TAC[p3h_stage_vol] THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[]);;

let P3H_HIST_EVENT_VOLUME = prove
 (`!(u:A->bool) C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k n0 hmin.
     P2_VOLUME_GROWTH_STATEMENT u /\ p3_std_initial g0 A0 /\
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3h_plus_disc dl hs /\
     1 <= k /\ k <= hs_count hs /\
     dl(hs_time hs k) <= &1 / &2 /\ dl(hs_time hs k) <= md(inv(A0 + &5)) /\
     &2 pow n0 <= exp(inv(sqrt(&2) * dl(hs_time hs k))) /\
     &141 * (&1 + &2 * p3h_capvol g0 A0) <= &n0 /\
     &0 < hmin /\ hmin <= p3_hscale hf rp dl (hs_time hs k)
     ==> p3h_stage_vol hs k + &(CARD(ev_index(hs_event hs k))) * hmin pow 3 <=
         exp(&6 * (hs_time hs k - hs_time hs (k - 1))) * p3h_stage_vol hs (k - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < p3_hscale hf rp dl (hs_time (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                 `hs:(A)rfs_history`; `k:num`; `n0:num`] P3H_HIST_EVENT_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kp:num->A->bool` (X_CHOOSE_THEN `kv:num->real`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "times")
    (CONJUNCTS_THEN2 (LABEL_TAC "stages") (LABEL_TAC "events")))) THEN
  USE_THEN "events" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "stages" (MP_TAC o SPEC `k - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k - 1 + 1 = k` SUBST1_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "stages" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k - 1) < hs_time hs k` ASSUME_TAC THENL
   [USE_THEN "times" (MP_TAC o SPEC `k - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 + 1 = k` SUBST1_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (hs_atlas hs k)
                  (hs_metric (hs:(A)rfs_history) k (hs_time hs k))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `hs_time (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) (k + 1)`;
                   `hs_metric (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) k`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
     [USE_THEN "times" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`] P3H_STAGE_VOL_HAS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `ts = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `a = hs_time (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `h = p3_hscale hf rp dl ts` THEN
  ABBREV_TAC `B = &n0 * sqrt(inv(&3 * inv(h pow 2)) pow 3) / &27` THEN
  ABBREV_TAC `Kc = &2 * h pow 3 * p3h_capvol g0 A0` THEN
  SUBGOAL_THEN `hmin pow 3 <= B - Kc` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `h pow 3` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "B" THEN EXPAND_TAC "Kc" THEN MATCH_MP_TAC P3H_BOX_CAP_ARITH THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3H_CAPVOL_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `VY = p3h_stage_vol (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `VX = p3h_stage_vol (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `m = CARD(ev_index(hs_event (hs:(A)rfs_history) k))` THEN
  MATCH_MP_TAC P3H_LE_EPS_LIMIT THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                 `hs_metric (hs:(A)rfs_history) (k - 1)`; `ts:real`;
                 `hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k`; `hs_event (hs:(A)rfs_history) k`;
                 `a:real`; `Kp:num->A->bool`; `kv:num->real`; `B:real`; `Kc:real`; `e:real`]
                P3H_EVENT_VOLUME_INEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                   `a:real`; `ts:real`; `hs_metric (hs:(A)rfs_history) (k - 1)`; `t:real`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ts - d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`; `k - 1`; `ts - d / &2`]
                P3H_HIST_SLAB_GROWTH) THEN
  SUBGOAL_THEN `k - 1 + 1 = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `exp(&6 * ((ts - d / &2) - a)) <= exp(&6 * (ts - a))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&6 * ((ts - d / &2) - a)) * VX <= exp(&6 * (ts - a)) * VX`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&m * hmin pow 3 <= &m * (B - Kc)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ABBREV_TAC `W = mfd_volume (hs_top hs (k - 1),hs_atlas hs (k - 1))
                    (hs_metric (hs:(A)rfs_history) (k - 1) (ts - d / &2))
                    (topspace(hs_top hs (k - 1)))` THEN
  SUBGOAL_THEN `(&1 + e) * W <= (&1 + e) * (exp(&6 * (ts - a)) * VX)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `VY = mfd_volume (hs_top hs k,hs_atlas hs k)
                       (hs_metric (hs:(A)rfs_history) k ts) (topspace(hs_top hs k))`
  SUBST1_TAC THENL
   [EXPAND_TAC "VY" THEN EXPAND_TAC "ts" THEN REWRITE_TAC[p3h_stage_vol]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Every event discards something; MT Lemma 17.12 with the hypothesis      *)
(* p3h_plus_disc.                                                          *)
(* ========================================================================= *)

let P3H_HIST_DISCARDS = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ 1 <= k /\ k <= hs_count hs
     ==> ~(ev_disc(hs_event hs k) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN
  ASM_CASES_TAC `ev_index(hs_event (hs:(A)rfs_history) k) = {}` THENL
   [MATCH_MP_TAC P3H_NECKLESS_EVENT_DISCARDS THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_event_ok]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_capp")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SUBSET] THEN DISCH_TAC THEN
  EXISTS_TAC `ev_capp (hs_event (hs:(A)rfs_history) k) i (vec 0)` THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC);;

(* MT Lemma 17.12 for histories with discarded, disjoint positive halves.  *)

let P3H_LEMMA_17_12_CORE = prove
 (`!u:A->bool. P2_VOLUME_GROWTH_STATEMENT u
   ==> !C eps hf md g0 A0.
         &1 < C /\ &0 < eps /\ p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0
         ==> ?d1712. &0 < d1712 /\
               !top0 atlas0 g00 Tb rmin dmin hmin.
                  &0 < rmin /\ &0 < dmin /\ &0 < hmin
                  ==> ?N. !rp dl (hs:(A)rfs_history).
                            hs_top hs 0 = top0 /\ hs_atlas hs 0 = atlas0 /\
                            hs_metric hs 0 (&0) = g00 /\
                            p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                            p3h_plus_disc dl hs /\
                            rfs_horizon hs <= Tb /\
                            (!t. &0 <= t ==> dl t <= d1712) /\
                            (!t. &0 <= t /\ t < Tb
                                 ==> rmin <= rp t /\ dmin <= dl t /\
                                     hmin <= p3_hscale hf rp dl t)
                            ==> hs_count hs <= N`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3H_CAPVOL_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `&141 * (&1 + &2 * p3h_capvol g0 A0)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN
  ABBREV_TAC `n0 = n1 + 1` THEN
  SUBGOAL_THEN `1 <= n0 /\ &141 * (&1 + &2 * p3h_capvol g0 A0) <= &n0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n0" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < md(inv(A0 + &5))` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_modulus md` THEN REWRITE_TAC[p3_modulus] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(A0 + &5)`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &n0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &2) (min (md(inv(A0 + &5))) (inv(&2 * &n0)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V0 = mfd_volume (top0,atlas0) (g00:A->real^3^3) (topspace top0)` THEN
  MP_TAC(SPEC `(V0 * exp(&6 * Tb)) / hmin pow 3` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  EXISTS_TAC `CARD(connected_components_of (top0:A topology)) + 2 * M` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN
  SUBGOAL_THEN `!k. k <= hs_count hs
                    ==> &0 <= hs_time (hs:(A)rfs_history) k /\ hs_time hs k < Tb`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `0`; `k:num`] APX_HS_TIME_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[rfs_history_ok];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `hs_time (hs:(A)rfs_history) (k + 1)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rfs_horizon (hs:(A)rfs_history)` THEN
    ASM_REWRITE_TAC[rfs_horizon] THEN
    MATCH_MP_TAC APX_HS_TIME_LE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= hs_count hs
        ==> p3h_stage_vol hs k <=
            exp(&6 * (hs_time hs k - hs_time hs (k - 1))) * p3h_stage_vol hs (k - 1) -
            &(CARD(ev_index(hs_event (hs:(A)rfs_history) k))) * hmin pow 3`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `Tb:real`)) (concl th) &&
      not (can (find_term (fun t -> t = `rmin:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < dl(hs_time (hs:(A)rfs_history) k) /\
                  dl(hs_time hs k) <= &1 / &2 /\ dl(hs_time hs k) <= md(inv(A0 + &5)) /\
                  dl(hs_time hs k) <= inv(&2 * &n0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `inv(&2 * &n0)`)) (concl th))) THEN
      ASM_REWRITE_TAC[REAL_LE_MIN];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:A->bool`; `C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                   `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                   `hs:(A)rfs_history`; `k:num`; `n0:num`; `hmin:real`]
                  P3H_HIST_EVENT_VOLUME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P3H_DL_BOXES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `rmin:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p3h_stage_vol (hs:(A)rfs_history)`; `hs_time (hs:(A)rfs_history)`;
                 `\k. CARD(ev_index(hs_event (hs:(A)rfs_history) k))`; `hmin pow 3`;
                 `Tb:real`; `hs_count (hs:(A)rfs_history)`] P3H_VOLUME_BUDGET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3H_STAGE_VOL_HAS) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3h_stage_vol (hs:(A)rfs_history) 0 = V0` SUBST1_TAC THENL
   [EXPAND_TAC "V0" THEN REWRITE_TAC[p3h_stage_vol] THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) 0 = &0` SUBST1_TAC THENL
     [ASM_MESON_TAC[rfs_history_ok]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `nsum(1..hs_count hs) (\k. CARD(ev_index(hs_event (hs:(A)rfs_history) k))) <= M`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(V0 * exp(&6 * Tb)) / hmin pow 3` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` P3H_HIST_COMPONENTS_COUNT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3H_HIST_DISCARDS THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                          `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

