(* ========================================================================= *)
(* Unit pc_p2a_p2cc: closeness of flow limits in the form                    *)
(* p2c_flow_limit_with (pc_p3_iface), where the maps phi k are exposed, so   *)
(* that the tools of the pc_lim units (LIM_BALL, LIM_DIST) and the transfer  *)
(* of necks use the same phi.  P2APC_P2C_CLOSE is P2BL_FLOW_LIMIT_CLOSE of   *)
(* pc_p2b_ltr (for p3_flow_limit) in this form: on a compact K and an open U *)
(* inside K, for times s in [a,b] inside J and any scale R > 0, the maps phi *)
(* k restrict to diffeomorphisms of U and R g(s) is rfs_mclose to R Q k      *)
(* times the pullback of the metric of V k for all large k.  Used for        *)
(* COR_9_94_L piece (b) (pc_p2a_s85a).                                       *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_p2b_ltr.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* P2APC_P2C_CLOSE (proof adapted from P2BL_FLOW_LIMIT_CLOSE of pc_p2b_ltr;  *)
(* the riemannian slices of the limit on J are a hypothesis, as              *)
(* p2c_flow_limit_with has no flow clause).                                  *)
(* ========================================================================= *)

let P2APC_P2C_CLOSE = prove
 (`!V x t Q J (top:B topology) atlas g xl W phi.
     p2c_flow_limit_with (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) x t Q J (top,atlas) g xl W phi /\
     (!k s. ~(topspace(rfs_vtop (V k) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V k) s) (rfs_vatlas (V k) s) /\
                riemannian_metric (rfs_vatlas (V k) s) (rfs_vmetric (V k) s)) /\
     (!s. s IN J ==> riemannian_metric atlas (g s))
     ==> !K U a b delta R.
           compact_in top K /\ open_in top U /\ U SUBSET K /\ real_interval[a,b] SUBSET J /\
           &0 < delta /\ &0 < R
           ==> ?k0. !k. k0 <= k
                  ==> !s. a <= s /\ s <= b
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
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "slices") (LABEL_TAC "riem"))) THEN
  REWRITE_TAC[p2c_flow_limit_with] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "close" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `U:B->bool`; `a:real`; `b:real`; `delta:real`; `R:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `m = rfs_kreg delta` THEN
  SUBGOAL_THEN `&0 < (&1 + inv R) pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `R:real` REAL_LT_INV) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "close" (MP_TAC o SPECL [`a:real`; `b:real`; `K:B->bool`; `m:num`;
                                       `delta pow 2 / (&2 * (&1 + inv R) pow m)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "diffeo") (LABEL_TAC "pt"))) THEN
  USE_THEN "diffeo" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  SUBGOAL_THEN `(U:B->bool) SUBSET W(k:num)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) U
      (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) k) (t k + s / Q k))
      (rfs_vatlas (V k) (t k + s / Q k)) (IMAGE ((phi:num->B->A) k) U) (phi k) psi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [EXISTS_TAC `psi:A->B` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s)` ASSUME_TAC THENL
   [USE_THEN "riem" MATCH_MP_TAC THEN
    UNDISCH_TAC `real_interval[a,b] SUBSET (J:real->bool)` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
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

