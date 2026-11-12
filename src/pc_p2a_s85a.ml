(* ========================================================================= *)
(* Unit pc_p2a_s85a: tools for COR_9_94_L piece (b) at a soul (unit          *)
(* pc_p2a_s85b): (1) the uniform neck transfer with target length L,         *)
(* P2AS85_NECK_FIX_L (the proof of P2B_PROP_9_79_NECK_FIX_FROM_REQ of        *)
(* pc_p2b_979 with the length argument L in place of &1; the L = 1 case is   *)
(* P2B_PROP_9_79_NECK_FIX); (2) the closeness of P2APC_P2C_CLOSE uniformly   *)
(* in the open set and in the scale R >= R0; (3) the transfer of evolving    *)
(* necks from all points of a compact set of a flow limit to the sequence;   *)
(* (4) a line from minimizing splits through a compact set (the argument of  *)
(* APXT_TWO_ENDS_LINE of pc_apx_twoends with the split points as a           *)
(* hypothesis); (5) a noncompact complete connected slice is not round       *)
(* (CMP_MYERS_DIAMETER).                                                     *)
(* ========================================================================= *)

needs "src/pc_p2a_l984.ml";;
needs "src/pc_p2a_p2cc.ml";;
needs "src/pc_apx_twoends.ml";;
needs "src/pc_cmp_myers.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* P2AS85_NECK_FIX_L, the uniform transfer of an evolving eps-neck of length *)
(* a to an evolving eps'-neck of length L < a (eps < eps'): one delta for    *)
(* all views, points and necks.  Proof of P2B_PROP_9_79_NECK_FIX_FROM_REQ    *)
(* (pc_p2b_979) with L for the target length; P2B_REQ_LRG_BASE and           *)
(* P2B_REQ_LRG_RM_NEAR are theorems (pc_p2b_979s).                           *)
(* ========================================================================= *)

let P2AS85_NECK_FIX_L = prove
 (`!eps eps' a L.
     &0 < eps /\ eps < eps' /\ eps' < &1 / &4 /\ &1 <= L /\ L < a
     ==> ?delta. &0 < delta /\
           !V x t e V' t' Q' psi.
              p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) /\
              rfs_evolving_neck V eps x t a e /\
              (!s. --a < s /\ s <= &0
                   ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                             (rfs_vatlas V' (t' + s / Q')) /\
                       riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                         (rfs_vmetric V' (t' + s / Q'))) /\
              p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps))
                (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                    (real->B->real^3^3)) t' Q' psi {s | --a < s /\ s <= &0} delta
              ==> rfs_evolving_neck V' eps' (psi x) t' L (psi o e)`,
  MP_TAC(MATCH_MP P2B9_NECK_CENTRE_UNIFORM P2B_REQ_LRG_RM_NEAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "cu" o INST_TYPE [`:A`,`:A`])) THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `eps':real`; `a:real`; `L:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `rfs_kreg eps'` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT] P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  MP_TAC(ISPECL [`eps:real`; `eps':real`; `M:real`; `K0:real`; `L:real`; `a:real`;
                 `rfs_kreg eps' + 2`] P2B9_DELTA_EXISTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:A`; `t:real`; `e:real^3->A`;
    `V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
    `t':real`; `Q':real`; `psi:A->B`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`] P2B9_NECK_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sup")))) THEN
  MATCH_MP_TAC P2B9_ENECK_CORE THEN
  MAP_EVERY EXISTS_TAC [`rfs_kreg eps'`; `M:real`; `K0:real`; `eps:real`; `a:real`;
                        `delta:real`; `eps pow 2`;
                        `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `t:real`; `Q':real`] THEN
  CONJ_TAC THENL [USE_THEN "base" ACCEPT_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_POW_2] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `eps pow 2 <= (&1 / &4) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d1:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN USE_THEN "sup" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "cu" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`eps:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* P2APC_P2C_CLOSE uniformly in the open set U inside the compact K and in   *)
(* the scale R >= R0 (one k0 for all; the chart conversion factor (1 + inv   *)
(* R) pow m is at most (1 + inv R0) pow m). Proof adapted from               *)
(* P2APC_P2C_CLOSE (pc_p2a_p2cc).                                            *)
(* ========================================================================= *)

let P2AS85_MUL_MONO_ARITH = prove
 (`!c1 c2 X B. &0 < c1 /\ c1 <= c2 /\ X < B /\ &0 < B ==> c1 * X <= c2 * B`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `X <= &0` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `c * X <= &0 <=> &0 <= c * --X`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c2 * X` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;

let P2AS85_P2C_CLOSE_UNIF = prove
 (`!V x t Q J (top:B topology) atlas g xl W phi.
     p2c_flow_limit_with (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) x t Q J (top,atlas) g xl W phi /\
     (!k s. ~(topspace(rfs_vtop (V k) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V k) s) (rfs_vatlas (V k) s) /\
                riemannian_metric (rfs_vatlas (V k) s) (rfs_vmetric (V k) s)) /\
     (!s. s IN J ==> riemannian_metric atlas (g s))
     ==> !K a b delta R0.
           compact_in top K /\ real_interval[a,b] SUBSET J /\ &0 < delta /\ &0 < R0
           ==> ?k0. !k U R s.
                  k0 <= k /\ open_in top U /\ U SUBSET K /\ R0 <= R /\ a <= s /\ s <= b
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
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `a:real`; `b:real`; `delta:real`; `R0:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `m = rfs_kreg delta` THEN
  SUBGOAL_THEN `&0 < (&1 + inv R0) pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `R0:real` REAL_LT_INV) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "close" (MP_TAC o SPECL [`a:real`; `b:real`; `K:B->bool`; `m:num`;
                                       `delta pow 2 / (&2 * (&1 + inv R0) pow m)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `U:B->bool`; `R:real`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + inv R) pow m <= (&1 + inv R0) pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MP_TAC(SPEC `R:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
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
  EXISTS_TAC `(&1 + inv R0) pow m * delta pow 2 / (&2 * (&1 + inv R0) pow m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AS85_MUL_MONO_ARITH THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `R:real` REAL_LT_INV) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < (&1 + inv R0) pow m` THEN CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* Transfer of evolving necks from the limit to the sequence, uniformly at   *)
(* all points z with R(z) >= R0 whose neck regions lie in one compact C:     *)
(* P2AS85_NECK_FIX_L gives one delta, and P2AS85_P2C_CLOSE_UNIF one k0 for   *)
(* the closeness p3_view_close at the scale R(z) on the neck region over the *)
(* normalized times (-a,0], i.e. the limit times s / R(z) in [-Tm,0] when a  *)
(* <= R0 Tm.                                                                 *)
(* ========================================================================= *)

let P2AS85_UNIF_TRANSFER = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q J kappa (top:B topology) atlas g xl W phi C eps eps' a L R0 Tm.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!k s. ~(topspace(rfs_vtop (V k) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V k) s) (rfs_vatlas (V k) s) /\
                riemannian_metric (rfs_vatlas (V k) s) (rfs_vmetric (V k) s)) /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     p2b_kappa_solution kappa (top,atlas) g /\
     compact_in top C /\ &0 < R0 /\ &0 < Tm /\ real_interval[--Tm,&0] SUBSET J /\
     a <= R0 * Tm /\
     &0 < eps /\ eps < eps' /\ eps' < &1 / &4 /\ &1 <= L /\ L < a
     ==> ?k0. !k z e.
            k0 <= k /\ R0 <= mfd_scalar atlas (g(&0)) z /\
            rfs_evolving_neck (p2b_kview (top,atlas) g) eps z (&0) a e /\
            IMAGE e (rfs_neck_dom eps) SUBSET C
            ==> rfs_evolving_neck (V k) eps' (phi k z) (t k) L (phi k o e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "slices")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)))) THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`; `a:real`; `L:real`]
    (INST_TYPE [`:B`,`:A`; `:A`,`:B`] P2AS85_NECK_FIX_L)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fix"))) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`]
                P2AS85_P2C_CLOSE_UNIF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`C:B->bool`; `--Tm`; `&0`; `delta:real`; `R0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_flow_limit_with (V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                   x t Q J (top,atlas) (g:real->B->real^3^3) xl W phi` THEN
    REWRITE_TAC[p2c_flow_limit_with] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `k0:num` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `z:B`; `e:real^3->B`] THEN STRIP_TAC THEN
  ABBREV_TAC `Rz = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) z` THEN
  SUBGOAL_THEN `&0 < Rz` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (top:B topology) (IMAGE (e:real^3->B) (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `eps:real`; `z:B`; `a:real`; `e:real^3->B`]
                  P2BL_KVIEW_NECK0) THEN
    ASM_REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->B`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. --a < s /\ s <= &0 ==> --Tm <= s / Rz /\ s / Rz <= &0` (LABEL_TAC "tw") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `--a < s /\ a <= R0 * Tm /\ R0 * Tm <= Rz * Tm ==> --Tm * Rz <= s`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. --a < s /\ s <= &0
        ==> (t:num->real) k + s / (Rz * Q k) = t k + (s / Rz) / Q k` (LABEL_TAC "ta") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  USE_THEN "fix" (MP_TAC o SPECL
   [`p2b_kview (top,atlas) (g:real->B->real^3^3)`; `z:B`; `&0`; `e:real^3->B`;
    `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`;
    `(t:num->real) k`; `Rz * (Q:num->real) k`; `(phi:num->B->A) k`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p2c_regular_view (p2b_kview (top,atlas) (g:real->B->real^3^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "ta" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `--a < s`)
                                                       (ASSUME `s <= &0`))]) THEN
    USE_THEN "slices" MATCH_MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    USE_THEN "tw" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `--a < s`) (ASSUME `s <= &0`)))) THEN
    USE_THEN "k0" (MP_TAC o SPECL [`k:num`; `IMAGE (e:real^3->B) (rfs_neck_dom eps)`;
                                   `Rz:real`; `s / Rz`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `psi:A->B` MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[mfd_diffeo] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPEC `(phi:num->B->A) k ((e:real^3->B) (basis 1))` o
      REWRITE_RULE[SUBSET]) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
      DISCH_TAC THEN EXISTS_TAC `(phi:num->B->A) k ((e:real^3->B) (basis 1))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p3_view_close; P2BL_KVIEW_ACCESS] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "tw" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (CONJ (ASSUME `--a < s`) (ASSUME `s <= &0`)))) THEN
  SUBGOAL_THEN `&0 + s / Rz <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_ADD_LID] THEN
  USE_THEN "ta" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `--a < s`)
                                                     (ASSUME `s <= &0`))]) THEN
  USE_THEN "k0" (MP_TAC o SPECL [`k:num`; `IMAGE (e:real^3->B) (rfs_neck_dom eps)`;
                                 `Rz:real`; `s / Rz`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* ========================================================================= *)
(* A line from minimizing splits through a compact set.  If for every R      *)
(* there are points p, q at distance >= R from x0 and a point y of the       *)
(* compact K with d(p,y) + d(y,q) = d(p,q), the manifold contains a line.    *)
(* This is part (A) of APXT_TWO_ENDS_LINE (pc_apx_twoends), whose two-ends   *)
(* hypothesis enters only through such split points (APXT_SPLIT_POINT); the  *)
(* proof from the cluster point on is unchanged.                             *)
(* ========================================================================= *)

let P2AS85_LINE_FROM_SPLITS = prove
 (`!top atlas (g:A->real^N^N) K x0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\ compact_in top K /\
     x0 IN topspace top /\
     (!R. ?p q y. p IN topspace top /\ q IN topspace top /\
                  R <= mfd_dist (top,atlas) g x0 p /\ R <= mfd_dist (top,atlas) g x0 q /\
                  y IN K /\
                  mfd_dist (top,atlas) g p y + mfd_dist (top,atlas) g y q =
                  mfd_dist (top,atlas) g p q)
     ==> ?lam:real->A. !s t. lam s IN topspace top /\
                             mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s)`,
  REPEAT GEN_TAC THEN INTRO_TAC "haus smooth riem comp conn cpt x0 splits" THEN
  SUBGOAL_THEN `!a b c:A. a IN topspace top /\ b IN topspace top /\ c IN topspace top
                ==> mfd_dist (top,atlas) (g:A->real^N^N) a c <=
                    mfd_dist (top,atlas) g a b + mfd_dist (top,atlas) g b c`
  (LABEL_TAC "tri") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `K:A->bool`; `x0:A`] APXT_COMPACT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D:real` (LABEL_TAC "D")) THEN
  SUBGOAL_THEN
   `!n. ?p q y. p IN topspace top /\ q IN topspace top /\
                &n + D + &1 <= mfd_dist (top,atlas) (g:A->real^N^N) x0 p /\
                &n + D + &1 <= mfd_dist (top,atlas) g x0 q /\
                y IN K /\ y IN topspace top /\
                mfd_dist (top,atlas) g p y + mfd_dist (top,atlas) g y q =
                mfd_dist (top,atlas) g p q`
  MP_TAC THENL
   [GEN_TAC THEN USE_THEN "splits" (MP_TAC o SPEC `&n + D + &1`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:num->A` (X_CHOOSE_THEN `qq:num->A`
    (X_CHOOSE_THEN `xx:num->A` (LABEL_TAC "all")))) THEN
  SUBGOAL_THEN `!n. &n + D + &1 <= mfd_dist (top,atlas) (g:A->real^N^N) x0 ((pp:num->A) n) /\
                    &n + D + &1 <= mfd_dist (top,atlas) g x0 ((qq:num->A) n)`
  (LABEL_TAC "far") THENL
   [GEN_TAC THEN USE_THEN "all" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (pp:num->A) n IN topspace top /\ (qq:num->A) n IN topspace top`
  (LABEL_TAC "pqtop") THENL
   [GEN_TAC THEN USE_THEN "all" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (xx:num->A) n IN K /\ xx n IN topspace top /\
        mfd_dist (top,atlas) (g:A->real^N^N) ((pp:num->A) n) (xx n) +
        mfd_dist (top,atlas) g (xx n) ((qq:num->A) n) =
        mfd_dist (top,atlas) g (pp n) (qq n)`
  (LABEL_TAC "split") THENL
   [GEN_TAC THEN USE_THEN "all" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `K:A->bool`; `xx:num->A`] APXT_CLUSTER_SEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `m:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mk") (LABEL_TAC "conv"))))) THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. &k + &1 <= mfd_dist (top,atlas) (g:A->real^N^N) z ((pp:num->A)((m:num->num) k)) /\
        &k + &1 <= mfd_dist (top,atlas) g z ((qq:num->A)(m k))`
  (LABEL_TAC "farz") THENL
   [GEN_TAC THEN
    USE_THEN "far" (MP_TAC o SPEC `(m:num->num) k`) THEN STRIP_TAC THEN
    USE_THEN "D" (ASSUME_TAC o C MATCH_MP (ASSUME `(z:A) IN K`)) THEN
    SUBGOAL_THEN `&k <= &((m:num->num) k)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    USE_THEN "tri" (MP_TAC o SPECL [`x0:A`; `z:A`; `(pp:num->A)((m:num->num) k)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "tri" (MP_TAC o SPECL [`x0:A`; `z:A`; `(qq:num->A)((m:num->num) k)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ?w1 w2. mfd_tnorm (g:A->real^N^N) z w1 = &1 /\ mfd_tnorm g z w2 = &1 /\
                mfd_geo (top,atlas) g z w1
                  (mfd_dist (top,atlas) g z ((pp:num->A)((m:num->num) k))) = pp(m k) /\
                mfd_geo (top,atlas) g z w2
                  (mfd_dist (top,atlas) g z ((qq:num->A)(m k))) = qq(m k)`
  MP_TAC THENL
   [GEN_TAC THEN USE_THEN "farz" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
    USE_THEN "pqtop" (MP_TAC o SPEC `(m:num->num) k`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((pp:num->A)((m:num->num) k) = z) /\ ~((qq:num->A)(m k) = z)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `z:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `z:A`; `(pp:num->A)((m:num->num) k)`] APXT_SEGMENT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `z:A`; `(qq:num->A)((m:num->num) k)`] APXT_SEGMENT) THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                                z ((pp:num->A)((m:num->num) k)) /\
                  mfd_joinable (top,atlas) z ((qq:num->A)(m k))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`w1:real^N`; `w2:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:num->real^N` (X_CHOOSE_THEN `w2:num->real^N`
    (LABEL_TAC "seg"))) THEN
  SUBGOAL_THEN
   `!k. &k <= mfd_dist (top,atlas) (g:A->real^N^N) z ((pp:num->A)((m:num->num) k)) /\
        &k <= mfd_dist (top,atlas) g z ((qq:num->A)(m k))`
  (LABEL_TAC "len") THENL
   [GEN_TAC THEN USE_THEN "farz" (MP_TAC o SPEC `k:num`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. mfd_dist (top,atlas) (g:A->real^N^N) z ((pp:num->A)((m:num->num) k)) +
        mfd_dist (top,atlas) g z ((qq:num->A)(m k)) <=
        mfd_dist (top,atlas) g (pp(m k)) (qq(m k)) +
        &2 * mfd_dist (top,atlas) g ((xx:num->A)(m k)) z`
  (LABEL_TAC "almost") THENL
   [X_GEN_TAC `k:num` THEN
    USE_THEN "split" (MP_TAC o SPEC `(m:num->num) k`) THEN STRIP_TAC THEN
    USE_THEN "pqtop" (MP_TAC o SPEC `(m:num->num) k`) THEN STRIP_TAC THEN
    USE_THEN "tri" (MP_TAC o SPECL [`z:A`; `(xx:num->A)((m:num->num) k)`;
                                    `(pp:num->A)((m:num->num) k)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "tri" (MP_TAC o SPECL [`z:A`; `(xx:num->A)((m:num->num) k)`;
                                    `(qq:num->A)((m:num->num) k)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "smooth" (fun th -> ASSUME_TAC(MP
      (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
               `z:A`; `(xx:num->A)((m:num->num) k)`] MFD_DIST_SYM) th)) THEN
    USE_THEN "smooth" (fun th -> ASSUME_TAC(MP
      (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
               `(pp:num->A)((m:num->num) k)`; `(xx:num->A)((m:num->num) k)`]
              MFD_DIST_SYM) th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e ==> ?N. !k. N <= k
        ==> &2 * mfd_dist (top,atlas) (g:A->real^N^N) ((xx:num->A)((m:num->num) k)) z < e`
  (LABEL_TAC "ddc") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o SPEC `e / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `z:A`; `w1:num->real^N`; `w2:num->real^N`;
                 `\k. mfd_dist (top,atlas) (g:A->real^N^N) z ((pp:num->A)((m:num->num) k))`;
                 `\k. mfd_dist (top,atlas) (g:A->real^N^N) z ((qq:num->A)((m:num->num) k))`;
                 `\k. &2 * mfd_dist (top,atlas) (g:A->real^N^N) ((xx:num->A)((m:num->num) k)) z`]
                APXT_RAY_PAIR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `v2:real^N` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC APXT_LINE_GLUE THEN
  MAP_EVERY EXISTS_TAC [`z:A`; `v1:real^N`; `v2:real^N`] THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* A complete connected slice with a noncompact topology is not round:       *)
(* constant curvature k > 0 bounds Ric below by k g, so                      *)
(* CMP_MYERS_DIAMETER_RIC bounds all distances from a base point, and the    *)
(* space is one closed ball, compact by mfd_complete.                        *)
(* ========================================================================= *)

let P2AS85_NOT_ROUND = prove
 (`!top atlas (g:B->real^3^3).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ ~compact_space top
     ==> ~p2b_round (top,atlas) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2b_round] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~compact_space (top:B topology)` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `topspace (top:B topology) = {}` THENL
   [ASM_REWRITE_TAC[compact_space; COMPACT_IN_EMPTY]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:B` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN
   `!z w. z IN topspace top
          ==> k * (w dot ((g:B->real^3^3) z ** w)) <= mfd_ricci atlas g z w w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `z:B`; `k:real`; `w:real^3`]
                  CMPZ_MFD_RICCI_SEC_LOWER) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `&0 <= k * (w dot ((g:B->real^3^3) z ** w))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_CASES_TAC `w:real^3 = vec 0` THENL
       [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `z:B`] RIEMANNIAN_METRIC_POS) THEN
        ASM_SIMP_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace top =
    mfd_cball (top,atlas) (g:B->real^3^3) x0
              (&2 * &1 + &2 * &(dimindex(:3) - 1) / (k * &1))` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) x0 y` ASSUME_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMP_MYERS_DIAMETER_RIC THEN
      ASM_REWRITE_TAC[REAL_LT_01];
      STRIP_TAC THEN ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  REWRITE_TAC[compact_space] THEN
  FIRST_X_ASSUM(SUBST1_TAC o
    check (fun th -> is_eq (concl th) && lhs(concl th) = `topspace (top:B topology)`)) THEN
  UNDISCH_TAC `mfd_complete (top,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)` THEN
  REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

