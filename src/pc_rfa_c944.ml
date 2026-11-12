(* ========================================================================= *)
(* Unit pc_rfa_c944: the route of MT Cor 9.44, the statement                 *)
(* P2B_COR_9_44_ROUTE_STATEMENT of pc_p2b_chainstmts:                        *)
(*   RFA_P2B_COR_9_44_ROUTE |- !w:B->bool. P2B_COR_9_44_ROUTE_STATEMENT w    *)
(* i.e. R-PINCH3 ==> COR_9_44.  Route: the compact limit makes phi k onto,   *)
(* so M is compact; the round limit makes the slices g(t0 - tau k) uniformly *)
(* almost round (after LIM_VIEW_RM_BOUND with the reverse point estimate     *)
(* LIM_POINT_SEC_REV); sec > 0 forward by RFA_P2_THM_4_23, the pinching at   *)
(* times tending to -infinity, R-PINCH3 for t < 0; left continuity of the    *)
(* sectional curvature at 0 and the positivity of mfd_rm_norm at time 0 give *)
(* a round g(0).                                                             *)
(* ========================================================================= *)

needs "src/pc_p2b_chainstmts.ml";;
needs "src/pc_lim_vol.ml";;
needs "src/pc_rfa_secpres.ml";;
needs "src/pc_rfa_splitend.ml";;
needs "src/pc_rfa_sec.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_lrg_flowsmooth.ml";;
needs "src/pc_lrg_constcurv.ml";;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_p2c_views.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* A diffeomorphism of a compact nonempty manifold onto an open              *)
(* subset of a connected Hausdorff manifold is onto, and the target is      *)
(* compact.                                                                  *)
(* ------------------------------------------------------------------------- *)

let RFA_C944_ONTO = prove
 (`!(top':B topology) (atlas':((B->bool)#(B->real^3))->bool) (top:A topology)
    (atlas:((A->bool)#(A->real^3))->bool) phi psi.
     compact_space top' /\ ~(topspace top' = {}) /\
     hausdorff_space top /\ connected_space top /\
     mfd_diffeo top' atlas' (topspace top') top atlas (IMAGE phi (topspace top')) phi psi
     ==> IMAGE phi (topspace top') = topspace top /\ compact_space top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (top',top) (phi:B->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology top' (topspace top'),
                                 subtopology top (IMAGE (phi:B->A) (topspace top'))) phi` THEN
    REWRITE_TAC[SUBTOPOLOGY_TOPSPACE; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (phi:B->A) (topspace top'))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[GSYM compact_space];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:B->A) (topspace top') = topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (phi:B->A) (topspace top')` o
      GEN_REWRITE_RULE I [CONNECTED_SPACE_CLOPEN_IN]) THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN; IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_MESON_TAC[compact_space]]);;


(* ------------------------------------------------------------------------- *)
(* The sectional curvature of a smooth family of chart metrics               *)
(* is jointly continuous (the argument of P2AU_LSEC_JOINT_CONT of           *)
(* pc_p2a_rigr2, there for Ricci flows on open intervals, here for any      *)
(* lrg_lsmooth family); so along a flow smooth up to b (rfs_flow_upto) the  *)
(* sectional curvature of a fixed plane at a fixed point is left continuous *)
(* at b (the smooth extension of RFA_UPTO_BOX).                              *)
(* ------------------------------------------------------------------------- *)

let RFA_C944_LSEC_CONT = prove
 (`!(O:real^N->bool) a b (Gt:real->real^N->real^N^N) (u:real^N) (v:real^N).
     lrg_lsmooth O a b Gt /\ ~collinear {vec 0,u,v}
     ==> (\z. lift(lsectional (Gt(drop(fstcart z))) (sndcart z) u v))
         continuous_on (interval(lift a,lift b) PCROSS O)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS (O:real^N->bool)` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  SUBGOAL_THEN `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
                continuous_on (S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^(1,N)finite_sum->real^N.
      w continuous_on (S:real^(1,N)finite_sum->bool)
      ==> (\z. (Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) ** w z)
          continuous_on S`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
                   `w:real^(1,N)finite_sum->real^N`;
                   `\(m:real^(N,N)finite_prod) (x:real^N). (matrify m:real^N^N) ** x`;
                   `S:real^(1,N)finite_sum->bool`] BILINEAR_CONTINUOUS_ON_COMPOSE) THEN
    ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^N. (\z. lift(x dot ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) ** y)))
                 continuous_on (S:real^(1,N)finite_sum->bool)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((u:real^N) dot ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) **
                 lriemann (Gt (drop(fstcart z))) (sndcart z) u v v)))
    continuous_on (S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN EXPAND_TAC "S" THEN
    MATCH_MP_TAC LRG_LSMOOTH_LRIEMANN THEN ASM_REWRITE_TAC[lrg_lsmooth];
    ALL_TAC] THEN
  ABBREV_TAC `den = \z. ((u:real^N) dot ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) ** u)) *
                        ((v:real^N) dot (Gt (drop(fstcart z)) (sndcart z) ** v)) -
                        (u dot (Gt (drop(fstcart z)) (sndcart z) ** v)) pow 2` THEN
  SUBGOAL_THEN `(lift o (den:real^(1,N)finite_sum->real)) continuous_on S` ASSUME_TAC THENL
   [EXPAND_TAC "den" THEN REWRITE_TAC[o_DEF; LIFT_SUB; REAL_POW_2; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN (S:real^(1,N)finite_sum->bool) ==> &0 < den z` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                                   FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    EXPAND_TAC "den" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC APX_SECT_DEN_POS THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\z. inv((den:real^(1,N)finite_sum->real) z) %
                  lift((u:real^N) dot ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) **
                       lriemann (Gt (drop(fstcart z))) (sndcart z) u v v))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    EXPAND_TAC "den" THEN REWRITE_TAC[lsectional; real_div; GSYM LIFT_CMUL] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(lift o (\z. inv((den:real^(1,N)finite_sum->real) z))) =
                (lift o inv o den)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;


let RFA_C944_SEC_LEFT_CONT = prove
 (`!top atlas a b (g:real->A->real^3^3) x u v.
     rfs_flow_upto (top,atlas) a b g /\ x IN topspace top /\ ~collinear {vec 0,u,v}
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !t. b - d < t /\ t <= b
                         ==> abs(mfd_sectional atlas (g t) x u v -
                                 mfd_sectional atlas (g b) x u v) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    SIMP_TAC[rfs_flow_upto; ricci_flow_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`] RFA_UPTO_BOX) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`ball(SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x,d0)`;
                 `b - d0`; `b + d0`; `Gb:real->real^3->real^3^3`; `u:real^3`; `v:real^3`]
                RFA_C944_LSEC_CONT) THEN
  ASM_REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC
    `pastecart (lift b) (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d0 d1` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `pastecart (lift t) (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x)`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL;
              DIST_PASTECART_CANCEL; DIST_LIFT; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Gb:real->real^3->real^3^3) t =
      metric_local atlas (chart_at atlas (x:A)) ((g:real->A->real^3^3) t) /\
    Gb b = metric_local atlas (chart_at atlas x) (g b)`
  (fun th -> REWRITE_TAC[th; mfd_sectional]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Uniform reverse curvature transfer.  For a flow limit and a               *)
(* compact K with |sec| <= B on the limit slices of [a,b], for large k every *)
(* plane at every point phi k z (z IN K) of the view has rescaled sectional *)
(* curvature within alpha of a sectional curvature of the limit at z (the   *)
(* proof of LIM_VIEW_RM_BOUND of pc_lim_vol, which keeps only the upper     *)
(* bound; here the point estimate LIM_POINT_SEC_REV is kept as it is).      *)
(* ------------------------------------------------------------------------- *)

let RFA_C944_VIEW_SEC = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi a b K B alpha.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     real_interval[a,b] SUBSET J /\
     (!s. a <= s /\ s <= b ==> riemannian_metric atlas (g s)) /\
     compact_in top K /\ &0 <= B /\ &0 < alpha /\
     (!s z u v. a <= s /\ s <= b /\ z IN K /\ ~collinear {vec 0,u,v}
                ==> abs(mfd_sectional atlas (g s) z u v) <= B)
     ==> ?k0. !k s z. k0 <= k /\ a <= s /\ s <= b /\ z IN K
                      ==> !u' v'. ~collinear {vec 0,u',v'}
                                  ==> ?u v. ~collinear {vec 0,u,v} /\
                                            abs(mfd_sectional (rfs_vatlas (V k) (t k + s / Q k))
                                                  (rfs_vmetric (V k) (t k + s / Q k))
                                                  (phi k z) u' v' / Q k -
                                                mfd_sectional atlas (g s) z u v) <= alpha`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rfa"))) THEN
  ABBREV_TAC `K0 = sqrt C * B + &1` THEN
  SUBGOAL_THEN `C * B pow 2 <= K0 pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN
    SUBGOAL_THEN `C * B pow 2 = (sqrt C * B) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `alpha:real`] (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`; `K:B->bool`; `2`; `eta pow 2 / &8`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `z:B`] THEN STRIP_TAC THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o SPEC `s:real`)
    (MP_TAC o SPECL [`s:real`; `z:B`]))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  ABBREV_TAC `VT = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VA = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VG = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  SUBGOAL_THEN `(z:B) IN W(k:num) /\ z IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:num->B->A) k z IN topspace (VT:A topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) k) (VT:A topology) (VA:((A->bool)#(A->real^3))->bool)
                   (IMAGE ((phi:num->B->A) k) (W k)) (phi k) (psi:A->B)` THEN
    REWRITE_TAC[mfd_diffeo] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (VT:A topology) VA /\ riemannian_metric VA (VG:A->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["VT"; "VA"; "VG"] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "riemannian_metric"))
          (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_vtop")) (concl th))) THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfa_rmd2 0 atlas ((g:real->B->real^3^3) s) z <= K0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * B pow 2` THEN ASM_REWRITE_TAC[rfa_rmd2] THEN
    USE_THEN "rfa" MATCH_MP_TAC THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (z:B)))
                      (FST(chart_at atlas z))` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `z:B`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM mfd_sectional] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `VT:A topology`;
                 `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`; `(W:num->B->bool) k`;
                 `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi:A->B`;
                 `(Q:num->real) k`; `K0:real`; `alpha:real`; `eta:real`; `z:B`]
                LIM_POINT_SEC_REV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&1 + inv(&1)) pow 2 *
                lck_dist2 2 (metric_local atlas (chart_at atlas (z:B)) ((g:real->B->real^3^3) s))
                  (\w. (Q:num->real) k %%
                       rfs_pullback (VA:((A->bool)#(A->real^3))->bool)
                         ((phi:num->B->A) k o chart_inv (chart_at atlas z)) (VG:A->real^3^3) w)
                  (SND(chart_at atlas z) z)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`;
                     `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`;
                     `(phi:num->B->A) k`; `psi:A->B`; `(g:real->B->real^3^3) s`;
                     `VG:A->real^3^3`; `&1`; `(Q:num->real) k`; `2`; `z:B`]
                    P2BL_LCK_CHART_CONVERT) THEN
      ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; MATRIX_CMUL_LID; ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + inv(&1)) pow 2 = &4` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x < e / &8 /\ &0 < e ==> &4 * x < e`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(ACCEPT_TAC o check (fun th -> not(is_forall(concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th)));
      ASM_SIMP_TAC[REAL_POW_LT]];
    DISCH_TAC] THEN
  FIRST_ASSUM ACCEPT_TAC);;


(* ------------------------------------------------------------------------- *)
(* The data of COR_9_44.  The views are the shifted kappa                    *)
(* views; the compact limit makes phi k onto M for large k, so M is         *)
(* compact; the round limit (curvature c0) makes tau k times the sectional  *)
(* curvature of g(t0 - tau k) uniformly close to c0 on all of M.            *)
(* ------------------------------------------------------------------------- *)

let RFA_C944_KVIEW = prove
 (`!top atlas (h:real->B->real^3^3) s.
     rfs_vtop (p2b_kview (top,atlas) h) s = (if s <= &0 then top else discrete_topology {}) /\
     rfs_vatlas (p2b_kview (top,atlas) h) s = atlas /\
     rfs_vmetric (p2b_kview (top,atlas) h) s = h s`,
  REWRITE_TAC[P2B_KVIEW_SLICE] THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vmetric]);;

let RFA_C944_ALMOST_ROUND = prove
 (`!kappa top atlas (g:real->B->real^3^3) t0 tau q (top':B topology) atlas' g' xl c0.
     p2b_kappa_solution kappa (top,atlas) g /\ t0 <= &0 /\ (!k. &0 < tau k) /\
     p3_flow_limit_on (\k. p2b_kview (top,atlas) (\t. g(t + t0))) q (\k. --(tau k))
                      (\k. inv(tau k)) {s | s < &1} (top',atlas') g' xl /\
     compact_space top' /\ riemannian_metric atlas' (g'(&0)) /\ &0 < c0 /\
     (!x u v. x IN topspace top' /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas' (g'(&0)) x u v = c0)
     ==> compact_space top /\
         !alpha. &0 < alpha
            ==> ?k0. !k x u v. k0 <= k /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                      ==> abs(tau k * mfd_sectional atlas (g(t0 - tau k)) x u v - c0)
                          <= alpha`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\ smooth_manifold_atlas top atlas /\
                connected_space top /\ ~(topspace top = {}) /\
                (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= &0 ==> riemannian_metric atlas ((g:real->B->real^3^3) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2C_FLOW_LIMIT_ON_WITH] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_flow_limit_on")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` (LABEL_TAC "lim"))) THEN
  USE_THEN "lim" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `~(topspace (top':B topology) = {}) /\ compact_in top' (topspace top')`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM compact_space; GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the views are smooth Riemannian *)
  SUBGOAL_THEN
   `!n tau'. ~(topspace(rfs_vtop ((\k:num. p2b_kview (top,atlas) (\t. (g:real->B->real^3^3)
                                     (t + t0))) n) tau') = {})
             ==> smooth_manifold_atlas
                   (rfs_vtop ((\k:num. p2b_kview (top,atlas) (\t. g(t + t0))) n) tau')
                   (rfs_vatlas ((\k:num. p2b_kview (top,atlas) (\t. g(t + t0))) n) tau') /\
                 riemannian_metric
                   (rfs_vatlas ((\k:num. p2b_kview (top,atlas) (\t. g(t + t0))) n) tau')
                   (rfs_vmetric ((\k:num. p2b_kview (top,atlas) (\t. g(t + t0))) n) tau')`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[RFA_C944_KVIEW] THEN
    COND_CASES_TAC THEN REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* for large k, phi k maps the whole limit onto M *)
  SUBGOAL_THEN `?k1. !k. k1 <= k ==> IMAGE ((phi:num->B->B) k) (topspace top') = topspace top /\
                                     compact_space top`
  (X_CHOOSE_THEN `k1:num` (LABEL_TAC "onto")) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `&0`; `topspace top':B->bool`; `0`; `&1`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
    REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET; IN_ELIM_THM; REAL_LT_01] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k1:num` THEN
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `&0` o CONJUNCT1)) THEN
    REWRITE_TAC[REAL_LE_REFL; RFA_C944_KVIEW; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    SUBGOAL_THEN `(W:num->B->bool) k = topspace top'` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `--((tau:num->real) k) <= &0` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x <= &0`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `psi:B->B`) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(phi:num->B->B) k`; `psi:B->B`] RFA_C944_ONTO) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "onto" (MP_TAC o SPEC `k1:num`) THEN SIMP_TAC[LE_REFL]; ALL_TAC] THEN
  (* the uniform estimate *)
  X_GEN_TAC `alpha:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\k:num. p2b_kview (top,atlas) (\t. (g:real->B->real^3^3)(t + t0))`;
                 `q:num->B`; `\k:num. --((tau:num->real) k)`; `\k:num. inv((tau:num->real) k)`;
                 `{s:real | s < &1}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
                 `&0`; `&0`; `topspace top':B->bool`; `c0:real`; `alpha:real`]
                RFA_C944_VIEW_SEC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "lim" ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `z:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `MAX k0 k1` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `x:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  USE_THEN "onto" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `MAX k0 k1 <= k` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `?z. z IN topspace top' /\ x = (phi:num->B->B) k z` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:B) IN topspace top` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "k0" (MP_TAC o SPECL [`k:num`; `&0`; `z:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN UNDISCH_TAC `MAX k0 k1 <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (X_CHOOSE_THEN `v0:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `mfd_sectional atlas' ((g':real->B->real^3^3) (&0)) z u0 v0 = c0`
  ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (dest_binary "real_le") (concl th) &&
    rand(concl th) = `alpha:real`)) THEN
  ASM_REWRITE_TAC[RFA_C944_KVIEW; real_div; REAL_MUL_LZERO; REAL_ADD_RID; REAL_INV_INV] THEN
  SUBGOAL_THEN `t0 - (tau:num->real) k = --(tau k) + t0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* From almost round slices at times t0 - tau k -> -infinity:                *)
(* sec > 0 for t < 0 (RFA_P2_THM_4_23 forward from such a slice) and the    *)
(* (1 + e)-pinching of R-PINCH3; the round slices for t < 0 give a round    *)
(* slice at 0 (left continuity at 0 and mfd_rm_norm > 0 at time 0).          *)
(* ------------------------------------------------------------------------- *)

let RFA_C944_PINCH_ARITH = prove
 (`!tau c0 e s1 s2.
     &0 < tau /\ &0 < c0 /\ &0 < e /\
     abs(tau * s1 - c0) <= e * c0 / (&2 + e) /\ abs(tau * s2 - c0) <= e * c0 / (&2 + e)
     ==> s1 <= (&1 + e) * s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = e * c0 / (&2 + e)` THEN
  SUBGOAL_THEN `a * (&2 + e) = e * c0` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `tau * s1 <= tau * ((&1 + e) * s2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + e) * (c0 - a)` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + e) * (tau * s2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

let RFA_C944_SEC_POS = prove
 (`!top atlas (g:real->B->real^3^3) t0 tau c0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     connected_space top /\ ~(topspace top = {}) /\
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     t0 <= &0 /\ (!k. &0 < (tau:num->real) k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
     &0 < c0 /\
     (!alpha. &0 < alpha
          ==> ?k0. !k x u v. k0 <= k /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> abs(tau k * mfd_sectional atlas (g(t0 - tau k)) x u v - c0)
                        <= alpha)
     ==> !t x u v. t < &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                   ==> &0 < mfd_sectional atlas (g t) x u v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "div")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ar"))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  USE_THEN "ar" (MP_TAC o SPEC `c0 / &2`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  USE_THEN "div" (MP_TAC o SPEC `t0 - t:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  SUBGOAL_THEN `t0 - t < (tau:num->real) (MAX k0 N) /\ &0 < tau (MAX k0 N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [USE_THEN "N" MATCH_MP_TAC THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* sec > 0 at the time t0 - tau(MAX k0 N) *)
  SUBGOAL_THEN
   `!y u' v'. y IN topspace top /\ ~collinear {vec 0,u',v'}
              ==> &0 < mfd_sectional atlas
                         ((g:real->B->real^3^3) (t0 - (tau:num->real) (MAX k0 N))) y u' v'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `abs((tau:num->real) (MAX k0 N) *
          mfd_sectional atlas ((g:real->B->real^3^3) (t0 - tau (MAX k0 N))) y u' v' - c0)
      <= c0 / &2`
    ASSUME_TAC THENL
     [USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < (tau:num->real) (MAX k0 N) *
           mfd_sectional atlas ((g:real->B->real^3^3) (t0 - tau (MAX k0 N))) y u' v'`
    MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ];
    ALL_TAC] THEN
  (* forward by RFA_P2_THM_4_23 *)
  MP_TAC(SPEC `{}:B->bool` (INST_TYPE [`:B`,`:A`] RFA_P2_THM_4_23)) THEN
  REWRITE_TAC[P2_THM_4_23_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `t0 - (tau:num->real) (MAX k0 N)`; `&0`; `g:real->B->real^3^3`;
                             `topspace top:B->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CF_RFO_FROM THEN
      MAP_EVERY EXISTS_TAC [`t0 - (tau:num->real) (MAX k0 N) - &1`; `&0`] THEN
      USE_THEN "upto" (MP_TAC o SPEC `t0 - (tau:num->real) (MAX k0 N) - &1`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[rfs_flow_upto] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `connected_components_of top = {topspace top:B->bool}` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[CONNECTED_COMPONENTS_OF_EQ_SING]; REWRITE_TAC[IN_SING]]];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RFA_C944_PINCHED = prove
 (`!top atlas (g:real->B->real^3^3) t0 tau c0.
     t0 <= &0 /\ (!k. &0 < (tau:num->real) k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
     &0 < c0 /\
     (!alpha. &0 < alpha
          ==> ?k0. !k x u v. k0 <= k /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> abs(tau k * mfd_sectional atlas (g(t0 - tau k)) x u v - c0)
                        <= alpha)
     ==> !e T1. &0 < e
                ==> ?t. t < T1 /\ t < &0 /\
                       !x y u v u' v'. x IN topspace top /\ y IN topspace top /\
                                       ~collinear {vec 0,u,v} /\ ~collinear {vec 0,u',v'}
                                       ==> mfd_sectional atlas (g t) x u v <=
                                           (&1 + e) * mfd_sectional atlas (g t) y u' v'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "div") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ar"))))) THEN
  MAP_EVERY X_GEN_TAC [`e:real`; `T1:real`] THEN DISCH_TAC THEN
  USE_THEN "ar" (MP_TAC o SPEC `e * c0 / (&2 + e)`) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_ARITH `&0 < e ==> &0 < &2 + e`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  USE_THEN "div" (MP_TAC o SPEC `t0 - T1:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  SUBGOAL_THEN `t0 - T1 < (tau:num->real) (MAX k0 N) /\ &0 < tau (MAX k0 N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [USE_THEN "N" MATCH_MP_TAC THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `t0 - (tau:num->real) (MAX k0 N)` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_C944_PINCH_ARITH THEN
  MAP_EVERY EXISTS_TAC [`(tau:num->real) (MAX k0 N)`; `c0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let RFA_C944_ROUND0 = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g /\
     (!t. t < &0 ==> ?k. &0 < k /\
                         !x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                                 ==> mfd_sectional atlas (g t) x u v = k)
     ==> p2b_round (top,atlas) (g(&0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "rnd")) THEN
  SUBGOAL_THEN `?x0. x0 IN topspace top /\
                     &0 < mfd_rm_norm atlas ((g:real->B->real^3^3) (&0)) x0`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
            ==> mfd_sectional atlas ((g:real->B->real^3^3) (&0)) x u v =
                mfd_sectional atlas (g(&0)) x0 (basis 1) (basis 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(a - b)) ==> a = b`) THEN DISCH_TAC THEN
    ABBREV_TAC `e = abs(mfd_sectional atlas ((g:real->B->real^3^3) (&0)) x u v -
                        mfd_sectional atlas (g(&0)) x0 (basis 1) (basis 2))` THEN
    SUBGOAL_THEN `rfs_flow_upto (top,atlas) (--(&1)) (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `--(&1)`; `&0`;
                   `g:real->B->real^3^3`; `x:B`; `u:real^3`; `v:real^3`]
                  RFA_C944_SEC_LEFT_CONT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1"))) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `--(&1)`; `&0`;
                   `g:real->B->real^3^3`; `x0:B`; `basis 1:real^3`; `basis 2:real^3`]
                  RFA_C944_SEC_LEFT_CONT) THEN
    ASM_REWRITE_TAC[LIM_NONCOLLINEAR_BASIS] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2"))) THEN
    ABBREV_TAC `t = --(min d1 d2) / &2` THEN
    SUBGOAL_THEN `t < &0 /\ &0 - d1 < t /\ &0 - d2 < t /\ t <= &0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "rnd" (fun th -> MP_TAC(MP (SPEC `t:real` th) (ASSUME `t < &0`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `kt:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kt"))) THEN
    SUBGOAL_THEN `mfd_sectional atlas ((g:real->B->real^3^3) t) x u v = kt /\
                  mfd_sectional atlas (g t) x0 (basis 1) (basis 2) = kt`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "kt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIM_NONCOLLINEAR_BASIS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(mfd_sectional atlas ((g:real->B->real^3^3) t) x u v -
          mfd_sectional atlas (g(&0)) x u v) < e / &2 /\
      abs(mfd_sectional atlas (g t) x0 (basis 1) (basis 2) -
          mfd_sectional atlas (g(&0)) x0 (basis 1) (basis 2)) < e / &2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [USE_THEN "d1" MATCH_MP_TAC; USE_THEN "d2" MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = mfd_sectional atlas ((g:real->B->real^3^3) (&0)) x0 (basis 1) (basis 2)` THEN
  SUBGOAL_THEN `mfd_rm_norm atlas ((g:real->B->real^3^3) (&0)) x0 = abs L` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_rm_norm] THEN
    SUBGOAL_THEN
     `{abs(mfd_sectional atlas ((g:real->B->real^3^3) (&0)) x0 u v) | u,v |
       ~collinear {vec 0,u,v}} = {abs L}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `r:real` THEN
      EQ_TAC THENL
       [STRIP_TAC THEN ASM_SIMP_TAC[];
        DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`basis 1:real^3`; `basis 2:real^3`] THEN
        ASM_REWRITE_TAC[LIM_NONCOLLINEAR_BASIS]];
      REWRITE_TAC[SUP_SING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional")) (concl th) &&
      can (find_term ((=) `(<=):real->real->bool`)) (concl th) &&
      not (can (find_term ((=) `x0:B`)) (concl th)))) THEN
    ASM_REWRITE_TAC[LIM_NONCOLLINEAR_BASIS; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[p2b_round] THEN EXISTS_TAC `L:real` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < mfd_rm_norm atlas ((g:real->B->real^3^3) (&0)) x0` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The main theorem RFA_P2B_COR_9_44_ROUTE.                                  *)
(* ------------------------------------------------------------------------- *)

let RFA_P2B_COR_9_44_ROUTE = prove
 (`!w:B->bool. P2B_COR_9_44_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_COR_9_44_ROUTE_STATEMENT; P2B_COR_9_44_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "pinch") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p2b_round (top',atlas') ((g':real->B->real^3^3) (&0))` THEN
  GEN_REWRITE_TAC LAND_CONV [p2b_round] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `t0:real`; `tau:num->real`; `q:num->B`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `c0:real`] RFA_C944_ALMOST_ROUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\ smooth_manifold_atlas top atlas /\
                connected_space top /\ ~(topspace top = {}) /\
                (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `t0:real`; `tau:num->real`; `c0:real`]
                RFA_C944_SEC_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `t0:real`; `tau:num->real`; `c0:real`]
                RFA_C944_PINCHED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "pinch" (MP_TAC o REWRITE_RULE[P2B_REQ_PINCH_ROUND3_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `g:real->B->real^3^3`; `&0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th))) THEN
    ASM_SIMP_TAC[rfs_flow_upto];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_C944_ROUND0 THEN EXISTS_TAC `kappa:real` THEN
  ASM_REWRITE_TAC[]);;

