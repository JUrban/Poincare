(* ========================================================================= *)
(* L5 of the limit-geometry layer (the statement LIM_CURV_STATEMENT of       *)
(* pc_lim_stmts).                                                            *)
(*   LIM_CURV |- !u w. LIM_CURV_STATEMENT u w: the scalar curvature of the  *)
(*     views at phi k y, divided by Q k, converges to that of the limit at  *)
(*     y; lower and upper sectional bounds of the rescaled views pass to   *)
(*     the limit.                                                           *)
(* Route: in the chart at y, the C^2 closeness of the clause of             *)
(* p2c_flow_limit_with (P2BL_LCK_CHART_CONVERT) and LCK_CURVATURE_STABILITY, *)
(* with the pullback identities P2B9S_PB_SCALAR and P2B9S_PB_SECTIONAL.     *)
(* ========================================================================= *)

needs "src/pc_lim_stmts.ml";;
needs "src/pc_lim_dist.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_rfa_mfd.ml";;

prioritize_real();;
type_invention_error := true;;
(* Curvature at one point under a diffeomorphism whose pullback metric,    *)
(* scaled by Q, is C^2-close to the metric at y in the chart at y.          *)

let LIM_POINT_CURV = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' Q K0 alpha eta y.
     (!s (G0:real^3->real^3^3) G y.
         metric_field s G0 /\ metric_field s G /\ y IN s /\
         lrm_deriv_norm2 0 G0 y <= K0 pow 2 /\ lck_dist2 2 G0 G y < eta pow 2
         ==> abs(lscalar G y - lscalar G0 y) <= alpha /\
             (!w. abs(lricci G y w w - lricci G0 y w w) <= alpha * (w dot (G0 y ** w))) /\
             (!u v. ~collinear {vec 0,u,v}
                    ==> abs(lsectional G y u v - lsectional G0 y u v) <= alpha)) /\
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U /\ &0 < Q /\
     rfa_rmd2 0 atlas g y <= K0 pow 2 /\
     lck_dist2 2 (metric_local atlas (chart_at atlas y) g)
                 (metric_local atlas (chart_at atlas y)
                    (\z. Q %% mfd_pullback_metric atlas atlas' psi g' z))
                 (SND(chart_at atlas y) y) < eta pow 2
     ==> abs(mfd_scalar atlas' g' (psi y) / Q - mfd_scalar atlas g y) <= alpha /\
         (!u v. ~collinear {vec 0,u,v}
                ==> ?u' v'. ~collinear {vec 0,u',v'} /\
                            abs(mfd_sectional atlas' g' (psi y) u' v' / Q -
                                mfd_sectional atlas g y u v) <= alpha)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `g':B->real^3^3`; `y:A`] P2B9S_PB_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `P:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `g':B->real^3^3`; `y:A`] P2B9S_PB_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `g':B->real^3^3`; `y:A`] P2B9S_PB_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sec" o CONJUNCT1) THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)` THEN
  ABBREV_TAC `p = SND (c:(A->bool)#(A->real^3)) y` THEN
  ABBREV_TAC `Lg = metric_local (atlas:((A->bool)#(A->real^3))->bool) c (g:A->real^3^3)` THEN
  ABBREV_TAC `Lp = metric_local (atlas:((A->bool)#(A->real^3))->bool) c
                     (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3))` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                             (Lg:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Lg" THEN
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = P INTER IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  SUBGOAL_THEN `(p:real^3) IN s0 /\ metric_field s0 (Lg:real^3->real^3^3) /\
                metric_field s0 (\z. Q %% (Lp:real^3->real^3^3) z) /\
                metric_field s0 (Lp:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))` ASSUME_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    SUBGOAL_THEN `open (s0:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "s0" THEN MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_field s0 (Lp:real^3->real^3^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `P:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s0" THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LRG_METRIC_FIELD_SCALE] THEN CONJ_TAC THENL
     [EXPAND_TAC "s0" THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        EXPAND_TAC "p" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s0" THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "D" (MP_TAC o SPECL [`s0:real^3->bool`; `Lg:real^3->real^3^3`;
                                  `\z. Q %% (Lp:real^3->real^3^3) z`; `p:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfa_rmd2")) (concl th))) THEN
      REWRITE_TAC[rfa_rmd2] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_forall(concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
      REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "stab"))) THEN
  MP_TAC(ISPECL [`s0:real^3->bool`; `Lp:real^3->real^3^3`; `Q:real`; `p:real^3`]
                P2C_SCALE_QUANTITIES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) y = lscalar (Lg:real^3->real^3^3) (p:real^3) /\
                mfd_scalar atlas (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3)) y =
                lscalar (Lp:real^3->real^3^3) p`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mfd_scalar] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_pullback_metric"))
          (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar")) (concl th) &&
      not (can (find_term ((=) `Lp:real^3->real^3^3`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Q * lscalar (\z. Q %% (Lp:real^3->real^3^3) z) (p:real^3)) / Q =
                  lscalar (\z. Q %% Lp z) p` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  USE_THEN "sec" (MP_TAC o C MATCH_MP (ASSUME `~collinear {vec 0,u:real^3,v}`) o
                  SPECL [`u:real^3`; `v:real^3`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u':real^3`; `v':real^3`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    can (find_term ((=) `u':real^3`)) (concl th) && is_eq(concl th))) THEN
  USE_THEN "stab" (MP_TAC o C MATCH_MP (ASSUME `~collinear {vec 0,u:real^3,v}`) o
                   SPECL [`u:real^3`; `v:real^3`]) THEN
  MP_TAC(ISPECL [`s0:real^3->bool`; `Lp:real^3->real^3^3`; `Q:real`; `p:real^3`;
                 `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The key estimate and the theorem L5 (LIM_CURV).                           *)
(* ========================================================================= *)
(* The key estimate of L5 at one time s and one point y, for every alpha.  *)

let LIM_CURV_KEY = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi s y.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     s IN J /\ y IN topspace top /\ riemannian_metric atlas (g s)
     ==> !alpha. &0 < alpha
            ==> ?k0. !k. k0 <= k
                   ==> (phi:num->B->A) k y IN topspace (rfs_vtop (V k) (t k + s / Q k)) /\
                       abs(mfd_scalar (rfs_vatlas (V k) (t k + s / Q k))
                                      (rfs_vmetric (V k) (t k + s / Q k)) (phi k y) / Q k -
                           mfd_scalar atlas ((g:real->B->real^3^3) s) y) <= alpha /\
                       (!u v. ~collinear {vec 0,u,v}
                              ==> ?u' v'. ~collinear {vec 0,u',v'} /\
                                          abs(mfd_sectional (rfs_vatlas (V k) (t k + s / Q k))
                                                (rfs_vmetric (V k) (t k + s / Q k))
                                                (phi k y) u' v' / Q k -
                                              mfd_sectional atlas (g s) y u v) <= alpha)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
X_GEN_TAC `alpha:real` THEN DISCH_TAC THEN
    ABBREV_TAC `K0 = abs(rfa_rmd2 0 atlas ((g:real->B->real^3^3) s) y) + &1` THEN
    SUBGOAL_THEN `rfa_rmd2 0 atlas ((g:real->B->real^3^3) s) y <= K0 pow 2` ASSUME_TAC THENL
     [EXPAND_TAC "K0" THEN
      MATCH_MP_TAC(REAL_ARITH `x <= abs x + &1 /\ abs x + &1 <= (abs x + &1) pow 2
                               ==> x <= (abs x + &1) pow 2`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * a <= a * a ==> a <= a * a`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`K0:real`; `alpha:real`] (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `s:real`; `{y:B}`; `2`; `eta pow 2 / &8`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET; COMPACT_IN_SING] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
    EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o SPEC `s:real`)
      (MP_TAC o SPECL [`s:real`; `y:B`]))) THEN
    REWRITE_TAC[REAL_LE_REFL; IN_SING] THEN DISCH_TAC THEN
    DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
    ABBREV_TAC `VT = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) k) (t k + s / Q k)` THEN
    ABBREV_TAC `VA = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) k) (t k + s / Q k)` THEN
    ABBREV_TAC `VG = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) k) (t k + s / Q k)` THEN
    SUBGOAL_THEN `(y:B) IN W(k:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(phi:num->B->A) k y IN topspace (VT:A topology)` ASSUME_TAC THENL
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
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `VT:A topology`;
                   `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`; `(W:num->B->bool) k`;
                   `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi:A->B`;
                   `(Q:num->real) k`; `K0:real`; `alpha:real`; `eta:real`; `y:B`]
                  LIM_POINT_CURV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(&1 + inv(&1)) pow 2 *
                  lck_dist2 2 (metric_local atlas (chart_at atlas (y:B)) ((g:real->B->real^3^3) s))
                    (\z. (Q:num->real) k %%
                         rfs_pullback (VA:((A->bool)#(A->real^3))->bool)
                           ((phi:num->B->A) k o chart_inv (chart_at atlas y)) (VG:A->real^3^3) z)
                    (SND(chart_at atlas y) y)` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`;
                       `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`;
                       `(phi:num->B->A) k`; `psi:A->B`; `(g:real->B->real^3^3) s`;
                       `VG:A->real^3^3`; `&1`; `(Q:num->real) k`; `2`; `y:B`]
                      P2BL_LCK_CHART_CONVERT) THEN
        ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; MATRIX_CMUL_LID; ETA_AX];
        ALL_TAC] THEN
      SUBGOAL_THEN `(&1 + inv(&1)) pow 2 = &4` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_forall(concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < eta pow 2` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_LT]; REAL_ARITH_TAC];
      SIMP_TAC[]]);;
(* L5: pointwise transfer of scalar and sectional curvature.               *)

let LIM_CURV = prove
 (`!u:A->bool w:B->bool. LIM_CURV_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `y:B`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `s:real`; `y:B`] LIM_CURV_KEY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "key")] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "key" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:real` THEN DISCH_THEN(X_CHOOSE_TAC `k1:num`) THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_LE_LIMIT THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_POS] THEN
    X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    USE_THEN "key" (MP_TAC o C MATCH_MP (ASSUME `&0 < h`) o SPEC `h:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (MP_TAC o SPEC `MAX k0 k1`)) THEN
    REWRITE_TAC[ARITH_RULE `k0 <= MAX k0 k1`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
      (MP_TAC o C MATCH_MP (ASSUME `~collinear {vec 0,u:real^3,v}`) o SPECL [`u:real^3`; `v:real^3`]))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`MAX k0 k1`; `(phi:num->B->A) (MAX k0 k1) y`;
                                  `u':real^3`; `v':real^3`]) THEN
    ASM_REWRITE_TAC[ARITH_RULE `k1 <= MAX k0 k1`] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:real` THEN DISCH_THEN(X_CHOOSE_TAC `k1:num`) THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x <= c <=> --c <= --x`] THEN
    MATCH_MP_TAC LIM_LE_LIMIT THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_POS] THEN
    X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    USE_THEN "key" (MP_TAC o C MATCH_MP (ASSUME `&0 < h`) o SPEC `h:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (MP_TAC o SPEC `MAX k0 k1`)) THEN
    REWRITE_TAC[ARITH_RULE `k0 <= MAX k0 k1`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
      (MP_TAC o C MATCH_MP (ASSUME `~collinear {vec 0,u:real^3,v}`) o SPECL [`u:real^3`; `v:real^3`]))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`MAX k0 k1`; `(phi:num->B->A) (MAX k0 k1) y`;
                                  `u':real^3`; `v':real^3`]) THEN
    ASM_REWRITE_TAC[ARITH_RULE `k1 <= MAX k0 k1`] THEN ASM_REAL_ARITH_TAC]);;

