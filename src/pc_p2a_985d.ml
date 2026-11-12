(* ========================================================================= *)
(* pc_p2a_985d: COR_9_94_L piece (b) part (2), the lower curvature bound,    *)
(* and the route theorem |- !w. P2B_PROP_9_85L_ROUTE_STATEMENT w.  By        *)
(* contradiction: points x n in the D-balls with K(x n) <=                   *)
(* R(p n) / (n + 2); R(p n) and R(x n) are comparable (LEMMA_9_65            *)
(* both ways); the THM_9_64 limit at x n is positively curved: (a) leaves    *)
(* the cylinder model, its one-to-one form would make p n a strong neck      *)
(* centre ((h) and the neck transfer), its Z/2 form is excluded by           *)
(* Z2X_EXCLUSION (souls at bounded distance, from P2A985C_PART1); then the   *)
(* curvature at the base point passes back to x n (the reverse direction of  *)
(* LIM_CURV_KEY), against K(x n) / R(x n) -> 0.                              *)
(* ========================================================================= *)

needs "src/pc_p2a_985c.ml";;
needs "src/pc_z2x_excl.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Geodesics, the exponential map and the regularity of distance functions *)
(* do not change under a constant scaling of the metric                    *)
(* (CHRISTOFFEL_SCALE, METRIC_LOCAL_CMUL, MFD_DIST_SCALE).                 *)
(* ========================================================================= *)

let P2A985D_GEODESIC_CMUL = prove
 (`!top atlas (g:B->real^3^3) Q gamma J.
     riemannian_metric atlas g /\ &0 < Q
     ==> (mfd_geodesic (top,atlas) (\z. Q %% g z) gamma J <=>
          mfd_geodesic (top,atlas) g gamma J)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_geodesic; METRIC_LOCAL_CMUL] THEN
  SUBGOAL_THEN
   `!c t u v. c IN atlas /\ (gamma:real->B) t IN FST c
              ==> christoffel (\y. Q %% metric_local atlas c (g:B->real^3^3) y)
                              (SND c (gamma t)) u v =
                  christoffel (metric_local atlas c g) (SND c (gamma t)) u v`
  (fun th -> SIMP_TAC[th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SCALE THEN
  EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  UNDISCH_TAC `riemannian_metric atlas (g:B->real^3^3)` THEN REWRITE_TAC[riemannian_metric] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2A985D_EXP_CMUL = prove
 (`!top atlas (g:B->real^3^3) Q x.
     riemannian_metric atlas g /\ &0 < Q
     ==> mfd_exp_dom (top,atlas) (\z. Q %% g z) x = mfd_exp_dom (top,atlas) g x /\
         !w. mfd_exp (top,atlas) (\z. Q %% g z) x w = mfd_exp (top,atlas) g x w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[mfd_exp_dom; mfd_exp; mfd_geo; mfd_geo_maxint; P2A985D_GEODESIC_CMUL]);;

let P2A985D_DIST_REGULAR_CMUL = prove
 (`!top atlas (g:B->real^3^3) Q p x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < Q /\
     mfd_joinable (top,atlas) x p
     ==> (p2b_dist_regular (top,atlas) (\z. Q %% g z) p x <=>
          p2b_dist_regular (top,atlas) g p x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2b_dist_regular] THEN
  ASM_SIMP_TAC[P2A985D_EXP_CMUL; MFD_DIST_SCALE; mfd_tnorm; MATRIX_VECTOR_LMUL; DOT_RMUL;
               SQRT_MUL; REAL_EQ_MUL_LCANCEL; SQRT_EQ_0; REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `!a. Q * a < &0 <=> a < &0` (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(SPEC `Q:real` REAL_MUL_RZERO)] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ]);;

(* ========================================================================= *)
(* The reverse direction of the pointwise curvature transfer: every plane   *)
(* at phi k y has sectional curvature (over Q k) close to that of some      *)
(* plane at y in the limit.  Adapted copies of LIM_POINT_CURV and           *)
(* LIM_CURV_KEY of pc_lim_curv: the second half of P2B9S_PB_SECTIONAL       *)
(* replaces the first, the scalar part is dropped; otherwise the proofs are *)
(* the same.                                                                *)
(* ========================================================================= *)

(* from pc_lim_curv.ml (LIM_POINT_CURV) *)
let P2A985D_POINT_CURV_REV = prove
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
     ==> (!u' v'. ~collinear {vec 0,u',v'}
                  ==> ?u v. ~collinear {vec 0,u,v} /\
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
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sec" o CONJUNCT2) THEN
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
  MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`] THEN DISCH_TAC THEN
  USE_THEN "sec" (MP_TAC o C MATCH_MP (ASSUME `~collinear {vec 0,u':real^3,v'}`) o
                  SPECL [`u':real^3`; `v':real^3`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "stab" (MP_TAC o C MATCH_MP (ASSUME `~collinear {vec 0,u:real^3,v}`) o
                   SPECL [`u:real^3`; `v:real^3`]) THEN
  MP_TAC(ISPECL [`s0:real^3->bool`; `Lp:real^3->real^3^3`; `Q:real`; `p:real^3`;
                 `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[]);;

(* from pc_lim_curv.ml (LIM_CURV_KEY) *)
let P2A985D_CURV_KEY_REV = prove
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
                       (!u' v'. ~collinear {vec 0,u',v'}
                                ==> ?u v. ~collinear {vec 0,u,v} /\
                                          abs(mfd_sectional (rfs_vatlas (V k) (t k + s / Q k))
                                                (rfs_vmetric (V k) (t k + s / Q k))
                                                (phi k y) u' v' / Q k -
                                              mfd_sectional atlas ((g:real->B->real^3^3) s) y u v)
                                          <= alpha)`,
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
                  P2A985D_POINT_CURV_REV) THEN
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

(* ========================================================================= *)
(* The THM_9_64 limit at x k in both forms (unscaled views with scales Q k, *)
(* and the rescaled flows with scale 1; adapted from P2AL84_THM964_AT of    *)
(* pc_p2a_l984 with Q a parameter); the neck transfer from a limit all of   *)
(* whose points are necks to points at rescaled distance <= rho (the second *)
(* half of P2AS85_CYL_TRANSFER); the Z/2 model is no limit at x k when      *)
(* souls stay at bounded rescaled distance (Z2X_EXCLUSION on the rescaled   *)
(* flows, P2A985D_DIST_REGULAR_CMUL for the souls).                         *)
(* ========================================================================= *)

let P2A985D_THM964_BOTH = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) (x:num->B) Q.
     P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_83K_STATEMENT w /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
          x k IN topspace (top k)) /\
     (!k. Q k = mfd_scalar (atlas k) (g k (&0)) (x k))
     ==> ?sub (top':B topology) atlas' g' xl.
           p3_subseq sub /\
           (!Tl. &0 < Tl
                 ==> p3_flow_limit (\k. p2b_kview (top (sub k),atlas (sub k)) (g (sub k)))
                                   (x o sub) (\k. &0) (\k. Q (sub k)) (top',atlas') g' xl Tl) /\
           (!Tl. &0 < Tl
                 ==> p3_flow_limit
                       (\k. p2b_kview (top (sub k),atlas (sub k))
                                      (\t y. Q (sub k) %% g (sub k) (t / Q (sub k)) y))
                       (x o sub) (\k. &0) (\k. &1) (top',atlas') g' xl Tl) /\
           p2b_kappa_solution kappa (top',atlas') g' /\ p2b_ksep top' atlas' /\
           mfd_scalar atlas' (g'(&0)) xl = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "seq") (LABEL_TAC "Qdef")))) THEN
  SUBGOAL_THEN
   `!k. &0 < (Q:num->real) k /\
        mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0)) ((x:num->B) k) / Q k = &1`
  (LABEL_TAC "Qpos") THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "Qdef" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `&0 < mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                      ((g:num->real->B->real^3^3) k (&0)) ((x:num->B) k)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2AL84_R_POS THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `(top:num->B topology) k`] THEN
      USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_DIV_REFL THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REMOVE_THEN "Qdef" (K ALL_TAC) THEN
  REWRITE_TAC[P2B_THM_9_64_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`kappa:real`; `top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
    `\k t y. (Q:num->real) k %% (g:num->real->B->real^3^3) k (t / Q k) y`; `x:num->B`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "seq" (MP_TAC o SPEC `0`) THEN
      REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "Qpos" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_C971_KSOL_SCALE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN REWRITE_TAC[GSYM real_div] THEN
    MP_TAC(ISPECL [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                   `(g:num->real->B->real^3^3) k (&0)`; `(Q:num->real) k`; `(x:num->B) k`]
                  RFA_C971_SCALAR_SCALE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `Tl:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\k. (top:num->B topology) ((sub:num->num) k)`;
                 `\k. (atlas:num->((B->bool)#(B->real^3))->bool) ((sub:num->num) k)`;
                 `\k. (g:num->real->B->real^3^3) ((sub:num->num) k)`;
                 `(x:num->B) o (sub:num->num)`;
                 `\k. (Q:num->real) ((sub:num->num) k)`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `Tl:real`] P2AL84_LIMIT_RESCALE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]]);;

(* A limit all of whose points are necks: points at rescaled distance <= rho *)
(* are eps-neck centres of length L for k large.                            *)

let P2A985D_NECKS_TRANSFER = prove
 (`?epsN. &0 < epsN /\
     !(top:num->B topology) atlas (g:num->real->B->real^3^3) (y0:num->B) Q kappa
      (top':B topology) atlas' g' yl eps L (q:num->B) N rho.
        (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ y0 k IN topspace (top k)) /\
        (!Tl. &0 < Tl
              ==> p3_flow_limit (\k. p2b_kview (top k,atlas k) (g k)) y0 (\k. &0) Q
                                (top',atlas') g' yl Tl) /\
        p2b_kappa_solution kappa (top',atlas') g' /\
        (!z. z IN topspace top' ==> &0 < mfd_scalar atlas' (g'(&0)) z) /\
        (!delta L' t z. &0 < delta /\ &1 <= L' /\ t <= &0 /\ z IN topspace top'
                        ==> ?e. rfs_evolving_neck (p2b_kview (top',atlas') g') delta z t L' e) /\
        &0 < eps /\ eps <= epsN /\ &1 <= L /\
        (!k. q k IN topspace (top k)) /\
        (!k. N <= k
             ==> sqrt(Q k) * mfd_dist (top k,atlas k) (g k (&0)) (y0 k) (q k) <= rho)
        ==> ?k0. !k. k0 <= k
                     ==> ?e. rfs_evolving_neck (p2b_kview (top k,atlas k) (g k)) eps (q k)
                                               (&0) L e`,
  X_CHOOSE_THEN `epsA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ann"))
    P2AS85_ANNULUS_NECKS THEN
  EXISTS_TAC `epsA:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "seq lim ksol rpos cyln ep epA L1 qin qk" THEN
  USE_THEN "ann" (MP_TAC o SPECL
    [`top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
     `g:num->real->B->real^3^3`; `y0:num->B`; `Q:num->real`; `kappa:real`; `kappa:real`;
     `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
     `yl:B`; `-- &1`; `eps:real`; `L:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "cyln" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0") o SPEC `rho:real`) THEN
  EXISTS_TAC `k0 + N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "k0" MATCH_MP_TAC THEN
  SUBGOAL_THEN `k0 <= k /\ N <= k:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `k0 + N <= k:num` THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "qk" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> -- &1 + &1 <= x`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "lim" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "seq" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
               ((g:num->real->B->real^3^3) k)`)) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                 ((g:num->real->B->real^3^3) k)` THEN
  SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol]);;

(* The Z/2 model is no limit of the rescaled flows when souls stay at        *)
(* bounded rescaled distance from the base points.                           *)

let P2A985D_NO_Z2 = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) (x:num->B) Q
    (top':B topology) atlas' g' xl (s:num->B) rr (p:real^3->B) lam.
     P2B_SOUL_TOPOLOGY_STATEMENT w /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ x k IN topspace (top k) /\
          s k IN topspace (top k) /\ &0 < Q k /\
          (!z. z IN topspace (top k) /\ ~(z = s k)
               ==> p2b_dist_regular (top k,atlas k) (g k (&0)) (s k) z) /\
          sqrt(Q k) * mfd_dist (top k,atlas k) (g k (&0)) (x k) (s k) <= rr) /\
     p3_flow_limit (\k. p2b_kview (top k,atlas k) (\t y. Q k %% g k (t / Q k) y)) x
                   (\k. &0) (\k. &1) (top',atlas') g' xl (&1) /\
     riemannian_metric atlas' (g'(&0)) /\ mfd_complete (top',atlas') (g'(&0)) /\ &0 < lam /\
     IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top' /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top' atlas' (ball(y,r)) p) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y \/ z = rfs_twist y)) /\
     (!t y. t <= &0 /\ ~(y = vec 0)
            ==> rfs_pullback atlas' p (g' t) y = lam %% cylinder_flow (t / lam) y)
     ==> F`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "soul seq lim riem comp lam im par two pb" THEN
  SUBGOAL_THEN
   `!k. p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
          (\t y. (Q:num->real) k %% (g:num->real->B->real^3^3) k (t / Q k) y)`
  (LABEL_TAC "kres") THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    MATCH_MP_TAC RFA_C971_KSOL_SCALE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n tau. ~(topspace(rfs_vtop (p2b_kview ((top:num->B topology) n,atlas n)
                 (\t y. (Q:num->real) n %% (g:num->real->B->real^3^3) n (t / Q n) y)) tau) = {})
             ==> smooth_manifold_atlas
                   (rfs_vtop (p2b_kview (top n,atlas n) (\t y. Q n %% g n (t / Q n) y)) tau)
                   (rfs_vatlas (p2b_kview (top n,atlas n) (\t y. Q n %% g n (t / Q n) y)) tau) /\
                 riemannian_metric
                   (rfs_vatlas (p2b_kview (top n,atlas n) (\t y. Q n %% g n (t / Q n) y)) tau)
                   (rfs_vmetric (p2b_kview (top n,atlas n) (\t y. Q n %% g n (t / Q n) y)) tau)) /\
    (!n tau. hausdorff_space
               (rfs_vtop (p2b_kview (top n,atlas n) (\t y. Q n %% g n (t / Q n) y)) tau))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `n:num` THEN
    USE_THEN "kres" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2AL84_KVIEW_SLICES) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "lim" (MP_TAC o REWRITE_RULE[P2C_FLOW_LIMIT_ON_WITH] o
                  MATCH_MP P2AL84_FLOW_LIMIT_ON) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` ASSUME_TAC)) THEN
  SUBGOAL_THEN `(&0) IN {s:real | --(&1) < s /\ s <= &0}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rr` ASSUME_TAC THENL
   [USE_THEN "seq" (MP_TAC o SPEC `0`) THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt((Q:num->real) 0) *
                mfd_dist ((top:num->B topology) 0,atlas 0) ((g:num->real->B->real^3^3) 0 (&0))
                         ((x:num->B) 0) ((s:num->B) 0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MP_TAC(MATCH_MP P2BL_KSOL_FACTS
      (ASSUME `p2b_kappa_solution kappa ((top:num->B topology) 0,atlas 0)
                 ((g:num->real->B->real^3^3) 0)`)) THEN
    STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2b_kappa_solution kappa ((top:num->B topology) 0,atlas 0)
                   ((g:num->real->B->real^3^3) 0)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  (* the souls lie in images of a compact set *)
  MP_TAC(ISPECL
    [`\k. p2b_kview ((top:num->B topology) k,atlas k)
            (\t y. (Q:num->real) k %% (g:num->real->B->real^3^3) k (t / Q k) y)`;
     `x:num->B`; `\k:num. &0`; `\k:num. &1`;
     `{s:real | --(&1) < s /\ s <= &0}`; `top':B topology`;
     `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
     `W:num->B->bool`; `phi:num->B->B`; `&0`; `rr + &1`]
    (REWRITE_RULE[LIM_BALL_STATEMENT] (ISPECL [`u:B->bool`; `w:B->bool`] LIM_BALL))) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:B->bool` (X_CHOOSE_THEN `k1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball")))) THEN
  MP_TAC(SPEC `w:B->bool` Z2X_EXCLUSION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`\k. p2b_kview ((top:num->B topology) k,atlas k)
            (\t y. (Q:num->real) k %% (g:num->real->B->real^3^3) k (t / Q k) y)`;
     `x:num->B`; `{s:real | --(&1) < s /\ s <= &0}`; `top':B topology`;
     `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
     `W:num->B->bool`; `phi:num->B->B`; `s:num->B`; `K:B->bool`; `p:real^3->B`;
     `lam:real`]) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL; P2AS85_DIV_LZERO] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "kres" (MP_TAC o SPEC `k:num`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[P2AS85_DIV_LZERO] o BETA_RULE o
               MATCH_MP P2BL_KSOL_FACTS) THEN
    MP_TAC(MATCH_MP P2BL_KSOL_FACTS
      (ASSUME `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                 ((g:num->real->B->real^3^3) k)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `connected_space ((top:num->B topology) k)` ASSUME_TAC THENL
     [UNDISCH_TAC `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                     ((g:num->real->B->real^3^3) k)` THEN
      SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_SIMP_TAC[REAL_LE_REFL; ETA_AX];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                   `(g:num->real->B->real^3^3) k (&0)`; `(Q:num->real) k`; `(s:num->B) k`;
                   `z:B`] P2A985D_DIST_REGULAR_CMUL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `k1:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2AS85_DIV_LZERO; REAL_ADD_RID; SQRT_1; REAL_INV_1; REAL_MUL_RID] THEN
    SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL; P2AS85_DIV_LZERO] THEN
    USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    MP_TAC(MATCH_MP P2BL_KSOL_FACTS
      (ASSUME `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                 ((g:num->real->B->real^3^3) k)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `mfd_joinable ((top:num->B topology) k,
                                (atlas:num->((B->bool)#(B->real^3))->bool) k)
                               ((x:num->B) k) ((s:num->B) k)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                     ((g:num->real->B->real^3^3) k)` THEN
      SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[MFD_DIST_SCALE; REAL_LE_REFL; ETA_AX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN USE_THEN "pb" (MP_TAC o SPECL [`&0`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; REWRITE_TAC[P2AS85_DIV_LZERO]]);;

(* ========================================================================= *)
(* The THM_9_64 limit at points x k is positively curved at time 0 when, at *)
(* bounded rescaled distance, there are points p k that are no strong       *)
(* eps-neck centres and souls s k: by (a) the alternative is the cylinder   *)
(* model; its one-to-one form makes every point a neck ((h)), so p k would  *)
(* be a strong neck centre for k large (P2A985D_NECKS_TRANSFER with L = 1); *)
(* its Z/2 form is P2A985D_NO_Z2.                                           *)
(* ========================================================================= *)

let P2A985D_LIMIT_POS = prove
 (`?epsP. &0 < epsP /\
     !(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) (x:num->B) Q
      (p:num->B) (s:num->B) r1 r2 (top':B topology) atlas' g' xl eps.
        P2B_PROP_9_83K_STATEMENT w /\ P2B_CYL_MODEL_NECKS_STATEMENT w /\
        P2B_SOUL_TOPOLOGY_STATEMENT w /\
        (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
             x k IN topspace (top k) /\ p k IN topspace (top k) /\ s k IN topspace (top k) /\
             Q k = mfd_scalar (atlas k) (g k (&0)) (x k) /\
             ~(?e. rfs_strong_neck (p2b_kview (top k,atlas k) (g k)) eps (p k) (&0) e) /\
             (!z. z IN topspace (top k) /\ ~(z = s k)
                  ==> p2b_dist_regular (top k,atlas k) (g k (&0)) (s k) z) /\
             sqrt(Q k) * mfd_dist (top k,atlas k) (g k (&0)) (x k) (p k) <= r1 /\
             sqrt(Q k) * mfd_dist (top k,atlas k) (g k (&0)) (x k) (s k) <= r2) /\
        (!Tl. &0 < Tl
              ==> p3_flow_limit (\k. p2b_kview (top k,atlas k) (g k)) x (\k. &0) Q
                                (top',atlas') g' xl Tl) /\
        (!Tl. &0 < Tl
              ==> p3_flow_limit (\k. p2b_kview (top k,atlas k) (\t y. Q k %% g k (t / Q k) y)) x
                                (\k. &0) (\k. &1) (top',atlas') g' xl Tl) /\
        p2b_kappa_solution kappa (top',atlas') g' /\ p2b_ksep top' atlas' /\
        &0 < eps /\ eps <= epsP
        ==> !y u v. y IN topspace top' /\ ~collinear {vec 0,u,v}
                    ==> &0 < mfd_sectional atlas' (g'(&0)) y u v`,
  X_CHOOSE_THEN `epsN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nt"))
    P2A985D_NECKS_TRANSFER THEN
  EXISTS_TAC `epsN:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "pk ch soul seq lim lim1 ksol ksep ep epN" THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa (top',atlas') (g':real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (atlas':((B->bool)#(B->real^3))->bool)
                                  ((g':real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` (LABEL_TAC "Qpos") THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `(top:num->B topology) k`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_cyl_model (top',atlas') (g':real->B->real^3^3)` MP_TAC THENL
   [USE_THEN "pk" (MP_TAC o REWRITE_RULE[P2B_PROP_9_83K_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                               `atlas':((B->bool)#(B->real^3))->bool`;
                               `g':real->B->real^3^3`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pm:real^3->B` (X_CHOOSE_THEN `lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC) ASSUME_TAC))))) o
    REWRITE_RULE[p2b_cyl_model]) THENL
   [(* one-to-one: p k would be a strong neck centre *)
    USE_THEN "ch" (MP_TAC o REWRITE_RULE[P2B_CYL_MODEL_NECKS_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                               `g':real->B->real^3^3`; `pm:real^3->B`; `lam:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "cyln")] THEN
    SUBGOAL_THEN
     `!z. z IN topspace top' ==> &0 < mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) z`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top':B topology`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "nt" (MP_TAC o SPECL
      [`top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
       `g:num->real->B->real^3^3`; `x:num->B`; `Q:num->real`; `kappa:real`;
       `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
       `xl:B`; `eps:real`; `&1`; `p:num->B`; `0`; `r1:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THEN
      X_GEN_TAC `k:num` THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (MP_TAC o SPEC `k0:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
    USE_THEN "seq" (MP_TAC o SPEC `k0:num`) THEN
    REWRITE_TAC[rfs_strong_neck] THEN ASM_REWRITE_TAC[];
    (* the Z/2 quotient *)
    SUBGOAL_THEN
     `p3_flow_limit (\k. p2b_kview ((top:num->B topology) k,atlas k)
                          (\t y. (Q:num->real) k %% (g:num->real->B->real^3^3) k (t / Q k) y))
                    (x:num->B) (\k. &0) (\k. &1) (top',atlas') (g':real->B->real^3^3) xl (&1)`
    ASSUME_TAC THENL
     [USE_THEN "lim1" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!k. p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                             ((g:num->real->B->real^3^3) k) /\
          (x:num->B) k IN topspace (top k) /\ (s:num->B) k IN topspace (top k) /\
          &0 < (Q:num->real) k /\
          (!z. z IN topspace (top k) /\ ~(z = s k)
               ==> p2b_dist_regular (top k,atlas k) (g k (&0)) (s k) z) /\
          sqrt(Q k) * mfd_dist (top k,atlas k) (g k (&0)) (x k) (s k) <= r2`
    ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      USE_THEN "Qpos" (MP_TAC o SPEC `k:num`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:num->B topology`;
                   `atlas:num->((B->bool)#(B->real^3))->bool`; `g:num->real->B->real^3^3`;
                   `x:num->B`; `Q:num->real`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                   `s:num->B`; `r2:real`; `pm:real^3->B`; `lam:real`] P2A985D_NO_Z2) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The lower curvature bound of part (2).                                   *)
(* ========================================================================= *)

let P2A985D_LOWER = prove
 (`!w:B->bool.
     P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w /\ P2B_LEMMA_9_65_STATEMENT w /\
     P2B_PROP_9_83K_STATEMENT w /\ P2B_CYL_MODEL_NECKS_STATEMENT w /\
     P2B_SOUL_TOPOLOGY_STATEMENT w
     ==> ?eps3. &0 < eps3 /\
           !eps D. &0 < eps /\ eps <= eps3 /\ &0 < D
             ==> ?D1. &1 < D1 /\
                   !kappa top atlas (g:real->B->real^3^3) p x u v.
                      p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                      ~compact_space top /\
                      (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                               ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\
                      p IN topspace top /\
                      ~(?e. rfs_strong_neck (p2b_kview (top,atlas) g) eps p (&0) e) /\
                      x IN mfd_ball (top,atlas) (g(&0)) p
                             (D * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
                      ~collinear {vec 0,u,v}
                      ==> inv D1 * mfd_scalar atlas (g(&0)) p <
                          mfd_sectional atlas (g(&0)) x u v`,
  GEN_TAC THEN INTRO_TAC "t964 p958 l965 pk ch soul" THEN
  MP_TAC(SPEC `w:B->bool` P2A985C_PART1) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1"))) THEN
  X_CHOOSE_THEN `epsP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pos")) P2A985D_LIMIT_POS THEN
  USE_THEN "p958" (X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k0sol")) o
    MATCH_MP P2AS85_KAPPA0) THEN
  EXISTS_TAC `min eps1 epsP` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `D:real`] THEN INTRO_TAC "ep ep3 D0" THEN
  SUBGOAL_THEN `eps <= eps1 /\ eps <= epsP` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "p1" (MP_TAC o SPECL [`eps:real`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Dp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Dp"))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`; `D:real`] P2AL84_LEMMA_965_SCALED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (LABEL_TAC "C1")) THEN
  SUBGOAL_THEN `&0 <= sqrt(abs C1)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  ABBREV_TAC `r1 = sqrt(abs C1) * D + &1` THEN
  SUBGOAL_THEN `&0 < r1 /\ &0 <= sqrt(abs C1) * D` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= sqrt(abs C1) * D` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    EXPAND_TAC "r1" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`; `r1:real`] P2AL84_LEMMA_965_SCALED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (LABEL_TAC "C2")) THEN
  (* the counterexamples *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!n:num. ?kappa top atlas (g:real->B->real^3^3) p x u v.
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
       ~compact_space top /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\
       p IN topspace top /\
       ~(?e. rfs_strong_neck (p2b_kview (top,atlas) g) eps p (&0) e) /\
       x IN mfd_ball (top,atlas) (g(&0)) p (D * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
       ~collinear {vec 0,u,v} /\
       mfd_sectional atlas (g(&0)) x u v <= inv(&n + &2) * mfd_scalar atlas (g(&0)) p`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "neg" (MP_TAC o SPEC `&n + &2`) THEN
    REWRITE_TAC[REAL_ARITH `&1 < &n + &2`; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT;
                GSYM CONJ_ASSOC; NOT_EXISTS_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kp:num->real` (X_CHOOSE_THEN `tpk:num->B topology`
    (X_CHOOSE_THEN `atk:num->((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `gk:num->real->B->real^3^3` (X_CHOOSE_THEN `pk:num->B`
    (X_CHOOSE_THEN `xk:num->B` (X_CHOOSE_THEN `uk:num->real^3`
    (X_CHOOSE_THEN `vk:num->real^3` (LABEL_TAC "cex")))))))) o REWRITE_RULE[SKOLEM_THM]) THEN
  (* per-n facts *)
  SUBGOAL_THEN
   `!n. p2b_kappa_solution kappa0 ((tpk:num->B topology) n,atk n)
                           ((gk:num->real->B->real^3^3) n) /\
        p2b_ksep (tpk n) (atk n) /\ (xk:num->B) n IN topspace (tpk n) /\
        (pk:num->B) n IN topspace (tpk n) /\
        &0 < mfd_scalar (atk n) (gk n (&0)) (pk n) /\
        &0 < mfd_scalar (atk n) (gk n (&0)) (xk n) /\
        sqrt(mfd_scalar (atk n) (gk n (&0)) (xk n)) *
        mfd_dist (tpk n,atk n) (gk n (&0)) (xk n) (pk n) <= r1 /\
        mfd_sectional (atk n) (gk n (&0)) (xk n) (uk n) (vk n) <=
        (inv(&n + &2) * C2) * mfd_scalar (atk n) (gk n (&0)) (xk n) /\
        ?s. s IN topspace (tpk n) /\
            (!z. z IN topspace (tpk n) /\ ~(z = s)
                 ==> p2b_dist_regular (tpk n,atk n) (gk n (&0)) s z) /\
            sqrt(mfd_scalar (atk n) (gk n (&0)) (xk n)) *
            mfd_dist (tpk n,atk n) (gk n (&0)) (xk n) s <= r1 + sqrt(abs C1) * Dp`
  (LABEL_TAC "facts") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "cex" (MP_TAC o SPEC `n:num`) THEN
    INTRO_TAC "ksol ksep ncpt posc pin nsn xin ncol small" THEN
    MP_TAC(MATCH_MP P2BL_KSOL_FACTS
      (ASSUME `p2b_kappa_solution ((kp:num->real) n) ((tpk:num->B topology) n,atk n)
                 ((gk:num->real->B->real^3^3) n)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `connected_space ((tpk:num->B topology) n) /\
      riemannian_metric (atk n) ((gk:num->real->B->real^3^3) n (&0))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `p2b_kappa_solution ((kp:num->real) n) ((tpk:num->B topology) n,atk n)
                     ((gk:num->real->B->real^3^3) n)` THEN
      REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2b_kappa_solution kappa0 ((tpk:num->B topology) n,atk n)
                                     ((gk:num->real->B->real^3^3) n)` ASSUME_TAC THENL
     [USE_THEN "k0sol" MATCH_MP_TAC THEN EXISTS_TAC `(kp:num->real) n` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(xk:num->B) n IN mfd_ball ((tpk:num->B topology) n,atk n)
                   ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n)
                   (D * inv(sqrt(mfd_scalar (atk n) (gk n (&0)) (pk n))))` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(xk:num->B) n IN topspace ((tpk:num->B topology) n)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n) /\
      &0 < mfd_scalar (atk n) (gk n (&0)) ((xk:num->B) n)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa0:real`; `(tpk:num->B topology) n`] THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < sqrt(mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n)) /\
      &0 < sqrt(mfd_scalar (atk n) (gk n (&0)) ((xk:num->B) n))`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n)) *
      mfd_dist ((tpk:num->B topology) n,atk n) (gk n (&0)) (pk n) ((xk:num->B) n) < D`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN ASM_SIMP_TAC[GSYM P2AS85_INV_LE] THEN
      ASM_REWRITE_TAC[REAL_NOT_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((xk:num->B) n) <=
      C1 * mfd_scalar (atk n) (gk n (&0)) ((pk:num->B) n)`
    ASSUME_TAC THENL
     [USE_THEN "C1" MATCH_MP_TAC THEN EXISTS_TAC `(tpk:num->B topology) n` THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_dist ((tpk:num->B topology) n,atk n) ((gk:num->real->B->real^3^3) n (&0))
               ((xk:num->B) n) ((pk:num->B) n) =
      mfd_dist (tpk n,atk n) (gk n (&0)) (pk n) (xk n) /\
      &0 <= mfd_dist (tpk n,atk n) (gk n (&0)) (pk n) (xk n)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!d. &0 <= d
          ==> sqrt(mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((xk:num->B) n)) * d <=
              sqrt(abs C1) * (sqrt(mfd_scalar (atk n) (gk n (&0)) ((pk:num->B) n)) * d)`
    (LABEL_TAC "cmp") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AS85_SCALE_ARITH THEN
      EXISTS_TAC `mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n)` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((xk:num->B) n)) *
      mfd_dist ((tpk:num->B topology) n,atk n) (gk n (&0)) (xk n) ((pk:num->B) n) < r1`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "cmp" (MP_TAC o SPEC `mfd_dist ((tpk:num->B topology) n,atk n)
                         ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n) ((xk:num->B) n)`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN
       `sqrt(abs C1) *
        (sqrt(mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n)) *
         mfd_dist ((tpk:num->B topology) n,atk n) (gk n (&0)) (pk n) ((xk:num->B) n)) <=
        sqrt(abs C1) * D`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      EXPAND_TAC "r1" THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n) <=
      C2 * mfd_scalar (atk n) (gk n (&0)) ((xk:num->B) n)`
    ASSUME_TAC THENL
     [USE_THEN "C2" MATCH_MP_TAC THEN EXISTS_TAC `(tpk:num->B topology) n` THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&n + &2) * mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0))
                                              ((pk:num->B) n)` THEN
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    (* the soul near p *)
    USE_THEN "Dp" (MP_TAC o SPECL [`(kp:num->real) n`; `(tpk:num->B topology) n`;
      `(atk:num->((B->bool)#(B->real^3))->bool) n`; `(gk:num->real->B->real^3^3) n`;
      `(pk:num->B) n`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:B` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    EXISTS_TAC `s:B` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `mfd_dist ((tpk:num->B topology) n,atk n) ((gk:num->real->B->real^3^3) n (&0))
               ((xk:num->B) n) s <=
      mfd_dist (tpk n,atk n) (gk n (&0)) (xk n) ((pk:num->B) n) +
      mfd_dist (tpk n,atk n) (gk n (&0)) (pk n) s /\
      &0 <= mfd_dist (tpk n,atk n) (gk n (&0)) (pk n) s`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "cmp" (MP_TAC o SPEC `mfd_dist ((tpk:num->B topology) n,atk n)
                       ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n) s`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN
     `sqrt(abs C1) *
      (sqrt(mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((pk:num->B) n)) *
       mfd_dist ((tpk:num->B topology) n,atk n) (gk n (&0)) (pk n) s) <= sqrt(abs C1) * Dp`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(mfd_scalar (atk n) ((gk:num->real->B->real^3^3) n (&0)) ((xk:num->B) n)) *
      mfd_dist ((tpk:num->B topology) n,atk n) (gk n (&0)) (xk n) s <=
      sqrt(mfd_scalar (atk n) (gk n (&0)) (xk n)) *
      mfd_dist (tpk n,atk n) (gk n (&0)) (xk n) ((pk:num->B) n) +
      sqrt(mfd_scalar (atk n) (gk n (&0)) (xk n)) * mfd_dist (tpk n,atk n) (gk n (&0)) (pk n) s`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the souls as a sequence *)
  USE_THEN "facts" (MP_TAC o REWRITE_RULE[SKOLEM_THM] o GEN `n:num` o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    CONJUNCT2 o CONJUNCT2 o SPEC `n:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `sk:num->B` (LABEL_TAC "souls")) THEN
  (* the limit at x n *)
  MP_TAC(BETA_RULE(ISPECL [`w:B->bool`; `kappa0:real`; `tpk:num->B topology`;
    `atk:num->((B->bool)#(B->real^3))->bool`; `gk:num->real->B->real^3^3`; `xk:num->B`;
    `\n. mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool) n)
                    ((gk:num->real->B->real^3^3) n (&0)) ((xk:num->B) n)`]
    P2A985D_THM964_BOTH)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim")
      (CONJUNCTS_THEN2 (LABEL_TAC "lim1")
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))))) THEN
  (* the limit is positively curved *)
  USE_THEN "pos" (MP_TAC o REWRITE_RULE[o_THM] o SPECL
    [`w:B->bool`; `kappa0:real`; `\k. (tpk:num->B topology) ((sub:num->num) k)`;
     `\k. (atk:num->((B->bool)#(B->real^3))->bool) ((sub:num->num) k)`;
     `\k. (gk:num->real->B->real^3^3) ((sub:num->num) k)`; `(xk:num->B) o (sub:num->num)`;
     `\k. mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool) ((sub:num->num) k))
                     ((gk:num->real->B->real^3^3) (sub k) (&0)) ((xk:num->B) (sub k))`;
     `(pk:num->B) o (sub:num->num)`; `(sk:num->B) o (sub:num->num)`;
     `r1:real`; `r1 + sqrt(abs C1) * Dp`; `top':B topology`;
     `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`; `eps:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    USE_THEN "facts" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) k`) THEN
    USE_THEN "souls" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) k`) THEN
    USE_THEN "cex" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) k`) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(LABEL_TAC "limpos")] THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa0 (top',atlas') (g':real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (atlas':((B->bool)#(B->real^3))->bool)
                                  ((g':real->B->real^3^3) (&0)) /\ (xl:B) IN topspace top'`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL] THEN
    USE_THEN "lim" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = mfd_sec_min atlas' ((g':real->B->real^3^3) (&0)) xl` THEN
  SUBGOAL_THEN `&0 < c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN MATCH_MP_TAC RFA_SECMIN_POS THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "limpos" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. ~collinear {vec 0,u,v}
          ==> c0 <= mfd_sectional atlas' ((g':real->B->real^3^3) (&0)) xl u v`
  (LABEL_TAC "c0le") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "c0" THEN MATCH_MP_TAC P2AL84_SECMIN_LE THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "limpos" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the curvature at x (sub k) *)
  USE_THEN "lim" (MP_TAC o REWRITE_RULE[P2C_FLOW_LIMIT_ON_WITH] o
                  MATCH_MP P2AL84_FLOW_LIMIT_ON o REWRITE_RULE[REAL_LT_01] o SPEC `&1`) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` ASSUME_TAC)) THEN
  SUBGOAL_THEN `!k. (phi:num->B->B) k xl = (xk:num->B) ((sub:num->num) k)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> p2al84_mentions "p2c_flow_limit_with" th)) THEN
    REWRITE_TAC[p2c_flow_limit_with; o_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n tau. ~(topspace(rfs_vtop (p2b_kview ((tpk:num->B topology) ((sub:num->num) n),
                                             atk (sub n)) ((gk:num->real->B->real^3^3) (sub n)))
                                 tau) = {})
             ==> smooth_manifold_atlas
                   (rfs_vtop (p2b_kview (tpk (sub n),atk (sub n)) (gk (sub n))) tau)
                   (rfs_vatlas (p2b_kview (tpk (sub n),atk (sub n)) (gk (sub n))) tau) /\
                 riemannian_metric
                   (rfs_vatlas (p2b_kview (tpk (sub n),atk (sub n)) (gk (sub n))) tau)
                   (rfs_vmetric (p2b_kview (tpk (sub n),atk (sub n)) (gk (sub n))) tau))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "facts" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL84_KVIEW_SLICES) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0) IN {s:real | --(&1) < s /\ s <= &0}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`\k. p2b_kview ((tpk:num->B topology) ((sub:num->num) k),
                     (atk:num->((B->bool)#(B->real^3))->bool) (sub k))
                    ((gk:num->real->B->real^3^3) (sub k))`;
     `(xk:num->B) o (sub:num->num)`; `\k:num. &0`;
     `\k. mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool) ((sub:num->num) k))
                     ((gk:num->real->B->real^3^3) (sub k) (&0)) ((xk:num->B) (sub k))`;
     `{s:real | --(&1) < s /\ s <= &0}`; `top':B topology`;
     `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
     `W:num->B->bool`; `phi:num->B->B`; `&0`; `xl:B`] P2A985D_CURV_KEY_REV) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c0 / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0" o
    SIMP_RULE[P2BL_KVIEW_ACCESS; REAL_LE_REFL; P2AS85_DIV_LZERO; REAL_ADD_RID; o_THM;
              ASSUME `!k. (phi:num->B->B) k xl = (xk:num->B) ((sub:num->num) k)`])) THEN
  X_CHOOSE_TAC `K:num` (SPEC `&2 * abs C2 / c0` REAL_ARCH_SIMPLE) THEN
  SUBGOAL_THEN `&K <= &((sub:num->num) (k0 + K))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MP_TAC(SPEC `k0 + K:num` (MATCH_MP P2BX0_SUBSEQ_GE (ASSUME `p3_subseq (sub:num->num)`))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `n = (sub:num->num) (k0 + K)` THEN
  USE_THEN "facts" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "cex" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "k0" (MP_TAC o REWRITE_RULE[ASSUME `(sub:num->num) (k0 + K) = n`] o
                 SPEC `k0 + K:num`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(uk:num->real^3) n`; `(vk:num->real^3) n`] o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (X_CHOOSE_THEN `v0:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `c0 <= mfd_sectional atlas' ((g':real->B->real^3^3) (&0)) xl u0 v0`
  ASSUME_TAC THENL [USE_THEN "c0le" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `c0 / &2 * mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool) n)
                         ((gk:num->real->B->real^3^3) n (&0)) ((xk:num->B) n) <=
    mfd_sectional (atk n) (gk n (&0)) (xk n) ((uk:num->real^3) n) ((vk:num->real^3) n)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c0 / &2 <= inv(&n + &2) * C2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c0 / &2`; `inv(&n + &2) * C2`;
                   `mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool) n)
                               ((gk:num->real->B->real^3^3) n (&0)) ((xk:num->B) n)`]
                  REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&n + &2) * C2 < c0 / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * abs C2 <= c0 * &n` ASSUME_TAC THENL
     [SUBGOAL_THEN `(&2 * abs C2) / c0 <= &n` MP_TAC THENL
       [SUBGOAL_THEN `(&2 * abs C2) / c0 = &2 * abs C2 / c0` SUBST1_TAC THENL
         [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&n + &2) * abs C2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &2`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The route theorem of COR_9_94_L piece (b) (pc_p2b_c994req): part (1)     *)
(* from P2A985C_PART1, part (2) from P2A985D_LOWER and P2A985C_UPPER with   *)
(* D1 the larger of the two constants.                                      *)
(* ========================================================================= *)

let P2A985D_PROP_9_85L_ROUTE = prove
 (`!w:B->bool. P2B_PROP_9_85L_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_PROP_9_85L_ROUTE_STATEMENT; P2B_PROP_9_85L_STATEMENT] THEN
  INTRO_TAC "t964 p958 l965 pk ch soul" THEN
  MP_TAC(SPEC `w:B->bool` P2A985C_PART1) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1"))) THEN
  MP_TAC(SPEC `w:B->bool` P2A985D_LOWER) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "low"))) THEN
  MP_TAC(SPEC `w:B->bool` P2A985C_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "up")] THEN
  EXISTS_TAC `min eps1 eps3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN INTRO_TAC "ep ep2 L1" THEN
  USE_THEN "p1" (MP_TAC o SPECL [`eps:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  USE_THEN "low" (MP_TAC o SPECL [`eps:real`; `D:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D1l:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1l"))) THEN
  USE_THEN "up" (MP_TAC o SPEC `D:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D1u:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1u"))) THEN
  MAP_EVERY EXISTS_TAC [`D:real`; `max D1l D1u`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `p:B`] THEN
  INTRO_TAC "ksol ksep ncpt pos pin nsn" THEN
  CONJ_TAC THENL
   [USE_THEN "D" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "D1l" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`; `x:B`;
    `u:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "D1u" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`; `x:B`;
    `u:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `inv(max D1l D1u) * mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p <=
    inv D1l * mfd_scalar atlas (g(&0)) p /\
    D1u * mfd_scalar atlas (g(&0)) p <= max D1l D1u * mfd_scalar atlas (g(&0)) p`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

