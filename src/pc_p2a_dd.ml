(* ========================================================================= *)
(* pc_p2a_dd: the statement A10 of pc_p2c_iface                              *)
(* (P2C_REQ_DIST_DISTORTION_STATEMENT), Hamilton's distance distortion (MT   *)
(* Cor 3.26) in integrated form: if Ric(g s) <= 2 k(s) g(s) on [t1,t2]       *)
(* (k continuous and positive) along a Ricci flow with complete slices, then *)
(* d_t1(x,y) <= d_t2(x,y) + int_[t1,t2] 8 sqrt(2 k(s) / 3) ds.               *)
(* Route: the local backward difference with MT's sharp constant at          *)
(* r0 = sqrt(3 / (2 k)) (section 1, adapted from pc_rfa_dist), right         *)
(* lower semicontinuity in time from the one-sided metric comparison under   *)
(* the Ricci upper bound (section 2), a Dini lemma for backward differences  *)
(* (section 3), the integral of the rate (section 4), and the assembly       *)
(* (section 5).                                                              *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_rfa_dist.ml";;
needs "src/pc_rfa_hbar.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* 1. The local backward difference of the distance with MT's sharp         *)
(* constant 2(n-1)(2/3 K r0 + 1/r0) (MT Prop 3.21 with Claim 3.24),         *)
(* under K r0^2 <= 3.  Adapted from RFA_DS_DERIV_LOWER and                  *)
(* RFA_P2B_REQ_RFA_DIST_LOCAL of pc_rfa_dist, which state the weaker        *)
(* constant 2(n-1)(K r0 + 1/r0).  Changes: the constant, the extra          *)
(* hypothesis K r0^2 <= 3 (the short case d < 2 r0 then still gives         *)
(* 2(n-1) K r0 <= 2(n-1)(2/3 K r0 + 1/r0)), and the use of the              *)
(* sharp lower bound in the local lemma.                                    *)
(* ========================================================================= *)

let P2AD_DERIV_LOWER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x v K r0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ v IN mfd_exp_dom (top,atlas) g x /\
     mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v /\
     &0 < mfd_tnorm g x v /\ &0 < r0 /\ &0 <= K /\ K * r0 pow 2 <= &3 /\
     (!y w. y IN mfd_ball (top,atlas) g x r0 UNION
                 mfd_ball (top,atlas) g (mfd_exp (top,atlas) g x v) r0
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w))) /\
     (\u. --(mfd_ricci atlas g (mfd_geo (top,atlas) g x v u)
               (mfd_velocity atlas (mfd_geo (top,atlas) g x v) (&0) (&1) u)
               (mfd_velocity atlas (mfd_geo (top,atlas) g x v) (&0) (&1) u)) /
          mfd_speed atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) u)
       real_integrable_on real_interval[&0,&1]
     ==> --(&2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0)) <=
         real_integral (real_interval[&0,&1])
           (\u. --(mfd_ricci atlas g (mfd_geo (top,atlas) g x v u)
                     (mfd_velocity atlas (mfd_geo (top,atlas) g x v) (&0) (&1) u)
                     (mfd_velocity atlas (mfd_geo (top,atlas) g x v) (&0) (&1) u)) /
                mfd_speed atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) u)`,
  REPEAT GEN_TAC THEN INTRO_TAC "haus sma rm xtop vdom dist dpos r0 K K3 ric int" THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `d = mfd_tnorm (g:A->real^N^N) x v` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[&0,&1] SUBSET J` ASSUME_TAC THENL
   [UNDISCH_TAC `v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
    ASM_REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN DISCH_TAC THEN
    UNDISCH_TAC `is_realinterval (J:real->bool)` THEN
    REWRITE_TAC[is_realinterval; SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC th THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval[&0,&1]
        ==> mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) (&0) (&1) u =
            mfd_vel atlas gam u /\
            mfd_speed atlas (g:A->real^N^N) gam (&0) (&1) u = d /\
            mfd_vel atlas gam u dot (g (gam u) ** mfd_vel atlas gam u) = d pow 2 /\
            mfd_tnorm g (gam u) (mfd_vel atlas gam u) = d`
  (LABEL_TAC "vs") THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) (&0) (&1) u =
                  mfd_vel atlas gam u`
    ASSUME_TAC THENL
     [MATCH_MP_TAC GEOM_VELOCITY_EQ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(gam:real->A) u IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) ((gam:real->A) u)
                    (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gam u) = d`
    ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gam:real->A`; `J:real->bool`; `u:real`; `&0`]
                    MFD_GEODESIC_SPEED) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[mfd_speed] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_tnorm (g:A->real^N^N) ((gam:real->A) u)
                     (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gam u) = d` THEN
      REWRITE_TAC[mfd_tnorm];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `(gam:real->A) u`] GEOD_TNORM_BASIC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `R1 = \u. mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                        (mfd_vel atlas gam u) (mfd_vel atlas gam u)` THEN
  SUBGOAL_THEN
   `!u. u IN real_interval[&0,&1]
        ==> --(mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                 (mfd_velocity atlas gam (&0) (&1) u) (mfd_velocity atlas gam (&0) (&1) u)) /
            mfd_speed atlas g gam (&0) (&1) u = --inv d * (R1:real->real) u`
  (LABEL_TAC "intg") THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    USE_THEN "vs" (MP_TAC o SPEC `u:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "R1" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&2 * r0 <= d` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `v:real^N`; `K:real`; `r0:real`]
           (REWRITE_RULE[CMP_RICCI_INTEGRAL_STATEMENT]
             (ISPECL [`(:A)`; `(:N)`] CMP_RICCI_INTEGRAL))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "ric" ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\t. mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) t) (mfd_vel atlas gam t)
             (mfd_vel atlas gam t)) = R1` SUBST1_TAC THENL
     [EXPAND_TAC "R1" THEN REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `real_integral (real_interval[&0,&1])
        (\u. --(mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                  (mfd_velocity atlas gam (&0) (&1) u) (mfd_velocity atlas gam (&0) (&1) u)) /
             mfd_speed atlas g gam (&0) (&1) u) =
      real_integral (real_interval[&0,&1]) (\u. --inv d * (R1:real->real) u)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN BETA_TAC THEN USE_THEN "intg" ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_LMUL] THEN
    ABBREV_TAC `I1 = real_integral (real_interval[&0,&1]) (R1:real->real)` THEN
    ABBREV_TAC `N1 = &(dimindex(:N) - 1)` THEN
    SUBGOAL_THEN `&0 <= N1 * K * r0 /\ &0 <= N1 * inv r0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "N1" THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE; REAL_LE_INV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv d * I1 <= &2 * N1 * (&2 / &3 * K * r0 + inv r0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv d * (d * &2 * N1 * (&2 / &3 * K * r0 + inv r0))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    UNDISCH_TAC `&0 <= N1 * K * r0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d < &2 * r0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval[&0,&1]
        ==> --(&(dimindex(:N) - 1) * K * d) <=
            --(mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                 (mfd_velocity atlas gam (&0) (&1) u) (mfd_velocity atlas gam (&0) (&1) u)) /
            mfd_speed atlas g gam (&0) (&1) u`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    USE_THEN "intg" (fun th -> ASM_SIMP_TAC[th]) THEN EXPAND_TAC "R1" THEN BETA_TAC THEN
    USE_THEN "vs" (MP_TAC o SPEC `u:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `(gam:real->A) u IN mfd_ball (top,atlas) (g:A->real^N^N) x r0 UNION
                         mfd_ball (top,atlas) g (mfd_exp (top,atlas) g x v) r0`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(u:real) IN J /\ &0 IN J /\ &1 IN J` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `real_interval[&0,&1] SUBSET J` THEN
        UNDISCH_TAC `(u:real) IN real_interval[&0,&1]` THEN
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[REAL_LE_REFL; REAL_POS];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `gam:real->A`; `J:real->bool`; `&0`; `u:real`] GEOH_GEO_SEG_DIST) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "j0") (LABEL_TAC "d0"))] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `gam:real->A`; `J:real->bool`; `&1`; `u:real`] GEOH_GEO_SEG_DIST) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "j1") (LABEL_TAC "d1"))] THEN
      SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) ((gam:real->A) (&0))
                      (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gam (&0)) = d /\
                    mfd_tnorm (g:A->real^N^N) ((gam:real->A) (&1))
                      (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gam (&1)) = d`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "vs" (MP_TAC o SPEC `&0`); USE_THEN "vs" (MP_TAC o SPEC `&1`)] THEN
        REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL] THEN SIMP_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(u:real) IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `abs(u - &0) = u /\ abs(u - &1) = &1 - u` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `mfd_dist (top,atlas) (g:A->real^N^N) ((gam:real->A) (&0)) (gam u) <= u * d /\
        mfd_dist (top,atlas) (g:A->real^N^N) ((gam:real->A) (&1)) (gam u) <= (&1 - u) * d`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [REMOVE_THEN "d0" MP_TAC; REMOVE_THEN "d1" MP_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[mfd_ball; IN_UNION; IN_ELIM_THM; mfd_exp] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(gam:real->A) (&0) = x` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_CASES_TAC `u * d < r0` THENL
       [DISJ1_TAC THEN USE_THEN "j0" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
        DISJ2_TAC THEN USE_THEN "j1" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "ric" (MP_TAC o SPECL [`(gam:real->A) u`;
      `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) u`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `Rr = mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                       (mfd_vel atlas gam u) (mfd_vel atlas gam u)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `Rr * inv d <= (&(dimindex(:N) - 1) * K * d pow 2) * inv d` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&(dimindex(:N) - 1) * K * d pow 2) * inv d = &(dimindex(:N) - 1) * K * d`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,&1]) (\u. --(&(dimindex(:N) - 1) * K * d))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS] THEN
    ABBREV_TAC `N1 = &(dimindex(:N) - 1)` THEN
    SUBGOAL_THEN `K * r0 <= &3 * inv r0` ASSUME_TAC THENL
     [SUBGOAL_THEN `(K * r0) * r0 <= (&3 * inv r0) * r0` MP_TAC THENL
       [SUBGOAL_THEN `(&3 * inv r0) * r0 = &3` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_2] THEN USE_THEN "K3" ACCEPT_TAC;
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= N1 * K * r0 /\ &0 <= N1 * inv r0 /\ N1 * K * d <= N1 * K * (&2 * r0) /\
                  N1 * K * r0 <= N1 * (&3 * inv r0)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "N1" THEN REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST]]);;

let P2AD_DIST_LOCAL = prove
 (`!top atlas a b (g:real->A->real^N^N) t x0 x1 K r0.
       hausdorff_space top /\
       ricci_flow_on (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       a < t /\ t < b /\ mfd_complete (top,atlas) (g t) /\
       x0 IN topspace top /\ x1 IN topspace top /\ mfd_joinable (top,atlas) x0 x1 /\
       &0 < r0 /\ &0 <= K /\ K * r0 pow 2 <= &3 /\
       (!y w. y IN mfd_ball (top,atlas) (g t) x0 r0 UNION mfd_ball (top,atlas) (g t) x1 r0
              ==> mfd_ricci atlas (g t) y w w <=
                  &(dimindex(:N) - 1) * K * (w dot (g t y ** w)))
       ==> !e. &0 < e
               ==> ?d. &0 < d /\
                       !s. &0 < s /\ s < d
                           ==> mfd_dist (top,atlas) (g(t - s)) x0 x1 <=
                               mfd_dist (top,atlas) (g t) x0 x1 +
                               s * (&2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0) +
                                    e)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "haus rf at tb cpl x0 x1 jn r0 K K3 ric" THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                (!s. a < s /\ s < b ==> riemannian_metric atlas ((g:real->A->real^N^N) s))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "rf" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `C = &2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0)` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV; REAL_POS];
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x0 x1` THEN
  ASM_CASES_TAC `d = &0` THENL
   [SUBGOAL_THEN `(x1:A) = x0` SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) t`; `x0:A`; `x1:A`] MFD_DIST_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `t - a` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) (t - s)`; `x0:A`] MFD_DIST_REFL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_LID] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`; `x0:A`; `x1:A`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`; `x0:A`; `x1:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`; `x0:A`; `v:real^N`] RFA_DS_GEO_FACTS) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) ((g:real->A->real^N^N) t) x0 v` THEN
  ABBREV_TAC `t1 = (a + t) / &2` THEN ABBREV_TAC `t2 = (t + b) / &2` THEN
  SUBGOAL_THEN `a < t1 /\ t1 < t /\ t < t2 /\ t2 < b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t1"; "t2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `gam:real->A`; `t:real`; `t1:real`; `t2:real`]
                RFA_DS_LENGTH_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `I0 = real_integral (real_interval[&0,&1])
           (\u. --(mfd_ricci atlas ((g:real->A->real^N^N) t) ((gam:real->A) u)
                     (mfd_velocity atlas gam (&0) (&1) u)
                     (mfd_velocity atlas gam (&0) (&1) u)) /
                mfd_speed atlas (g t) gam (&0) (&1) u)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "der")) THEN
  SUBGOAL_THEN `--C <= I0` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN EXPAND_TAC "I0" THEN EXPAND_TAC "gam" THEN
    MATCH_MP_TAC P2AD_DERIV_LOWER THEN ASM_REWRITE_TAC[IN_UNIV] THEN
    UNDISCH_TAC `(\u. --(mfd_ricci atlas ((g:real->A->real^N^N) t) ((gam:real->A) u)
                     (mfd_velocity atlas gam (&0) (&1) u)
                     (mfd_velocity atlas gam (&0) (&1) u)) /
                mfd_speed atlas (g t) gam (&0) (&1) u)
                real_integrable_on real_interval[&0,&1]` THEN
    EXPAND_TAC "gam" THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. mfd_length atlas ((g:real->A->real^N^N) s) (gam:real->A) (&0) (&1)`;
                 `I0:real`; `t:real`; `real_interval[t1,t2]`; `e:real`] RFA_LEFT_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb"))) THEN
  EXISTS_TAC `min d1 (t - t1)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "lb" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) (t - s)`; `gam:real->A`; `&0`; `&1`]
                MFD_DIST_LE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s * --I0 <= s * C` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* 2. Under Ric(g r) <= B g(r) on [t1,t2] the metric does not shrink        *)
(* faster than exp(-2 B): g(s) <= exp(2 B (u - s)) g(u) for                 *)
(* s <= u (one-sided Gronwall on d/dr w.(g r w) = -2 Ric(w,w),              *)
(* RFA_QFORM_DERIV), hence d_s <= exp(B (u - s)) d_u                        *)
(* (RFAH_DIST_COMPARE).                                                     *)
(* ========================================================================= *)

let P2AD_EXP_DERIV = prove
 (`!B s t. ((\r. exp(&2 * B * (r - s))) has_real_derivative
            (&2 * B * exp(&2 * B * (t - s)))) (atreal t)`,
  REPEAT GEN_TAC THEN REAL_DIFF_TAC THEN CONV_TAC REAL_RING);;

let P2AD_QFORM_LOWER = prove
 (`!top atlas a b (g:real->A->real^N^N) t1 t2 B z w.
        ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t2 < b /\ z IN topspace top /\
        (!s. t1 <= s /\ s <= t2
             ==> mfd_ricci atlas (g s) z w w <= B * (w dot (g s z ** w)))
        ==> !s u. t1 <= s /\ s <= u /\ u <= t2
                  ==> w dot (g s z ** w) <= exp(&2 * B * (u - s)) * (w dot (g u z ** w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ric"))))) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `u:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\r. exp(&2 * B * (r - s)) * (w dot ((g:real->A->real^N^N) r z ** w))`;
    `\r. exp(&2 * B * (r - s)) *
         (--(&2) * mfd_ricci atlas ((g:real->A->real^N^N) r) z w w) +
         (&2 * B * exp(&2 * B * (r - s))) * (w dot (g r z ** w))`;
    `real_interval[s,u]`; `s:real`; `u:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `r:real` THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`; `g:real->A->real^N^N`; `r:real`; `z:A`;
                     `w:real^N`] RFA_QFORM_DERIV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(ISPECL [`\r. exp(&2 * B * (r - s))`; `&2 * B * exp(&2 * B * (r - s))`;
                     `\r. w dot ((g:real->A->real^N^N) r z ** w)`;
                     `--(&2) * mfd_ricci atlas ((g:real->A->real^N^N) r) z w w`;
                     `r:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_REWRITE_TAC[P2AD_EXP_DERIV];
      USE_THEN "ric" (MP_TAC o SPEC `r:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `&2 * B * (r - s)` REAL_EXP_POS_LE) THEN
      SPEC_TAC(`exp(&2 * B * (r - s))`,`E:real`) THEN
      SPEC_TAC(`w dot ((g:real->A->real^N^N) r z ** w)`,`Q:real`) THEN
      SPEC_TAC(`mfd_ricci atlas ((g:real->A->real^N^N) r) z w w`,`R:real`) THEN
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= E * (B * Q - R)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID]]);;

let P2AD_DIST_LATER = prove
 (`!top atlas a b (g:real->A->real^N^N) t1 t2 B s u x y.
        ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t2 < b /\
        (!r z w. t1 <= r /\ r <= t2 /\ z IN topspace top
                 ==> mfd_ricci atlas (g r) z w w <= B * (w dot (g r z ** w))) /\
        t1 <= s /\ s <= u /\ u <= t2 /\ mfd_joinable (top,atlas) x y
        ==> mfd_dist (top,atlas) (g s) x y <=
            exp(B * (u - s)) * mfd_dist (top,atlas) (g u) x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) u`; `(g:real->A->real^N^N) s`;
                 `exp(&2 * B * (u - s))`; `x:A`; `y:A`] RFAH_DIST_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:A`; `w:real^N`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`; `g:real->A->real^N^N`; `t1:real`; `t2:real`;
                     `B:real`; `z:A`; `w:real^N`] P2AD_QFORM_LOWER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real`; `u:real`]) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[RFAH_SQRT_EXP2]]);;


(* ========================================================================= *)
(* 3. A Dini lemma for backward differences.  If at every point of (a,b]    *)
(* the backward difference f(s - h) - f(s) is o(h), and f is lower          *)
(* semicontinuous from the right wherever f(s + h) stays bounded above,     *)
(* then f a <= f b.  (Mirror image of P2BX_DINI_MONO of pc_p2b_l925,        *)
(* which uses forward differences and lower semicontinuity from the left;   *)
(* proved here directly to avoid loading that file.)                        *)
(* ========================================================================= *)

let P2AD_DINI_BACK_EPS = prove
 (`!(f:real->real) a b ee.
     a <= b /\ &0 < ee /\
     (!s e. a < s /\ s <= b /\ &0 < e
            ==> ?d. &0 < d /\
                    !h. &0 < h /\ h < d /\ a <= s - h ==> f(s - h) <= f s + e * h) /\
     (!s e M. a <= s /\ s < b /\ &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d /\ s + h <= b /\ f(s + h) <= M
                          ==> f s <= f(s + h) + e)
     ==> f a <= f b + ee * (b - a)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "BK") (LABEL_TAC "LS")))) THEN
  ABBREV_TAC
   `S = {s | a <= s /\ s <= b /\
             !u. s <= u /\ u <= b ==> (f:real->real) u <= f b + ee * (b - u)}` THEN
  SUBGOAL_THEN `(b:real) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `u:real = b` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN S ==> a <= s` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` INF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  ABBREV_TAC `m = inf S` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LB") (LABEL_TAC "GLB")) THEN
  SUBGOAL_THEN `a <= m /\ m <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "GLB" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "LB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. m < u /\ u <= b ==> (f:real->real) u <= f b + ee * (b - u)`
  (LABEL_TAC "ABOVE") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?s. s IN S /\ s <= u` STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `?s. s IN S /\ s <= u` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `u <= m:real` MP_TAC THENL
       [USE_THEN "GLB" MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN
        ASM_MESON_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `(s:real) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) m <= f b + ee * (b - m)` (LABEL_TAC "ATM") THENL
   [ASM_CASES_TAC `m:real = b` THENL
     [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID; REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `m < b:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `e1 = (f:real->real) m - (f b + ee * (b - m))` THEN
    SUBGOAL_THEN `&0 < e1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "LS" (MP_TAC o SPECL [`m:real`; `e1 / &2`; `(f:real->real) b + ee * (b - a)`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
    ABBREV_TAC `h = min (d / &2) (b - m)` THEN
    SUBGOAL_THEN `&0 < h /\ h < d /\ m + h <= b` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ABOVE" (MP_TAC o SPEC `m + h:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "d" (MP_TAC o SPEC `h:real`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `ee * (b - (m + h)) <= ee * (b - a)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `ee * (b - (m + h)) <= ee * (b - m)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `m:real = a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "BK" (MP_TAC o SPECL [`m:real`; `ee / &2`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
    ABBREV_TAC `h0 = min (d / &2) (m - a)` THEN
    SUBGOAL_THEN `&0 < h0 /\ h0 < d /\ a <= m - h0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "h0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `m - h0 IN S` MP_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `m < u:real` THENL
       [USE_THEN "ABOVE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `u:real = m` THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "ATM" ACCEPT_TAC; ALL_TAC] THEN
      USE_THEN "d" (MP_TAC o SPEC `m - u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `m - (m - u) = u:real`] THEN
      SUBGOAL_THEN `ee / &2 * (m - u) <= ee * (m - u)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ATM" MP_TAC THEN REAL_ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `m <= m - h0` MP_TAC THENL
       [USE_THEN "LB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REMOVE_THEN "ATM" MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2AD_DINI_BACK = prove
 (`!(f:real->real) a b.
     a <= b /\
     (!s e. a < s /\ s <= b /\ &0 < e
            ==> ?d. &0 < d /\
                    !h. &0 < h /\ h < d /\ a <= s - h ==> f(s - h) <= f s + e * h) /\
     (!s e M. a <= s /\ s < b /\ &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d /\ s + h <= b /\ f(s + h) <= M
                          ==> f s <= f(s + h) + e)
     ==> f a <= f b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `a:real = b` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `a < b:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`;
                 `((f:real->real) a - f b) / (&2 * (b - a))`] P2AD_DINI_BACK_EPS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < ((f:real->real) a - f b) / (&2 * (b - a))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `((f:real->real) a - f b) / (&2 * (b - a)) * (b - a) = (f a - f b) / &2`
  SUBST1_TAC THENL
   [UNDISCH_TAC `a < b:real` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* 4. The integral Phi(s) of a continuous nonnegative rate phi over [t1,s]: *)
(* additivity, monotonicity, and the backward difference                    *)
(* Phi(s) - Phi(s - h) >= h (phi s - e) for small h.                        *)
(* ========================================================================= *)

let P2AD_INT_COMBINE = prove
 (`!phi t1 t2 s u.
     phi real_continuous_on real_interval[t1,t2] /\ t1 <= s /\ s <= u /\ u <= t2
     ==> real_integral (real_interval[t1,u]) phi =
         real_integral (real_interval[t1,s]) phi + real_integral (real_interval[s,u]) phi`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[t1,t2]` THEN
  ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC);;

let P2AD_INT_MONO = prove
 (`!phi t1 t2 s u.
     phi real_continuous_on real_interval[t1,t2] /\
     (!x. t1 <= x /\ x <= t2 ==> &0 <= phi x) /\
     t1 <= s /\ s <= u /\ u <= t2
     ==> real_integral (real_interval[t1,s]) phi <= real_integral (real_interval[t1,u]) phi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real->real`; `t1:real`; `t2:real`; `s:real`; `u:real`]
                P2AD_INT_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_ADDR] THEN
  MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[t1,t2]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let P2AD_INT_POS = prove
 (`!phi t1 t2 s.
     phi real_continuous_on real_interval[t1,t2] /\
     (!x. t1 <= x /\ x <= t2 ==> &0 <= phi x) /\ t1 <= s /\ s <= t2
     ==> &0 <= real_integral (real_interval[t1,s]) phi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real->real`; `t1:real`; `t2:real`; `t1:real`; `s:real`]
                P2AD_INT_MONO) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_INTEGRAL_REFL]);;

let P2AD_INT_BACK = prove
 (`!phi t1 t2 s e.
     phi real_continuous_on real_interval[t1,t2] /\ t1 < s /\ s <= t2 /\ &0 < e
     ==> ?d. &0 < d /\
             !h. &0 < h /\ h < d /\ t1 <= s - h
                 ==> real_integral (real_interval[t1,s - h]) phi <=
                     real_integral (real_interval[t1,s]) phi - h * (phi s - e)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o GEN_REWRITE_RULE I [real_continuous_on]) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cont"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real->real`; `t1:real`; `t2:real`; `s - h:real`; `s:real`]
                P2AD_INT_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `h * ((phi:real->real) s - e) <= real_integral (real_interval[s - h,s]) phi`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[s - h,s]) (\x:real. (phi:real->real) s - e)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `s - h <= s:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[t1,t2]` THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
        USE_THEN "cont" (MP_TAC o SPEC `x:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]];
    REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* 5. The choice r0 = sqrt(3 / (2 k)) (then K r0^2 = 3/2 and the            *)
(* sharp constant is 8 sqrt(2 k / 3)), and the main theorem.                *)
(* ========================================================================= *)

let P2AD_R0 = prove
 (`!k. &0 < k
       ==> &0 < sqrt(&3 / (&2 * k)) /\ k * sqrt(&3 / (&2 * k)) pow 2 <= &3 /\
           &2 * &(dimindex(:3) - 1) *
           (&2 / &3 * k * sqrt(&3 / (&2 * k)) + inv(sqrt(&3 / (&2 * k)))) =
           &8 * sqrt(&2 * k / &3)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &3 / (&2 * k)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = sqrt(&3 / (&2 * k))` THEN
  SUBGOAL_THEN `&0 < r /\ r pow 2 = &3 / (&2 * k)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 * k / &3) = inv r` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_POW_INV] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `r pow 2 = &3 / (&2 * k)` THEN UNDISCH_TAC `&0 < r` THEN
    UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem (the statement P2C_REQ_DIST_DISTORTION_STATEMENT of      *)
(* pc_p2c_iface).                                                            *)
(* ------------------------------------------------------------------------- *)

let P2AD_REQ_DIST_DISTORTION = prove
 (`!u:A->bool. P2C_REQ_DIST_DISTORTION_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_REQ_DIST_DISTORTION_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `k:real->real`; `t1:real`; `t2:real`; `x:A`; `y:A`] THEN
  INTRO_TAC "haus rf cpl at1 t12 t2b xt yt kc kpos ric" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  ABBREV_TAC `phi = \s. &8 * sqrt(&2 * (k:real->real) s / &3)` THEN
  SUBGOAL_THEN `(phi:real->real) real_continuous_on real_interval[t1,t2]`
  ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    MP_TAC(ISPECL [`\s. &2 / &3 * (k:real->real) s`; `sqrt`; `real_interval[t1,t2]`]
                  REAL_CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT; o_DEF] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_CONTINUOUS_ON_EQ) THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. t1 <= s /\ s <= t2 ==> &0 <= (phi:real->real) s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (k:real->real) s` ASSUME_TAC THENL
     [USE_THEN "kpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "phi" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) (x:A) y` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[MFD_DIST_NOT_JOINABLE; REAL_LE_ADDR] THEN
    MATCH_MP_TAC P2AD_INT_POS THEN EXISTS_TAC `t2:real` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  (* A bound B0 of k on [t1,t2] *)
  MP_TAC(ISPECL [`k:real->real`; `real_interval[t1,t2]`] REAL_CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY; IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `B0 = (k:real->real) s0` THEN
  SUBGOAL_THEN `&0 < B0` ASSUME_TAC THENL
   [EXPAND_TAC "B0" THEN USE_THEN "kpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r z w. t1 <= r /\ r <= t2 /\ z IN topspace top
            ==> mfd_ricci atlas ((g:real->A->real^3^3) r) z w w <=
                (&2 * B0) * (w dot (g r z ** w))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (k:real->real) r * (w dot ((g:real->A->real^3^3) r z ** w))` THEN
    CONJ_TAC THENL [USE_THEN "ric" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= w dot ((g:real->A->real^3^3) r z ** w)` ASSUME_TAC THENL
     [ASM_CASES_TAC `w:real^3 = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(g:real->A->real^3^3) r`; `z:A`] RIEMANNIAN_METRIC_POS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* The Dini lemma for F(s) = d_s(x,y) + int_[t1,s] phi *)
  MP_TAC(ISPECL
   [`\s. mfd_dist (top,atlas) ((g:real->A->real^3^3) s) x y +
         real_integral (real_interval[t1,s]) phi`;
    `t1:real`; `t2:real`] P2AD_DINI_BACK) THEN
  REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_ADD_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* backward differences *)
    MAP_EVERY X_GEN_TAC [`s:real`; `e:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (k:real->real) s` ASSUME_TAC THENL
     [USE_THEN "kpos" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `(k:real->real) s` P2AD_R0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
      `g:real->A->real^3^3`; `s:real`; `x:A`; `y:A`; `(k:real->real) s`;
      `sqrt(&3 / (&2 * (k:real->real) s))`] P2AD_DIST_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        USE_THEN "cpl" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
        MAP_EVERY X_GEN_TAC [`z:A`; `w:real^3`] THEN DISCH_TAC THEN
        USE_THEN "ric" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
          is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
        REWRITE_TAC[mfd_ball; IN_UNION; IN_ELIM_THM] THEN
        MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1"))) THEN
    MP_TAC(ISPECL [`phi:real->real`; `t1:real`; `t2:real`; `s:real`; `e / &2`]
                  P2AD_INT_BACK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2"))) THEN
    EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    USE_THEN "d1" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "d2" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real->real) s = &8 * sqrt(&2 * k s / &3)` SUBST1_TAC THENL
     [EXPAND_TAC "phi" THEN REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    (* lower semicontinuity from the right *)
    MAP_EVERY X_GEN_TAC [`s:real`; `e:real`; `M:real`] THEN STRIP_TAC THEN
    ABBREV_TAC `B = &2 * B0` THEN
    SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL [EXPAND_TAC "B" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `min (inv(&2 * (B + &1))) (e / (&2 * (B + &1) * (abs M + &1)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    X_GEN_TAC `h:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
      `g:real->A->real^3^3`; `t1:real`; `t2:real`; `B:real`; `s:real`; `s + h:real`;
      `x:A`; `y:A`] P2AD_DIST_LATER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(s + h) - s = h:real`] THEN
    MP_TAC(ISPECL [`phi:real->real`; `t1:real`; `t2:real`; `s:real`; `s + h:real`]
                  P2AD_INT_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`phi:real->real`; `t1:real`; `t2:real`; `s + h:real`] P2AD_INT_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->A->real^3^3) (s + h)) x y`
    MP_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(B * h) <= &1 + &2 * (B * h)` MP_TAC THENL
     [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B + &1) * h` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B + &1) * inv(&2 * (B + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < B` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * (B * h) * (abs M + &1) <= e` MP_TAC THENL
     [SUBGOAL_THEN `&0 < &2 * (B + &1) * (abs M + &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `h * (&2 * (B + &1) * (abs M + &1)) < e` ASSUME_TAC THENL
       [UNDISCH_TAC `h < e / (&2 * (B + &1) * (abs M + &1))` THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &2 * (abs M + &1) * h` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `h * (&2 * (B + &1) * (abs M + &1)) < e` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC
     `mfd_dist (top,atlas) ((g:real->A->real^3^3) (s + h)) x y +
      real_integral (real_interval[t1,s + h]) phi <= M` THEN
    SPEC_TAC(`mfd_dist (top,atlas) ((g:real->A->real^3^3) (s + h)) x y`, `d0:real`) THEN
    SPEC_TAC(`mfd_dist (top,atlas) ((g:real->A->real^3^3) s) x y`, `ds:real`) THEN
    SPEC_TAC(`real_integral (real_interval[t1,s]) phi`, `Is:real`) THEN
    SPEC_TAC(`real_integral (real_interval[t1,s + h]) phi`, `Ih:real`) THEN
    SPEC_TAC(`exp(B * h)`, `E:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `E * d0 <= (&1 + &2 * (B * h)) * d0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(B * h) * d0 <= (B * h) * (abs M + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

