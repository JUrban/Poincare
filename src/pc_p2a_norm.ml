(* ========================================================================= *)
(* Unit pc_p2a_norm: the normalization statement P2_NORMALIZE_STATEMENT of   *)
(* pc_p3_iface (S0; MT p. 353): a compact smooth 3-manifold with a           *)
(* Riemannian metric g carries, for every b0 > 0, a rescaled metric q g that *)
(* is normalized (abs Rm <= 1 and vol B(x,r) >= 2/3 pi r^3 for r <= 1) with  *)
(* abs Rm(q g) <= b0.  Route: abs Rm is bounded on the compact manifold      *)
(* (P3H_RMD2_COMPACT_BOUND_FIXED), scales like 1/q                           *)
(* (RFA_MFD_RM_NORM_CMUL_LE); small g-balls have volume >= 2/3 pi rho^3      *)
(* uniformly, by Gunther's bound CMP_GUNTHER on a uniform injectivity radius *)
(* (GEOJR_UNIFORM_RADIUS) and the model bound sn_K(t)^2 >= t^2 / 2 for K t^2 *)
(* <= 1 (CMP_SN_LOWER_HALF); balls and volumes scale by MFD_BALL_SCALE and   *)
(* MFD_HAS_VOLUME_SCALE.                                                     *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_cmp_gunther.ml";;
needs "src/pc_cmp_rad.ml";;
needs "src/pc_cmp_ode.ml";;
needs "src/pc_geo_inj.ml";;
needs "src/pc_geo_lisom.ml";;
needs "src/pc_grg_vol.ml";;
needs "src/pc_grg_dist2.ml";;
needs "src/pc_rfa_shiscale.ml";;
needs "src/pc_p3_c17curv.ml";;

prioritize_real();;
type_invention_error := true;;

(* The 3-dimensional model volume is at least half the Euclidean one for    *)
(* K r^2 <= 1.                                                               *)

let P2AN_VMODEL_LOWER = prove
 (`!K r. &0 <= K /\ &0 < r /\ K * r pow 2 <= &1
         ==> &2 / &3 * pi * r pow 3 <= cmp_vmodel (:3) K r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_vmodel; DIMINDEX_3] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[VOLUME_BALL; REAL_POS; REAL_POW_ONE] THEN
  SUBGOAL_THEN
   `((\t. t pow 2 / &2) has_real_integral (r pow 3 / &6)) (real_interval[&0,r])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t:real. t pow 3 / &6`; `\t:real. t pow 2 / &2`; `&0`; `r:real`]
                  REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `x - &0 pow 3 / &6 = x`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `r pow 3 / &6 <= real_integral (real_interval[&0,r]) (\t. cmp_sn K t pow 2)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[real_integrable_on];
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[ETA_AX; CMPV_SN_CONTINUOUS_ON];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `t = &0` THENL
       [ASM_REWRITE_TAC[CMP_SN_ZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`K:real`; `t:real`] CMP_SN_LOWER_HALF) THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * r pow 2` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 / &3 * pi * r pow 3 = (&4 * pi) * (r pow 3 / &6) /\
    &3 * (&4 / &3 * pi * &1) * real_integral (real_interval[&0,r]) (\t. cmp_sn K t pow 2) =
    (&4 * pi) * real_integral (real_interval[&0,r]) (\t. cmp_sn K t pow 2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

(* A uniform bound of abs Rm on a compact manifold.                          *)

let P2AN_RM_BOUND = prove
 (`!top atlas (g:A->real^3^3).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        compact_space top /\ riemannian_metric atlas g
        ==> ?B. &0 < B /\ !x. x IN topspace top ==> mfd_rm_norm atlas g x <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `topspace top:A->bool`] P3H_RMD2_COMPACT_BOUND_FIXED) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `sqrt(abs B) + &1` THEN CONJ_TAC THENL
   [MP_TAC(SPEC `abs B` SQRT_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(rfa_rmd2 0 atlas (g:A->real^3^3) x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3H_RM_NORM_LE_RMD2 THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= b + &1`) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[] THEN
    REAL_ARITH_TAC]);;

(* Small balls are not collapsed, uniformly: vol B(x,rho) >= 2/3 pi rho^3.  *)

let P2AN_SMALL_BALLS = prove
 (`!top atlas (g:A->real^3^3).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        compact_space top /\ riemannian_metric atlas g
        ==> ?rho0. &0 < rho0 /\
                   !x rho. x IN topspace top /\ &0 < rho /\ rho <= rho0
                           ==> ?v. mfd_has_volume (top,atlas) g
                                     (mfd_ball (top,atlas) g x rho) v /\
                                   &2 / &3 * pi * rho pow 3 <= v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`] P2AN_RM_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`] GEOJR_UNIFORM_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r0 (inv(sqrt B))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `rho:real`] THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `rho:real`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt B` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt B * rho <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt B * inv(sqrt B)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cmp_vmodel (:3) B rho` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AN_VMODEL_LOWER THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `B * rho pow 2 = (sqrt B * rho) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:3)`] CMP_GUNTHER) THEN REWRITE_TAC[CMP_GUNTHER_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`;
    `B:real`; `rho:real`; `v:real`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
   [MP_TAC CMPO_ONE_LT_PI2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `r0:real` THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`y:A`; `e1:real^3`; `e2:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x rho` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_rm_norm atlas (g:A->real^3^3) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y`) THEN
      MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The headline (statement P2_NORMALIZE_STATEMENT of pc_p3_iface).           *)
(* ------------------------------------------------------------------------- *)

let P2AN_NORMALIZE = prove
 (`!u:A->bool. P2_NORMALIZE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2_NORMALIZE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`] THEN
  STRIP_TAC THEN X_GEN_TAC `b0:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`] P2AN_RM_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`] P2AN_SMALL_BALLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SB"))) THEN
  ABBREV_TAC `q = B / b0 + B + inv(rho0 pow 2) + &1` THEN
  SUBGOAL_THEN `&0 < q /\ B / b0 <= q /\ B <= q /\ inv(rho0 pow 2) <= q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= B / b0 /\ &0 <= inv(rho0 pow 2)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_POW_LE]; ALL_TAC] THEN
    EXPAND_TAC "q" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top ==> mfd_rm_norm atlas (\x. q %% (g:A->real^3^3) x) x <= B / q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `B / q <= &1 /\ B / q <= b0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `B / b0 <= q` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[rfs_normalized] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B / q` THEN
    ASM_SIMP_TAC[];
    ALL_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B / q` THEN
    ASM_SIMP_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `r:real`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MFD_BALL_SCALE] THEN
  SUBGOAL_THEN `&0 < sqrt q` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv rho0 <= sqrt q` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv rho0 = sqrt(inv(rho0 pow 2))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_INV] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "SB" (MP_TAC o SPECL [`x:A`; `r / sqrt q`]) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rho0 * inv rho0` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sqrt(q pow 3) * v` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`;
                   `mfd_ball (top,atlas) (g:A->real^3^3) x (r / sqrt q)`;
                   `v:real`; `q:real`] MFD_HAS_VOLUME_SCALE) THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(q pow 3) = sqrt q pow 3` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      REWRITE_TAC[GSYM REAL_POW_POW] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt q pow 3 * (&2 / &3 * pi * (r / sqrt q) pow 3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < sqrt q` THEN
    SPEC_TAC(`sqrt q`,`s:real`) THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]]);;

