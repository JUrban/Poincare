(* ========================================================================= *)
(* Unit pc_p2c_t533 (Part 2C, flowlim route): MT Thm 5.33,                   *)
(* P2C_THM_5_33_STATEMENT (views with Riemannian limit metrics): limits of   *)
(* pinched views rescaled by Q n -> oo have nonnegative sectional curvature. *)
(* A negative sectional curvature K of the limit at y gives sectional        *)
(* curvatures <= K Q n / 2 of the views at phi n y (C^2 closeness, the      *)
(* scaling and the pullback); the Hamilton-Ivey pinching then forces the     *)
(* scalar curvature to grow like Q n log Q n, while the scalar curvature of  *)
(* the rescaled approximants stays bounded (C^2 closeness again).            *)
(* ========================================================================= *)

needs "src/pc_p2c_flloc.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_rfa_secpres.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The growth of z (log z - 3), and the curvature of one                     *)
(* rescaled approximant at a point (scaling and pullback by a diffeo).      *)
(* ------------------------------------------------------------------------- *)

let P2CP_ZLOG = prove
 (`!y z. exp(&3) <= y /\ y <= z ==> y * (log y - &3) <= z * (log z - &3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
   [MP_TAC(SPEC `&3` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= log y /\ log y <= log z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `log(exp(&3)) <= log y` MP_TAC THENL
       [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
        REWRITE_TAC[LOG_EXP]];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `z * (log y - &3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

(* The rescaled pullback of a slice metric by a diffeo of an open set W of   *)
(* the limit manifold, read in the chart at y.                               *)

let P2CP_APPROX_CURV = prove
 (`!(top:B topology) atlas (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool)
    gX W (f:B->A) f' q y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topX atlasX /\
     riemannian_metric atlasX gX /\
     mfd_diffeo top atlas W topX atlasX (IMAGE f W) f f' /\ y IN W /\ &0 < q
     ==> metric_field (IMAGE (SND(chart_at atlas y)) (FST(chart_at atlas y) INTER W))
                      (\z. q %% rfs_pullback atlasX (f o chart_inv (chart_at atlas y)) gX z) /\
         SND(chart_at atlas y) y IN
         IMAGE (SND(chart_at atlas y)) (FST(chart_at atlas y) INTER W) /\
         lscalar (\z. q %% rfs_pullback atlasX (f o chart_inv (chart_at atlas y)) gX z)
                 (SND(chart_at atlas y) y) = mfd_scalar atlasX gX (f y) / q /\
         !u v. ~collinear {vec 0,u,v}
               ==> ?u' v'. ~collinear {vec 0,u',v'} /\
                           lsectional (\z. q %% rfs_pullback atlasX
                                                  (f o chart_inv (chart_at atlas y)) gX z)
                                      (SND(chart_at atlas y) y) u v =
                           mfd_sectional atlasX gX (f y) u' v' / q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (top:B topology) W` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [SUBGOAL_THEN `(W:B->bool) SUBSET topspace top` MP_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)` THEN
  ABBREV_TAC `e = (f:B->A) o chart_inv (c:(B->bool)#(B->real^3))` THEN
  ABBREV_TAC `S = IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:B->bool))` THEN
  SUBGOAL_THEN `SND(c:(B->bool)#(B->real^3)) y IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (topX:A topology) atlasX (S:real^3->bool) (e:real^3->A)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "e"] THEN MATCH_MP_TAC P2CV_CHART_PARAM THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `IMAGE (f:B->A) W`; `f':A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (S:real^3->bool) (rfs_pullback atlasX (e:real^3->A) (gX:A->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `topX:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) (SND(c:(B->bool)#(B->real^3)) y) = (f:B->A) y` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`S:real^3->bool`; `rfs_pullback atlasX (e:real^3->A) (gX:A->real^3^3)`;
                   `q:real`; `SND(c:(B->bool)#(B->real^3)) y`] LSCALAR_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:A->real^3^3`; `S:real^3->bool`; `e:real^3->A`;
                   `SND(c:(B->bool)#(B->real^3)) y`] APX_PULLBACK_SCALAR_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `gX:A->real^3^3`;
                 `S:real^3->bool`; `e:real^3->A`; `SND(c:(B->bool)#(B->real^3)) y`]
                APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `N':real^3->bool`
    (X_CHOOSE_THEN `h':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`N':real^3->bool`; `N:real^3->bool`;
                 `SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) ((f:B->A) y)) o
                  (e:real^3->A)`;
                 `h':real^3->real^3`; `SND(c:(B->bool)#(B->real^3)) y`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative
                    (SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) ((f:B->A) y)) o
                     (e:real^3->A)) (at (SND(c:(B->bool)#(B->real^3)) y))` THEN
  SUBGOAL_THEN `!p r:real^3. ~collinear {vec 0,p,r} ==> ~collinear {vec 0,(D:real^3->real^3) p,D r}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `{vec 0,(D:real^3->real^3) p,D r} = IMAGE D {vec 0,p,r}` SUBST1_TAC THENL
     [MP_TAC(MATCH_MP LINEAR_0 (ASSUME `linear (D:real^3->real^3)`)) THEN
      SIMP_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`D:real^3->real^3`; `{vec 0:real^3,p,r}`] COLLINEAR_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(D:real^3->real^3) u`; `(D:real^3->real^3) v`] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `rfs_pullback atlasX (e:real^3->A) (gX:A->real^3^3)`;
                 `q:real`; `SND(c:(B->bool)#(B->real^3)) y`; `u:real^3`; `v:real^3`]
                APX_LSECTIONAL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `gX:A->real^3^3`;
                 `S:real^3->bool`; `e:real^3->A`; `SND(c:(B->bool)#(B->real^3)) y`;
                 `u:real^3`; `v:real^3`] APX_PULLBACK_SECTIONAL_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Thm 5.33.                                                                 *)
(* ------------------------------------------------------------------------- *)

let P2CP_LE_POW2 = prove
 (`!x. &1 <= x ==> x <= x pow 2`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

let P2CP_PINCHED_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)).
     rfs_pinched V <=>
     !t x. &0 <= t /\ x IN topspace(rfs_vtop V t)
           ==> rfs_pinched_at (rfs_vatlas V t) (rfs_vmetric V t) t x`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_pinched; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

(* The arithmetic of the contradiction: sectional curvature <= --K0 q / 2,   *)
(* the pinching, and scalar curvature <= q (R0 + 1) for q large.            *)

let P2CP_PINCH_CONTRA = prove
 (`!K0 R0 q sm R tau.
     &0 < K0 /\ &0 < q /\ &0 <= tau /\
     &2 / K0 * (exp(&3) + exp(&4 + abs(R0 + &1) / K0)) < q /\
     sm <= --(K0 * q / &2) /\
     (&0 < --sm ==> &2 * --sm * (log(--sm) + log(&1 + tau) - &3) <= R) /\
     R <= q * (R0 + &1)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `y1 = K0 * q / &2` THEN
  SUBGOAL_THEN `exp(&3) <= y1 /\ exp(&4 + abs(R0 + &1) / K0) <= y1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(&3) + exp(&4 + abs(R0 + &1) / K0) < y1` MP_TAC THENL
     [EXPAND_TAC "y1" THEN
      ABBREV_TAC `E = exp(&3) + exp(&4 + abs(R0 + &1) / K0)` THEN
      SUBGOAL_THEN `E = K0 / &2 * (&2 / K0 * E)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < K0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `K0 * q / &2 = K0 / &2 * q` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `&3` REAL_EXP_POS_LT) THEN
      MP_TAC(SPEC `&4 + abs(R0 + &1) / K0` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < y1` ASSUME_TAC THENL
   [MP_TAC(SPEC `&3` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y1 <= --sm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&1 + tau)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y1 * (log y1 - &3) <= --sm * (log(--sm) - &3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CP_ZLOG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&4 + abs(R0 + &1) / K0 <= log y1` ASSUME_TAC THENL
   [SUBGOAL_THEN `log(exp(&4 + abs(R0 + &1) / K0)) <= log y1` MP_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      REWRITE_TAC[LOG_EXP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `--sm * (log(--sm) - &3) <= --sm * (log(--sm) + log(&1 + tau) - &3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * y1 * (log y1 - &3) <= q * (R0 + &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * --sm * (log(--sm) + log(&1 + tau) - &3)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "y1" THEN
  SUBGOAL_THEN `&2 * (K0 * q / &2) * (log (K0 * q / &2) - &3) =
                q * (K0 * (log (K0 * q / &2) - &3))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `K0 * (&1 + abs(R0 + &1) / K0) <= K0 * (log y1 - &3)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `K0 * (&1 + abs(R0 + &1) / K0) = K0 + abs(R0 + &1)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < K0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Thm 5.33 for views with Riemannian limit metrics. *)

let P2CP_SEC_NONNEG = prove
 (`!V x t Q J (top:B topology) atlas g xl.
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) /\
          rfs_pinched (V n) /\ (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {})) /\
     (!B. ?N. !n. N <= n ==> B < Q n) /\
     p3_flow_limit_on V x t Q J (top,atlas) g xl /\
     (!s. s IN J ==> riemannian_metric atlas (g s))
     ==> !s y u v. s IN J /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                   ==> &0 <= mfd_sectional atlas (g s) y u v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
    (CONJUNCTS_THEN2 (LABEL_TAC "fl") (LABEL_TAC "riem")))) THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `y0:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  USE_THEN "fl" (MP_TAC o REWRITE_RULE[p3_flow_limit_on]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Qpos") (X_CHOOSE_THEN `W:num->B->bool`
    (X_CHOOSE_THEN `phi:num->B->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv"))))))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y0:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s0)` ASSUME_TAC THENL
   [USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `S0 = IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)))
                         (FST(chart_at atlas y0))` THEN
  ABBREV_TAC `G0 = metric_local (atlas:((B->bool)#(B->real^3))->bool) (chart_at atlas (y0:B))
                     ((g:real->B->real^3^3) s0)` THEN
  ABBREV_TAC `yc = SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)) y0` THEN
  SUBGOAL_THEN `metric_field (S0:real^3->bool) (G0:real^3->real^3^3) /\ (yc:real^3) IN S0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "G0"; "yc"] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->B->real^3^3) s0)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `K0 = --(mfd_sectional atlas ((g:real->B->real^3^3) s0) (y0:B) u v)` THEN
  SUBGOAL_THEN `&0 < K0 /\ lsectional (G0:real^3->real^3^3) yc u v = --K0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K0"; "G0"; "yc"] THEN REWRITE_TAC[mfd_sectional] THEN
    UNDISCH_TAC `mfd_sectional atlas ((g:real->B->real^3^3) s0) (y0:B) u v < &0` THEN
    REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `R0 = lscalar (G0:real^3->real^3^3) yc` THEN
  (* a frame and a bound for the curvature of the limit at yc *)
  MP_TAC(ISPECL [`S0:real^3->bool`; `G0:real^3->real^3^3`; `yc:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K1 = max (&1) (lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc)` THEN
  SUBGOAL_THEN `&1 <= K1 /\ lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc <= K1 pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `max (&1) (lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc)` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC P2CP_LE_POW2 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 4 (S0:real^3->bool) (lrm4 (G0:real^3->real^3^3))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S0:real^3->bool`; `G0:real^3->real^3^3`] LRM4_TENSOR_FIELD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. abs(lrm4 (G0:real^3->real^3^3) yc a) <=
        abs K1 * norm((M:real^3^3) ** a 1) * norm(M ** a 2) * norm(M ** a 3) * norm(M ** a 4)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:num->real^3` THEN
    MP_TAC(ISPECL [`4`; `S0:real^3->bool`; `G0:real^3->real^3^3`; `lrm4 (G0:real^3->real^3^3)`;
                   `yc:real^3`; `M:real^3^3`; `a:num->real^3`; `K1 pow 2`]
                  LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4; POW_2_SQRT_ABS] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc <= K1 pow 2` THEN
    REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S0:real^3->bool`; `G0:real^3->real^3^3`; `yc:real^3`; `M:real^3^3`;
                 `abs(K1:real)`] LRG_RM0_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN DISCH_THEN(LABEL_TAC "RM0") THEN
  (* the closeness needed and the time of comparison *)
  ABBREV_TAC `delta = min (&1 / &10) (min (K0 / (&16 * (&1 + abs K1)))
                                         (inv(&72 * (&1 + abs K1))))` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= &1 / &10 /\ &8 * (&1 + abs K1) * delta <= K0 / &2 /\
                &8 * &9 * (&1 + abs K1) * delta <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 + abs K1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "delta" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&8 * (&1 + abs K1) * K0 / (&16 * (&1 + abs K1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `&8 * (&1 + abs K1) * K0 / (&16 * (&1 + abs K1)) = K0 / &2`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < &1 + abs K1` THEN CONV_TAC REAL_FIELD; REWRITE_TAC[REAL_LE_REFL]]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&8 * &9 * (&1 + abs K1) * inv(&72 * (&1 + abs K1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `&8 * &9 * (&1 + abs K1) * inv(&72 * (&1 + abs K1)) = &1`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < &1 + abs K1` THEN CONV_TAC REAL_FIELD; REWRITE_TAC[REAL_LE_REFL]]]];
    ALL_TAC] THEN
  USE_THEN "conv" (MP_TAC o SPECL [`s0:real`; `s0:real`; `{y0:B}`; `2`; `delta pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET; COMPACT_IN_SING] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  USE_THEN "Qinf" (MP_TAC o SPEC `&2 / K0 * (exp(&3) + exp(&4 + abs(R0 + &1) / K0))`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  USE_THEN "k0" (MP_TAC o C MP (ARITH_RULE `k0 <= k0 + N:num`) o SPEC `k0 + N:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[SING_SUBSET]) (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `psi:A->B` o
     C MP (CONJ (SPEC `s0:real` REAL_LE_REFL) (SPEC `s0:real` REAL_LE_REFL)) o SPEC `s0:real`)
    (MP_TAC o SPECL [`s0:real`; `y0:B`]))) THEN
  REWRITE_TAC[REAL_LE_REFL; IN_SING] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `k = k0 + N:num` THEN
  ABBREV_TAC `tau = (t:num->real) k + s0 / Q k` THEN
  SUBGOAL_THEN `&2 / K0 * (exp(&3) + exp(&4 + abs(R0 + &1) / K0)) < (Q:num->real) k`
  ASSUME_TAC THENL
   [USE_THEN "N" MATCH_MP_TAC THEN EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the slice at tau *)
  SUBGOAL_THEN `(phi:num->B->A) k y0 IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) k) (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                   (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi` THEN
    REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE ((phi:num->B->A) k) (W k) SUBSET topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)`
    MP_TAC THENL [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `tau:real`; `(phi:num->B->A) k y0`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= tau` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `(phi:num->B->A) k y0 IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)` THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `tau < &0`) o SPEC `tau:real` o check (fun th ->
      can (find_term ((=) `discrete_topology:(A->bool)->A topology`)) (concl th))) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  (* the approximant at yc *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau`; `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau`;
                 `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`; `(Q:num->real) k`;
                 `y0:B`] P2CP_APPROX_CURV) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Gk = \z. (Q:num->real) k %%
                   rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                     ((phi:num->B->A) k o chart_inv (chart_at (atlas:((B->bool)#(B->real^3))->bool)
                                                         (y0:B)))
                     (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) z` THEN
  ABBREV_TAC `S = IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)))
                        (FST(chart_at atlas y0) INTER (W:num->B->bool) k)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "scal") (MP_TAC o SPECL [`u:real^3`; `v:real^3`])))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
  (* C^2 closeness at yc *)
  SUBGOAL_THEN `metric_field (S:real^3->bool) (G0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `S0:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["S"; "S0"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) < delta /\
                &0 <= sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G0:real^3->real^3^3`; `Gk:real^3->real^3^3`; `yc:real^3`;
                 `M:real^3^3`; `abs(K1:real)`] APX_SECTIONAL_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K1:real`; `S:real^3->bool`; `G0:real^3->real^3^3`; `Gk:real^3->real^3^3`;
                 `yc:real^3`] APX_SCALAR_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&8 * (&1 + abs K1) * sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) <=
                &8 * (&1 + abs K1) * delta /\
                &8 * &9 * (&1 + abs K1) * sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) <=
                &8 * &9 * (&1 + abs K1) * delta` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC; ALL_TAC]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the sectional curvature and sec_min of the view at phi k y0 *)
  SUBGOAL_THEN `mfd_sectional (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                  ((phi:num->B->A) k y0) u' v' <= --(K0 * Q k / &2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_sectional (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                    ((phi:num->B->A) k y0) u' v' =
                  (Q:num->real) k * lsectional (Gk:real^3->real^3^3) yc u v` SUBST1_TAC THENL
     [UNDISCH_TAC `lsectional (Gk:real^3->real^3^3) yc u v =
                   mfd_sectional (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                     ((phi:num->B->A) k y0) u' v' / (Q:num->real) k` THEN
      UNDISCH_TAC `&0 < (Q:num->real) k` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Q:num->real) k * --(K0 / &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_sec_min (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                  ((phi:num->B->A) k y0) <= --(K0 * Q k / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_sectional (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                  ((phi:num->B->A) k y0) u' v'` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN
    EXISTS_TAC `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the scalar curvature of the view at phi k y0 *)
  SUBGOAL_THEN `mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                  ((phi:num->B->A) k y0) <= (Q:num->real) k * (R0 + &1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `lscalar (Gk:real^3->real^3^3) yc <= R0 + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "scal" SUBST1_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the pinching *)
  USE_THEN "views" (MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC `k:num`) THEN
  REWRITE_TAC[P2CP_PINCHED_ALT] THEN
  DISCH_THEN(MP_TAC o SPECL [`tau:real`; `(phi:num->B->A) k y0`]) THEN
  ASM_REWRITE_TAC[rfs_pinched_at] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC P2CP_PINCH_CONTRA THEN
  MAP_EVERY EXISTS_TAC
   [`K0:real`; `R0:real`; `(Q:num->real) k`;
    `mfd_sec_min (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) ((phi:num->B->A) k y0)`;
    `mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) ((phi:num->B->A) k y0)`;
    `tau:real`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The headline: P2C_THM_5_33_STATEMENT, for views with Riemannian limit     *)
(* metrics.                                                                  *)
(* ------------------------------------------------------------------------- *)

let P2CP_THM_5_33 = prove
 (`!(u:A->bool) (w:B->bool). P2C_THM_5_33_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2C_THM_5_33_STATEMENT] THEN MATCH_ACCEPT_TAC P2CP_SEC_NONNEG);;

