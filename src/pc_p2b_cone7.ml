(* ========================================================================= *)
(* Unit pc_p2b_cone7: step (C) of the blow-up of MT Sec 10.6: distance       *)
(* comparison for local limits in the form of                                *)
(* P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT (one chart phi k on a ball of       *)
(* real^3, pullback metrics converging to the limit metric in lck_dist2).    *)
(* Library-style core P2BK_OSA_DIST_COMPARE: for a diffeomorphism phi from   *)
(* an open set U of real^3 (open_set_atlas U, metric G0) into a manifold     *)
(* whose pulled-back metric is d-close to G0 as quadratic forms, distances   *)
(* near a point of U agree up to the factors sqrt(1 + d) and                 *)
(* 1 / sqrt(1 - d).  Built on P2BC_BALL_IMAGE_IN and                         *)
(* P2BC_BALL_PREIMAGE_IN (pc_p2b_cap) and LIM_CURVES_STAY (pc_lim_close).    *)
(* ========================================================================= *)

needs "src/pc_p2b_lcreqn.ml";;
needs "src/pc_lim_close.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_apx_local.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Open-set manifolds as sources of diffeomorphisms.  The manifold pullback  *)
(* from open_set_atlas U is the chart-level pullback rfs_pullback            *)
(* (P2BK_OSA_PB), and a parametrization restricts to a diffeomorphism from   *)
(* the open-set manifold of a smaller open set (P2BK_OSA_DIFFEO).            *)
(* ========================================================================= *)

let P2BK_OSA_CHART_INV = prove
 (`!U (z:real^N). open U /\ z IN U ==> chart_inv (U,(\x:real^N. x)) z = z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`; `open_set_atlas (U:real^N->bool)`;
                 `U:real^N->bool`; `\x:real^N. x`] CHART_INV) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_ATLAS_CASES] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

let P2BK_OSA_PB = prove
 (`!U (atlas:((B->bool)#(B->real^N))->bool) (e:real^N->B) (g:B->real^N^N) y.
     open U /\ y IN U
     ==> mfd_pullback_metric (open_set_atlas U) atlas e g y = rfs_pullback atlas e g y`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mfd_pullback_metric; rfs_pullback; RFB_OPEN_SET_CHART_AT; SND] THEN
  REWRITE_TAC[LRG_MPULLBACK_EQ] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (SND (chart_at (atlas:((B->bool)#(B->real^N))->bool) ((e:real^N->B) y)) o e o
       chart_inv (U,(\x:real^N. x))) (at y) =
    frechet_derivative (SND (chart_at atlas (e y)) o e) (at y)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[o_THM; P2BK_OSA_CHART_INV];
    ASM_SIMP_TAC[o_THM; P2BK_OSA_CHART_INV]]);;

let P2BK_OSA_DIFFEO = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) s (e:real^N->B) U.
     mfd_param top atlas s e /\ open U /\ U SUBSET s
     ==> ?e'. mfd_diffeo (subtopology euclidean U) (open_set_atlas U) U
                         top atlas (IMAGE e U) e e' /\
              (!x. x IN U ==> e'(e x) = x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e':B->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  EXISTS_TAC `e':B->real^N` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`; `s:real^N->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `IMAGE (e:real^N->B) s`; `e:real^N->B`; `e':B->real^N`; `U:real^N->bool`]
    MFD_DIFFEO_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM OPEN_IN]; ALL_TAC] THEN
  REWRITE_TAC[mfd_diffeo] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sm1") (LABEL_TAC "sm2"))))) THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV;
                  SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_smooth_map; RFB_OPEN_SET_ATLAS_CASES] THEN
    MAP_EVERY X_GEN_TAC [`c:(real^N->bool)#(real^N->real^N)`;
                         `c':(B->bool)#(B->real^N)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    REWRITE_TAC[FST; SND; IMAGE_ID; INTER_IDEMPOT] THEN
    USE_THEN "sm1" (MP_TAC o SPECL [`((:real^N),(\x:real^N. x))`; `c':(B->bool)#(B->real^N)`] o
                    REWRITE_RULE[mfd_smooth_map]) THEN
    ASM_REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND; IMAGE_ID; INTER_UNIV] THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `SND (c':(B->bool)#(B->real^N)) o (e:real^N->B) o
                chart_inv ((:real^N),(\x:real^N. x))` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[P2BK_OSA_CHART_INV; OPEN_UNIV; IN_UNIV];
    REWRITE_TAC[mfd_smooth_map; RFB_OPEN_SET_ATLAS_CASES] THEN
    MAP_EVERY X_GEN_TAC [`c:(B->bool)#(B->real^N)`;
                         `c':(real^N->bool)#(real^N->real^N)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    REWRITE_TAC[FST; SND] THEN
    USE_THEN "sm2" (MP_TAC o SPECL [`c:(B->bool)#(B->real^N)`; `((:real^N),(\x:real^N. x))`] o
                    REWRITE_RULE[mfd_smooth_map]) THEN
    ASM_REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND; IN_UNIV] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `y:B` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:B) IN IMAGE (e:real^N->B) U` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    ASM_MESON_TAC[SUBSET]]);;

(* ========================================================================= *)
(* The two halves of the distance comparison for an open-set source.  Upper  *)
(* bound from P2BC_BALL_IMAGE_IN; lower bound from P2BC_BALL_PREIMAGE_IN,    *)
(* with the curve condition from LIM_CURVES_STAY.                            *)
(* ========================================================================= *)

(* Two elementary limit forms. *)

let P2BK_LE_FROM_LT = prove
 (`!a b q. &0 < q /\ &0 <= b /\ (!rho. b < rho ==> a < q * rho) ==> a <= q * b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b + (a - q * b) / (&2 * q)`) THEN
  SUBGOAL_THEN `&0 < (a - q * b) / (&2 * q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN UNDISCH_TAC `q * b < a` THEN UNDISCH_TAC `&0 < q` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 < (a - q * b) / (&2 * q)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q * (b + (a - q * b) / (&2 * q)) = (a + q * b) / &2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  UNDISCH_TAC `q * b < a` THEN REAL_ARITH_TAC);;

let P2BK_LE_FROM_LT2 = prove
 (`!a b c M. &0 < c /\ a < M /\ (!r. a < r /\ r <= M ==> b < c * r) ==> b <= c * a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min M (a + (b - c * a) / (&2 * c))`) THEN
  SUBGOAL_THEN `&0 < (b - c * a) / (&2 * c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN UNDISCH_TAC `c * a < b` THEN UNDISCH_TAC `&0 < c` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `&0 < (b - c * a) / (&2 * c)` THEN UNDISCH_TAC `a < M` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * min M (a + (b - c * a) / (&2 * c)) <= (b + c * a) / &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * (a + (b - c * a) / (&2 * c))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  UNDISCH_TAC `c * a < b` THEN REAL_ARITH_TAC);;

(* Upper bound: distances in the target are at most sqrt(1 + d) times those *)
(* of the open-set source. *)

let P2BK_OSA_DIST_UPPER = prove
 (`!top atlas (gM:B->real^3^3) (phi:real^3->B) phi' (G0:real^3->real^3^3) U d w w'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas gM /\
     open U /\ metric_field U G0 /\
     mfd_diffeo (subtopology euclidean U) (open_set_atlas U) U top atlas (IMAGE phi U)
                phi phi' /\
     &0 <= d /\
     (!y v. y IN U
            ==> v dot (rfs_pullback atlas phi gM y ** v) <= (&1 + d) * (v dot (G0 y ** v))) /\
     w IN U /\ mfd_joinable (subtopology euclidean U,open_set_atlas U) w w'
     ==> mfd_joinable (top,atlas) (phi w) (phi w') /\
         mfd_dist (top,atlas) gM (phi w) (phi w') <=
         sqrt(&1 + d) * mfd_dist (subtopology euclidean U,open_set_atlas U) G0 w w'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!rho. mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w w' < rho
          ==> mfd_joinable (top,atlas) ((phi:real^3->B) w) (phi w') /\
              mfd_dist (top,atlas) (gM:B->real^3^3) (phi w) (phi w') < sqrt(&1 + d) * rho`
    (LABEL_TAC "key") THENL
   [X_GEN_TAC `rho:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`; `open_set_atlas (U:real^3->bool)`;
                   `G0:real^3->real^3^3`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`;
                   `gM:B->real^3^3`; `U:real^3->bool`; `IMAGE (phi:real^3->B) U`;
                   `phi:real^3->B`; `phi':B->real^3`; `w:real^3`; `rho:real`;
                   `sqrt(&1 + d) * rho`; `&1 + d`; `w':real^3`] P2BC_BALL_IMAGE_IN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_RIEMANNIAN; REAL_LE_REFL;
                   REAL_ARITH `&0 <= d ==> &0 < &1 + d`] THEN
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `gamma:real->real^3` THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`;
                       `open_set_atlas (U:real^3->bool)`;
                       `gamma:real->real^3`; `&0`; `&1`; `t:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
        ASM_SIMP_TAC[P2BK_OSA_PB];
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "key" (MP_TAC o SPEC
      `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w w' + &1`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BK_LE_FROM_LT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN UNDISCH_TAC `&0 <= d` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_RIEMANNIAN];
    X_GEN_TAC `rho:real` THEN DISCH_TAC THEN USE_THEN "key" (MP_TAC o SPEC `rho:real`) THEN
    ASM_SIMP_TAC[]]);;

(* Preimages: a point q of the target near phi w lies in the image, and    *)
(* its preimage is within 1/sqrt(1 - d) times the target distance of w, for *)
(* w near y1 and short distances (LIM_CURVES_STAY gives the curve clause of *)
(* P2BC_BALL_PREIMAGE_IN).                                                  *)

let P2BK_OSA_PREIMAGE = prove
 (`!top atlas (gM:B->real^3^3) (phi:real^3->B) phi' (G0:real^3->real^3^3) U y1 R R0 d w q.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas gM /\
     open U /\ metric_field U G0 /\
     mfd_diffeo (subtopology euclidean U) (open_set_atlas U) U top atlas (IMAGE phi U)
                phi phi' /\
     compact_in (subtopology euclidean U)
       (subtopology euclidean U closure_of
        mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R) /\
     subtopology euclidean U closure_of
       mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R SUBSET U /\
     &0 <= d /\ d < &1 /\
     (!y v. y IN U
            ==> (&1 - d) * (v dot (G0 y ** v)) <= v dot (rfs_pullback atlas phi gM y ** v)) /\
     w IN mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R0 /\
     mfd_joinable (top,atlas) (phi w) q /\
     mfd_dist (top,atlas) gM (phi w) q < sqrt(&1 - d) * (R - R0)
     ==> q IN IMAGE phi U /\
         mfd_joinable (subtopology euclidean U,open_set_atlas U) w (phi' q) /\
         mfd_dist (subtopology euclidean U,open_set_atlas U) G0 w (phi' q) <=
         inv(sqrt(&1 - d)) * mfd_dist (top,atlas) gM (phi w) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (U:real^3->bool)) (open_set_atlas U) /\
                riemannian_metric (open_set_atlas U) (G0:real^3->real^3^3)`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN U` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`; `open_set_atlas (U:real^3->bool)`;
                   `G0:real^3->real^3^3`; `y1:real^3`; `R0:real`] MFD_BALL_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - d /\ &0 < sqrt(&1 - d)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC SQRT_POS_LT] THEN
    UNDISCH_TAC `d < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q < r /\
        r <= sqrt(&1 - d) * (R - R0)
        ==> q IN IMAGE phi U /\
            mfd_joinable (subtopology euclidean U,open_set_atlas U) w ((phi':B->real^3) q) /\
            mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w (phi' q) <
            inv(sqrt(&1 - d)) * r`
    (LABEL_TAC "key") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`; `open_set_atlas (U:real^3->bool)`;
                   `G0:real^3->real^3^3`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`;
                   `gM:B->real^3^3`; `U:real^3->bool`; `IMAGE (phi:real^3->B) U`;
                   `phi:real^3->B`; `phi':B->real^3`; `w:real^3`; `r:real`; `inv(&1 - d)`;
                   `q:B`] P2BC_BALL_PREIMAGE_IN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`;
                       `open_set_atlas (U:real^3->bool)`; `G0:real^3->real^3^3`;
                       `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `gM:B->real^3^3`; `U:real^3->bool`; `IMAGE (phi:real^3->B) U`;
                       `phi:real^3->B`; `phi':B->real^3`; `y1:real^3`; `w:real^3`;
                       `R:real`; `R0:real`; `&1 - d`; `gamma:real->B`] LIM_CURVES_STAY) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[P2BK_OSA_PB] THEN
          UNDISCH_TAC `mfd_length atlas (gM:B->real^3^3) gamma (&0) (&1) < r` THEN
          UNDISCH_TAC `r <= sqrt(&1 - d) * (R - R0)` THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t
                                ==> (x:B) IN IMAGE (f:real^3->B) s ==> x IN IMAGE f t`) THEN
        MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`;
                       `open_set_atlas (U:real^3->bool)`;
                       `G0:real^3->real^3^3`; `y1:real^3`; `R:real`] MFD_BALL_OPEN) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
        REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
        MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN DISCH_TAC THEN
        ASM_SIMP_TAC[P2BK_OSA_PB] THEN
        MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&1 - d` THEN
        ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[SQRT_INV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "key" (MP_TAC o SPEC
      `(mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q +
        sqrt(&1 - d) * (R - R0)) / &2`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q <
                 sqrt(&1 - d) * (R - R0)` THEN REAL_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC P2BK_LE_FROM_LT2 THEN EXISTS_TAC `sqrt(&1 - d) * (R - R0)` THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  USE_THEN "key" (MP_TAC o SPEC `r:real`) THEN ASM_SIMP_TAC[]);;

(* Lower bound: distances in the open-set source are at most 1/sqrt(1 - d)  *)
(* times those of the target, for points near y1 and short distances.      *)

let P2BK_OSA_DIST_LOWER = prove
 (`!top atlas (gM:B->real^3^3) (phi:real^3->B) phi' (G0:real^3->real^3^3) U y1 R R0 d w w'.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas gM /\
     open U /\ metric_field U G0 /\
     mfd_diffeo (subtopology euclidean U) (open_set_atlas U) U top atlas (IMAGE phi U)
                phi phi' /\
     (!x. x IN U ==> phi'(phi x) = x) /\
     compact_in (subtopology euclidean U)
       (subtopology euclidean U closure_of
        mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R) /\
     subtopology euclidean U closure_of
       mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R SUBSET U /\
     &0 <= d /\ d < &1 /\
     (!y v. y IN U
            ==> (&1 - d) * (v dot (G0 y ** v)) <= v dot (rfs_pullback atlas phi gM y ** v)) /\
     w IN mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R0 /\ w' IN U /\
     mfd_joinable (top,atlas) (phi w) (phi w') /\
     mfd_dist (top,atlas) gM (phi w) (phi w') < sqrt(&1 - d) * (R - R0)
     ==> mfd_joinable (subtopology euclidean U,open_set_atlas U) w w' /\
         mfd_dist (subtopology euclidean U,open_set_atlas U) G0 w w' <=
         inv(sqrt(&1 - d)) * mfd_dist (top,atlas) gM (phi w) (phi w')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `gM:B->real^3^3`;
                 `phi:real^3->B`; `phi':B->real^3`; `G0:real^3->real^3^3`; `U:real^3->bool`;
                 `y1:real^3`; `R:real`; `R0:real`; `d:real`; `w:real^3`;
                 `(phi:real^3->B) w'`] P2BK_OSA_PREIMAGE) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* A small source ball with compact closure in the open-set manifold, and a  *)
(* Euclidean ball inside a smaller source ball (from                         *)
(* MFD_DIST_LOCAL_EUCLIDEAN at the identity chart).                          *)
(* ========================================================================= *)

let P2BK_OSA_BALL_SETUP = prove
 (`!U (G0:real^3->real^3^3) y1.
     open U /\ metric_field U G0 /\ y1 IN U
     ==> ?R r rk. &0 < R /\ &0 < r /\ ball(y1,r) SUBSET U /\
               &0 < rk /\ cball(y1,rk) SUBSET U /\
               mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R SUBSET cball(y1,rk) /\
               compact_in (subtopology euclidean U)
                 (subtopology euclidean U closure_of
                  mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R) /\
               subtopology euclidean U closure_of
                 mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R SUBSET U /\
               ball(y1,r) SUBSET
                 mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 (R / &8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`; `open_set_atlas (U:real^3->bool)`;
                 `G0:real^3->real^3^3`; `U:real^3->bool`; `\z:real^3. z`; `y1:real^3`]
    MFD_DIST_LOCAL_EUCLIDEAN) THEN
  ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN; OPEN_SET_ATLAS;
               RFB_OPEN_SET_RIEMANNIAN; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:real` (X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "out"))))))))) THEN
  ABBREV_TAC `R = c1 * rr / &2` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c2` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < c1` THEN UNDISCH_TAC `c1 <= c2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = min rr (R / &8 / c2)` THEN
  SUBGOAL_THEN `&0 < r /\ r <= rr /\ c2 * r <= R / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c2 * (R / &8 / c2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [UNDISCH_TAC `&0 < c2` THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < c2` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 R SUBSET
    ball(y1,rr / &2)`
    ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(y:real^3) IN U /\ y IN ball(y1,rr)` THENL
     [USE_THEN "in" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      REWRITE_TAC[IN_BALL] THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
      EXISTS_TAC `c1:real` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `c1 * dist(y1:real^3,y) <=
                   mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 y` THEN
      UNDISCH_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 y < R` THEN
      EXPAND_TAC "R" THEN REAL_ARITH_TAC;
      USE_THEN "out" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 y < R` THEN
      EXPAND_TAC "R" THEN
      SUBGOAL_THEN `&0 < c1 * rr` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(y1:real^3,rr / &2) SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y1:real^3,rr)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN
    UNDISCH_TAC `&0 < rr` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure(U INTER mfd_ball (subtopology euclidean U,open_set_atlas U)
                      (G0:real^3->real^3^3) y1 R) SUBSET cball(y1,rr / &2)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CBALL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y1:real^3,rr / &2)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subtopology euclidean U closure_of
      mfd_ball (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 R =
    closure(U INTER mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 R)`
    ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET u ==> u INTER t = t`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y1:real^3,rr / &2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`R:real`; `r:real`; `rr / &2`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < rr / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < rr` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 R SUBSET
    cball(y1,rr / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y1:real^3,rr / &2)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y1:real^3,rr)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y1:real^3,rr)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY_EUCLIDEAN; COMPACT_EQ_BOUNDED_CLOSED; CLOSED_CLOSURE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y1:real^3,rr / &2)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(y1:real^3,rr / &2)` THEN
    ASM_REWRITE_TAC[BOUNDED_CBALL];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y1:real^3,rr / &2)` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN U /\ y IN ball(y1,rr)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN CONJ_TAC THENL
       [UNDISCH_TAC `cball(y1:real^3,rr) SUBSET U` THEN REWRITE_TAC[SUBSET; IN_CBALL] THEN
        DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `dist(y1:real^3,y) < r` THEN
        UNDISCH_TAC `r <= rr` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `dist(y1:real^3,y) < r` THEN UNDISCH_TAC `r <= rr` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "in" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `c2 * dist(y1:real^3,y)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `c2 * r` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]]);;

(* On a compact convex subset K of U, the distance of the open-set manifold *)
(* is at most a constant times the Euclidean distance (segments, with       *)
(* GRGD_METRIC_BOUNDS and GRGD_SEGMENT_LENGTH_UPPER).                        *)

let P2BK_OSA_DIST_EUCLID = prove
 (`!U (G0:real^3->real^3^3) K.
     open U /\ metric_field U G0 /\ compact K /\ convex K /\ K SUBSET U
     ==> ?C. &0 < C /\
             !p q. p IN K /\ q IN K
                   ==> mfd_joinable (subtopology euclidean U,open_set_atlas U) p q /\
                       mfd_dist (subtopology euclidean U,open_set_atlas U) G0 p q <=
                       C * dist(p,q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`open_set_atlas (U:real^3->bool)`; `G0:real^3->real^3^3`; `U:real^3->bool`;
                 `\x:real^3. x`; `K:real^3->bool`] GRGD_METRIC_BOUNDS) THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `sqrt C` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `c <= C` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real^3`; `q:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[p:real^3,q] SUBSET K` ASSUME_TAC THENL
   [UNDISCH_TAC `convex(K:real^3->bool)` THEN REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN U /\ (q:real^3) IN U` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`; `open_set_atlas (U:real^3->bool)`;
                 `U:real^3->bool`; `\x:real^3. x`; `p:real^3`; `q:real^3`] GRGD_CHART_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ABBREV_TAC `gam = \t. chart_inv (U,(\x:real^3. x)) (p + t % (q - p))` THEN
  SUBGOAL_THEN `(gam:real->real^3) (&0) = p /\ gam (&1) = q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gam" THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                VECTOR_ARITH `p + q - p:real^N = q`] THEN
    ASM_SIMP_TAC[P2BK_OSA_CHART_INV];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`; `open_set_atlas (U:real^3->bool)`;
                   `gam:real->real^3`; `&0`; `&1`] MFD_C1_CURVE_JOINABLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length (open_set_atlas U) (G0:real^3->real^3^3) gam (&0) (&1)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (U:real^3->bool)`; `open_set_atlas (U:real^3->bool)`;
                   `G0:real^3->real^3^3`; `gam:real->real^3`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_RIEMANNIAN];
    ALL_TAC] THEN
  EXPAND_TAC "gam" THEN MATCH_MP_TAC GRGD_SEGMENT_LENGTH_UPPER THEN
  MAP_EVERY EXISTS_TAC [`subtopology euclidean (U:real^3->bool)`; `c:real`; `K:real^3->bool`] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_RIEMANNIAN; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID]);;

(* ========================================================================= *)
(* The distance comparison near a point of an open-set source (library       *)
(* form).  The radii r, rk, rho0 depend only on U, G0 and y1; the comparison *)
(* holds for every target manifold, diffeomorphism and d <= 1/2.  Points of  *)
(* the target within rho0 of phi w are images of points of the closed ball   *)
(* cball(y1,rk).                                                             *)
(* ========================================================================= *)

let P2BK_OSA_DIST_COMPARE = prove
 (`!U (G0:real^3->real^3^3) y1.
     open U /\ metric_field U G0 /\ y1 IN U
     ==> ?r rk rho0.
             &0 < r /\ &0 < rk /\ &0 < rho0 /\ ball(y1,r) SUBSET cball(y1,rk) /\
             cball(y1,rk) SUBSET U /\
             !top atlas (gM:B->real^3^3) (phi:real^3->B) phi' d w w'.
               hausdorff_space top /\ smooth_manifold_atlas top atlas /\
               riemannian_metric atlas gM /\
               mfd_diffeo (subtopology euclidean U) (open_set_atlas U) U top atlas
                          (IMAGE phi U) phi phi' /\
               (!x. x IN U ==> phi'(phi x) = x) /\
               &0 <= d /\ d <= &1 / &2 /\
               (!y v. y IN U
                      ==> abs(v dot (rfs_pullback atlas phi gM y ** v) - v dot (G0 y ** v))
                          <= d * (v dot (G0 y ** v))) /\
               w IN ball(y1,r) /\ w' IN ball(y1,r)
               ==> mfd_joinable (subtopology euclidean U,open_set_atlas U) w w' /\
                   mfd_joinable (top,atlas) (phi w) (phi w') /\
                   mfd_dist (top,atlas) gM (phi w) (phi w') <=
                   sqrt(&1 + d) *
                   mfd_dist (subtopology euclidean U,open_set_atlas U) G0 w w' /\
                   mfd_dist (subtopology euclidean U,open_set_atlas U) G0 w w' <=
                   inv(sqrt(&1 - d)) * mfd_dist (top,atlas) gM (phi w) (phi w') /\
                   (!q. mfd_joinable (top,atlas) (phi w) q /\
                        mfd_dist (top,atlas) gM (phi w) q < rho0
                        ==> q IN IMAGE phi U /\ phi' q IN cball(y1,rk) /\
                            mfd_joinable (subtopology euclidean U,open_set_atlas U) w (phi' q) /\
                            mfd_dist (subtopology euclidean U,open_set_atlas U) G0 w (phi' q)
                            <= inv(sqrt(&1 - d)) * mfd_dist (top,atlas) gM (phi w) q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G0:real^3->real^3^3`; `y1:real^3`] P2BK_OSA_BALL_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `rk:real`
    STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `rk:real`; `R / &2`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 R` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1
                  (R / &8)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
    UNDISCH_TAC `&0 < R` THEN MESON_TAC[REAL_ARITH `&0 < R /\ x < R / &8 ==> x < R`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `gM:B->real^3^3`; `phi:real^3->B`; `phi':B->real^3`; `d:real`;
                       `w:real^3`; `w':real^3`] THEN
  INTRO_TAC "haus smooth riem diffeo inv d0 d1 qf w w'" THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (U:real^3->bool)) (open_set_atlas U) /\
                riemannian_metric (open_set_atlas U) (G0:real^3->real^3^3)`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN U /\ (w':real^3) IN U` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^3) IN mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 (R / &8) /\
    (w':real^3) IN mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 (R / &8)`
    STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_joinable (subtopology euclidean U,open_set_atlas U) (y1:real^3) w /\
    mfd_joinable (subtopology euclidean U,open_set_atlas U) (y1:real^3) w' /\
    mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 w < R / &8 /\
    mfd_dist (subtopology euclidean U,open_set_atlas U) G0 y1 w' < R / &8`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 (R / &8)` THEN
    UNDISCH_TAC `(w':real^3) IN mfd_ball (subtopology euclidean U,open_set_atlas U) G0 y1 (R / &8)` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (subtopology euclidean U,open_set_atlas U) (w:real^3) y1`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (subtopology euclidean U,open_set_atlas U) (w:real^3) w'`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `y1:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w y1 =
    mfd_dist (subtopology euclidean U,open_set_atlas U) G0 y1 w`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w w' < R / &4`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w y1 +
                mfd_dist (subtopology euclidean U,open_set_atlas U) G0 y1 w'` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w y1 =
                 mfd_dist (subtopology euclidean U,open_set_atlas U) G0 y1 w` THEN
    UNDISCH_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 w <
                 R / &8` THEN
    UNDISCH_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 w' <
                 R / &8` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y v. y IN U
                      ==> (&1 - d) * (v dot ((G0:real^3->real^3^3) y ** v)) <=
                          v dot (rfs_pullback atlas (phi:real^3->B) (gM:B->real^3^3) y ** v)`
    (LABEL_TAC "qfl") THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "qf" (MP_TAC o SPECL [`y:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + d) <= &5 / &4 /\ &7 / &10 <= sqrt(&1 - d) /\
                inv(sqrt(&1 - d)) <= &10 / &7 /\ &0 < sqrt(&1 - d)`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&7 / &10 <= sqrt(&1 - d)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN UNDISCH_TAC `d <= &1 / &2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN UNDISCH_TAC `&0 <= d` THEN UNDISCH_TAC `d <= &1 / &2` THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `&10 / &7 = inv(&7 / &10)` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&7 / &10 <= sqrt(&1 - d)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `gM:B->real^3^3`;
                 `phi:real^3->B`; `phi':B->real^3`; `G0:real^3->real^3^3`; `U:real^3->bool`;
                 `d:real`; `w:real^3`; `w':real^3`] P2BK_OSA_DIST_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "qf" (MP_TAC o SPECL [`y:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `gM:B->real^3^3`;
                   `phi:real^3->B`; `phi':B->real^3`; `G0:real^3->real^3^3`; `U:real^3->bool`;
                   `y1:real^3`; `R:real`; `R / &8`; `d:real`; `w:real^3`; `w':real^3`]
      P2BK_OSA_DIST_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `d <= &1 / &2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `&0 <= mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w w'`
        ASSUME_TAC THENL
       [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `sqrt(&1 + d) * mfd_dist (subtopology euclidean U,open_set_atlas U)
                         (G0:real^3->real^3^3) w w'
        <= &5 / &4 * mfd_dist (subtopology euclidean U,open_set_atlas U) G0 w w' /\
        &7 / &10 * (R - R / &8) <= sqrt(&1 - d) * (R - R / &8)`
        STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) (phi w') <=
                   sqrt(&1 + d) *
                   mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w w'` THEN
      UNDISCH_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w w' <
                   R / &4` THEN
      UNDISCH_TAC `&0 < R` THEN
      UNDISCH_TAC `sqrt(&1 + d) * mfd_dist (subtopology euclidean U,open_set_atlas U)
                     (G0:real^3->real^3^3) w w' <=
                   &5 / &4 * mfd_dist (subtopology euclidean U,open_set_atlas U) G0 w w'` THEN
      UNDISCH_TAC `&7 / &10 * (R - R / &8) <= sqrt(&1 - d) * (R - R / &8)` THEN
      REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `q:B` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `gM:B->real^3^3`;
                 `phi:real^3->B`; `phi':B->real^3`; `G0:real^3->real^3^3`; `U:real^3->bool`;
                 `y1:real^3`; `R:real`; `R / &8`; `d:real`; `w:real^3`; `q:B`]
    P2BK_OSA_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `d <= &1 / &2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&7 / &10 * (R - R / &8) <= sqrt(&1 - d) * (R - R / &8)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < R` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q < R / &2` THEN
    UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_ball (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 R
               SUBSET cball(y1,rk)` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 w +
              mfd_dist (subtopology euclidean U,open_set_atlas U) G0 w ((phi':B->real^3) q)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(sqrt(&1 - d)) * mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q <=
    &10 / &7 * mfd_dist (top,atlas) (gM:B->real^3^3) (phi w) q`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) w
                 ((phi':B->real^3) q) <=
               inv(sqrt(&1 - d)) * mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q` THEN
  UNDISCH_TAC `inv(sqrt(&1 - d)) * mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q <=
               &10 / &7 * mfd_dist (top,atlas) (gM:B->real^3^3) (phi w) q` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (gM:B->real^3^3) ((phi:real^3->B) w) q < R / &2` THEN
  UNDISCH_TAC `mfd_dist (subtopology euclidean U,open_set_atlas U) (G0:real^3->real^3^3) y1 w <
               R / &8` THEN
  UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Local limits in one chart.  For parametrizations phi k of ball(vec 0,r0)  *)
(* whose pullback metrics converge to G0 in lck_dist2 0 on cball(vec 0,rb),  *)
(* the distances of the targets between points phi k w, phi k w' with w, w'  *)
(* near vec 0 converge to those of the open-set manifold ball(vec 0,rb) with *)
(* metric G0, with relative error e for all large k (P2BK_LOCAL_LIMIT_DIST). *)
(* This is the form in which P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT delivers  *)
(* its limit at time 0.                                                      *)
(* ========================================================================= *)

(* Quadratic-form closeness from lck_dist2 0 (LCK_DIST_C0). *)

let P2BK_LCK_QF = prove
 (`!top atlas (gM:B->real^3^3) (phi:real^3->B) (G0:real^3->real^3^3) r0 y d v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas gM /\
     mfd_param top atlas (ball(vec 0,r0)) phi /\ metric_field (ball(vec 0,r0)) G0 /\
     y IN ball(vec 0,r0) /\ &0 < d /\
     lck_dist2 0 G0 (rfs_pullback atlas phi gM) y < d pow 2
     ==> abs(v dot (rfs_pullback atlas phi gM y ** v) - v dot (G0 y ** v))
         <= d * (v dot (G0 y ** v))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lck_dist2 0 (G0:real^3->real^3^3)
                     (rfs_pullback atlas (phi:real^3->B) (gM:B->real^3^3)) y) *
              (v dot (G0 y ** v))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_C0 THEN EXISTS_TAC `ball(vec 0:real^3,r0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(d pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `v:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  UNDISCH_TAC `metric_field (ball(vec 0:real^3,r0)) (G0:real^3->real^3^3)` THEN
  REWRITE_TAC[metric_field] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[]);;

let P2BK_INV_SQRT_LE = prove
 (`!e. &0 <= e /\ e <= &1 / &2 ==> inv(sqrt(&1 - e)) <= &1 + e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&1 - e)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN UNDISCH_TAC `e <= &1 / &2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 - e) pow 2 = &1 - e` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN UNDISCH_TAC `e <= &1 / &2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * (&1 - e - e * e)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e * e <= &1 / &2 * &1 / &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `e <= &1 / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&1 + e) * sqrt(&1 - e)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `&0 <= e` THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_POW_MUL; REAL_POW_ONE] THEN
      UNDISCH_TAC `&0 <= e * (&1 - e - e * e)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(sqrt(&1 - e)) * ((&1 + e) * sqrt(&1 - e))` THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < sqrt(&1 - e)` THEN CONV_TAC REAL_FIELD]);;

let P2BK_LOCAL_LIMIT_DIST = prove
 (`!(top:num->B topology) atlas (gM:num->B->real^3^3) (phi:num->real^3->B)
    (G0:real^3->real^3^3) r0 rb.
     &0 < rb /\ rb < r0 /\ metric_field (ball(vec 0,r0)) G0 /\
     (!k. hausdorff_space (top k) /\ smooth_manifold_atlas (top k) (atlas k) /\
          riemannian_metric (atlas k) (gM k) /\
          mfd_param (top k) (atlas k) (ball(vec 0,r0)) (phi k)) /\
     (!eta. &0 < eta
            ==> ?k0. !k w. k0 <= k /\ w IN cball(vec 0,rb)
                           ==> lck_dist2 0 G0 (rfs_pullback (atlas k) (phi k) (gM k)) w < eta)
     ==> ?r rk rho0.
           &0 < r /\ &0 < rk /\ &0 < rho0 /\ ball(vec 0:real^3,r) SUBSET cball(vec 0,rk) /\ rk < rb /\
           !e. &0 < e /\ e <= &1 / &2
               ==> ?k0. !k w w'.
                      k0 <= k /\ w IN ball(vec 0,r) /\ w' IN ball(vec 0,r)
                      ==> mfd_joinable (subtopology euclidean (ball(vec 0,rb)),
                                        open_set_atlas (ball(vec 0,rb))) w w' /\
                          mfd_joinable (top k,atlas k) (phi k w) (phi k w') /\
                          abs(mfd_dist (top k,atlas k) (gM k) (phi k w) (phi k w') -
                              mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                        open_set_atlas (ball(vec 0,rb))) G0 w w')
                          <= e * mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                           open_set_atlas (ball(vec 0,rb))) G0 w w' /\
                          (!q. mfd_joinable (top k,atlas k) (phi k w) q /\
                               mfd_dist (top k,atlas k) (gM k) (phi k w) q < rho0
                               ==> ?y. y IN cball(vec 0,rk) /\ q = phi k y /\
                                       mfd_joinable (subtopology euclidean (ball(vec 0,rb)),
                                                     open_set_atlas (ball(vec 0,rb))) w y /\
                                       mfd_dist (subtopology euclidean (ball(vec 0,rb)),
                                                 open_set_atlas (ball(vec 0,rb))) G0 w y
                                       <= (&1 + e) * mfd_dist (top k,atlas k) (gM k) (phi k w) q)`,
  REPEAT GEN_TAC THEN INTRO_TAC "rb0 rb1 G0 mk conv" THEN
  SUBGOAL_THEN `metric_field (ball(vec 0:real^3,rb)) (G0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r0)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^3,rb)`; `G0:real^3->real^3^3`; `vec 0:real^3`]
    P2BK_OSA_DIST_COMPARE) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `rk:real` (X_CHOOSE_THEN `rho0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cmp"))))))))) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `rk:real`; `rho0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(rb <= rk) ==> rk < rb`) THEN DISCH_TAC THEN
    UNDISCH_TAC `cball(vec 0:real^3,rk) SUBSET ball(vec 0,rb)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN
    DISCH_THEN(MP_TAC o SPEC `rk % basis 1:real^3`) THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    UNDISCH_TAC `&0 < rk` THEN UNDISCH_TAC `rb <= rk` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  USE_THEN "conv" (MP_TAC o SPEC `e pow 2`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `w:real^3`; `w':real^3`] THEN
  STRIP_TAC THEN
  USE_THEN "mk" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                 `ball(vec 0:real^3,r0)`; `(phi:num->real^3->B) k`; `ball(vec 0:real^3,rb)`]
    P2BK_OSA_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi':B->real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "cmp" (MP_TAC o SPECL
    [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
     `(gM:num->B->real^3^3) k`; `(phi:num->real^3->B) k`; `phi':B->real^3`; `e:real`;
     `w:real^3`; `w':real^3`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BK_LCK_QF THEN
    MAP_EVERY EXISTS_TAC [`(top:num->B topology) k`; `r0:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN ball(vec 0,rb)` THEN REWRITE_TAC[IN_BALL_0] THEN
      UNDISCH_TAC `rb < r0` THEN REAL_ARITH_TAC;
      USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN ball(vec 0,rb)` THEN
      REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pre"))))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(&1 + e) <= &1 + e /\ &1 - e <= sqrt(&1 - e) /\ &0 < sqrt(&1 - e) /\
                inv(sqrt(&1 - e)) <= &1 + e`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 - e <= sqrt(&1 - e) /\ &0 < sqrt(&1 - e)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
        SUBGOAL_THEN `&0 <= e * (&1 - e)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `e <= &1 / &2` THEN
          REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        MATCH_MP_TAC SQRT_POS_LT THEN UNDISCH_TAC `e <= &1 / &2` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `&0 <= e * e` MP_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC P2BK_INV_SQRT_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ABBREV_TAC `dS = mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                               open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w w'` THEN
    ABBREV_TAC `dM = mfd_dist ((top:num->B topology) k,
                               (atlas:num->((B->bool)#(B->real^3))->bool) k)
                              ((gM:num->B->real^3^3) k) ((phi:num->real^3->B) k w) (phi k w')` THEN
    SUBGOAL_THEN `&0 <= dS` ASSUME_TAC THENL
     [EXPAND_TAC "dS" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN
      ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_RIEMANNIAN; OPEN_BALL];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&1 - e) * dS <= dM` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 - e) * (inv(sqrt(&1 - e)) * dM)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&1 + e) * dS <= (&1 + e) * dS /\ (&1 - e) * dS <= sqrt(&1 - e) * dS`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `dM <= sqrt(&1 + e) * dS` THEN UNDISCH_TAC `sqrt(&1 - e) * dS <= dM` THEN
    UNDISCH_TAC `sqrt(&1 + e) * dS <= (&1 + e) * dS` THEN
    UNDISCH_TAC `(&1 - e) * dS <= sqrt(&1 - e) * dS` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `q:B` THEN STRIP_TAC THEN
  USE_THEN "pre" (MP_TAC o SPEC `q:B`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^3` THEN
  SUBGOAL_THEN `(phi':B->real^3) q = u` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(phi':B->real^3) q IN cball(vec 0,rk)` THEN
  UNDISCH_TAC `mfd_joinable (subtopology euclidean (ball(vec 0:real^3,rb)),
                             open_set_atlas (ball(vec 0,rb))) w ((phi':B->real^3) q)` THEN
  UNDISCH_TAC `mfd_dist (subtopology euclidean (ball(vec 0:real^3,rb)),
                         open_set_atlas (ball(vec 0,rb))) (G0:real^3->real^3^3) w
                 ((phi':B->real^3) q) <=
               inv(sqrt(&1 - e)) *
               mfd_dist ((top:num->B topology) k,(atlas:num->((B->bool)#(B->real^3))->bool) k)
                 ((gM:num->B->real^3^3) k) ((phi:num->real^3->B) k w) q` THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(sqrt(&1 - e)) *
              mfd_dist ((top:num->B topology) k,(atlas:num->((B->bool)#(B->real^3))->bool) k)
                ((gM:num->B->real^3^3) k) ((phi:num->real^3->B) k w) (phi k u)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

