(* ========================================================================= *)
(* Unit pc_p2b_979s (Part 2B, MT Prop 9.79): the static cases of the open    *)
(* form P2_PROP_9_79_OPEN and the infrastructure for the slice forms.        *)
(*                                                                           *)
(* - the statement P2B_REQ_LRG_DERIV_STATEMENT; it and the statements        *)
(*   P2B_REQ_LRG_RM_NEAR_STATEMENT, P2B_REQ_LRG_BASE_STATEMENT are theorems  *)
(*   (LRG_DERIV_STABILITY, LRG_RM_NEAR_BOUND, LRG_CK_BASE_CHANGE), so the    *)
(*   neck forms of pc_p2b_979 hold unconditionally;                          *)
(* - naturality of the curvature quantities under pullback by local          *)
(*   diffeomorphisms; compact bounds of the curvature derivatives;           *)
(* - pointwise stability of R, sectional curvature, the squared norm of grad *)
(*   R, Lap R and the squared norm of Ric (from                              *)
(*   P2B_REQ_LRG_DERIV_STATEMENT);                                           *)
(* - lengths and intrinsic distances under a local diffeomorphism with a     *)
(*   C^0-close pullback metric;                                              *)
(* - chart representations of pullback metrics, gluing a metric on a clopen  *)
(*   set, rescaling of lck_dist2, naturality of lck_dist2;                   *)
(* - the eps-round component case and the C-component case of the open form  *)
(*   (the last two sections).                                                *)
(* ========================================================================= *)

needs "src/pc_p2b_979.ml";;
needs "src/pc_lrg_ckbase.ml";;
needs "src/pc_rfa_shi.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_grg_distcont.ml";;
needs "src/pc_lrg_dbase.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The statement P2B_REQ_LRG_DERIV_STATEMENT: stability of the squared norm  *)
(* of grad R, Lap R and the squared norm of Ric under C^4 closeness at a     *)
(* metric with bounded Rm, nabla Rm and nabla^2 Rm (clause (8) of caps and   *)
(* C-components).                                                            *)
(* ------------------------------------------------------------------------- *)

let P2B_REQ_LRG_DERIV_STATEMENT = new_definition
 `P2B_REQ_LRG_DERIV_STATEMENT <=>
    !K0 alpha. &0 < alpha
      ==> ?eta. &0 < eta /\
            !s (G0:real^3->real^3^3) G y.
               metric_field s G0 /\ metric_field s G /\ y IN s /\
               lrm_deriv_norm2 0 G0 y <= K0 /\ lrm_deriv_norm2 1 G0 y <= K0 /\
               lrm_deriv_norm2 2 G0 y <= K0 /\ lck_dist2 4 G0 G y < eta pow 2
               ==> abs(lgrad2 G (lscalar G) y - lgrad2 G0 (lscalar G0) y) <= alpha /\
                   abs(llap G (lscalar G) y - llap G0 (lscalar G0) y) <= alpha /\
                   abs(ltnorm2 2 G (lric2 G) y - ltnorm2 2 G0 (lric2 G0) y) <= alpha`;;

(* ------------------------------------------------------------------------- *)
(* The statements P2B_REQ_LRG_RM_NEAR_STATEMENT, P2B_REQ_LRG_BASE_STATEMENT  *)
(* and P2B_REQ_LRG_DERIV_STATEMENT are theorems (from pc_lrg_base,           *)
(* pc_lrg_ckbase, pc_lrg_dbase).                                             *)
(* ------------------------------------------------------------------------- *)

let P2B_REQ_LRG_DERIV = prove
 (`P2B_REQ_LRG_DERIV_STATEMENT`,
  REWRITE_TAC[P2B_REQ_LRG_DERIV_STATEMENT; LRG_DERIV_STABILITY]);;

let P2B_REQ_LRG_RM_NEAR = prove
 (`P2B_REQ_LRG_RM_NEAR_STATEMENT`,
  REWRITE_TAC[P2B_REQ_LRG_RM_NEAR_STATEMENT; LRG_RM_NEAR_BOUND]);;

let P2B_REQ_LRG_BASE = prove
 (`P2B_REQ_LRG_BASE_STATEMENT`,
  REWRITE_TAC[P2B_REQ_LRG_BASE_STATEMENT; LRG_CK_BASE_CHANGE]);;

let P2B_PROP_9_79_NECK_FIX_FROM_LRGB = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_REQ_LRG_BASE_STATEMENT ==> P2B_PROP_9_79_NECK_FIX_STATEMENT u w`,
  MESON_TAC[P2B_PROP_9_79_NECK_FIX_FROM_REQ; P2B_REQ_LRG_RM_NEAR]);;

let P2B_NECK_OPEN = prove
 (`!(u:A->bool) (w:B->bool). P2B_NECK_OPEN_STATEMENT u w`,
  MESON_TAC[P2B_NECK_OPEN_FROM_REQ; P2B_REQ_LRG_BASE]);;

let P2B_NECK_OPEN_L = prove
 (`!(u:A->bool) (w:B->bool). P2B_NECK_OPEN_L_STATEMENT u w`,
  MESON_TAC[P2B_NECK_OPEN_L_FROM_REQ; P2B_REQ_LRG_BASE]);;

let P2B_PROP_9_79_NECK_FIX = prove
 (`!(u:A->bool) (w:B->bool). P2B_PROP_9_79_NECK_FIX_STATEMENT u w`,
  MESON_TAC[P2B_PROP_9_79_NECK_FIX_FROM_LRGB; P2B_REQ_LRG_BASE]);;

let P2B9S_OPEN_NECK = MP P2B9_OPEN_NECK P2B_REQ_LRG_BASE;;

(* ========================================================================= *)
(* Naturality under pullback, compact bounds.                                *)
(* ========================================================================= *)

let P2B9S_RMD2_CONTINUOUS = prove
 (`!m top atlas (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
     ==> continuous_map (top,euclideanreal) (rfa_rmd2 m atlas g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `\z:A. lrm_deriv_norm2 m (metric_local atlas (U,phi) (g:A->real^N^N)) (phi z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    BETA_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`m:num`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(U:A->bool,phi:A->real^N)`; `z:A`] RFA_RMD2_CHART) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:A. lrm_deriv_norm2 m (metric_local atlas (U,phi) (g:A->real^N^N)) (phi z)) =
    (\y. lrm_deriv_norm2 m (metric_local atlas (U,phi) g) y) o (phi:A->real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
  MATCH_MP_TAC LRM_DERIV_NORM2_CONTINUOUS THEN
  UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
  REWRITE_TAC[riemannian_metric] THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND]);;

let P2B9S_RMD2_COMPACT_BOUND = prove
 (`!m top atlas (g:A->real^N^N) K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?B. !y. y IN K ==> rfa_rmd2 m atlas g y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `euclideanreal`; `rfa_rmd2 m atlas (g:A->real^N^N)`;
                 `K:A->bool`] IMAGE_COMPACT_IN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P2B9S_RMD2_CONTINUOUS]; ALL_TAC] THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  ASM_MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`]);;

let P2B9S_PB_LOCAL_REP = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U
     ==> ?P P' K K'.
           open P /\ SND(chart_at atlas y) y IN P /\
           diffeomorphism_on P P' K K' /\
           metric_field P' (metric_local atlas' (chart_at atlas' (psi y)) g') /\
           K (SND(chart_at atlas y) y) = SND(chart_at atlas' (psi y)) (psi y) /\
           (!z. z IN P
                ==> metric_local atlas (chart_at atlas y)
                                 (mfd_pullback_metric atlas atlas' psi g') z =
                    mpullback K (metric_local atlas' (chart_at atlas' (psi y)) g') z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(psi:A->B) y IN U'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (psi:A->B) U SUBSET U'` THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ (psi:A->B) y IN topspace top'`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
                         REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN
                         ASSUME_TAC th) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
                CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(psi:A->B) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas':((B->bool)#(B->real^N))->bool) ((psi:A->B) y)`,
           `c':(B->bool)#(B->real^N)`) THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V0:A->bool`; `phi:A->real^N`; `V1:B->bool`; `chi:B->real^N`] THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi:A->real^N) {x | x IN V0 INTER U /\ (psi:A->B) x IN V1}`;
    `IMAGE (chi:B->real^N) {y' | y' IN V1 INTER U' /\ (psi':B->A) y' IN V0}`;
    `(chi:B->real^N) o (psi:A->B) o chart_inv (V0:A->bool,phi:A->real^N)`;
    `(phi:A->real^N) o (psi':B->A) o chart_inv (V1:B->bool,chi:B->real^N)`] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `U':B->bool`;
                 `psi:A->B`; `psi':B->A`; `V0:A->bool`; `phi:A->real^N`;
                 `V1:B->bool`; `chi:B->real^N`] MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN SIMP_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `IMAGE (chi:B->real^N) V1` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas' (g':B->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V1:B->bool,chi:B->real^N)`) THEN ASM_REWRITE_TAC[FST; SND];
      CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN SIMP_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]];
    REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `V0:A->bool`; `phi:A->real^N`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x':A` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2C_PULLBACK_METRIC_LOCAL_W THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `U:A->bool`; `top':B topology`;
                          `U':B->bool`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[]]);;

let P2B9S_PB_SCALAR = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U
     ==> mfd_scalar atlas (mfd_pullback_metric atlas atlas' psi g') y =
         mfd_scalar atlas' g' (psi y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B9S_PB_LOCAL_REP) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `P':real^N->bool`
    (X_CHOOSE_THEN `K:real^N->real^N` (X_CHOOSE_THEN `K':real^N->real^N`
      STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[mfd_scalar] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lscalar (mpullback (K:real^N->real^N)
                 (metric_local atlas' (chart_at atlas' ((psi:A->B) y)) (g':B->real^N^N)))
                 (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `P:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    can (term_match [] `(K:real^N->real^N) a = b`) (concl th) &&
    not (is_forall (concl th)))) THEN
  MATCH_MP_TAC LSCALAR_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`P':real^N->bool`; `P:real^N->bool`; `K':real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

let P2B9S_PB_DERIVS = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U
     ==> rfs_scalar_grad2 atlas (mfd_pullback_metric atlas atlas' psi g') y =
         rfs_scalar_grad2 atlas' g' (psi y) /\
         rfs_scalar_lap atlas (mfd_pullback_metric atlas atlas' psi g') y =
         rfs_scalar_lap atlas' g' (psi y) /\
         rfs_ric_norm2 atlas (mfd_pullback_metric atlas atlas' psi g') y =
         rfs_ric_norm2 atlas' g' (psi y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B9S_PB_LOCAL_REP) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `P':real^N->bool`
    (X_CHOOSE_THEN `K:real^N->real^N` (X_CHOOSE_THEN `K':real^N->real^N`
      STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[rfs_scalar_grad2; rfs_scalar_lap; rfs_ric_norm2; P2C_LRIC2_ETA] THEN
  ABBREV_TAC `L' = metric_local atlas' (chart_at atlas' ((psi:A->B) y)) (g':B->real^N^N)` THEN
  ABBREV_TAC `L = metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas (y:A))
                    (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N))` THEN
  ABBREV_TAC `p = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)) y` THEN
  SUBGOAL_THEN `!z. z IN P ==> lscalar (L:real^N->real^N^N) z = lscalar L' ((K:real^N->real^N) z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lscalar (mpullback (K:real^N->real^N) L') z` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `P:real^N->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC LSCALAR_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`P':real^N->bool`; `P:real^N->bool`; `K':real^N->real^N`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on P' (\z. lift(lscalar (L':real^N->real^N^N) z))` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lgrad2 (mpullback (K:real^N->real^N) L') (lscalar L' o K) p` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `P:real^N->bool` THEN
      ASM_SIMP_TAC[o_THM];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(K:real^N->real^N) p`)) THEN
      MATCH_MP_TAC LGRAD2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`P':real^N->bool`; `P:real^N->bool`; `K':real^N->real^N`] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "p" THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `llap (mpullback (K:real^N->real^N) L') (lscalar L' o K) p` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `P:real^N->bool` THEN
      ASM_SIMP_TAC[o_THM];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(K:real^N->real^N) p`)) THEN
      MATCH_MP_TAC LLAP_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`P':real^N->bool`; `P:real^N->bool`; `K':real^N->real^N`] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "p" THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltnorm2 2 (mpullback (K:real^N->real^N) L') (ltpullback K (lric2 L')) p` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_EQ THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[ltpullback; lric2] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `lricci (mpullback (K:real^N->real^N) L') p (u 1) (u 2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `P:real^N->bool` THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC LRICCI_PULLBACK THEN
        MAP_EVERY EXISTS_TAC [`P':real^N->bool`; `P:real^N->bool`; `K':real^N->real^N`] THEN
        ASM_REWRITE_TAC[]];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(K:real^N->real^N) p`)) THEN
      MATCH_MP_TAC LTNORM2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`P':real^N->bool`; `P:real^N->bool`; `K':real^N->real^N`] THEN
      ASM_SIMP_TAC[LRG_LRIC2_FIELD]]]);;

let P2B9S_PB_SECTIONAL = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U
     ==> (!u v. ~collinear {vec 0,u,v}
                ==> ?u' v'. ~collinear {vec 0,u',v'} /\
                            mfd_sectional atlas (mfd_pullback_metric atlas atlas' psi g') y u v =
                            mfd_sectional atlas' g' (psi y) u' v') /\
         (!u' v'. ~collinear {vec 0,u',v'}
                  ==> ?u v. ~collinear {vec 0,u,v} /\
                            mfd_sectional atlas' g' (psi y) u' v' =
                            mfd_sectional atlas (mfd_pullback_metric atlas atlas' psi g') y u v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B9S_PB_LOCAL_REP) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `P':real^N->bool`
    (X_CHOOSE_THEN `K:real^N->real^N` (X_CHOOSE_THEN `K':real^N->real^N`
      STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[mfd_sectional] THEN
  ABBREV_TAC `L' = metric_local atlas' (chart_at atlas' ((psi:A->B) y)) (g':B->real^N^N)` THEN
  ABBREV_TAC `L = metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas (y:A))
                    (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N))` THEN
  ABBREV_TAC `p = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)) y` THEN
  MP_TAC(ISPECL [`P':real^N->bool`; `P:real^N->bool`; `K:real^N->real^N`;
                 `K':real^N->real^N`; `p:real^N`] LRG_DIFFEO_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `J = frechet_derivative (K:real^N->real^N) (at p)` THEN
  ABBREV_TAC `J2 = frechet_derivative (K':real^N->real^N) (at ((K:real^N->real^N) p))` THEN
  SUBGOAL_THEN `!u v. lsectional (L:real^N->real^N^N) p u v =
                      lsectional L' ((K:real^N->real^N) p) (J u) (J v)` (LABEL_TAC "sec") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lsectional (mpullback (K:real^N->real^N) L') p u v` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `P:real^N->bool` THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "J" THEN MATCH_MP_TAC MFDR_LSECTIONAL_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`P':real^N->bool`; `P:real^N->bool`; `K':real^N->real^N`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v:real^N. collinear {vec 0, (J:real^N->real^N) u, J v} <=>
                             collinear {vec 0,u,v}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `{vec 0:real^N, (J:real^N->real^N) u, J v} = IMAGE (J:real^N->real^N) {vec 0,u,v}`
    SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_CLAUSES] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]);
      ALL_TAC] THEN
    MATCH_MP_TAC COLLINEAR_LINEAR_IMAGE_EQ THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "col") THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(K:real^N->real^N) p`)) THEN
  SUBGOAL_THEN `!w:real^N. (J:real^N->real^N) ((J2:real^N->real^N) w) = w` (LABEL_TAC "inv")
  THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(J:real^N->real^N) u`; `(J:real^N->real^N) v`] THEN
    USE_THEN "col" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sec" (fun th -> REWRITE_TAC[th]);
    MAP_EVERY EXISTS_TAC [`(J2:real^N->real^N) u'`; `(J2:real^N->real^N) v'`] THEN
    CONJ_TAC THENL
     [USE_THEN "col" (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      USE_THEN "inv" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      USE_THEN "sec" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "inv" (fun th -> REWRITE_TAC[th])]]);;

let P2B9S_PB_FIELD = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U
     ==> ?P. open P /\ SND(chart_at atlas y) y IN P /\
             metric_field P (metric_local atlas (chart_at atlas y)
                                          (mfd_pullback_metric atlas atlas' psi g'))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B9S_PB_LOCAL_REP) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `P':real^N->bool`
    (X_CHOOSE_THEN `K:real^N->real^N` (X_CHOOSE_THEN `K':real^N->real^N`
      STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `P:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `mpullback (K:real^N->real^N)
                (metric_local atlas' (chart_at atlas' ((psi:A->B) y)) (g':B->real^N^N))` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`P':real^N->bool`; `K':real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Pointwise stability of curvature quantities.                              *)
(* ========================================================================= *)

let P2B9S_SCALE_DIFF = prove
 (`!R a b alpha k. &0 < R /\ abs(a - b) <= alpha
                   ==> abs(R pow k * a - R pow k * b) <= alpha * R pow k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL; REAL_ABS_POW] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]);;

let P2B9S_SCALE_DIFF1 = prove
 (`!R a b alpha. &0 < R /\ abs(a - b) <= alpha ==> abs(R * a - R * b) <= alpha * R`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`R:real`; `a:real`; `b:real`; `alpha:real`; `1`] P2B9S_SCALE_DIFF) THEN
  ASM_REWRITE_TAC[REAL_POW_1]);;

let P2B9S_DIV_DIFF = prove
 (`!R x y alpha. &0 < R /\ abs(x / R - y / R) <= alpha ==> abs(x - y) <= alpha * R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x - y = R * (x / R - y / R)` SUBST1_TAC THENL
   [MP_TAC(REAL_ARITH `&0 < R ==> ~(R = &0)`) THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
  MATCH_MP_TAC P2B9S_SCALE_DIFF1 THEN ASM_REWRITE_TAC[]);;

let P2B9S_POINT_STAB = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' R K0 alpha eta y.
     (!s (G0:real^3->real^3^3) G y.
         metric_field s G0 /\ metric_field s G /\ y IN s /\
         lrm_deriv_norm2 0 G0 y <= K0 /\ lrm_deriv_norm2 1 G0 y <= K0 /\
         lrm_deriv_norm2 2 G0 y <= K0 /\ lck_dist2 4 G0 G y < eta pow 2
         ==> abs(lscalar G y - lscalar G0 y) <= alpha /\
             (!u v. ~collinear {vec 0,u,v}
                    ==> abs(lsectional G y u v - lsectional G0 y u v) <= alpha) /\
             abs(lgrad2 G (lscalar G) y - lgrad2 G0 (lscalar G0) y) <= alpha /\
             abs(llap G (lscalar G) y - llap G0 (lscalar G0) y) <= alpha /\
             abs(ltnorm2 2 G (lric2 G) y - ltnorm2 2 G0 (lric2 G0) y) <= alpha) /\
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U /\ &0 < R /\
     rfa_rmd2 0 atlas (\z. R %% g z) y <= K0 /\ rfa_rmd2 1 atlas (\z. R %% g z) y <= K0 /\
     rfa_rmd2 2 atlas (\z. R %% g z) y <= K0 /\
     lck_dist2 4 (metric_local atlas (chart_at atlas y) (\z. R %% g z))
                 (metric_local atlas (chart_at atlas y)
                    (\z. R %% mfd_pullback_metric atlas atlas' psi g' z))
                 (SND(chart_at atlas y) y) < eta pow 2
     ==> abs(mfd_scalar atlas' g' (psi y) - mfd_scalar atlas g y) <= alpha * R /\
         (!u v. ~collinear {vec 0,u,v}
                ==> abs(mfd_sectional atlas (mfd_pullback_metric atlas atlas' psi g') y u v -
                        mfd_sectional atlas g y u v) <= alpha * R) /\
         abs(rfs_scalar_grad2 atlas' g' (psi y) - rfs_scalar_grad2 atlas g y)
           <= alpha * R pow 3 /\
         abs(rfs_scalar_lap atlas' g' (psi y) - rfs_scalar_lap atlas g y) <= alpha * R pow 2 /\
         abs(rfs_ric_norm2 atlas' g' (psi y) - rfs_ric_norm2 atlas g y) <= alpha * R pow 2`,
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
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
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
  SUBGOAL_THEN `metric_field P (Lp:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Lp" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s = P INTER IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  SUBGOAL_THEN `open (s:real^3->bool) /\ (p:real^3) IN s /\
                metric_field s (Lg:real^3->real^3^3) /\ metric_field s (Lp:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))` ASSUME_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    SUBGOAL_THEN `open (s:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN EXPAND_TAC "p" THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "p" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN SET_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `P:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "D" (MP_TAC o SPECL [`s:real^3->bool`; `\w. R %% (Lg:real^3->real^3^3) w`;
                                  `\w. R %% (Lp:real^3->real^3^3) w`; `p:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LRG_METRIC_FIELD_SCALE] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfa_rmd2")) (concl th) ||
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th)))) THEN
    ASM_REWRITE_TAC[rfa_rmd2; METRIC_LOCAL_CMUL; ETA_AX] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `Lg:real^3->real^3^3`; `R:real`; `p:real^3`]
                P2C_SCALE_QUANTITIES) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `Lp:real^3->real^3^3`; `R:real`; `p:real^3`]
                P2C_SCALE_QUANTITIES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `g':B->real^3^3`; `y:A`] P2B9S_PB_SCALAR) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `g':B->real^3^3`; `y:A`] P2B9S_PB_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mfd_scalar; mfd_sectional; rfs_scalar_grad2; rfs_scalar_lap; rfs_ric_norm2;
              P2C_LRIC2_ETA] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2B9S_SCALE_DIFF1 THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC P2B9S_DIV_DIFF THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `Lp:real^3->real^3^3`; `R:real`; `p:real^3`;
                   `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `Lg:real^3->real^3^3`; `R:real`; `p:real^3`;
                   `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lsectional")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2B9S_SCALE_DIFF THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2B9S_SCALE_DIFF THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2B9S_SCALE_DIFF THEN ASM_REWRITE_TAC[]]);;

let P2B9S_LRG_D = prove
 (`P2B_REQ_LRG_DERIV_STATEMENT
   ==> !K0 alpha. &0 < alpha
         ==> ?eta. &0 < eta /\
               !s (G0:real^3->real^3^3) G y.
                  metric_field s G0 /\ metric_field s G /\ y IN s /\
                  lrm_deriv_norm2 0 G0 y <= K0 /\ lrm_deriv_norm2 1 G0 y <= K0 /\
                  lrm_deriv_norm2 2 G0 y <= K0 /\ lck_dist2 4 G0 G y < eta pow 2
                  ==> abs(lscalar G y - lscalar G0 y) <= alpha /\
                      (!u v. ~collinear {vec 0,u,v}
                             ==> abs(lsectional G y u v - lsectional G0 y u v) <= alpha) /\
                      abs(lgrad2 G (lscalar G) y - lgrad2 G0 (lscalar G0) y) <= alpha /\
                      abs(llap G (lscalar G) y - llap G0 (lscalar G0) y) <= alpha /\
                      abs(ltnorm2 2 G (lric2 G) y - ltnorm2 2 G0 (lric2 G0) y) <= alpha`,
  REWRITE_TAC[P2B_REQ_LRG_DERIV_STATEMENT] THEN DISCH_THEN(LABEL_TAC "R") THEN
  REPEAT STRIP_TAC THEN
  REMOVE_THEN "R" (MP_TAC o SPECL [`K0:real`; `alpha:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e1"))) THEN
  MP_TAC(ISPECL [`&1 + abs K0`; `alpha:real`]
                (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e2"))) THEN
  EXISTS_TAC `min eta1 eta2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `min eta1 eta2 pow 2 <= eta1 pow 2 /\ min eta1 eta2 pow 2 <= eta2 pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 2 (G0:real^3->real^3^3) G y <= lck_dist2 4 G0 G y` ASSUME_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "e1" (MP_TAC o SPECL [`s:real^3->bool`; `G0:real^3->real^3^3`;
                                    `G:real^3->real^3^3`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REMOVE_THEN "e2" (MP_TAC o SPECL [`s:real^3->bool`; `G0:real^3->real^3^3`;
                                    `G:real^3->real^3^3`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K0:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `abs K0 <= (&1 + abs K0) pow 2 ==> K0 <= (&1 + abs K0) pow 2`) THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN
      SPEC_TAC(`abs K0`,`a:real`) THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a * a /\ &0 <= a ==> a <= (&1 + a) * (&1 + a)`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL];
      ASM_REAL_ARITH_TAC];
    SIMP_TAC[]]);;


(* ========================================================================= *)
(* Lengths and intrinsic distances under local diffeos.                      *)
(* ========================================================================= *)

let P2B9S_PB_SPEED = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) (gamma:real->A) a b t.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
     (!s. s IN real_interval[a,b] ==> gamma s IN U) /\ t IN real_interval[a,b]
     ==> mfd_c1_curve (top',atlas') (psi o gamma) a b /\
         mfd_speed atlas' g' (psi o gamma) a b t =
         mfd_speed atlas (mfd_pullback_metric atlas atlas' psi g') gamma a b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `mfd_c1_curve (top',atlas':((B->bool)#(B->real^N))->bool)
                 ((psi:A->B) o (gamma:real->A)) a b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_PUSH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `U:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN U` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B)((gamma:real->A) t) IN topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(psi:A->B)((gamma:real->A) t)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at (atlas':((B->bool)#(B->real^N))->bool)
                            ((psi:A->B)((gamma:real->A) t))` THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N) ((gamma:real->A) t) =
                mpullback (SND (c':(B->bool)#(B->real^N)) o psi o
                           chart_inv (c:(A->bool)#(A->real^N)))
                          (metric_local atlas' c' g') (SND c (gamma t))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_pullback_metric] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `(psi:A->B) o (gamma:real->A)`; `a:real`; `b:real`;
                 `t:real`; `FST(c':(B->bool)#(B->real^N))`; `SND(c':(B->bool)#(B->real^N))`]
                MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N)`;
                 `gamma:real->A`; `a:real`; `b:real`;
                 `t:real`; `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N)`;
                 `(gamma:real->A) t`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vector_derivative (\s. SND (c':(B->bool)#(B->real^N)) ((psi:A->B)((gamma:real->A)(drop s))))
      (at (lift t) within interval[lift a,lift b]) =
    frechet_derivative (SND c' o psi o chart_inv (c:(A->bool)#(A->real^N)))
      (at (SND c (gamma t)))
      (vector_derivative (\s. SND c (gamma(drop s)))
         (at (lift t) within interval[lift a,lift b]))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `U:A->bool`; `psi:A->B`; `gamma:real->A`;
                   `a:real`; `b:real`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`;
                   `lift t`] GRGD_PUSH_VD) THEN
    ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (SND (c':(B->bool)#(B->real^N)) o (psi:A->B) o
                               chart_inv (c:(A->bool)#(A->real^N)))
                              (at (SND c ((gamma:real->A) t))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `U:A->bool`; `psi:A->B`; `c:(A->bool)#(A->real^N)`;
                   `c':(B->bool)#(B->real^N)`; `(gamma:real->A) t`]
                  GRGD_CHART_MAP_DIFF) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[has_derivative];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback; o_THM] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c ((gamma:real->A) t)) = gamma t`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_INV) THEN
    REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC GRGD_QUAD_CONGR THEN ASM_REWRITE_TAC[]);;

let P2B9S_PB_LENGTH = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) (gamma:real->A) a b.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
     (!s. s IN real_interval[a,b] ==> gamma s IN U)
     ==> mfd_c1_curve (top',atlas') (psi o gamma) a b /\
         (mfd_speed atlas (mfd_pullback_metric atlas atlas' psi g') gamma a b)
           real_integrable_on real_interval[a,b] /\
         mfd_length atlas' g' (psi o gamma) a b =
         mfd_length atlas (mfd_pullback_metric atlas atlas' psi g') gamma a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b]
                    ==> mfd_c1_curve (top',atlas':((B->bool)#(B->real^N))->bool)
                                     ((psi:A->B) o (gamma:real->A)) a b /\
                        mfd_speed atlas' (g':B->real^N^N) (psi o gamma) a b t =
                        mfd_speed atlas (mfd_pullback_metric atlas atlas' psi g') gamma a b t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2B9S_PB_SPEED THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `U:A->bool`; `U':B->bool`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top',atlas':((B->bool)#(B->real^N))->bool)
                             ((psi:A->B) o (gamma:real->A)) a b`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
     [UNDISCH_TAC `a:real < b` THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
    EXISTS_TAC `mfd_speed atlas' (g':B->real^N^N) ((psi:A->B) o (gamma:real->A)) a b` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
    EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN ASM_SIMP_TAC[]]);;

let P2B9S_LENGTH_COMPARE = prove
 (`!atlas (g:A->real^N^N) g' c (gamma:real->A) a b.
     &0 <= c /\
     (mfd_speed atlas g gamma a b) real_integrable_on real_interval[a,b] /\
     (mfd_speed atlas g' gamma a b) real_integrable_on real_interval[a,b] /\
     (!t v. a <= t /\ t <= b
            ==> v dot (g'(gamma t) ** v) <= c * (v dot (g(gamma t) ** v)))
     ==> mfd_length atlas g' gamma a b <= sqrt c * mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_length] THEN ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; ETA_AX] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_speed; GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2B9S_DIST_IN_PB_LE = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) U U' psi psi' S c x y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ S SUBSET U /\ &0 < c /\
     (!z v. z IN S
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' z ** v) <=
                c * (v dot (g z ** v))) /\
     mfd_joinable_in (top,atlas) S x y
     ==> mfd_joinable_in (top',atlas') (IMAGE psi S) (psi x) (psi y) /\
         mfd_dist_in (top',atlas') g' (IMAGE psi S) (psi x) (psi y) <=
         sqrt c * mfd_dist_in (top,atlas) g S x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!gamma:real->A.
       mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^N))->bool) gamma (&0) (&1) /\
       gamma(&0) = x /\ gamma(&1) = y /\
       (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)
       ==> mfd_c1_curve (top':B topology,atlas':((B->bool)#(B->real^N))->bool)
                        ((psi:A->B) o gamma) (&0) (&1) /\
           (!t. &0 <= t /\ t <= &1 ==> (psi o gamma) t IN IMAGE psi S) /\
           mfd_dist_in (top',atlas') (g':B->real^N^N) (IMAGE psi S) (psi x) (psi y) <=
           sqrt c * mfd_length atlas (g:A->real^N^N) gamma (&0) (&1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `g':B->real^N^N`;
                   `gamma:real->A`; `&0`; `&1`] P2B9S_PB_LENGTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01; IN_REAL_INTERVAL] THEN ASM SET_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN `!t. &0 <= t /\ t <= &1
                      ==> ((psi:A->B) o (gamma:real->A)) t IN IMAGE psi S`
    ASSUME_TAC THENL
     [REWRITE_TAC[o_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas' (g':B->real^N^N) ((psi:A->B) o (gamma:real->A)) (&0) (&1)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                     `g':B->real^N^N`; `IMAGE (psi:A->B) S`;
                     `(psi:A->B) o (gamma:real->A)`; `&0`; `&1`] MFD_DIST_IN_LE_LENGTH) THEN
      ASM_REWRITE_TAC[o_THM; IN_REAL_INTERVAL] THEN
      DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[o_THM];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2B9S_LENGTH_COMPARE THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable_in (top':B topology,atlas':((B->bool)#(B->real^N))->bool)
                                (IMAGE (psi:A->B) S) (psi x) (psi y)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_joinable_in]) THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[mfd_joinable_in] THEN EXISTS_TAC `(psi:A->B) o (gamma:real->A)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `gamma:real->A`) THEN ASM_REWRITE_TAC[o_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [mfd_dist_in] THEN MATCH_MP_TAC REAL_LE_INF THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN
    ASM_MESON_TAC[mfd_joinable_in];
    X_GEN_TAC `L:real` THEN REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `gamma:real->A`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[]]);;

let P2B9S_DIST_IN_PB_GE = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) U U' psi psi' S c x y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ S SUBSET U /\ &0 < c /\
     (!z v. z IN S
            ==> v dot (g z ** v) <=
                c * (v dot (mfd_pullback_metric atlas atlas' psi g' z ** v))) /\
     x IN S /\ y IN S /\
     mfd_joinable_in (top',atlas') (IMAGE psi S) (psi x) (psi y)
     ==> mfd_joinable_in (top,atlas) S x y /\
         mfd_dist_in (top,atlas) g S x y <=
         sqrt c * mfd_dist_in (top',atlas') g' (IMAGE psi S) (psi x) (psi y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN
   `!gamma':real->B.
       mfd_c1_curve (top':B topology,atlas':((B->bool)#(B->real^N))->bool) gamma' (&0) (&1) /\
       gamma'(&0) = (psi:A->B) x /\ gamma'(&1) = psi y /\
       (!t. &0 <= t /\ t <= &1 ==> gamma' t IN IMAGE psi S)
       ==> mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                        ((psi':B->A) o gamma') (&0) (&1) /\
           (psi' o gamma') (&0) = x /\ (psi' o gamma') (&1) = y /\
           (!t. &0 <= t /\ t <= &1 ==> (psi' o gamma') t IN S) /\
           mfd_dist_in (top,atlas) (g:A->real^N^N) S x y <=
           sqrt c * mfd_length atlas' (g':B->real^N^N) gamma' (&0) (&1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> (gamma':real->B) t IN U'` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                               ((psi':B->A) o (gamma':real->B)) (&0) (&1)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC GRGD_C1_CURVE_PUSH THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                            `U':B->bool`] THEN
      ASM_REWRITE_TAC[REAL_LT_01; IN_REAL_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN `((psi':B->A) o (gamma':real->B)) (&0) = x /\
                  ((psi':B->A) o (gamma':real->B)) (&1) = y`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[o_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> ((psi':B->A) o (gamma':real->B)) t IN S`
    ASSUME_TAC THENL
     [REWRITE_TAC[o_THM] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (find_term ((=) `IMAGE (psi:A->B) S`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `g':B->real^N^N`;
                   `(psi':B->A) o (gamma':real->B)`; `&0`; `&1`] P2B9S_PB_LENGTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01; IN_REAL_INTERVAL] THEN ASM SET_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_length atlas' (g':B->real^N^N)
                    ((psi:A->B) o (psi':B->A) o (gamma':real->B)) (&0) (&1) =
                  mfd_length atlas' g' gamma' (&0) (&1)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_LENGTH_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^N^N) ((psi':B->A) o (gamma':real->B)) (&0) (&1)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `S:A->bool`;
                     `(psi':B->A) o (gamma':real->B)`; `&0`; `&1`] MFD_DIST_IN_LE_LENGTH) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_length atlas' (g':B->real^N^N) (gamma':real->B) (&0) (&1) =
                  mfd_length atlas (mfd_pullback_metric atlas atlas' (psi:A->B) g')
                             ((psi':B->A) o gamma') (&0) (&1)`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2B9S_LENGTH_COMPARE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable_in (top:A topology,atlas:((A->bool)#(A->real^N))->bool) S x y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_joinable_in (top':B topology,atlas':((B->bool)#(B->real^N))->bool)
                   (IMAGE (psi:A->B) S) (psi x) (psi y)` THEN
    REWRITE_TAC[mfd_joinable_in] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma':real->B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(psi':B->A) o (gamma':real->B)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `gamma':real->B`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [mfd_dist_in] THEN MATCH_MP_TAC REAL_LE_INF THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN
    ASM_MESON_TAC[mfd_joinable_in];
    X_GEN_TAC `L:real` THEN REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma':real->B` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `gamma':real->B`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[]]);;

let P2B9S_PB_FIELDS = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) U U' psi psi' y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U
     ==> y IN topspace top /\
         ?s. open s /\ SND(chart_at atlas y) y IN s /\
             metric_field s (metric_local atlas (chart_at atlas y) g) /\
             metric_field s (metric_local atlas (chart_at atlas y)
                               (mfd_pullback_metric atlas atlas' psi g'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `g':B->real^N^N`; `y:A`] P2B9S_PB_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `P:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))) (FST (chart_at atlas y)))
                  (metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas y)
                     (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(P:real^N->bool) INTER IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))) (FST (chart_at atlas y))` THEN
  SUBGOAL_THEN `open (IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))) (FST (chart_at atlas y)))`
  ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `open ((P:real^N->bool) INTER
                       IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                             (FST (chart_at atlas y)))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_INTER; FUN_IN_IMAGE] THEN CONJ_TAC THEN
  MATCH_MP_TAC METRIC_FIELD_SUBSET THENL
   [EXISTS_TAC `IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                      (FST (chart_at atlas y))` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    EXISTS_TAC `P:real^N->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET]]);;

let P2B9S_PB_QF = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) U U' psi psi' R k d y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U /\ &0 < R /\
     lck_dist2 k (metric_local atlas (chart_at atlas y) (\z. R %% g z))
                 (metric_local atlas (chart_at atlas y)
                    (\z. R %% mfd_pullback_metric atlas atlas' psi g' z))
                 (SND(chart_at atlas y) y) <= d
     ==> !v. abs(v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) -
                 v dot (g y ** v)) <= sqrt d * (v dot (g y ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y:A`]
                P2B9S_PB_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[METRIC_LOCAL_CMUL; ETA_AX]) THEN
  ABBREV_TAC `p = SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)) y` THEN
  ABBREV_TAC `Lg = metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas (y:A))
                     (g:A->real^N^N)` THEN
  ABBREV_TAC `Lp = metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas (y:A))
                     (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N))` THEN
  SUBGOAL_THEN `(Lg:real^N->real^N^N) p = g (y:A) /\
                (Lp:real^N->real^N^N) p = mfd_pullback_metric atlas atlas' (psi:A->B)
                                            (g':B->real^N^N) y`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Lg"; "Lp"; "p"] THEN CONJ_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `\w. R %% (Lg:real^N->real^N^N) w`;
                 `\w. R %% (Lp:real^N->real^N^N) w`; `p:real^N`; `v:real^N`] LCK_DIST_C0) THEN
  ASM_SIMP_TAC[LRG_METRIC_FIELD_SCALE] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `&0 <= v dot ((g:A->real^N^N) y ** v)` ASSUME_TAC THENL
   [ASM_CASES_TAC `v:real^N = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`] RIEMANNIAN_METRIC_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (\w. R %% (Lg:real^N->real^N^N) w) (\w. R %% Lp w) p) <=
                sqrt d` MP_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `q = sqrt(lck_dist2 k (\w. R %% (Lg:real^N->real^N^N) w) (\w. R %% Lp w) p)` THEN
  ABBREV_TAC `a = v dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N) y ** v)` THEN
  ABBREV_TAC `b = v dot ((g:A->real^N^N) y ** v)` THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs(a - b) <= q * b` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `R:real` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `R * abs (a - b) <= q * R * b` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

let P2B9S_COMPONENT_CURVE = prove
 (`!top atlas (gamma:real->A) a b U t.
     mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b /\
     U IN connected_components_of top /\ gamma a IN U /\ t IN real_interval[a,b]
     ==> gamma t IN U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (gamma:real->A) (real_interval[a,b]) SUBSET U` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL;
                  CONNECTED_IN_EUCLIDEANREAL_INTERVAL];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(gamma:real->A) a` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN
      ASM_MESON_TAC[mfd_c1_curve]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let P2B9S_DIST_COMPONENT = prove
 (`!top atlas (g:A->real^N^N) U x y.
     U IN connected_components_of top /\ x IN U
     ==> mfd_dist (top,atlas) g x y = mfd_dist_in (top,atlas) g U x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist; mfd_dist_in] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `L:real` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2B9S_COMPONENT_CURVE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `&0`; `&1`] THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL]);;

let P2B9S_JOINABLE_IN_COMPONENT = prove
 (`!top atlas U (x:A) y.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     U IN connected_components_of top /\ x IN U /\ y IN U
     ==> mfd_joinable (top,atlas) x y /\ mfd_joinable_in (top,atlas) U x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED_COMPONENT] THEN REWRITE_TAC[connected_component_of] THEN
    EXISTS_TAC `U:A->bool` THEN ASM_SIMP_TAC[CONNECTED_IN_CONNECTED_COMPONENTS_OF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y` THEN
  REWRITE_TAC[mfd_joinable; mfd_joinable_in] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2B9S_COMPONENT_CURVE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `&0`; `&1`] THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL]);;

let P2B9S_DIST_COMPACT_BOUND = prove
 (`!top atlas (g:A->real^N^N) K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?B. !x y. x IN K /\ y IN K ==> mfd_dist (top,atlas) g x y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prod_topology (top:A topology) top`; `euclideanreal`;
                 `\(x,y). mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x y`;
                 `(K:A->bool) CROSS K`] IMAGE_COMPACT_IN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_DIST_CONTINUOUS; COMPACT_IN_CROSS]; ALL_TAC] THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  ASM_MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`]);;


(* ========================================================================= *)
(* Chart pullbacks, gluing, rescaling, naturality of lck.                    *)
(* ========================================================================= *)

let P2B9S_PB_LOCAL_CHART = prove
 (`!top atlas top' atlas' (f:A->B) f' (g':B->real^N^N) (U:A->bool)
    (phi:A->real^N) (V:B->bool) (psi:B->real^N) W W' x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_diffeo top atlas W top' atlas' W' f f' /\
        (U,phi) IN atlas /\ (V,psi) IN atlas' /\ x IN U /\ x IN W /\ f x IN V
        ==> metric_local atlas (U,phi) (mfd_pullback_metric atlas atlas' f g')
                         (phi x) =
            mpullback (psi o f o chart_inv (U,phi))
                      (metric_local atlas' (V,psi) g') (phi x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) x IN W'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:A->B) W SUBSET W'` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (W':B->bool)`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [metric_local] THEN BETA_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN U`)]) THEN
  REWRITE_TAC[mfd_pullback_metric] THEN BETA_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c0:(A->bool)#(A->real^N)`) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) x`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)`,
           `c0':(B->bool)#(B->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V0:B->bool`; `psi0:B->real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`U0:A->bool`; `phi0:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(U0:A->bool,phi0:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  (* the chart representative h0 of f at x is smooth near phi0 x *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `W':B->bool`; `f:A->B`; `f':B->A`;
                 `U0:A->bool`; `phi0:A->real^N`; `V0:B->bool`; `psi0:B->real^N`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `h0 = (psi0:B->real^N) o (f:A->B) o chart_inv (U0:A->bool,phi0:A->real^N)` THEN
  SUBGOAL_THEN `(h0:real^N->real^N) differentiable at ((phi0:A->real^N) x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi0:A->real^N)
                      {z | z IN U0 INTER W /\ (f:A->B) z IN V0}`;
                   `h0:real^N->real^N`; `(phi0:A->real^N) x`; `vec 0:real^N`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h0:real^N->real^N) ((phi0:A->real^N) x) = (psi0:B->real^N) (f x)`
  ASSUME_TAC THENL
   [EXPAND_TAC "h0" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the derivative identity, by locality and the chain rule *)
  SUBGOAL_THEN
   `frechet_derivative ((psi:B->real^N) o (f:A->B) o chart_inv (U,phi))
                       (at ((phi:A->real^N) x)) =
    chart_jac (V0,psi0) (V,psi) (f x) o
    frechet_derivative (h0:real^N->real^N) (at ((phi0:A->real^N) x)) o
    chart_jac (U,phi) (U0,phi0) x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`]
                  MFDM_CHART) THEN
    DISCH_THEN(MP_TAC o SPEC `(V0:B->bool,psi0:B->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN

    TRANS_TAC EQ_TRANS
     `frechet_derivative
        (\y. chart_trans (V0:B->bool,psi0:B->real^N) (V,psi)
               ((h0:real^N->real^N)
                  (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)))
        (at ((phi:A->real^N) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `IMAGE (phi:A->real^N)
                    {z | z IN U INTER {z | z IN U0 INTER W /\ (f:A->B) z IN V0} /\
                         f z IN V}` THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                       `(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`;
                       `{z | z IN U0 INTER W /\ (f:A->B) z IN V0}`; `f:A->B`]
                      MFDM_CHART_DOMAIN_OPEN) THEN
        REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                           `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                           `(U0:A->bool,phi0:A->real^N)`; `(V0:B->bool,psi0:B->real^N)`;
                           `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
            ASM_REWRITE_TAC[FST; SND] THEN SIMP_TAC[];
            MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
            EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
          SIMP_TAC[]];
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `x:A` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
        X_GEN_TAC `z:A` THEN STRIP_TAC THEN EXPAND_TAC "h0" THEN
        REWRITE_TAC[o_THM] THEN
        MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                      `U:A->bool`; `phi:A->real^N`; `U0:A->bool`; `phi0:A->real^N`;
                      `z:A`] CHART_TRANS_AT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC CHART_TRANS_AT THEN
        MAP_EVERY EXISTS_TAC
         [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `w:real^N` THEN
    REWRITE_TAC[chart_jac; SND] THEN
    SUBGOAL_THEN
     `chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) differentiable at (phi x) /\
      chart_trans (U,phi) (U0,phi0) (phi x) = phi0 x`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `chart_jac (U:A->bool,phi:A->real^N) (U0,phi0) x` THEN
        MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[IN_INTER];
        MATCH_MP_TAC CHART_TRANS_AT THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `chart_trans (V0:B->bool,psi0:B->real^N) (V,psi) differentiable
      at (psi0((f:A->B) x))`
    ASSUME_TAC THENL
     [REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `chart_jac (V0:B->bool,psi0:B->real^N) (V,psi) ((f:A->B) x)` THEN
      MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
      MAP_EVERY EXISTS_TAC
       [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\y. (h0:real^N->real^N) (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y))
      differentiable at (phi x)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(\y. (h0:real^N->real^N) (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)) =
        h0 o chart_trans (U,phi) (U0,phi0)`
       SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`\y. (h0:real^N->real^N) (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)`;
      `chart_trans (V0:B->bool,psi0:B->real^N) (V,psi)`;
      `(phi:A->real^N) x`; `w:real^N`] LRG_FRECHET_DERIVATIVE_CHAIN)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL
     [`chart_trans (U:A->bool,phi:A->real^N) (U0,phi0)`; `h0:real^N->real^N`;
      `(phi:A->real^N) x`; `w:real^N`] LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LRG_MPULLBACK_EQ] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((psi:B->real^N) o (f:A->B) o chart_inv (U,phi)) ((phi:A->real^N) x) =
    psi (f x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                `V0:B->bool`; `psi0:B->real^N`; `V:B->bool`; `psi:B->real^N`;
                `g':B->real^N^N`; `(f:A->B) x`] METRIC_LOCAL_JAC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `linear(chart_jac (U:A->bool,phi:A->real^N) (U0,phi0) (x:A)) /\
    linear(chart_jac (V0:B->bool,psi0:B->real^N) (V,psi) ((f:A->B) x)) /\
    linear(frechet_derivative (h0:real^N->real^N) (at ((phi0:A->real^N) x)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHART_JAC_LINEAR THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC CHART_JAC_LINEAR THEN
      MAP_EVERY EXISTS_TAC
       [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE; MATRIX_TRANSP_MUL;
               MATRIX_MUL_ASSOC]);;

let P2B9S_PB_FIELD_CHART = prove
 (`!top atlas top' atlas' W W' (f:A->B) f' (g':B->real^N^N)
    (c:(A->bool)#(A->real^N)) x.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas W top' atlas' W' f f' /\ c IN atlas /\ x IN FST c /\ x IN W
     ==> ?O. open O /\ SND c x IN O /\
             metric_field O (metric_local atlas c (mfd_pullback_metric atlas atlas' f g'))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `(f:A->B) x IN W'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (W':B->bool)`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) x`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W':B->bool`;
                 `f:A->B`; `f':B->A`; `FST(c:(A->bool)#(A->real^N))`;
                 `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(B->bool)#(B->real^N))`; `SND(c':(B->bool)#(B->real^N))`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                {z | z IN FST c INTER W /\ (f:A->B) z IN FST(c':(B->bool)#(B->real^N))}` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]; ALL_TAC] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `mpullback (SND(c':(B->bool)#(B->real^N)) o (f:A->B) o
                         chart_inv (c:(A->bool)#(A->real^N)))
                (metric_local atlas' c' (g':B->real^N^N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    EXISTS_TAC `IMAGE (SND(c':(B->bool)#(B->real^N)))
                  {y | y IN FST c' INTER W' /\ (f':B->A) y IN FST(c:(A->bool)#(A->real^N))}` THEN
    EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) o (f':B->A) o
                chart_inv (c':(B->bool)#(B->real^N))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c':(B->bool)#(B->real^N))) (FST c')` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas' (g':B->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `f':B->A`; `g':B->real^N^N`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c':(B->bool)#(B->real^N))`; `SND(c':(B->bool)#(B->real^N))`;
                   `W:A->bool`; `W':B->bool`; `z:A`] P2B9S_PB_LOCAL_CHART) THEN
    ASM_REWRITE_TAC[PAIR]]);;

let P2B9S_RIEMANNIAN_GLUE = prove
 (`!top atlas (g:A->real^N^N) W h.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ closed_in top W /\
     (!c x. c IN atlas /\ x IN FST c /\ x IN W
            ==> ?O. open O /\ SND c x IN O /\ metric_field O (metric_local atlas c h))
     ==> riemannian_metric atlas (\z. if z IN W then h z else g z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                             (metric_local atlas c (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!S. open_in top (S:A->bool)
                    ==> open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER S))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `S:A->bool`] MFDR_RESTRICT_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!S G. (!z. z IN FST c INTER S
               ==> (\z. if z IN W then (h:A->real^N^N) z else g z) z = G z)
          ==> !w. w IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER S)
                  ==> metric_local atlas c (\z. if z IN W then h z else g z) w =
                      metric_local atlas c G w`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    REWRITE_TAC[metric_local] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c (z:A)) = z` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[IN_INTER] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:A) IN W` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `x:A`] o check (fun th ->
      can (find_term ((=) `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)`))
          (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(O:real^N->bool) INTER IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER; FUN_IN_IMAGE] THEN
    MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
    EXISTS_TAC `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `O:real^N->bool` THEN
      ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET];
      REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`W:A->bool`; `h:A->real^N^N`] o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `G:A->real^N^N`)) (concl th))) THEN
      ANTS_TAC THENL [SIMP_TAC[IN_INTER]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `open_in top (topspace top DIFF (W:A->bool))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE]; ALL_TAC] THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER (topspace top DIFF W))` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST (c:(A->bool)#(A->real^N)))`)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
    EXISTS_TAC `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`topspace top DIFF (W:A->bool)`; `g:A->real^N^N`] o
        check (fun th -> is_forall (concl th) &&
                         can (find_term ((=) `G:A->real^N^N`)) (concl th))) THEN
      ANTS_TAC THENL [SIMP_TAC[IN_INTER; IN_DIFF]; SIMP_TAC[]]]]);;

let P2B9S_LNABLA_ITER_CMUL = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) c.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> !l y u. y IN U
                 ==> lnabla_iter k l G (\x u. c * tf x u) y u = c * lnabla_iter k l G tf y u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `tf:real^N->(num->real^N)->real`;
                 `c:real`; `&0`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x u. c * (tf:real^N->(num->real^N)->real) x u + &0 * tf x u) =
                (\x u. c * tf x u)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_RID]);;

let P2B9S_LCK_SCALE_BOTH = prove
 (`!k s (G0:real^N->real^N^N) G c y.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ &0 < c
     ==> lck_dist2 k (\z. c %% G0 z) (\z. c %% G z) y =
         sum(0..k) (\l. inv c pow l *
                        ltnorm2 (2 + l) G0
                          (lnabla_iter 2 l G0 (\z u. lmetric2 G z u - lmetric2 G0 z u)) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Tm = \z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u` THEN
  SUBGOAL_THEN `(\z u. lmetric2 (\z. c %% (G:real^N->real^N^N) z) z u -
                       lmetric2 (\z. c %% G0 z) z u) =
                (\z u. c * (Tm:real^N->(num->real^N)->real) z u)` ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN REWRITE_TAC[FUN_EQ_THM; lmetric2; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `\z. c %% (G0:real^N->real^N^N) z`; `G0:real^N->real^N^N`;
                 `\z u. c * (Tm:real^N->(num->real^N)->real) z u`; `s:real^N->bool`]
                LRG_LNABLA_ITER_CHRISTOFFEL_EQ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CHRISTOFFEL_SCALE]; DISCH_TAC] THEN
  SUBGOAL_THEN `!u. smooth_map_on s (\y. lift((Tm:real^N->(num->real^N)->real) y u))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `Tm:real^N->(num->real^N)->real`; `c:real`] P2B9S_LNABLA_ITER_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[lck_dist2] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[P2C_LTNORM2_METRIC_SCALE] THEN
  SUBGOAL_THEN `ltnorm2 (2 + l) (G0:real^N->real^N^N)
                  (lnabla_iter 2 l (\z. c %% G0 z)
                     (\z u. c * (Tm:real^N->(num->real^N)->real) z u)) y =
                ltnorm2 (2 + l) G0 (\x u. c * lnabla_iter 2 l G0 Tm x u) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[ltnorm2] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LRG_LTNORM2_CMUL; REAL_MUL_ASSOC; ETA_AX] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_INV] THEN
  UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;

let P2B9S_LCK_SCALE_LE = prove
 (`!k s (G0:real^N->real^N^N) G c y.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ &0 < c
     ==> lck_dist2 k (\z. c %% G0 z) (\z. c %% G z) y <=
         (&1 + inv c) pow k * lck_dist2 k G0 G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `c:real`; `y:real^N`] P2B9S_LCK_SCALE_BOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lck_dist2; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + inv c) pow l` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
    MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let P2B9S_PB_PB = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) z.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ z IN U'
     ==> mfd_pullback_metric atlas' atlas psi' (mfd_pullback_metric atlas atlas' psi g') z =
         g' z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `(psi':B->A) z IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B) ((psi':B->A) z) = z` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:B) IN topspace top' /\ (psi':B->A) z IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (U':B->bool)`));
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`))] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `z:B`] CHART_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(psi':B->A) z`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((psi':B->A) z)` THEN
  ABBREV_TAC `c' = chart_at (atlas':((B->bool)#(B->real^N))->bool) (z:B)` THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = SND (c':(B->bool)#(B->real^N)) o (psi:A->B) o
                  chart_inv (c:(A->bool)#(A->real^N))` THEN
  ABBREV_TAC `K' = SND (c:(A->bool)#(A->real^N)) o (psi':B->A) o
                   chart_inv (c':(B->bool)#(B->real^N))` THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `U':B->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `psi':B->A`; `psi:A->B`; `FST(c':(B->bool)#(B->real^N))`;
                 `SND(c':(B->bool)#(B->real^N))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_SIMP_TAC[MFD_DIFFEO_SYM; PAIR] THEN
  ABBREV_TAC `O' = IMAGE (SND (c':(B->bool)#(B->real^N)))
                     {w | w IN FST c' INTER U' /\ (psi':B->A) w IN FST(c:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `O = IMAGE (SND (c:(A->bool)#(A->real^N)))
                    {w | w IN FST c INTER U /\ (psi:A->B) w IN FST(c':(B->bool)#(B->real^N))}` THEN
  SUBGOAL_THEN `SND (c':(B->bool)#(B->real^N)) z IN O'` ASSUME_TAC THENL
   [EXPAND_TAC "O'" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `(K':real^N->real^N) (SND (c':(B->bool)#(B->real^N)) z) =
                SND (c:(A->bool)#(A->real^N)) ((psi':B->A) z)` ASSUME_TAC THENL
   [EXPAND_TAC "K'" THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `c':(B->bool)#(B->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `pb = mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N)` THEN
  SUBGOAL_THEN `metric_local atlas (c:(A->bool)#(A->real^N)) (pb:A->real^N^N)
                  (SND c ((psi':B->A) z)) =
                mpullback (K:real^N->real^N) (metric_local atlas' (c':(B->bool)#(B->real^N))
                                                (g':B->real^N^N))
                  (SND c ((psi':B->A) z))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `pb:A->real^N^N`; `(psi':B->A) z`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "pb" THEN REWRITE_TAC[mfd_pullback_metric] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_pullback_metric] THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `mpullback (K':real^N->real^N)
      (mpullback (K:real^N->real^N) (metric_local atlas' (c':(B->bool)#(B->real^N))
                                       (g':B->real^N^N)))
      (SND c' (z:B))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_PT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) ((psi':B->A) z) IN O` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `O:real^N->bool` &&
      can (find_term ((=) `K':real^N->real^N`)) (concl th))) THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        lhs(concl th) = `(K':real^N->real^N) (SND (c':(B->bool)#(B->real^N)) z)`
      then SUBST1_TAC(SYM th) else failwith "no") THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K':real^N->real^N`; `K:real^N->real^N`;
                 `metric_local atlas' (c':(B->bool)#(B->real^N)) (g':B->real^N^N)`;
                 `SND (c':(B->bool)#(B->real^N)) z`] P2A_MPULLBACK_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  TRANS_TAC EQ_TRANS
   `mpullback (\w:real^N. w) (metric_local atlas' (c':(B->bool)#(B->real^N))
                                (g':B->real^N^N)) (SND c' (z:B))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN EXISTS_TAC `O':real^N->bool` THEN
    ASM_SIMP_TAC[o_THM];
    REWRITE_TAC[P2B9_MPULLBACK_ID] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `g':B->real^N^N`; `z:B`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[]]);;

let P2B9S_DIFFEO_ON_RESTRICT = prove
 (`!s t (f:real^N->real^N) g t'.
     diffeomorphism_on s t f g /\ open t' /\ t' SUBSET t
     ==> diffeomorphism_on (IMAGE g t') t' f g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^N. y IN t' ==> y IN t` ASSUME_TAC THENL
   [UNDISCH_TAC `t' SUBSET (t:real^N->bool)` THEN REWRITE_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN t ==> (g:real^N->real^N) y IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^N->real^N) t = s` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^N->real^N) t' = {x | x IN s /\ (f:real^N->real^N) x IN t'}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      STRIP_TAC THEN EXISTS_TAC `(f:real^N->real^N) x` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(g:real^N->real^N) y` THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let P2B9S_LCK_NATURAL = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (H0:B->real^N^N) H1 k y s.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U /\
     open s /\ SND(chart_at atlas' (psi y)) (psi y) IN s /\
     metric_field s (metric_local atlas' (chart_at atlas' (psi y)) H0) /\
     metric_field s (metric_local atlas' (chart_at atlas' (psi y)) H1)
     ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (mfd_pullback_metric atlas atlas' psi H0))
                     (metric_local atlas (chart_at atlas y) (mfd_pullback_metric atlas atlas' psi H1))
                     (SND(chart_at atlas y) y) =
         lck_dist2 k (metric_local atlas' (chart_at atlas' (psi y)) H0)
                     (metric_local atlas' (chart_at atlas' (psi y)) H1)
                     (SND(chart_at atlas' (psi y)) (psi y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `(psi:A->B) y IN U'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ (psi:A->B) y IN topspace top'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`));
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (U':B->bool)`))] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(psi:A->B) y`] CHART_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)` THEN
  ABBREV_TAC `c' = chart_at (atlas':((B->bool)#(B->real^N))->bool) ((psi:A->B) y)` THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = SND (c':(B->bool)#(B->real^N)) o (psi:A->B) o
                  chart_inv (c:(A->bool)#(A->real^N))` THEN
  ABBREV_TAC `K' = SND (c:(A->bool)#(A->real^N)) o (psi':B->A) o
                   chart_inv (c':(B->bool)#(B->real^N))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `U':B->bool`;
                 `psi:A->B`; `psi':B->A`; `FST(c:(A->bool)#(A->real^N))`;
                 `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(B->bool)#(B->real^N))`; `SND(c':(B->bool)#(B->real^N))`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  ABBREV_TAC `O = IMAGE (SND (c:(A->bool)#(A->real^N)))
                    {w | w IN FST c INTER U /\ (psi:A->B) w IN FST(c':(B->bool)#(B->real^N))}` THEN
  ABBREV_TAC `O' = IMAGE (SND (c':(B->bool)#(B->real^N)))
                     {w | w IN FST c' INTER U' /\ (psi':B->A) w IN FST(c:(A->bool)#(A->real^N))}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) y IN O /\
                SND (c':(B->bool)#(B->real^N)) ((psi:A->B) y) IN O'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O"; "O'"] THEN CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^N->real^N) (SND (c:(A->bool)#(A->real^N)) y) =
                SND (c':(B->bool)#(B->real^N)) ((psi:A->B) y)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN O
                    ==> metric_local atlas (c:(A->bool)#(A->real^N))
                          (mfd_pullback_metric atlas atlas' (psi:A->B) (H0:B->real^N^N)) w =
                        mpullback (K:real^N->real^N) (metric_local atlas' c' H0) w /\
                        metric_local atlas c (mfd_pullback_metric atlas atlas' psi (H1:B->real^N^N)) w =
                        mpullback K (metric_local atlas' (c':(B->bool)#(B->real^N)) H1) w`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN EXPAND_TAC "K" THEN CONJ_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `psi:A->B`; `psi':B->A`] P2B9S_PB_LOCAL_CHART) THEN
    DISCH_THEN(fun th -> MP_TAC(ISPECL [`H0:B->real^N^N`; `FST(c:(A->bool)#(A->real^N))`;
                   `SND(c:(A->bool)#(A->real^N))`; `FST(c':(B->bool)#(B->real^N))`;
                   `SND(c':(B->bool)#(B->real^N))`; `U:A->bool`; `U':B->bool`; `x:A`] th) THEN
               MP_TAC(ISPECL [`H1:B->real^N^N`; `FST(c:(A->bool)#(A->real^N))`;
                   `SND(c:(A->bool)#(A->real^N))`; `FST(c':(B->bool)#(B->real^N))`;
                   `SND(c':(B->bool)#(B->real^N))`; `U:A->bool`; `U':B->bool`; `x:A`] th)) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "diffeomorphism_on")) (concl th))) THEN
  ABBREV_TAC `t' = (O':real^N->bool) INTER s` THEN
  SUBGOAL_THEN `open (t':real^N->bool) /\ t' SUBSET O' /\
                SND (c':(B->bool)#(B->real^N)) ((psi:A->B) y) IN t'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER; INTER_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^N->bool`; `O':real^N->bool`; `K:real^N->real^N`; `K':real^N->real^N`;
                 `t':real^N->bool`] P2B9S_DIFFEO_ON_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open (IMAGE (K':real^N->real^N) t') /\ IMAGE K' t' SUBSET O /\
                SND (c:(A->bool)#(A->real^N)) y IN IMAGE K' t'` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[diffeomorphism_on];
      UNDISCH_TAC `t' SUBSET (O':real^N->bool)` THEN
      UNDISCH_TAC `IMAGE (K':real^N->real^N) O' = O` THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `SND (c':(B->bool)#(B->real^N)) ((psi:A->B) y)` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
          rator(lhs(concl th)) = `K:real^N->real^N` then SUBST1_TAC(SYM th) else failwith "no") THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lck_dist2 k (mpullback (K:real^N->real^N)
                   (metric_local atlas' (c':(B->bool)#(B->real^N)) (H0:B->real^N^N)))
                (mpullback K (metric_local atlas' c' (H1:B->real^N^N)))
                (SND (c:(A->bool)#(A->real^N)) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `IMAGE (K':real^N->real^N) t'` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `H1:B->real^N^N`)) (concl th) &&
      can (find_term ((=) `O:real^N->bool`)) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `t':real^N->bool`; `IMAGE (K':real^N->real^N) t'`;
                 `K:real^N->real^N`; `K':real^N->real^N`;
                 `metric_local atlas' (c':(B->bool)#(B->real^N)) (H0:B->real^N^N)`;
                 `metric_local atlas' (c':(B->bool)#(B->real^N)) (H1:B->real^N^N)`;
                 `SND (c:(A->bool)#(A->real^N)) y`] LCK_DIST2_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t'" THEN REWRITE_TAC[INTER_SUBSET];
    SIMP_TAC[]]);;

let P2B9S_METRIC_LOCAL_EQ_ON = prove
 (`!top atlas (h1:A->real^N^N) h2 W x.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     (!z. z IN W ==> h1 z = h2 z) /\ x IN W
     ==> ?s. open s /\ SND(chart_at atlas x) x IN s /\
             !w. w IN s ==> metric_local atlas (chart_at atlas x) h1 w =
                            metric_local atlas (chart_at atlas x) h2 w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (W:A->bool)`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `W:A->bool`] MFDR_RESTRICT_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    REWRITE_TAC[metric_local] THEN ASM_SIMP_TAC[]]);;

let P2B9S_PB_CMUL = prove
 (`!atlas atlas' (f:A->B) (G:B->real^N^N) q x.
     mfd_pullback_metric atlas atlas' f (\z. q %% G z) x =
     q %% mfd_pullback_metric atlas atlas' f G x`,
  REWRITE_TAC[mfd_pullback_metric; METRIC_LOCAL_CMUL; mpullback] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let P2B9S_ROUND_TARGET_METRIC = prove
 (`!top atlas (g1:A->real^N^N) top' atlas' (g':B->real^N^N) U U' psi psi'.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g1 /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ closed_in top' U' /\
     (!x u v. x IN U /\ ~collinear {vec 0,u,v} ==> mfd_sectional atlas g1 x u v = &1)
     ==> riemannian_metric atlas'
           (\z. if z IN U' then mfd_pullback_metric atlas' atlas psi' g1 z else g' z) /\
         (!z u v. z IN U' /\ ~collinear {vec 0,u,v}
                  ==> mfd_sectional atlas'
                        (\z. if z IN U' then mfd_pullback_metric atlas' atlas psi' g1 z
                             else g' z) z u v = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `mfd_diffeo (top':B topology) (atlas':((B->bool)#(B->real^N))->bool) U'
                           (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U
                           (psi':B->A) (psi:A->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2B9S_RIEMANNIAN_GLUE THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC P2B9S_PB_FIELD_CHART THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `top:A topology`; `U':B->bool`; `U:A->bool`;
                          `psi:A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:B`; `u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_sectional (atlas':((B->bool)#(B->real^N))->bool)
                  (\z. if z IN U' then mfd_pullback_metric atlas'
                                          (atlas:((A->bool)#(A->real^N))->bool) (psi':B->A)
                                          (g1:A->real^N^N) z
                       else (g':B->real^N^N) z) z u v =
                mfd_sectional atlas' (mfd_pullback_metric atlas' atlas psi' g1) z u v`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_sectional] THEN MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `\z. if z IN U' then mfd_pullback_metric atlas' atlas (psi':B->A)
                                          (g1:A->real^N^N) z
                        else (g':B->real^N^N) z`;
                   `mfd_pullback_metric atlas' atlas (psi':B->A) (g1:A->real^N^N)`;
                   `U':B->bool`; `z:B`] P2B9S_METRIC_LOCAL_EQ_ON) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U':B->bool`; `U:A->bool`; `psi':B->A`; `psi:A->B`;
                 `g1:A->real^N^N`; `z:B`] P2B9S_PB_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^N` (X_CHOOSE_THEN `v':real^N` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let P2B9S_ROUND_CLOSE_NAT = prove
 (`!top atlas (g1:A->real^N^N) top' atlas' (g':B->real^N^N) U U' psi psi' q k y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g1 /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ &0 < q /\ y IN U
     ==> lck_dist2 k (metric_local atlas' (chart_at atlas' (psi y))
                        (\z. if z IN U' then mfd_pullback_metric atlas' atlas psi' g1 z
                             else g' z))
                     (metric_local atlas' (chart_at atlas' (psi y)) (\z. q %% g' z))
                     (SND(chart_at atlas' (psi y)) (psi y)) =
         lck_dist2 k (metric_local atlas (chart_at atlas y) g1)
                     (metric_local atlas (chart_at atlas y)
                        (\z. q %% mfd_pullback_metric atlas atlas' psi g' z))
                     (SND(chart_at atlas y) y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `mfd_diffeo (top':B topology) (atlas':((B->bool)#(B->real^N))->bool) U'
                           (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U
                           (psi':B->A) (psi:A->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B) y IN U'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi':B->A) ((psi:A->B) y) = y` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `pb = mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N)` THEN
  ABBREV_TAC `y' = (psi:A->B) y` THEN
  (* the two target metrics agree on U' with pullbacks along psi' *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `\z. if z IN U' then mfd_pullback_metric atlas' atlas (psi':B->A)
                                        (g1:A->real^N^N) z
                      else (g':B->real^N^N) z`;
                 `mfd_pullback_metric atlas' atlas (psi':B->A) (g1:A->real^N^N)`;
                 `U':B->bool`; `y':B`] P2B9S_METRIC_LOCAL_EQ_ON) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `\z. q %% (g':B->real^N^N) z`;
                 `mfd_pullback_metric atlas' atlas (psi':B->A) (\z. q %% (pb:A->real^N^N) z)`;
                 `U':B->bool`; `y':B`] P2B9S_METRIC_LOCAL_EQ_ON) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2B9S_PB_CMUL] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN EXPAND_TAC "pb" THEN
    MATCH_MP_TAC P2B9S_PB_PB THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`; `U':B->bool`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC)] THEN
  TRANS_TAC EQ_TRANS
   `lck_dist2 k (metric_local atlas' (chart_at atlas' (y':B))
                   (mfd_pullback_metric atlas' (atlas:((A->bool)#(A->real^N))->bool) (psi':B->A)
                      (g1:A->real^N^N)))
                (metric_local (atlas':((B->bool)#(B->real^N))->bool) (chart_at atlas' y')
                   (mfd_pullback_metric atlas' atlas psi' (\z. q %% (pb:A->real^N^N) z)))
                (SND(chart_at atlas' y') y')` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `(s1:real^N->bool) INTER s2` THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g1:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y:A`] P2B9S_PB_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `metric_field s (metric_local (atlas:((A->bool)#(A->real^N))->bool)
                  (chart_at atlas (y:A)) (\z. q %% (pb:A->real^N^N) z))` ASSUME_TAC THENL
   [REWRITE_TAC[METRIC_LOCAL_CMUL] THEN MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U':B->bool`; `U:A->bool`; `psi':B->A`; `psi:A->B`;
                 `g1:A->real^N^N`; `\z. q %% (pb:A->real^N^N) z`; `k:num`; `y':B`;
                 `s:real^N->bool`] P2B9S_LCK_NATURAL) THEN
  ASM_REWRITE_TAC[]);;

let P2B9S_CLOSE_TRIANGLE = prove
 (`!M k k' s (Lg1:real^N->real^N^N) Lg Lp R q p d1 d2.
     (!s (G0:real^N->real^N^N) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k G0 G1 y <= &1 / &4
         ==> lck_dist2 k G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k G1 G2 y) /\
     &0 <= M /\ metric_field s Lg1 /\ metric_field s Lg /\ metric_field s Lp /\ p IN s /\
     &0 < R /\ &0 < q /\ k <= k' /\
     lck_dist2 k Lg1 (\w. q %% Lg w) p <= d1 /\ d1 <= &1 / &4 /\
     lck_dist2 k' (\w. R %% Lg w) (\w. R %% Lp w) p <= d2
     ==> sqrt(lck_dist2 k Lg1 (\w. q %% Lp w) p) <=
         sqrt d1 + sqrt(M * (&1 + R / q) pow k * d2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `metric_field s (\w. q %% (Lg:real^N->real^N^N) w) /\
                metric_field s (\w. q %% (Lp:real^N->real^N^N) w) /\
                metric_field s (\w. R %% (Lg:real^N->real^N^N) w) /\
                metric_field s (\w. R %% (Lp:real^N->real^N^N) w)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_METRIC_FIELD_SCALE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `Lg1:real^N->real^N^N`;
                 `\w. q %% (Lg:real^N->real^N^N) w`; `\w. q %% (Lp:real^N->real^N^N) w`;
                 `p:real^N`] LCK_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' ==> x <= a + b ==> x <= a' + b'`) THEN
  CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `M * lck_dist2 k (\w. q %% (Lg:real^N->real^N^N) w) (\w. q %% Lp w) p` THEN
  CONJ_TAC THENL
   [USE_THEN "B" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\w. q %% (Lg:real^N->real^N^N) w) = (\w. (q / R) %% (\w. R %% Lg w) w) /\
                (\w. q %% (Lp:real^N->real^N^N) w) = (\w. (q / R) %% (\w. R %% Lp w) w)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN CONJ_TAC THEN GEN_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + inv(q / R)) pow k *
              lck_dist2 k (\w. R %% (Lg:real^N->real^N^N) w) (\w. R %% Lp w) p` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2B9S_LCK_SCALE_LE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 k' (\w. R %% (Lg:real^N->real^N^N) w) (\w. R %% Lp w) p` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2B9S_SQRT_LE_POW2 = prove
 (`!L B. &0 <= L /\ sqrt L <= B ==> L <= B pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt L pow 2` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]]);;

let P2B9S_ROUND_POINT = prove
 (`!top atlas (g:A->real^N^N) (g1:A->real^N^N) top' atlas' (g':B->real^N^N)
    U U' psi psi' q R M k k' d1 d2 y.
     (!s (G0:real^N->real^N^N) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k G0 G1 y <= &1 / &4
         ==> lck_dist2 k G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k G1 G2 y) /\
     &0 <= M /\
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas g1 /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U /\ &0 < q /\ &0 < R /\
     k <= k' /\
     lck_dist2 k (metric_local atlas (chart_at atlas y) g1)
                 (metric_local atlas (chart_at atlas y) (\x. q %% g x))
                 (SND(chart_at atlas y) y) <= d1 /\ d1 <= &1 / &4 /\
     lck_dist2 k' (metric_local atlas (chart_at atlas y) (\x. R %% g x))
                  (metric_local atlas (chart_at atlas y)
                     (\x. R %% mfd_pullback_metric atlas atlas' psi g' x))
                  (SND(chart_at atlas y) y) <= d2
     ==> lck_dist2 k (metric_local atlas' (chart_at atlas' (psi y))
                        (\z. if z IN U' then mfd_pullback_metric atlas' atlas psi' g1 z
                             else g' z))
                     (metric_local atlas' (chart_at atlas' (psi y)) (\z. q %% g' z))
                     (SND(chart_at atlas' (psi y)) (psi y))
         <= (sqrt d1 + sqrt(M * (&1 + R / q) pow k * d2)) pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g1:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `q:real`; `k:num`; `y:A`]
                P2B9S_ROUND_CLOSE_NAT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y:A`] P2B9S_PB_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                                     (FST (chart_at atlas y)))
                             (metric_local atlas (chart_at atlas y) (g1:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s1 = (s:real^N->bool) INTER
                   IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                         (FST (chart_at atlas y))` THEN
  SUBGOAL_THEN `open (IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                            (FST (chart_at atlas y)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `open (s1:real^N->bool) /\
                SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)) y IN s1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER; FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field s1 (metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas (y:A))
                       (g1:A->real^N^N)) /\
    metric_field s1 (metric_local atlas (chart_at atlas y) (g:A->real^N^N)) /\
    metric_field s1 (metric_local atlas (chart_at atlas y)
                       (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    ASM_MESON_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[METRIC_LOCAL_CMUL; ETA_AX]) THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`M:real`; `k:num`; `k':num`; `s1:real^N->bool`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))
                    (g1:A->real^N^N)`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))
                    (g:A->real^N^N)`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))
                    (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N))`;
                 `R:real`; `q:real`;
                 `SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)) y`;
                 `d1:real`; `d2:real`] P2B9S_CLOSE_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC P2B9S_SQRT_LE_POW2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `s1:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX]);;

let P2B9S_DELTA_ARITH = prove
 (`!eps d1 A0 d2 delta.
     &0 < eps /\ &0 <= d1 /\ d1 < eps pow 2 /\ &0 <= A0 /\ &0 <= d2 /\ d2 < delta pow 2 /\
     &0 < delta /\ delta <= (eps - sqrt d1) / (sqrt A0 + &1)
     ==> (sqrt d1 + sqrt(A0 * d2)) pow 2 < eps pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
  REWRITE_TAC[ARITH_RULE `~(2 = 0)`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[SQRT_POS_LE] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt d1 < eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt d2 < delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt A0 /\ &0 <= sqrt d2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL] THEN
  SUBGOAL_THEN `sqrt A0 * sqrt d2 <= sqrt A0 * delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt A0 * delta < eps - sqrt d1` ASSUME_TAC THENL
   [UNDISCH_TAC `delta <= (eps - sqrt d1) / (sqrt A0 + &1)` THEN
    SUBGOAL_THEN `&0 < sqrt A0 + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC `&0 < delta` THEN UNDISCH_TAC `&0 <= sqrt A0` THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    SPEC_TAC(`sqrt A0`,`a:real`) THEN GEN_TAC THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < delta /\ delta * (a + &1) <= e ==> a * delta < e`) THEN
    ASM_REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2B9S_PB_LCK_POS = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) U U' psi psi' R k y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U /\ &0 < R
     ==> &0 <= lck_dist2 k (metric_local atlas (chart_at atlas y) (\x. R %% g x))
                           (metric_local atlas (chart_at atlas y)
                              (\x. R %% mfd_pullback_metric atlas atlas' psi g' x))
                           (SND(chart_at atlas y) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y:A`] P2B9S_PB_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[METRIC_LOCAL_CMUL] THEN CONJ_TAC THEN
  MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX]);;


(* ========================================================================= *)
(* The eps-round component case of the open form.                            *)
(* ========================================================================= *)

let P2B9S_OPEN_ROUND = prove
 (`!eps top atlas (g:A->real^3^3) x U.
     &0 < eps /\ eps <= &1 / &2 /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     rfs_round_component (top,atlas) g eps U /\ x IN U /\ &0 < mfd_scalar atlas g x
     ==> ?delta. &0 < delta /\
           !top' atlas' (g':B->real^3^3) psi psi'.
              smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
              mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
              IMAGE psi U IN connected_components_of top' /\
              rfs_mclose (rfs_kreg delta) delta atlas U
                (\y. mfd_scalar atlas g x %% g y)
                (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
              ==> rfs_round_component (top',atlas') g' eps (IMAGE psi U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_round_component (top,atlas) (g:A->real^3^3) eps U` THEN
  REWRITE_TAC[rfs_round_component] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `g1:A->real^3^3` STRIP_ASSUME_TAC))))) THEN
  UNDISCH_TAC `rfs_mclose (rfs_kreg eps) eps atlas U (g1:A->real^3^3)
                 (\x. q %% (g:A->real^3^3) x)` THEN
  REWRITE_TAC[rfs_mclose] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN
  MP_TAC(SPEC `k:num` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT] P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B"))) THEN
  ABBREV_TAC `A0 = M * (&1 + R / q) pow k` THEN
  SUBGOAL_THEN `&0 <= A0` ASSUME_TAC THENL
   [EXPAND_TAC "A0" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 k (metric_local atlas (chart_at atlas (x:A)) (g1:A->real^3^3))
                  (metric_local atlas (chart_at atlas x) (\x. q %% (g:A->real^3^3) x))
                  (SND(chart_at atlas x) x)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                      (FST (chart_at atlas x))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; METRIC_LOCAL_CMUL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)`;
      MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)`] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt d1 < eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  EXISTS_TAC `min eps ((eps - sqrt d1) / (sqrt A0 + &1))` THEN
  ABBREV_TAC `delta = min eps ((eps - sqrt d1) / (sqrt A0 + &1))` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= eps /\ delta <= (eps - sqrt d1) / (sqrt A0 + &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    SUBGOAL_THEN `&0 <= sqrt A0` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                       `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `&0 <= d2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg delta)
                  (metric_local atlas (chart_at atlas (x:A)) (\y. R %% (g:A->real^3^3) y))
                  (metric_local atlas (chart_at atlas x)
                     (\y. R %% mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y))
                  (SND(chart_at atlas x) x)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC P2B9S_PB_LCK_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`;
                          `IMAGE (psi:A->B) U`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_round_component] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology top (U:A->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o MATCH_MP MFD_DIFFEO_MAPS);
    ALL_TAC] THEN
  EXISTS_TAC `q:real` THEN
  EXISTS_TAC `\z. if z IN IMAGE (psi:A->B) U
                  then mfd_pullback_metric atlas' atlas (psi':B->A) (g1:A->real^3^3) z
                  else (g':B->real^3^3) z` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`]
                P2B9S_ROUND_TARGET_METRIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_CONNECTED_COMPONENTS_OF THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(sqrt d1 + sqrt(M * (&1 + R / q) pow k * d2)) pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2B9S_DELTA_ARITH THEN EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g1:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`;
                 `q:real`; `R:real`; `M:real`; `k:num`; `rfs_kreg delta`;
                 `d1:real`; `d2:real`; `y:A`] P2B9S_ROUND_POINT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "B" ACCEPT_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "k" THEN MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    SIMP_TAC[]]);;


(* ========================================================================= *)
(* The C-component case of the open form (diffeomorphism type, margin        *)
(* arithmetic, scalar range on compact sets, distance transfer on            *)
(* components, parameter choice, the case itself).                           *)
(* ========================================================================= *)

let P2B9S_CCOMP_TYPE = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi'.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
     smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     (mfd_diffeomorphic (subtopology top U) (restrict_atlas atlas U)
        (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas \/
      rfs_has_twisted (subtopology top U) (restrict_atlas atlas U))
     ==> (mfd_diffeomorphic (subtopology top' U') (restrict_atlas atlas' U')
            (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas \/
          rfs_has_twisted (subtopology top' U') (restrict_atlas atlas' U'))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "alt")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top /\ (U':B->bool) SUBSET topspace top'`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top (U:A->bool))
                  (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U) /\
                smooth_manifold_atlas (subtopology top' (U':B->bool))
                  (restrict_atlas (atlas':((B->bool)#(B->real^3))->bool) U')`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo (subtopology top (U:A->bool))
                  (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U)
                  (topspace (subtopology top U))
                  (subtopology top' (U':B->bool))
                  (restrict_atlas (atlas':((B->bool)#(B->real^3))->bool) U')
                  (topspace (subtopology top' U')) (psi:A->B) psi'`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `U':B->bool`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`]
                  APX_MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  REMOVE_THEN "alt" DISJ_CASES_TAC THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`subtopology top' (U':B->bool)`;
                   `restrict_atlas (atlas':((B->bool)#(B->real^3))->bool) U'`;
                   `subtopology top (U:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                   `subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`]
                  MFD_DIFFEOMORPHIC_TRANS) THEN
    ASM_REWRITE_TAC[SPHERE3_ATLAS] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mfd_diffeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`psi':B->A`; `psi:A->B`] THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN UNDISCH_TAC `rfs_has_twisted (subtopology top (U:A->bool))
                                 (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U)` THEN
    REWRITE_TAC[rfs_has_twisted] THEN DISCH_THEN(X_CHOOSE_TAC `p:real^3->A`) THEN
    EXISTS_TAC `(psi:A->B) o (p:real^3->A)` THEN MATCH_MP_TAC APX_TWISTED_CHART_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (U:A->bool)`;
                          `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                          `psi':B->A`] THEN
    ASM_REWRITE_TAC[]]);;

let P2B9S_MARGIN_GRAD_POLY = prove
 (`!m R0 d E r r' G G' alpha.
     &0 < m /\ &0 < R0 /\ &0 <= d /\ d < E /\ m * R0 <= r /\
     G <= d pow 2 * r pow 3 /\ G' <= G + alpha * R0 pow 3 /\ r - alpha * R0 <= r' /\
     &0 <= alpha /\ &3 * alpha <= m /\
     alpha * (&1 + &3 * E pow 2 * m pow 2) <= (E pow 2 - d pow 2) * m pow 3
     ==> &0 < r' /\ G' <= E pow 2 * r' pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = alpha * R0` THEN
  SUBGOAL_THEN `&0 <= a /\ &3 * a <= r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m * R0` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `m * R0` THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(r - a) pow 3 <= r' pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r pow 3 - &3 * r pow 2 * a <= (r - a) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a pow 2 * (&3 * r - a) /\
                             (r - a) pow 3 = r pow 3 - &3 * r pow 2 * a + a pow 2 * (&3 * r - a)
                             ==> r pow 3 - &3 * r pow 2 * a <= (r - a) pow 3`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `m pow 3 * R0 pow 3 <= r pow 3 /\ m pow 3 * (r pow 2 * R0) <= m pow 2 * r pow 3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_ARITH `m pow 3 * (r pow 2 * R0) = (m pow 2 * r pow 2) * (m * R0)`;
                  REAL_ARITH `m pow 2 * r pow 3 = (m pow 2 * r pow 2) * r`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `m pow 3 * (alpha * R0 pow 3 + &3 * E pow 2 * r pow 2 * a) <=
                (E pow 2 - d pow 2) * m pow 3 * r pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `alpha * (&1 + &3 * E pow 2 * m pow 2) * r pow 3` THEN CONJ_TAC THENL
     [EXPAND_TAC "a" THEN
      REWRITE_TAC[REAL_ARITH
       `m pow 3 * (alpha * R0 pow 3 + &3 * E pow 2 * r pow 2 * alpha * R0) =
        alpha * (m pow 3 * R0 pow 3) +
        (&3 * E pow 2 * alpha) * (m pow 3 * (r pow 2 * R0))`;
       REAL_ARITH `alpha * (&1 + &3 * E pow 2 * m pow 2) * r pow 3 =
                   alpha * r pow 3 + (&3 * E pow 2 * alpha) * (m pow 2 * r pow 3)`] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_POS];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
      ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `alpha * R0 pow 3 + &3 * E pow 2 * r pow 2 * a <= (E pow 2 - d pow 2) * r pow 3`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `m pow 3` THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN
    UNDISCH_TAC `m pow 3 * (alpha * R0 pow 3 + &3 * E pow 2 * r pow 2 * a) <=
                 (E pow 2 - d pow 2) * m pow 3 * r pow 3` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `E pow 2 * (r pow 3 - &3 * r pow 2 * a) <= E pow 2 * r' pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2B9S_MARGIN_LAP_POLY = prove
 (`!m R0 d E r r' X X' alpha.
     &0 < m /\ &0 < R0 /\ &0 <= d /\ d < E /\ m * R0 <= r /\
     abs X <= d * r pow 2 /\ abs(X' - X) <= &3 * alpha * R0 pow 2 /\ r - alpha * R0 <= r' /\
     &0 <= alpha /\ &3 * alpha <= m /\
     alpha * (&3 + &2 * E * m) <= (E - d) * m pow 2
     ==> &0 < r' /\ abs X' <= E * r' pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = alpha * R0` THEN
  SUBGOAL_THEN `&0 <= a /\ &3 * a <= r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m * R0` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `m * R0` THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(r - a) pow 2 <= r' pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 - &2 * r * a <= (r - a) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a pow 2 /\ (r - a) pow 2 = r pow 2 - &2 * r * a + a pow 2
                             ==> r pow 2 - &2 * r * a <= (r - a) pow 2`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `m pow 2 * R0 pow 2 <= r pow 2 /\ m pow 2 * (r * R0) <= m * r pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_ARITH `m pow 2 * (r * R0) = (m * r) * (m * R0)`;
                  REAL_ARITH `m * r pow 2 = (m * r) * r`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `m pow 2 * (&3 * alpha * R0 pow 2 + &2 * E * r * a) <=
                (E - d) * m pow 2 * r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `alpha * (&3 + &2 * E * m) * r pow 2` THEN CONJ_TAC THENL
     [EXPAND_TAC "a" THEN
      REWRITE_TAC[REAL_ARITH
       `m pow 2 * (&3 * alpha * R0 pow 2 + &2 * E * r * alpha * R0) =
        (&3 * alpha) * (m pow 2 * R0 pow 2) + (&2 * E * alpha) * (m pow 2 * (r * R0))`;
       REAL_ARITH `alpha * (&3 + &2 * E * m) * r pow 2 =
                   (&3 * alpha) * r pow 2 + (&2 * E * alpha) * (m * r pow 2)`] THEN
      SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * alpha * R0 pow 2 + &2 * E * r * a <= (E - d) * r pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `m pow 2` THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN
    UNDISCH_TAC `m pow 2 * (&3 * alpha * R0 pow 2 + &2 * E * r * a) <=
                 (E - d) * m pow 2 * r pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `E * (r pow 2 - &2 * r * a) <= E * r' pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2B9S_GRAD_RATIO_IMP = prove
 (`!r G d. &0 < r /\ &0 <= G /\ &0 <= d /\ sqrt G / (r * sqrt r) <= d
           ==> G <= d pow 2 * r pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r * sqrt r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt G <= d * r * sqrt r` ASSUME_TAC THENL
   [UNDISCH_TAC `sqrt G / (r * sqrt r) <= d` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt G pow 2 <= (d * r * sqrt r) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_POW_MUL; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;

let P2B9S_GRAD_RATIO_BACK = prove
 (`!r G E. &0 < r /\ &0 <= G /\ &0 <= E /\ G <= E pow 2 * r pow 3
           ==> sqrt G / (r * sqrt r) <= E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r * sqrt r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(E pow 2 * r pow 3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `E pow 2 * r pow 3 = (E * r) pow 2 * r` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL] THEN
  SUBGOAL_THEN `&0 <= E * r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT] THEN REAL_ARITH_TAC);;

let P2B9S_LAP_RATIO_IMP = prove
 (`!r X d. &0 < r /\ abs X / r pow 2 <= d ==> abs X <= d * r pow 2`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `abs X / r pow 2 <= d` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT]);;

let P2B9S_LAP_RATIO_BACK = prove
 (`!r X E. &0 < r /\ abs X <= E * r pow 2 ==> abs X / r pow 2 <= E`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT]);;

let P2B9S_COMPACT_SCALAR_RANGE = prove
 (`!top atlas (g:A->real^N^N) U.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top U /\ ~(U = {})
     ==> ?y0 y1. y0 IN U /\ y1 IN U /\
                 (!y. y IN U ==> mfd_scalar atlas g y0 <= mfd_scalar atlas g y /\
                                 mfd_scalar atlas g y <= mfd_scalar atlas g y1) /\
                 inf(IMAGE (mfd_scalar atlas g) U) = mfd_scalar atlas g y0 /\
                 sup(IMAGE (mfd_scalar atlas g) U) = mfd_scalar atlas g y1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_compact (IMAGE (mfd_scalar atlas (g:A->real^N^N)) U)` ASSUME_TAC THENL
   [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (mfd_scalar atlas (g:A->real^N^N)) U = {})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (mfd_scalar atlas (g:A->real^N^N)) U` REAL_COMPACT_ATTAINS_INF) THEN
  MP_TAC(ISPEC `IMAGE (mfd_scalar atlas (g:A->real^N^N)) U` REAL_COMPACT_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`y0:A`; `y1:A`] THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INF_LE THEN EXISTS_TAC `mfd_scalar atlas (g:A->real^N^N) y0` THEN
      EXISTS_TAC `mfd_scalar atlas (g:A->real^N^N) y0` THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE; FORALL_IN_IMAGE; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_INF THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE]];
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE];
      MATCH_MP_TAC REAL_LE_SUP THEN EXISTS_TAC `mfd_scalar atlas (g:A->real^N^N) y1` THEN
      EXISTS_TAC `mfd_scalar atlas (g:A->real^N^N) y1` THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE; FORALL_IN_IMAGE; REAL_LE_REFL]]]);;

let P2B9S_LT_FROM_SQUARES = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x pow 2 < y pow 2 ==> x < y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `y pow 2 <= x pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);;

let P2B9S_DIAM_UPPER = prove
 (`!C D Rn Rn' D' dl a.
     &0 < C /\ &0 <= D /\ &0 < Rn /\ D pow 2 * Rn < C pow 2 /\
     &0 <= dl /\ dl <= &1 /\ &0 <= a /\ &0 <= D' /\ D' <= sqrt(&1 + dl) * D /\
     &0 < Rn' /\ Rn' <= Rn + a /\ D pow 2 * (dl * Rn + &2 * a) < C pow 2 - D pow 2 * Rn
     ==> D' < C * inv(sqrt Rn')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt Rn'` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC P2B9S_LT_FROM_SQUARES THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `D' pow 2 <= (&1 + dl) * D pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt(&1 + dl) * D) pow 2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `&0 <= &1 + dl` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `D' pow 2 * Rn' <= ((&1 + dl) * D pow 2) * (Rn + a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `dl * (D pow 2 * a) <= D pow 2 * a` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `dl * x <= &1 * x ==> dl * x <= x`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
    ALL_TAC] THEN
  UNDISCH_TAC `D' pow 2 * Rn' <= ((&1 + dl) * D pow 2) * (Rn + a)` THEN
  UNDISCH_TAC `dl * (D pow 2 * a) <= D pow 2 * a` THEN
  UNDISCH_TAC `D pow 2 * (dl * Rn + &2 * a) < C pow 2 - D pow 2 * Rn` THEN
  REAL_ARITH_TAC);;

let P2B9S_DIAM_LOWER = prove
 (`!C D Rm Rm' D' dl a.
     &0 < C /\ &0 <= D /\ &0 <= dl /\ dl < &1 /\ &0 <= a /\ &0 < Rm - a /\
     sqrt(&1 - dl) * D <= D' /\ Rm - a <= Rm' /\
     C pow 2 * D pow 2 * (a + dl * Rm) < C pow 2 * Rm * D pow 2 - &1
     ==> inv C * inv(sqrt Rm') < D'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Rm'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt Rm'` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - dl` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D'` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 - dl) * D` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C * sqrt Rm'` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN
  MP_TAC(SPECL [`&1`; `D':real`; `C * sqrt Rm'`] REAL_LT_LDIV_EQ) THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2B9S_LT_FROM_SQUARES THEN REWRITE_TAC[REAL_POS] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_ONE] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `(&1 - dl) * D pow 2 <= D' pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt(&1 - dl) * D) pow 2` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 - dl) * D pow 2) * (Rm - a) <= D' pow 2 * Rm'` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C pow 2 * (((&1 - dl) * D pow 2) * (Rm - a)) <= C pow 2 * (D' pow 2 * Rm')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C pow 2 * D pow 2 * dl * a` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
  UNDISCH_TAC `C pow 2 * (((&1 - dl) * D pow 2) * (Rm - a)) <= C pow 2 * (D' pow 2 * Rm')` THEN
  UNDISCH_TAC `&0 <= C pow 2 * D pow 2 * dl * a` THEN
  UNDISCH_TAC `C pow 2 * D pow 2 * (a + dl * Rm) < C pow 2 * Rm * D pow 2 - &1` THEN
  REAL_ARITH_TAC);;

let P2B9S_GRAD2_POS = prove
 (`!top atlas (g:A->real^N^N) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ y IN topspace top
     ==> &0 <= rfs_scalar_grad2 atlas g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_scalar_grad2] THEN MATCH_MP_TAC LGRAD2_POS THEN
  EXISTS_TAC `IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                    (FST (chart_at atlas y))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
  REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2B9S_CCOMP_TARGET_POINT = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    R0 K0 alpha eta d2 delta y.
     (!s (G0:real^3->real^3^3) G y.
         metric_field s G0 /\ metric_field s G /\ y IN s /\
         lrm_deriv_norm2 0 G0 y <= K0 /\ lrm_deriv_norm2 1 G0 y <= K0 /\
         lrm_deriv_norm2 2 G0 y <= K0 /\ lck_dist2 4 G0 G y < eta pow 2
         ==> abs(lscalar G y - lscalar G0 y) <= alpha /\
             (!u v. ~collinear {vec 0,u,v}
                    ==> abs(lsectional G y u v - lsectional G0 y u v) <= alpha) /\
             abs(lgrad2 G (lscalar G) y - lgrad2 G0 (lscalar G0) y) <= alpha /\
             abs(llap G (lscalar G) y - llap G0 (lscalar G0) y) <= alpha /\
             abs(ltnorm2 2 G (lric2 G) y - ltnorm2 2 G0 (lric2 G0) y) <= alpha) /\
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U /\ &0 < R0 /\
     rfa_rmd2 0 atlas (\z. R0 %% g z) y <= K0 /\ rfa_rmd2 1 atlas (\z. R0 %% g z) y <= K0 /\
     rfa_rmd2 2 atlas (\z. R0 %% g z) y <= K0 /\
     lck_dist2 (rfs_kreg delta) (metric_local atlas (chart_at atlas y) (\z. R0 %% g z))
                (metric_local atlas (chart_at atlas y)
                   (\z. R0 %% mfd_pullback_metric atlas atlas' psi g' z))
                (SND(chart_at atlas y) y) <= d2 /\
     d2 < delta pow 2 /\ &0 < delta /\ delta <= eta /\ delta <= &1 / &4
     ==> abs(mfd_scalar atlas' g' (psi y) - mfd_scalar atlas g y) <= alpha * R0 /\
         (!u v. ~collinear {vec 0,u,v}
                ==> abs(mfd_sectional atlas (mfd_pullback_metric atlas atlas' psi g') y u v -
                        mfd_sectional atlas g y u v) <= alpha * R0) /\
         abs(rfs_scalar_grad2 atlas' g' (psi y) - rfs_scalar_grad2 atlas g y) <=
         alpha * R0 pow 3 /\
         abs(rfs_scalar_lap atlas' g' (psi y) - rfs_scalar_lap atlas g y) <= alpha * R0 pow 2 /\
         abs(rfs_ric_norm2 atlas' g' (psi y) - rfs_ric_norm2 atlas g y) <= alpha * R0 pow 2 /\
         (!v. v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
              (&1 + delta) * (v dot (g y ** v))) /\
         (!v. (&1 - delta) * (v dot (g y ** v)) <=
              v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sqrt d2 <= delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `R0:real`;
                 `rfs_kreg delta`; `d2:real`; `y:A`] P2B9S_PB_QF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^3. abs(v dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** v) -
                        v dot ((g:A->real^3^3) y ** v)) <= delta * (v dot (g y ** v))`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt d2 * ((v:real^3) dot ((g:A->real^3^3) y ** v))` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y:A`] P2B9S_PB_FIELDS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    ASM_CASES_TAC `v:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `y:A`] RIEMANNIAN_METRIC_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!v:real^3. v dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** v) <=
         (&1 + delta) * (v dot ((g:A->real^3^3) y ** v))) /\
    (!v:real^3. (&1 - delta) * (v dot ((g:A->real^3^3) y ** v)) <=
         v dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** v))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN X_GEN_TAC `v:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> try fst(dest_var t) = "delta" with Failure _ -> false)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 4 (metric_local atlas (chart_at atlas (y:A)) (\z. R0 %% (g:A->real^3^3) z))
                (metric_local atlas (chart_at atlas y)
                   (\z. R0 %% mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) z))
                (SND(chart_at atlas y) y) < eta pow 2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y:A`] P2B9S_PB_FIELDS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg delta)
                  (metric_local atlas (chart_at atlas (y:A)) (\z. R0 %% (g:A->real^3^3) z))
                  (metric_local atlas (chart_at atlas y)
                     (\z. R0 %% mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) z))
                  (SND(chart_at atlas y) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_SIMP_TAC[P2C_KREG_FOUR; METRIC_LOCAL_CMUL] THEN
      CONJ_TAC THEN MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d2:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `delta pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `R0:real`; `K0:real`;
                 `alpha:real`; `eta:real`; `y:A`] P2B9S_POINT_STAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "D" ACCEPT_TAC; SIMP_TAC[]]);;

let P2B9S_CCOMP_DIST = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) U psi psi' delta a b.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
     U IN connected_components_of top /\ IMAGE psi U IN connected_components_of top' /\
     &0 <= delta /\ delta < &1 /\
     (!y v. y IN U ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                       (&1 + delta) * (v dot (g y ** v))) /\
     (!y v. y IN U ==> (&1 - delta) * (v dot (g y ** v)) <=
                       v dot (mfd_pullback_metric atlas atlas' psi g' y ** v)) /\
     a IN U /\ b IN U
     ==> mfd_dist (top',atlas') g' (psi a) (psi b) <=
         sqrt(&1 + delta) * mfd_dist (top,atlas) g a b /\
         sqrt(&1 - delta) * mfd_dist (top,atlas) g a b <=
         mfd_dist (top',atlas') g' (psi a) (psi b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(psi:A->B) a IN IMAGE psi U /\ (psi:A->B) b IN IMAGE psi U` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `U:A->bool`; `a:A`; `b:A`] P2B9S_DIST_COMPONENT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `IMAGE (psi:A->B) U`; `(psi:A->B) a`; `(psi:A->B) b`] P2B9S_DIST_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `a:A`; `b:A`] P2B9S_JOINABLE_IN_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`; `U:A->bool`;
                 `&1 + delta`; `a:A`; `b:A`] P2B9S_DIST_IN_PB_LE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`; `U:A->bool`;
                 `inv(&1 - delta)`; `a:A`; `b:A`] P2B9S_DIST_IN_PB_GE) THEN
  SUBGOAL_THEN `&0 < &1 - delta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET_REFL; REAL_LT_INV_EQ] THEN
    MAP_EVERY X_GEN_TAC [`z:A`; `v:real^N`] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 - delta) *
              (sqrt(inv(&1 - delta)) *
               mfd_dist_in (top',atlas') (g':B->real^N^N) (IMAGE (psi:A->B) U) (psi a) (psi b))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    REWRITE_TAC[REAL_MUL_ASSOC; GSYM SQRT_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; SQRT_1; REAL_MUL_LID; REAL_LE_REFL]]);;

let P2B9S_RANGE_TRANSFER = prove
 (`!(f:A->real) (f':B->real) (psi:A->B) U Rn Rm e y0 y1.
     y0 IN U /\ y1 IN U /\ (!y. y IN U ==> Rn <= f y /\ f y <= Rm) /\ f y0 = Rn /\ f y1 = Rm /\
     (!y. y IN U ==> abs(f'(psi y) - f y) <= e)
     ==> sup(IMAGE f' (IMAGE psi U)) <= Rm + e /\ Rm - e <= sup(IMAGE f' (IMAGE psi U)) /\
         Rn - e <= inf(IMAGE f' (IMAGE psi U)) /\ inf(IMAGE f' (IMAGE psi U)) <= Rn + e /\
         (!z. z IN IMAGE psi U ==> Rn - e <= f' z /\ f' z <= Rm + e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN U ==> Rn - e <= (f':B->real) ((psi:A->B) y) /\ f' (psi y) <= Rm + e`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (is_forall o concl))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN IMAGE (psi:A->B) U ==> Rn - e <= (f':B->real) z /\ f' z <= Rm + e`
  ASSUME_TAC THENL [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(IMAGE (f':B->real) (IMAGE (psi:A->B) U) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((f':B->real)((psi:A->B) y0) - Rn) <= e /\ abs(f'(psi y1) - Rm) <= e`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
       can (find_term ((=) `f':B->real`)) (concl th) &&
       can (find_term ((=) `e:real`)) (concl th) && not(can (find_term ((=) `Rn:real`)) (concl th))
     then MP_TAC(SPEC `y0:A` th) THEN MP_TAC(SPEC `y1:A` th) else failwith "no") THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SUP_LE THEN ASM_SIMP_TAC[FORALL_IN_IMAGE];
    MATCH_MP_TAC REAL_LE_SUP THEN MAP_EVERY EXISTS_TAC
     [`Rm + e`; `(f':B->real)((psi:A->B) y1)`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; FORALL_IN_IMAGE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INF THEN ASM_SIMP_TAC[FORALL_IN_IMAGE];
    MATCH_MP_TAC REAL_INF_LE THEN MAP_EVERY EXISTS_TAC
     [`Rn - e`; `(f':B->real)((psi:A->B) y0)`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; FORALL_IN_IMAGE] THEN ASM_REAL_ARITH_TAC]);;

let P2B9S_DIST_SUP_TRANSFER = prove
 (`!(d:A->A->real) (d':B->B->real) (psi:A->B) U D c1 c2.
     ~(U = {}) /\ (!a b. a IN U /\ b IN U ==> d a b <= D) /\
     sup {d a b | a IN U /\ b IN U} = D /\ &0 <= c1 /\ &0 < c2 /\
     (!a b. a IN U /\ b IN U ==> d' (psi a) (psi b) <= c1 * d a b /\
                                 c2 * d a b <= d' (psi a) (psi b))
     ==> sup {d' a' b' | a' IN IMAGE psi U /\ b' IN IMAGE psi U} <= c1 * D /\
         c2 * D <= sup {d' a' b' | a' IN IMAGE psi U /\ b' IN IMAGE psi U}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b. a IN U /\ b IN U ==> (d':B->B->real) ((psi:A->B) a) (psi b) <= c1 * D`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c1 * (d:A->A->real) a b` THEN ASM_SIMP_TAC[REAL_LE_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~({(d':B->B->real) a' b' | a' IN IMAGE (psi:A->B) U /\ b' IN IMAGE psi U} = {}) /\
                (!x. x IN {(d':B->B->real) a' b' | a' IN IMAGE (psi:A->B) U /\ b' IN IMAGE psi U}
                     ==> x <= c1 * D)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(U:A->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `a0:A`) THEN
      MAP_EVERY EXISTS_TAC [`(d':B->B->real) ((psi:A->B) a0) (psi a0)`;
                            `(psi:A->B) a0`; `(psi:A->B) a0`] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE];
      GEN_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`a':B`; `b':B`] THEN
      REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `D:real`)) THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    UNDISCH_TAC `~(U:A->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `a0:A`) THEN
    MAP_EVERY EXISTS_TAC [`(d:A->A->real) a0 a0`; `a0:A`; `a0:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `a:A`; `b:A`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(d':B->B->real) ((psi:A->B) a) (psi b)` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_SUP THEN
  MAP_EVERY EXISTS_TAC [`c1 * D`; `(d':B->B->real) ((psi:A->B) a) (psi b)`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`(psi:A->B) a`; `(psi:A->B) b`] THEN ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let P2B9S_LIN_SMALL = prove
 (`!b c. &0 < b /\ &0 < c ==> &0 < b / c /\ !x. x <= b / c ==> x * c <= b`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV];
    UNDISCH_TAC `x <= b / c` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ]]);;

let P2B9S_CCOMP_PARAMS = prove
 (`!m R0 Rn Rm C D d6 d9 d10.
     &0 < m /\ &0 < R0 /\ &0 < Rn /\ Rn <= Rm /\ m * R0 = Rn /\ &1 < C /\ &0 <= D /\
     inv C * Rm < d6 /\ &0 <= d9 /\ d9 < C /\ &0 <= d10 /\ d10 < C /\
     D pow 2 * Rn < C pow 2 /\ &1 < C pow 2 * Rm * D pow 2
     ==> ?alpha dl0. &0 < alpha /\ &0 < dl0 /\ &3 * alpha <= m /\
           alpha * (&1 + &3 * ((d9 + C) / &2) pow 2 * m pow 2) <=
           (((d9 + C) / &2) pow 2 - d9 pow 2) * m pow 3 /\
           alpha * (&3 + &2 * ((d10 + C) / &2) * m) <= ((d10 + C) / &2 - d10) * m pow 2 /\
           inv C * (Rm + alpha * R0) < d6 - alpha * R0 /\
           (!dl. &0 <= dl /\ dl <= dl0
                 ==> D pow 2 * (dl * Rn + &2 * (alpha * R0)) < C pow 2 - D pow 2 * Rn /\
                     C pow 2 * D pow 2 * (alpha * R0 + dl * Rm) < C pow 2 * Rm * D pow 2 - &1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `E9 = (d9 + C) / &2` THEN ABBREV_TAC `E10 = (d10 + C) / &2` THEN
  SUBGOAL_THEN `d9 < E9 /\ d10 < E10` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E9"; "E10"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < E9 pow 2 - d9 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(2 = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E9 /\ &0 <= E10 /\ &0 < inv C /\ &0 < C` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_INV) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `A8 = C pow 2 - D pow 2 * Rn` THEN
  ABBREV_TAC `A7 = C pow 2 * Rm * D pow 2 - &1` THEN
  SUBGOAL_THEN `&0 < A8 /\ &0 < A7 /\ &0 < d6 - inv C * Rm` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A8"; "A7"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D pow 2 /\ &0 <= C pow 2 * D pow 2` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[REAL_LE_POW_2; REAL_LE_MUL]; ALL_TAC] THEN
  (* the six bounds for alpha *)
  MP_TAC(SPECL [`(E9 pow 2 - d9 pow 2) * m pow 3`; `&1 + &3 * E9 pow 2 * m pow 2`]
               P2B9S_LIN_SMALL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_POS];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`(E10 - d10) * m pow 2`; `&3 + &2 * E10 * m`] P2B9S_LIN_SMALL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_SUB_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &3 + x`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`(d6 - inv C * Rm) / &2`; `R0 * (&1 + inv C)`] P2B9S_LIN_SMALL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(SPECL [`A8 / &3`; `&2 * D pow 2 * R0 + R0`] P2B9S_LIN_SMALL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 < y ==> &0 < x + y`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POS];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`A7 / &3`; `C pow 2 * D pow 2 * R0 + R0`] P2B9S_LIN_SMALL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 < y ==> &0 < x + y`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2];
    STRIP_TAC] THEN
  ABBREV_TAC `alpha = min (m / &3)
                     (min (((E9 pow 2 - d9 pow 2) * m pow 3) / (&1 + &3 * E9 pow 2 * m pow 2))
                     (min (((E10 - d10) * m pow 2) / (&3 + &2 * E10 * m))
                     (min (((d6 - inv C * Rm) / &2) / (R0 * (&1 + inv C)))
                     (min ((A8 / &3) / (&2 * D pow 2 * R0 + R0))
                          ((A7 / &3) / (C pow 2 * D pow 2 * R0 + R0))))))` THEN
  SUBGOAL_THEN
   `&0 < alpha /\ alpha <= m / &3 /\
    alpha <= ((E9 pow 2 - d9 pow 2) * m pow 3) / (&1 + &3 * E9 pow 2 * m pow 2) /\
    alpha <= ((E10 - d10) * m pow 2) / (&3 + &2 * E10 * m) /\
    alpha <= ((d6 - inv C * Rm) / &2) / (R0 * (&1 + inv C)) /\
    alpha <= (A8 / &3) / (&2 * D pow 2 * R0 + R0) /\
    alpha <= (A7 / &3) / (C pow 2 * D pow 2 * R0 + R0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "alpha" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `alpha:real` THEN
  EXISTS_TAC `min ((A8 / &3) / (D pow 2 * Rn + &1))
                  ((A7 / &3) / (C pow 2 * D pow 2 * Rm + &1))` THEN
  SUBGOAL_THEN `&0 < D pow 2 * Rn + &1 /\ &0 < C pow 2 * D pow 2 * Rm + &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= Rm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  SUBGOAL_THEN `&0 < A8 / &3 /\ &0 < A7 / &3` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  SUBGOAL_THEN `&0 <= alpha * R0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `alpha * (R0 * (&1 + inv C)) <= (d6 - inv C * Rm) / &2` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `dl:real` THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
    SUBGOAL_THEN `dl * (D pow 2 * Rn + &1) <= A8 / &3 /\
                  dl * (C pow 2 * D pow 2 * Rm + &1) <= A7 / &3` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `dl <= (A8 / &3) / (D pow 2 * Rn + &1)`;
        UNDISCH_TAC `dl <= (A7 / &3) / (C pow 2 * D pow 2 * Rm + &1)`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `alpha * (&2 * D pow 2 * R0 + R0) <= A8 / &3 /\
                  alpha * (C pow 2 * D pow 2 * R0 + R0) <= A7 / &3` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN ASM_REAL_ARITH_TAC]);;

let P2B9S_CCOMP_SOURCE = prove
 (`!C top atlas (g:A->real^3^3) x U.
     &1 < C /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     rfs_c_component (top,atlas) g C U /\ x IN U
     ==> ?Rn Rm D d6 d9 d10 K0 y0 y1.
           &0 < Rn /\ Rn <= mfd_scalar atlas g x /\ mfd_scalar atlas g x <= Rm /\
           y0 IN U /\ y1 IN U /\ mfd_scalar atlas g y0 = Rn /\ mfd_scalar atlas g y1 = Rm /\
           (!y. y IN U ==> Rn <= mfd_scalar atlas g y /\ mfd_scalar atlas g y <= Rm) /\
           inf(IMAGE (mfd_scalar atlas g) U) = Rn /\ sup(IMAGE (mfd_scalar atlas g) U) = Rm /\
           &0 <= D /\
           (!a b. a IN U /\ b IN U ==> &0 <= mfd_dist (top,atlas) g a b /\
                                       mfd_dist (top,atlas) g a b <= D) /\
           sup {mfd_dist (top,atlas) g a b | a IN U /\ b IN U} = D /\
           D pow 2 * Rn < C pow 2 /\ &1 < C pow 2 * Rm * D pow 2 /\
           inv C * Rm < d6 /\
           (!y u v. y IN U /\ ~collinear {vec 0,u,v} ==> d6 <= mfd_sectional atlas g y u v) /\
           &0 <= d9 /\ d9 < C /\
           (!y. y IN U ==> sqrt(rfs_scalar_grad2 atlas g y) /
                           (mfd_scalar atlas g y * sqrt(mfd_scalar atlas g y)) <= d9) /\
           &0 <= d10 /\ d10 < C /\
           (!y. y IN U ==> abs(rfs_scalar_lap atlas g y + &2 * rfs_ric_norm2 atlas g y) /
                           mfd_scalar atlas g y pow 2 <= d10) /\
           (!y. y IN U
                ==> rfa_rmd2 0 atlas (\z. mfd_scalar atlas g x %% g z) y <= K0 /\
                    rfa_rmd2 1 atlas (\z. mfd_scalar atlas g x %% g z) y <= K0 /\
                    rfa_rmd2 2 atlas (\z. mfd_scalar atlas g x %% g z) y <= K0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
  REWRITE_TAC[rfs_c_component; rfs_inf_gt; rfs_sup_lt] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d6:real` STRIP_ASSUME_TAC o check (fun th ->
    is_exists(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional")) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d9:real` STRIP_ASSUME_TAC o check (fun th ->
    is_exists(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_grad2")) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d10:real` STRIP_ASSUME_TAC o check (fun th ->
    is_exists(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_lap")) (concl th))) THEN
  SUBGOAL_THEN `~(U:A->bool = {}) /\ U SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF; CONNECTED_COMPONENTS_OF_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN U ==> &0 < mfd_scalar atlas (g:A->real^3^3) y` ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`] P2B_MFD_SCALAR_POS) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U:A->bool`] P2B9S_COMPACT_SCALAR_RANGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:A` (X_CHOOSE_THEN `y1:A` STRIP_ASSUME_TAC)) THEN
  (* distances *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U:A->bool`] P2B9S_DIST_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  ABBREV_TAC `D = sup {mfd_dist (top,atlas) (g:A->real^3^3) a b | a IN U /\ b IN U}` THEN
  SUBGOAL_THEN `!a b:A. a IN U /\ b IN U
                       ==> &0 <= mfd_dist (top,atlas) (g:A->real^3^3) a b /\
                           mfd_dist (top,atlas) g a b <= D` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                     `a:A`; `b:A`] P2B9S_JOINABLE_IN_COMPONENT) THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_SUP THEN
      MAP_EVERY EXISTS_TAC [`B:real`; `mfd_dist (top,atlas) (g:A->real^3^3) a b`] THEN
      REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
        STRIP_TAC THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  (* curvature derivative bounds *)
  SUBGOAL_THEN `?K0. !y. y IN U
                   ==> rfa_rmd2 0 atlas (\z. mfd_scalar atlas (g:A->real^3^3) x %% g z) y <= K0 /\
                       rfa_rmd2 1 atlas (\z. mfd_scalar atlas g x %% g z) y <= K0 /\
                       rfa_rmd2 2 atlas (\z. mfd_scalar atlas g x %% g z) y <= K0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `riemannian_metric atlas (\z. mfd_scalar atlas (g:A->real^3^3) x %% g z)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MAP_EVERY (fun l -> MP_TAC(ISPECL [l; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`;
                 `\z. mfd_scalar atlas (g:A->real^3^3) x %% g z`; `U:A->bool`]
                P2B9S_RMD2_COMPACT_BOUND)) [`2`; `1`; `0`] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `B0:real`) THEN DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `B2:real`) THEN
    EXISTS_TAC `max B0 (max B1 B2)` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_LE_MAX] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`mfd_scalar atlas (g:A->real^3^3) y0`;
                        `mfd_scalar atlas (g:A->real^3^3) y1`; `D:real`;
                        `d6:real`; `d9:real`; `d10:real`; `K0:real`; `y0:A`; `y1:A`] THEN
  ASM_SIMP_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM; LEFT_IMP_EXISTS_THM]) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y0 /\ &0 < mfd_scalar atlas g y1`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `D * sqrt(mfd_scalar atlas (g:A->real^3^3) y0) < C` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_lt" (concl th) &&
        can (find_term ((=) `D:real`)) (lhand(concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "inf")) (concl th))) THEN
      ASM_REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; SQRT_POS_LT];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `C pow 2` THEN REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `(D * sqrt(mfd_scalar atlas (g:A->real^3^3) y0)) pow 2 < C pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_RULE `~(2 = 0)`] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE]];
    SUBGOAL_THEN `&1 < C * sqrt(mfd_scalar atlas (g:A->real^3^3) y1) * D` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_lt" (concl th) &&
        can (find_term ((=) `D:real`)) (rand(concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "sup")) (concl th))) THEN
      ASM_REWRITE_TAC[GSYM REAL_INV_MUL] THEN
      SUBGOAL_THEN `&0 < C * sqrt(mfd_scalar atlas (g:A->real^3^3) y1)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT]; ALL_TAC] THEN
      MP_TAC(SPECL [`&1`; `D:real`; `C * sqrt(mfd_scalar atlas (g:A->real^3^3) y1)`]
                   REAL_LT_LDIV_EQ) THEN
      ASM_REWRITE_TAC[real_div; REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 pow 2 < (C * sqrt(mfd_scalar atlas (g:A->real^3^3) y1) * D) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_RULE `~(2 = 0)`; REAL_POS];
      ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE; REAL_POW_ONE] THEN
      REAL_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_lt" (concl th) &&
      rand(concl th) = `d6:real`)) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y:A`; `u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(rfs_scalar_grad2 atlas (g:A->real^3^3) x) /
                (mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC P2B9S_GRAD2_POS THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(rfs_scalar_lap atlas (g:A->real^3^3) x + &2 * rfs_ric_norm2 atlas g x) /
                mfd_scalar atlas g x pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS; REAL_LE_POW_2];
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN
    ASM_REWRITE_TAC[]]);;

let P2B9S_OPEN_CCOMP = prove
 (`P2B_REQ_LRG_DERIV_STATEMENT
   ==> !C top atlas (g:A->real^3^3) x U.
         &1 < C /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
         rfs_c_component (top,atlas) g C U /\ x IN U
         ==> ?delta. &0 < delta /\
               !top' atlas' (g':B->real^3^3) psi psi'.
                  smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
                  mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
                  IMAGE psi U IN connected_components_of top' /\
                  rfs_mclose (rfs_kreg delta) delta atlas U
                    (\y. mfd_scalar atlas g x %% g y)
                    (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                  ==> rfs_c_component (top',atlas') g' C (IMAGE psi U)`,
  DISCH_THEN(LABEL_TAC "LRGD" o MATCH_MP P2B9S_LRG_D) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `U:A->bool`] P2B9S_CCOMP_SOURCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Rn:real` (X_CHOOSE_THEN `Rm:real` (X_CHOOSE_THEN `D:real`
    (X_CHOOSE_THEN `d6:real` (X_CHOOSE_THEN `d9:real` (X_CHOOSE_THEN `d10:real`
      (X_CHOOSE_THEN `K0:real` (X_CHOOSE_THEN `y0:A` (X_CHOOSE_THEN `y1:A`
        STRIP_ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `U IN connected_components_of (top:A topology) /\ compact_in top U /\
                (mfd_diffeomorphic (subtopology top U)
                   (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U)
                   (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas \/
                 rfs_has_twisted (subtopology top U) (restrict_atlas atlas U))`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "type"))) THENL
   [UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
    REWRITE_TAC[rfs_c_component] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = Rn / R0` THEN
  SUBGOAL_THEN `&0 < m /\ m * R0 = Rn` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:real`; `R0:real`; `Rn:real`; `Rm:real`; `C:real`; `D:real`;
                `d6:real`; `d9:real`; `d10:real`] P2B9S_CCOMP_PARAMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `alpha:real` (X_CHOOSE_THEN `dl0:real` STRIP_ASSUME_TAC)) THEN
  USE_THEN "LRGD" (fun th -> MP_TAC(MATCH_MP (SPECL [`K0:real`; `alpha:real`] th)
                                            (ASSUME `&0 < alpha`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Dform"))) THEN
  EXISTS_TAC `min (&1 / &4) (min eta dl0)` THEN
  ABBREV_TAC `delta = min (&1 / &4) (min eta dl0)` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= &1 / &4 /\ delta <= eta /\ delta <= dl0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                       `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `rfs_mclose (rfs_kreg delta) delta atlas U (\y. R0 %% (g:A->real^3^3) y)
                 (\y. R0 %% mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y)` THEN
  REWRITE_TAC[rfs_mclose] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> abs(mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y) -
                mfd_scalar atlas (g:A->real^3^3) y) <= alpha * R0 /\
            (!u v. ~collinear {vec 0,u,v}
                   ==> abs(mfd_sectional atlas (mfd_pullback_metric atlas atlas' psi g') y u v -
                           mfd_sectional atlas g y u v) <= alpha * R0) /\
            abs(rfs_scalar_grad2 atlas' g' (psi y) - rfs_scalar_grad2 atlas g y) <=
            alpha * R0 pow 3 /\
            abs(rfs_scalar_lap atlas' g' (psi y) - rfs_scalar_lap atlas g y) <= alpha * R0 pow 2 /\
            abs(rfs_ric_norm2 atlas' g' (psi y) - rfs_ric_norm2 atlas g y) <= alpha * R0 pow 2 /\
            (!v. v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                 (&1 + delta) * (v dot (g y ** v))) /\
            (!v. (&1 - delta) * (v dot (g y ** v)) <=
                 v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2B9S_CCOMP_TARGET_POINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`;
                          `IMAGE (psi:A->B) U`; `psi':B->A`; `K0:real`; `eta:real`; `d2:real`] THEN
    ASM_SIMP_TAC[] THEN USE_THEN "Dform" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `alpha * R0 <= Rn / &3 /\ &0 <= alpha * R0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `m * R0 = Rn` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `&3 * alpha <= m` THEN UNDISCH_TAC `&0 < R0` THEN
      SPEC_TAC(`R0:real`,`r:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&3 * (alpha * r) <= m * r ==> alpha * r <= (m * r) / &3`) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3)`; `mfd_scalar atlas' (g':B->real^3^3)`;
                 `psi:A->B`; `U:A->bool`; `Rn:real`; `Rm:real`; `alpha * R0`;
                 `y0:A`; `y1:A`] P2B9S_RANGE_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "PT" (MP_TAC o SPEC `y:A`) THEN
    ASM_SIMP_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN U /\ b IN U
          ==> mfd_dist (top',atlas') (g':B->real^3^3) ((psi:A->B) a) (psi b) <=
              sqrt(&1 + delta) * mfd_dist (top,atlas) (g:A->real^3^3) a b /\
              sqrt(&1 - delta) * mfd_dist (top,atlas) g a b <=
              mfd_dist (top',atlas') g' (psi a) (psi b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2B9S_CCOMP_DIST THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `psi':B->A`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "PT" (MP_TAC o SPEC `y:A`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_dist (top,atlas) (g:A->real^3^3)`;
                 `mfd_dist (top',atlas') (g':B->real^3^3)`; `psi:A->B`; `U:A->bool`; `D:real`;
                 `sqrt(&1 + delta)`; `sqrt(&1 - delta)`] P2B9S_DIST_SUP_TRANSFER) THEN
  SUBGOAL_THEN `~(U:A->bool = {}) /\ &0 <= &1 + delta /\ &0 < &1 - delta`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    CONJ_TAC THENL [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POS_LT];
    STRIP_TAC] THEN
  SUBGOAL_THEN `!y u v. y IN U /\ ~collinear {vec 0,u,v}
                       ==> d6 - alpha * R0 <=
                           mfd_sectional atlas' (g':B->real^3^3) ((psi:A->B) y) u v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`;
                   `g':B->real^3^3`; `y:A`] P2B9S_PB_SECTIONAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "PT" (fun th -> MP_TAC(SPECL [`u1:real^3`; `v1:real^3`]
      (CONJUNCT1(CONJUNCT2(MATCH_MP th (ASSUME `(y:A) IN U`)))))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `u1:real^3`; `v1:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d6:real`)) (concl th) &&
      not(can (find_term ((=) `alpha:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv C /\ &0 < C /\ &0 < Rm` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d6 - alpha * R0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv C * (Rm + alpha * R0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_c_component; rfs_inf_gt; rfs_sup_lt] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology top (U:A->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o MATCH_MP MFD_DIFFEO_MAPS);
    MATCH_MP_TAC P2B9S_CCOMP_TYPE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `U:A->bool`; `psi:A->B`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "type" ACCEPT_TAC;
    REWRITE_TAC[IN_IMAGE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `d6 - alpha * R0` THEN ASM_SIMP_TAC[];
    EXISTS_TAC `d6 - alpha * R0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv C * (Rm + alpha * R0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC P2B9S_DIAM_LOWER THEN
    MAP_EVERY EXISTS_TAC [`D:real`; `Rm:real`; `delta:real`; `alpha * R0`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2B9S_DIAM_UPPER THEN
    MAP_EVERY EXISTS_TAC [`D:real`; `Rn:real`; `delta:real`; `alpha * R0`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 <= sqrt(&1 - delta) * D` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 - delta) * D` THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    EXISTS_TAC `(d9 + C) / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
    X_GEN_TAC `w:real` THEN X_GEN_TAC `z:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) SUBST1_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    SUBGOAL_THEN `(y:A) IN topspace top /\ (psi:A->B) y IN topspace top'`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
      CONJ_TAC THENL
       [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`));
        MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (IMAGE (psi:A->B) U)`))] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y /\ m * R0 <= mfd_scalar atlas g y`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Rm:real`)) (concl th) &&
        not(can (find_term ((=) `alpha:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) y`;
                  `rfs_scalar_grad2 atlas (g:A->real^3^3) y`; `d9:real`]
                 P2B9S_GRAD_RATIO_IMP) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC P2B9S_GRAD2_POS THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(SPECL [`m:real`; `R0:real`; `d9:real`; `(d9 + C) / &2`;
                  `mfd_scalar atlas (g:A->real^3^3) y`;
                  `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y)`;
                  `rfs_scalar_grad2 atlas (g:A->real^3^3) y`;
                  `rfs_scalar_grad2 atlas' (g':B->real^3^3) ((psi:A->B) y)`; `alpha:real`]
                 P2B9S_MARGIN_GRAD_POLY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MATCH_MP_TAC P2B9S_GRAD_RATIO_BACK THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2B9S_GRAD2_POS THEN EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    EXISTS_TAC `(d10 + C) / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
    X_GEN_TAC `w:real` THEN X_GEN_TAC `z:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) SUBST1_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y /\ m * R0 <= mfd_scalar atlas g y`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Rm:real`)) (concl th) &&
        not(can (find_term ((=) `alpha:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) y`;
                  `rfs_scalar_lap atlas (g:A->real^3^3) y + &2 * rfs_ric_norm2 atlas g y`;
                  `d10:real`] P2B9S_LAP_RATIO_IMP) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`m:real`; `R0:real`; `d10:real`; `(d10 + C) / &2`;
                  `mfd_scalar atlas (g:A->real^3^3) y`;
                  `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y)`;
                  `rfs_scalar_lap atlas (g:A->real^3^3) y + &2 * rfs_ric_norm2 atlas g y`;
                  `rfs_scalar_lap atlas' (g':B->real^3^3) ((psi:A->B) y) +
                   &2 * rfs_ric_norm2 atlas' g' (psi y)`; `alpha:real`]
                 P2B9S_MARGIN_LAP_POLY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MATCH_MP_TAC P2B9S_LAP_RATIO_BACK THEN ASM_REWRITE_TAC[]]);;

let P2B9S_LRG_D_U = MP P2B9S_LRG_D P2B_REQ_LRG_DERIV;;

let P2B9S_OPEN_CCOMP_U = MP P2B9S_OPEN_CCOMP P2B_REQ_LRG_DERIV;;

