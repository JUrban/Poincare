(* ========================================================================= *)
(* Unit pc_p2a_lgeo2: view level of the L-geodesic equation, generic in N.   *)
(* Region charts: the local metric of a region chart at time s is the        *)
(* pullback of the slice metric at s by the transition to any slice chart    *)
(* (P2A_RLOCAL_SLICE); the transitions between region charts of two regions  *)
(* with a common time are diffeomorphisms (P2A_REGION_CHART_DIFFEO) that     *)
(* carry one region-chart metric to the other (P2A_RLOCAL_TRANS).            *)
(*                                                                           *)
(* First: the local form of MFD_PULLBACK_METRIC_LOCAL.                       *)
(* ========================================================================= *)

needs "src/pc_p2a_lgeo1.ml";;

prioritize_real();;
type_invention_error := true;;

(* The local metric of a pullback metric under a diffeomorphism between    *)
(* open subsets W, W' (adapted from the proof of MFD_PULLBACK_METRIC_LOCAL  *)
(* of pc_mfd_restrict, which assumes W, W' are the whole spaces).           *)

let P2A_PULLBACK_METRIC_LOCAL_W = prove
 (`!top atlas W top' atlas' W' (f:A->B) f' (g':B->real^N^N) (U:A->bool)
    (phi:A->real^N) (V:B->bool) (psi:B->real^N) x.
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
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (W':B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
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
           [MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN EXISTS_TAC `top':B topology` THEN
            ASM_SIMP_TAC[OPEN_IN_INTER] THEN
            MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
            EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
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

(* ========================================================================= *)
(* Region slices, region charts and their transitions.                       *)
(* ========================================================================= *)

let P2A_REGION_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b s.
     p2a_region V W a b /\ a < s /\ s <= b
     ==> smooth_manifold_atlas (p2a_vtop V s) (p2a_vatlas V s) /\
         open_in (p2a_vtop V s) W /\
         smooth_manifold_atlas (p2a_vtop V b) (p2a_vatlas V b) /\
         open_in (p2a_vtop V b) W /\
         mfd_diffeo (p2a_vtop V b) (p2a_vatlas V b) W
                    (p2a_vtop V s) (p2a_vatlas V s) W (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_region; P2A_PERSISTS_ALT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_SIMP_TAC[]);;

let P2A_MPULLBACK_LOCAL = prove
 (`!(h1:real^N->real^N) h2 G s z.
     open s /\ z IN s /\ (!y. y IN s ==> h1 y = h2 y)
     ==> mpullback h1 G z = mpullback h2 G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (h1:real^N->real^N) (at z) =
                frechet_derivative h2 (at z)` SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let P2A_RLOCAL_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b (U:A->bool) (phi:A->real^N) s (c':(A->bool)#(A->real^N)) x.
     p2a_region V W a b /\ (U,phi) IN p2a_vatlas V b /\ a < s /\ s <= b /\
     c' IN p2a_vatlas V s /\ x IN U /\ x IN W /\ x IN FST c'
     ==> p2a_rlocal V W b (U INTER W,phi) s (phi x) =
         mpullback (chart_trans (U INTER W,phi) c')
                   (metric_local (p2a_vatlas V s) c' (p2a_vmetric V s)) (phi x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!(h:real^N->real^N) G.
      (!z. z IN U INTER W ==> h((phi:A->real^N) z) = SND(c':(A->bool)#(A->real^N)) z)
      ==> mpullback h G (phi x) = mpullback (chart_trans (U INTER W,phi) c') G (phi x)`
  (LABEL_TAC "loc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b` THEN
      EXISTS_TAC `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[chart_trans] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `z:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_rlocal; p2a_rmetric] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b`;
                 `U:A->bool`; `phi:A->real^N`; `W:A->bool`] METRIC_LOCAL_RESTRICT) THEN
  ASM_SIMP_TAC[IN_INTER] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `s:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b`;
                   `U:A->bool`; `phi:A->real^N`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                   `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) b`; `x:A`] METRIC_LOCAL_TRANS) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "loc" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[chart_trans] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `z:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b`; `W:A->bool`;
                 `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) s`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) s`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`;
                 `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) s`;
                 `U:A->bool`; `phi:A->real^N`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`; `x:A`]
                P2A_PULLBACK_METRIC_LOCAL_W) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
  USE_THEN "loc" MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTER; o_THM] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b`;
                 `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `z:A`]
                MFDR_CHART_INV_RESTRICT) THEN
  ASM_SIMP_TAC[IN_INTER]);;

let P2A_MPULLBACK_COMPOSE = prove
 (`!(h:real^N->real^N) (k:real^N->real^N) G z.
     h differentiable at z /\ k differentiable at (h z)
     ==> mpullback h (mpullback k G) z = mpullback (k o h) G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback; o_THM] THEN
  SUBGOAL_THEN
   `frechet_derivative ((k:real^N->real^N) o (h:real^N->real^N)) (at z) =
    frechet_derivative k (at (h z)) o frechet_derivative h (at z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `u:real^N` THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `z:real^N`; `u:real^N`]
                  LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[o_DEF; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at z)) /\
                linear(frechet_derivative (k:real^N->real^N) (at (h z)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

let P2A_DIFFEO_ON_EQ = prove
 (`!s t (f:real^N->real^N) g f' g'.
     diffeomorphism_on s t f g /\ (!x. x IN s ==> f' x = f x) /\
     (!y. y IN t ==> g' y = g y)
     ==> diffeomorphism_on s t f' g'`,
  REWRITE_TAC[diffeomorphism_on] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET; IN_IMAGE; FUN_IN_IMAGE];
    ASM_MESON_TAC[SUBSET; IN_IMAGE; FUN_IN_IMAGE];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `f:real^N->real^N` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `g:real^N->real^N` THEN
    ASM_SIMP_TAC[]]);;

let P2A_REGION_BB = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W1 a1 b1 W2 a2 b2 t0.
     p2a_region V W1 a1 b1 /\ p2a_region V W2 a2 b2 /\
     a1 < t0 /\ t0 <= b1 /\ a2 < t0 /\ t0 <= b2
     ==> mfd_diffeo (p2a_vtop V b1) (p2a_vatlas V b1) (W1 INTER W2)
                    (p2a_vtop V b2) (p2a_vatlas V b2) (W1 INTER W2) (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:A. y) = (\y. y) o (\y. y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_DIFFEO_COMPOSE THEN
  EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) t0` THEN
  EXISTS_TAC `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) t0` THEN
  EXISTS_TAC `W1 INTER W2:A->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) t0) (W1 INTER W2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_INTER]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    MP_TAC(ISPECL
     [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) t0`;
      `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) t0`; `W1:A->bool`;
      `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) b1`;
      `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) b1`; `W1:A->bool`;
      `\y:A. y`; `\y:A. y`; `W1 INTER W2:A->bool`] MFD_DIFFEO_RESTRICT) THEN
    ASM_SIMP_TAC[MFD_DIFFEO_SYM; IMAGE_ID; INTER_SUBSET];
    MP_TAC(ISPECL
     [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) t0`;
      `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) t0`; `W2:A->bool`;
      `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) b2`;
      `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) b2`; `W2:A->bool`;
      `\y:A. y`; `\y:A. y`; `W1 INTER W2:A->bool`] MFD_DIFFEO_RESTRICT) THEN
    ASM_SIMP_TAC[MFD_DIFFEO_SYM; IMAGE_ID; INTER_SUBSET]]);;

let P2A_REGION_CHART_DIFFEO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W1 a1 b1 W2 a2 b2 t0 U1 (phi1:A->real^N) U2 phi2.
     p2a_region V W1 a1 b1 /\ p2a_region V W2 a2 b2 /\
     a1 < t0 /\ t0 <= b1 /\ a2 < t0 /\ t0 <= b2 /\
     (U1,phi1) IN p2a_vatlas V b1 /\ (U2,phi2) IN p2a_vatlas V b2
     ==> diffeomorphism_on (IMAGE phi1 ((U1 INTER W1) INTER (U2 INTER W2)))
                           (IMAGE phi2 ((U1 INTER W1) INTER (U2 INTER W2)))
                           (chart_trans (U1 INTER W1,phi1) (U2 INTER W2,phi2))
                           (chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`;
                 `W2:A->bool`; `a2:real`; `b2:real`; `t0:real`] P2A_REGION_BB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) b1`;
    `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) b1`; `W1 INTER W2:A->bool`;
    `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) b2`;
    `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) b2`; `W1 INTER W2:A->bool`;
    `\y:A. y`; `\y:A. y`; `U1:A->bool`; `phi1:A->real^N`; `U2:A->bool`;
    `phi2:A->real^N`] MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{x:A | x IN U1 INTER (W1 INTER W2) /\ x IN U2} = (U1 INTER W1) INTER (U2 INTER W2) /\
    {y:A | y IN U2 INTER (W1 INTER W2) /\ y IN U1} = (U1 INTER W1) INTER (U2 INTER W2)`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC P2A_DIFFEO_ON_EQ THEN
  MAP_EVERY EXISTS_TAC [`(phi2:A->real^N) o (\y:A. y) o chart_inv (U1:A->bool,phi1:A->real^N)`;
                        `(phi1:A->real^N) o (\y:A. y) o chart_inv (U2:A->bool,phi2:A->real^N)`] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM; chart_trans; SND] THEN
  CONJ_TAC THEN X_GEN_TAC `z:A` THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b1`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b1`;
                   `U1:A->bool`; `phi1:A->real^N`; `W1:A->bool`; `z:A`]
                  MFDR_CHART_INV_RESTRICT);
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b2`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`;
                   `U2:A->bool`; `phi2:A->real^N`; `W2:A->bool`; `z:A`]
                  MFDR_CHART_INV_RESTRICT)] THEN
  ASM_SIMP_TAC[IN_INTER]);;

let P2A_REGION_SLICE_CHART = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b U (phi:A->real^N) s (c':(A->bool)#(A->real^N)).
     p2a_region V W a b /\ a < s /\ s <= b /\
     (U,phi) IN p2a_vatlas V b /\ c' IN p2a_vatlas V s
     ==> diffeomorphism_on (IMAGE phi ((U INTER W) INTER FST c'))
                           (IMAGE (SND c') ((U INTER W) INTER FST c'))
                           (chart_trans (U INTER W,phi) c') (chart_trans c' (U INTER W,phi))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) b`;
    `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) b`; `W:A->bool`;
    `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) s`;
    `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) s`; `W:A->bool`;
    `\y:A. y`; `\y:A. y`; `U:A->bool`; `phi:A->real^N`;
    `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
   MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  SUBGOAL_THEN
   `{x:A | x IN U INTER W /\ x IN FST(c':(A->bool)#(A->real^N))} =
    (U INTER W) INTER FST c' /\
    {y:A | y IN FST c' INTER W /\ y IN U} = (U INTER W) INTER FST c'`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC P2A_DIFFEO_ON_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`SND(c':(A->bool)#(A->real^N)) o (\y:A. y) o chart_inv (U:A->bool,phi:A->real^N)`;
    `(phi:A->real^N) o (\y:A. y) o chart_inv (c':(A->bool)#(A->real^N))`] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM; chart_trans; SND] THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b`;
                 `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `z:A`]
                MFDR_CHART_INV_RESTRICT) THEN
  ASM_SIMP_TAC[IN_INTER]);;

let P2A_MPULLBACK_PT = prove
 (`!(h:real^N->real^N) G1 G2 z.
     G1(h z) = G2(h z) ==> mpullback h G1 z = mpullback h G2 z`,
  SIMP_TAC[mpullback]);;

let P2A_DIFFEO_ON_DIFFERENTIABLE = prove
 (`!s t (f:real^N->real^N) g x.
     diffeomorphism_on s t f g /\ x IN s ==> f differentiable at x`,
  REWRITE_TAC[diffeomorphism_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let P2A_RLOCAL_TRANS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W1 a1 b1 W2 a2 b2 U1 (phi1:A->real^N) U2 phi2 s z.
     p2a_region V W1 a1 b1 /\ p2a_region V W2 a2 b2 /\
     (U1,phi1) IN p2a_vatlas V b1 /\ (U2,phi2) IN p2a_vatlas V b2 /\
     a1 < s /\ s <= b1 /\ a2 < s /\ s <= b2 /\
     z IN IMAGE phi1 ((U1 INTER W1) INTER (U2 INTER W2))
     ==> p2a_rlocal V W1 b1 (U1 INTER W1,phi1) s z =
         mpullback (chart_trans (U1 INTER W1,phi1) (U2 INTER W2,phi2))
                   (p2a_rlocal V W2 b2 (U2 INTER W2,phi2) s) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `s:real`]
                P2A_REGION_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `s:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `c' = chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) s) (x:A)` THEN
  SUBGOAL_THEN `(c':(A->bool)#(A->real^N)) IN p2a_vatlas V s /\ (x:A) IN FST c'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) s` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `M = metric_local (p2a_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) s) c'
                    (p2a_vmetric V s)` THEN
  ABBREV_TAC `h = chart_trans (U1 INTER W1:A->bool,phi1:A->real^N) (U2 INTER W2,phi2)` THEN
  ABBREV_TAC `k = chart_trans (U2 INTER W2:A->bool,phi2:A->real^N) c'` THEN
  SUBGOAL_THEN `(h:real^N->real^N) ((phi1:A->real^N) x) = phi2 x` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b1`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b1`;
                   `U1:A->bool`; `phi1:A->real^N`; `W1:A->bool`; `x:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  (* the two slice formulas *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`;
                 `U1:A->bool`; `phi1:A->real^N`; `s:real`;
                 `c':(A->bool)#(A->real^N)`; `x:A`] P2A_RLOCAL_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `mpullback (h:real^N->real^N)
      (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                     (real->A->real^N^N)) W2 b2 (U2 INTER W2,phi2) s) ((phi1:A->real^N) x) =
    mpullback h (mpullback (k:real^N->real^N) M) (phi1 x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_PT THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "k" THEN EXPAND_TAC "M" THEN MATCH_MP_TAC P2A_RLOCAL_SLICE THEN
    MAP_EVERY EXISTS_TAC [`a2:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* differentiability of h and k *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`;
                 `W2:A->bool`; `a2:real`; `b2:real`; `s:real`;
                 `U1:A->bool`; `phi1:A->real^N`; `U2:A->bool`; `phi2:A->real^N`]
                P2A_REGION_CHART_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`;
                 `U2:A->bool`; `phi2:A->real^N`; `s:real`; `c':(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^N) differentiable at ((phi1:A->real^N) x) /\
                (k:real^N->real^N) differentiable at (h(phi1 x))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC P2A_DIFFEO_ON_DIFFERENTIABLE THENL
     [MAP_EVERY EXISTS_TAC
       [`IMAGE (phi1:A->real^N) ((U1 INTER W1) INTER (U2 INTER W2))`;
        `IMAGE (phi2:A->real^N) ((U1 INTER W1) INTER (U2 INTER W2))`;
        `chart_trans (U2 INTER W2:A->bool,phi2:A->real^N) (U1 INTER W1,phi1)`] THEN
      EXPAND_TAC "h" THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
      MAP_EVERY EXISTS_TAC
       [`IMAGE (phi2:A->real^N) ((U2 INTER W2) INTER FST(c':(A->bool)#(A->real^N)))`;
        `IMAGE (SND(c':(A->bool)#(A->real^N))) ((U2 INTER W2) INTER FST c')`;
        `chart_trans (c':(A->bool)#(A->real^N)) (U2 INTER W2,phi2)`] THEN
      EXPAND_TAC "k" THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2A_MPULLBACK_COMPOSE] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN
  EXISTS_TAC `IMAGE (phi1:A->real^N) ((U1 INTER W1) INTER (U2 INTER W2))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  MAP_EVERY EXPAND_TAC ["h"; "k"] THEN REWRITE_TAC[chart_trans; SND] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b1`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b1`;
                 `U1:A->bool`; `phi1:A->real^N`; `W1:A->bool`; `y:A`]
                MFDR_CHART_INV_RESTRICT) THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b2`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b2`;
                 `U2:A->bool`; `phi2:A->real^N`; `W2:A->bool`; `y:A`]
                MFDR_CHART_INV_RESTRICT) THEN
  ASM_SIMP_TAC[IN_INTER]);;

let P2A_RLOCAL_FIELD = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b c s.
     p2a_region V W a b /\ c IN restrict_atlas (p2a_vatlas V b) W /\ a < s /\ s <= b
     ==> metric_field (IMAGE (SND c) (FST c)) (p2a_rlocal V W b c s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_region; p2a_flow_upto; ricci_flow_on] THEN
  STRIP_TAC THEN REWRITE_TAC[p2a_rlocal] THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas (p2a_vatlas (V:(real->A topology)#
       (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b) W)
      (p2a_rmetric V W b s)`
  MP_TAC THENL
   [ASM_CASES_TAC `s:real = b` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE];
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* L-geodesics are continuous into the slices (P2A_LGEOD_CONT), unpacking of *)
(* an L-geodesic near a parameter s0 into a chart solution with an explicit  *)
(* smooth s-family (P2A_LGEOD_PIECE), chart velocities transform with the    *)
(* transition (P2A_CURVE_CHART_VEL), transformed pieces solve the system in  *)
(* the other chart (P2A_TRANS_ODE), and the local uniqueness of L-geodesics  *)
(* with the same position and the same velocity in a slice chart             *)
(* (P2A_LGEOD_LOCAL_UNIQUE).                                                 *)
(* ========================================================================= *)

let P2A_REGION_SUBTOP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b s.
     p2a_region V W a b /\ a < s /\ s <= b
     ==> subtopology (p2a_vtop V s) W = subtopology (p2a_vtop V b) W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[mfd_diffeo] THEN
  REWRITE_TAC[HOMEOMORPHIC_MAPS_ID] THEN MESON_TAC[]);;

let P2A_REGION_OPEN_TRANSFER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b s O.
     p2a_region V W a b /\ a < s /\ s <= b /\ open_in (p2a_vtop V s) O
     ==> open_in (p2a_vtop V b) (W INTER O)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                P2A_REGION_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                P2A_REGION_SUBTOP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology (p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b) W) (W INTER O)`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY]]);;

let P2A_LGEOD_CONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s0 O.
     p2a_Lgeod V tt gamma b /\ &0 <= s0 /\ s0 pow 2 <= b /\
     open_in (p2a_vtop V (tt - s0 pow 2)) O /\ gamma(s0 pow 2) IN O
     ==> ?e. &0 < e /\
             !s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < e ==> gamma(s pow 2) IN O`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Lgeod] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real`
    (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` (X_CHOOSE_THEN `d:real`
    (X_CHOOSE_THEN `Av:real^1->real^N` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `(gamma:real->A)(s0 pow 2) IN FST(c:(A->bool)#(A->real^N)) /\
                a' < tt - s0 pow 2 /\ tt - s0 pow 2 <= b'`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th ->
      can (term_match [] `!s. P s ==> (gamma:real->A)(s pow 2) IN FST(c:(A->bool)#(A->real^N)) /\ Q s`)
          (concl th))) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  UNDISCH_TAC `(c:(A->bool)#(A->real^N)) IN
               restrict_atlas (p2a_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') W` THEN
  SUBST1_TAC(SYM(ISPEC `c:(A->bool)#(A->real^N)` PAIR)) THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `phi = SND(c:(A->bool)#(A->real^N))` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`;
                 `tt - s0 pow 2`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`;
                 `tt - s0 pow 2`; `O:A->bool`] P2A_REGION_OPEN_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER (W INTER O)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) b'` THEN
    EXISTS_TAC `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) b'` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v. (phi:A->real^N) ((gamma:real->A)(drop v pow 2))) continuous
    (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h:real^1. drop h % (Av:real^1->real^N) (lift s0)` THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s0` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u")) THEN
    EXPAND_TAC "phi" THEN ASM_SIMP_TAC[LIFT_DROP; REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(phi:A->real^N)((gamma:real->A)(s0 pow 2))` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(gamma:real->A)(s0 pow 2)` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[continuous_within] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 d` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN
  ASM_REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(phi:A->real^N)((gamma:real->A)(s pow 2)) IN IMAGE phi (U INTER (W INTER O))`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN FST(c:(A->bool)#(A->real^N))` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      can (term_match [] `!s. P s ==> (gamma:real->A)(s pow 2) IN FST(c:(A->bool)#(A->real^N)) /\ Q s`)
          (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b'`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b'`;
                 `U:A->bool`; `phi:A->real^N`; `W:A->bool`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `z:A` th) THEN MP_TAC(SPEC `(gamma:real->A)(s pow 2)` th)) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN MESON_TAC[]);;

let P2A_TIME_WINDOW = prove
 (`!a1 b1 tt s0.
     &0 <= s0 /\ a1 < tt - s0 pow 2 /\ tt - s0 pow 2 <= b1 /\
     (&0 < s0 ==> tt - s0 pow 2 < b1)
     ==> ?e. &0 < e /\
             !s. abs(s - s0) < e ==> a1 < tt - s pow 2 /\ tt - s pow 2 <= b1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s0 = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_ZERO; ARITH_EQ; REAL_SUB_RZERO]) THEN
    EXISTS_TAC `sqrt(tt - a1)` THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT; REAL_SUB_RZERO] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s pow 2 < tt - a1` ASSUME_TAC THENL
     [SUBGOAL_THEN `tt - a1 = sqrt(tt - a1) pow 2` SUBST1_TAC THENL
       [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_SUB_LT]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; ARITH_EQ];
      ALL_TAC] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `m = min (tt - s0 pow 2 - a1) (b1 - (tt - s0 pow 2))` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (&1) (m / (&2 * s0 + &1))` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_01; REAL_LT_DIV; REAL_ARITH `&0 < s0 ==> &0 < &2 * s0 + &1`] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(s pow 2 - s0 pow 2) < m` MP_TAC THENL
   [SUBGOAL_THEN `s pow 2 - s0 pow 2 = (s - s0) * (s + s0)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(s + s0) <= &2 * s0 + &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(s - s0) * (&2 * s0 + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
    SUBGOAL_THEN `m = (m / (&2 * s0 + &1)) * (&2 * s0 + &1)` SUBST1_TAC THENL
     [MATCH_MP_TAC(GSYM REAL_DIV_RMUL) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC]);;

let P2A_SWIN_INTERVAL = prove
 (`!b s0 d. is_interval {u:real^1 | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IS_INTERVAL_1; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:real^1`; `q:real^1`; `x:real^1`] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `drop q pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2A_LGEOD_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s0.
     p2a_Lgeod V tt gamma b /\ &0 <= s0 /\ s0 pow 2 <= b
     ==> ?W a' b' U (phi:A->real^N) d (A:real^1->real^N).
           p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\ &0 < d /\
           p2a_lsmooth (IMAGE phi (U INTER W)) (s0 - d) (s0 + d)
                       (\s. p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)) /\
           (!s. abs(s - s0) < d ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
           (!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < d
                ==> gamma(s pow 2) IN U INTER W) /\
           (!u. &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d
                ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A u)
                      (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
                    (A has_vector_derivative
                       p2a_lacc (p2a_rlocal V W b' (U INTER W,phi)) tt (drop u)
                                (phi(gamma(drop u pow 2))) (A u))
                      (at u within {v | &0 <= drop v /\ drop v pow 2 <= b})) /\
           ode_solution (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
             (interval(lift(s0 - d),lift(s0 + d)) PCROSS
              (IMAGE phi (U INTER W) PCROSS (:real^N)))
             {u | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d}
             (\u. pastecart (phi(gamma(drop u pow 2))) (A u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Lgeod] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real`
    (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` (X_CHOOSE_THEN `d0:real`
    (X_CHOOSE_THEN `A:real^1->real^N` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `?U (phi:A->real^N).
                  (U,phi) IN p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b' /\
                  c = (U INTER W,phi)`
  (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THENL
   [UNDISCH_TAC `(c:(A->bool)#(A->real^N)) IN
                 restrict_atlas (p2a_vatlas (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') W` THEN
    SUBST1_TAC(SYM(ISPEC `c:(A->bool)#(A->real^N)` PAIR)) THEN
    REWRITE_TAC[IN_RESTRICT_ATLAS; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  (* the time window *)
  SUBGOAL_THEN `?e0. &0 < e0 /\
                     !s. abs(s - s0) < e0 ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_TIME_WINDOW THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a' < tt - s0 pow 2 /\ tt - s0 pow 2 <= b'` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th ->
        is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s")) THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s0 - min d0 s0 / &2` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s")) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s0 pow 2` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `tt - (s0 - min d0 s0 / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x < y ==> tt - y < tt - x`) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d = min d0 e0` THEN
  SUBGOAL_THEN `&0 < d /\ d <= d0 /\ d <= e0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                        `d:real`; `A:real^1->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the s-family *)
    MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b') W`;
      `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b') W`;
      `a':real`; `b':real`; `p2a_rmetric (V:(real->A topology)#
                               (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'`;
      `(U INTER W:A->bool,phi:A->real^N)`; `tt:real`; `s0 - d`; `s0 + d`]
     P2A_UPTO_SFAMILY) THEN
    REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) W a' b'` THEN
    REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s" &&
      can (find_term (fun t -> t = `FST(c:(A->bool)#(A->real^N))`)) (concl th) = false &&
      can (find_term (fun t -> t = `U INTER W:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u" &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[P2A_LSOL_ODE; P2A_SWIN_INTERVAL] THEN
  X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop u` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s" &&
      can (find_term (fun t -> t = `U INTER W:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
    is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u" &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]);;

let P2A_SDOM_INTERVAL = prove
 (`!b. &0 <= b
       ==> {v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} = interval[vec 0,lift(sqrt b)]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC;
                                    LIFT_DROP] THEN
  X_GEN_TAC `v:real^1` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]]]);;

let P2A_CURVE_CHART_VEL = prove
 (`!(gamma:real->A) (c0:(A->bool)#(A->real^N)) c1 b s0 L w w1 e.
     &0 < b /\ &0 <= s0 /\ s0 pow 2 <= b /\ &0 < e /\
     (!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < e
          ==> gamma(s pow 2) IN FST c0 INTER FST c1) /\
     (!q. q IN FST c0 ==> chart_inv c0 (SND c0 q) = q) /\
     (chart_trans c0 c1 has_derivative L) (at (SND c0 (gamma(s0 pow 2)))) /\
     ((\v. SND c0 (gamma(drop v pow 2))) has_vector_derivative w)
       (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
     ((\v. SND c1 (gamma(drop v pow 2))) has_vector_derivative w1)
       (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> w1 = L w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^1. SND(c0:(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2))`;
                 `chart_trans (c0:(A->bool)#(A->real^N)) c1`; `w:real^N`;
                 `L:real^N->real^N`; `lift s0`;
                 `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}`]
                GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\v:real^1. SND(c1:(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2)))
     has_vector_derivative L (w:real^N))
    (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`chart_trans (c0:(A->bool)#(A->real^N)) c1 o
       (\v:real^1. SND c0 ((gamma:real->A)(drop v pow 2)))`; `e:real`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM; chart_trans] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop v` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s")) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `dist(v:real^1,lift s0) < e` THEN
      REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
      SIMP_TAC[IN_INTER]];
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
  MAP_EVERY EXISTS_TAC
   [`\v:real^1. SND(c1:(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2))`;
    `vec 0:real^1`; `lift(sqrt b)`; `lift s0`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP P2A_SDOM_INTERVAL
    (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < b`))]) THEN
  ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1] THEN
  ASM_SIMP_TAC[SQRT_POS_LT] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]);;

let P2A_REGION_OPEN_BACK = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b s O.
     p2a_region V W a b /\ a < s /\ s <= b /\ open_in (p2a_vtop V b) O /\ O SUBSET W
     ==> open_in (p2a_vtop V s) O`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                P2A_REGION_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                P2A_REGION_SUBTOP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology (p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) s) W) O`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY];
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY]]);;

let P2A_TRANS_ODE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W1 a1 b1 U1 (phi1:A->real^N) W2 a2 b2 U2 phi2 t0 tt (gamma:real->A) b
    (A2:real^1->real^N) J sa sb.
     p2a_region V W1 a1 b1 /\ p2a_region V W2 a2 b2 /\
     (U1,phi1) IN p2a_vatlas V b1 /\ (U2,phi2) IN p2a_vatlas V b2 /\
     a1 < t0 /\ t0 <= b1 /\ a2 < t0 /\ t0 <= b2 /\
     is_interval J /\ J SUBSET {v | &0 <= drop v /\ drop v pow 2 <= b} /\
     (!u. u IN J
          ==> sa < drop u /\ drop u < sb /\
              gamma(drop u pow 2) IN (U2 INTER W2) INTER (U1 INTER W1) /\
              a1 < tt - drop u pow 2 /\ tt - drop u pow 2 <= b1 /\
              a2 < tt - drop u pow 2 /\ tt - drop u pow 2 <= b2 /\
              ((\v. phi2(gamma(drop v pow 2))) has_vector_derivative A2 u)
                (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
              (A2 has_vector_derivative
                 p2a_lacc (p2a_rlocal V W2 b2 (U2 INTER W2,phi2)) tt (drop u)
                          (phi2(gamma(drop u pow 2))) (A2 u))
                (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}))
     ==> ode_solution (p2a_lfield (p2a_rlocal V W1 b1 (U1 INTER W1,phi1)) tt)
           (interval(lift sa,lift sb) PCROSS (IMAGE phi1 (U1 INTER W1) PCROSS (:real^N))) J
           (\u. pastecart (chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1)
                             (phi2(gamma(drop u pow 2))))
                          (frechet_derivative
                             (chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1))
                             (at (phi2(gamma(drop u pow 2)))) (A2 u))) /\
         (!u. u IN J
              ==> ((\r. chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1)
                           (phi2(gamma(drop r pow 2)))) has_vector_derivative
                   frechet_derivative (chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1))
                     (at (phi2(gamma(drop u pow 2)))) (A2 u))
                  (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`;
                 `W1:A->bool`; `a1:real`; `b1:real`; `t0:real`;
                 `U2:A->bool`; `phi2:A->real^N`; `U1:A->bool`; `phi1:A->real^N`]
                P2A_REGION_CHART_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!u. u IN J
        ==> pastecart u
              (pastecart (chart_trans (U2 INTER W2:A->bool,phi2:A->real^N) (U1 INTER W1,phi1)
                            (phi2((gamma:real->A)(drop u pow 2))))
                         (frechet_derivative
                            (chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1))
                            (at (phi2(gamma(drop u pow 2)))) ((A2:real^1->real^N) u))) IN
            interval(lift sa,lift sb) PCROSS (IMAGE phi1 (U1 INTER W1) PCROSS (:real^N)) /\
            ((\r. chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1)
                    (phi2(gamma(drop r pow 2)))) has_vector_derivative
             frechet_derivative (chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1))
               (at (phi2(gamma(drop u pow 2)))) (A2 u))
            (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
            ((\r. frechet_derivative (chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1))
                     (at (phi2(gamma(drop r pow 2)))) (A2 r)) has_vector_derivative
             p2a_lacc (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W1 b1 (U1 INTER W1,phi1)) tt (drop u)
               (chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1) (phi2(gamma(drop u pow 2))))
               (frechet_derivative (chart_trans (U2 INTER W2,phi2) (U1 INTER W1,phi1))
                  (at (phi2(gamma(drop u pow 2)))) (A2 u)))
            (at u within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  ASSUME_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL
     [REWRITE_TAC[P2A_LSOL_ODE] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "pastecart")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "pastecart")) (concl th))) THEN
      ASM_SIMP_TAC[]]] THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
    is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u")) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `chart_trans (U2 INTER W2:A->bool,phi2:A->real^N) (U1 INTER W1,phi1)
      (phi2((gamma:real->A)(drop u pow 2))) = phi1(gamma(drop u pow 2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b2`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`;
                   `U2:A->bool`; `phi2:A->real^N`; `W2:A->bool`;
                   `(gamma:real->A)(drop u pow 2)`] MFDR_CHART_INV_RESTRICT) THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `t0:real`]
                  P2A_REGION_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (phi1:A->real^N) ((U2 INTER W2) INTER (U1 INTER W1))`;
    `IMAGE (phi2:A->real^N) ((U2 INTER W2) INTER (U1 INTER W1))`;
    `chart_trans (U2 INTER W2:A->bool,phi2:A->real^N) (U1 INTER W1,phi1)`;
    `chart_trans (U1 INTER W1:A->bool,phi1:A->real^N) (U2 INTER W2,phi2)`;
    `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) W2 b2 (U2 INTER W2,phi2)`;
    `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) W1 b1 (U1 INTER W1,phi1)`;
    `tt:real`; `\v:real^1. (phi2:A->real^N)((gamma:real->A)(drop v pow 2))`;
    `A2:real^1->real^N`; `u:real^1`;
    `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}`] P2A_LSOL_TRANS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(U1 INTER W1:A->bool,phi1:A->real^N)) (FST(U1 INTER W1,phi1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2A_RLOCAL_FIELD THEN
        MAP_EVERY EXISTS_TAC [`a1:real`] THEN ASM_REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
        EXISTS_TAC `U1:A->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
      REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC P2A_RLOCAL_TRANS THEN
      MAP_EVERY EXISTS_TAC [`a2:real`; `a1:real`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC[]);;

let P2A_LGEOD_LOCAL_UNIQUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma1 gamma2 b s0 (c0:(A->bool)#(A->real^N)) w.
     &0 < b /\ &0 <= s0 /\ s0 pow 2 <= b /\
     p2a_Lgeod V tt gamma1 b /\ p2a_Lgeod V tt gamma2 b /\
     gamma1(s0 pow 2) = gamma2(s0 pow 2) /\
     c0 IN p2a_vatlas V (tt - s0 pow 2) /\ gamma1(s0 pow 2) IN FST c0 /\
     ((\v. SND c0 (gamma1(drop v pow 2))) has_vector_derivative w)
       (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
     ((\v. SND c0 (gamma2(drop v pow 2))) has_vector_derivative w)
       (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> ?e. &0 < e /\
             !s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < e
                 ==> gamma1(s pow 2) = gamma2(s pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `b:real`; `s0:real`]
                P2A_LGEOD_PIECE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W1:A->bool` (X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `b1:real`
    (X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N` (X_CHOOSE_THEN `d1:real`
    (X_CHOOSE_THEN `A1:real^1->real^N` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma2:real->A`; `b:real`; `s0:real`]
                P2A_LGEOD_PIECE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W2:A->bool` (X_CHOOSE_THEN `a2:real` (X_CHOOSE_THEN `b2:real`
    (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N` (X_CHOOSE_THEN `d2:real`
    (X_CHOOSE_THEN `A2:real^1->real^N` STRIP_ASSUME_TAC))))))) THEN
  RULE_ASSUM_TAC(fun th -> if concl th = `(gamma1:real->A)(s0 pow 2) = gamma2(s0 pow 2)`
                           then SYM th else th) THEN
  ABBREV_TAC `t0 = tt - s0 pow 2` THEN
  ABBREV_TAC `p = (gamma1:real->A)(s0 pow 2)` THEN
  SUBGOAL_THEN `a1 < t0 /\ t0 <= b1 /\ a2 < t0 /\ t0 <= b2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t0"] THEN ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN U1 INTER W1 /\ p IN U2 INTER W2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LE_REFL];
    ALL_TAC] THEN
  (* slices at t0 and open sets there *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `t0:real`] P2A_REGION_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `t0:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0`; `c0:(A->bool)#(A->real^N)`]
                MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0) (U1 INTER W1) /\
                open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0) (U2 INTER W2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
      MAP_EVERY EXISTS_TAC [`W1:A->bool`; `a1:real`; `b1:real`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b1`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b1`;
                     `(U1:A->bool,phi1:A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[FST];
      MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
      MAP_EVERY EXISTS_TAC [`W2:A->bool`; `a2:real`; `b2:real`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b2`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b2`;
                     `(U2:A->bool,phi2:A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[FST]];
    ALL_TAC] THEN
  ABBREV_TAC `O = FST(c0:(A->bool)#(A->real^N)) INTER (U1 INTER W1) INTER (U2 INTER W2)` THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0) (O:A->bool) /\ (p:A) IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `b:real`; `s0:real`; `O:A->bool`]
                P2A_LGEOD_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `tt:real`; `gamma2:real->A`; `b:real`; `s0:real`; `O:A->bool`]
                P2A_LGEOD_CONT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min (min d1 d2) (min e1 e2)` THEN
  SUBGOAL_THEN `&0 < e /\ e <= d1 /\ e <= d2 /\ e <= e1 /\ e <= e2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `h = chart_trans (U2 INTER W2:A->bool,phi2:A->real^N) (U1 INTER W1,phi1)` THEN
  SUBGOAL_THEN `!q:A. q IN U1 INTER W1 /\ q IN U2 INTER W2 ==> (h:real^N->real^N)(phi2 q) = phi1 q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans; SND] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b2`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b2`;
                   `U2:A->bool`; `phi2:A->real^N`; `W2:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the velocity in chart c1 from the c0 velocity *)
  ABBREV_TAC `L1 = frechet_derivative (chart_trans (c0:(A->bool)#(A->real^N)) (U1 INTER W1,phi1))
                                      (at (SND c0 (p:A)))` THEN
  SUBGOAL_THEN `(chart_trans (c0:(A->bool)#(A->real^N)) (U1 INTER W1,phi1) has_derivative L1)
                (at (SND c0 (p:A)))` ASSUME_TAC THENL
   [EXPAND_TAC "L1" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC P2A_DIFFEO_ON_DIFFERENTIABLE THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (SND(c0:(A->bool)#(A->real^N))) ((U1 INTER W1) INTER FST c0)`;
      `IMAGE (phi1:A->real^N) ((U1 INTER W1) INTER FST(c0:(A->bool)#(A->real^N)))`;
      `chart_trans (U1 INTER W1:A->bool,phi1:A->real^N) c0`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN MATCH_MP_TAC P2A_REGION_SLICE_CHART THEN
      MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `a1:real`; `b1:real`; `t0:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A1:real^1->real^N)(lift s0) = (L1:real^N->real^N) w` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_CURVE_CHART_VEL THEN
    MAP_EVERY EXISTS_TAC [`gamma1:real->A`; `c0:(A->bool)#(A->real^N)`;
                          `(U1 INTER W1:A->bool,phi1:A->real^N)`; `b:real`; `s0:real`;
                          `e:real`] THEN
    ASM_REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gamma1:real->A)(s pow 2) IN O` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `e1:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "O" THEN SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s0` o check (fun th ->
        is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u" &&
        can (find_term ((=) `A1:real^1->real^N`)) (concl th))) THEN
      ASM_SIMP_TAC[LIFT_DROP; REAL_SUB_REFL; REAL_ABS_0]];
    ALL_TAC] THEN
  (* the transformed velocity of gamma2 in chart c1 *)
  ABBREV_TAC `B2 = frechet_derivative (h:real^N->real^N) (at ((phi2:A->real^N) p))
                                      ((A2:real^1->real^N)(lift s0))` THEN
  ABBREV_TAC `J = {u:real^1 | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < e}` THEN
  SUBGOAL_THEN `is_interval (J:real^1->bool) /\
                J SUBSET {v | &0 <= drop v /\ drop v pow 2 <= b} /\ lift s0 IN J`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[P2A_SWIN_INTERVAL; SUBSET; IN_ELIM_THM; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `U1:A->bool`; `phi1:A->real^N`;
                 `W2:A->bool`; `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`;
                 `t0:real`; `tt:real`; `gamma2:real->A`; `b:real`; `A2:real^1->real^N`;
                 `J:real^1->bool`; `s0 - d1`; `s0 + d1`] P2A_TRANS_ODE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `u:real^1` THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(gamma2:real->A)(drop u pow 2) IN O` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "O" THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a1 < tt - drop(u:real^1) pow 2 /\ tt - drop u pow 2 <= b1) /\
                  (a2 < tt - drop u pow 2 /\ tt - drop u pow 2 <= b2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `d1:real`)) (concl th) &&
          can (find_term ((=) `b1:real`)) (concl th)));
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `d2:real`)) (concl th) &&
          can (find_term ((=) `b2:real`)) (concl th)))] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u" &&
      can (find_term ((=) `A2:real^1->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  (* B2 is the c1 velocity of gamma2, hence equal to L1 w *)
  SUBGOAL_THEN `(B2:real^N) = (L1:real^N->real^N) w` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_CURVE_CHART_VEL THEN
    MAP_EVERY EXISTS_TAC [`gamma2:real->A`; `c0:(A->bool)#(A->real^N)`;
                          `(U1 INTER W1:A->bool,phi1:A->real^N)`; `b:real`; `s0:real`;
                          `e:real`] THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    SUBGOAL_THEN `!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < e
                      ==> (gamma2:real->A)(s pow 2) IN O` ASSUME_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "O" THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`\r:real^1. (h:real^N->real^N)((phi2:A->real^N)((gamma2:real->A)(drop r pow 2)))`;
      `e:real`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `h:real^N->real^N`)) (concl th) &&
        can (find_term ((=) `phi2:A->real^N`)) (concl th) &&
        not (can (find_term ((=) `J:real^1->bool`)) (concl th)))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `drop v` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `O:A->bool`)) (concl th) &&
        can (find_term ((=) `gamma2:real->A`)) (concl th) &&
        can (find_term ((=) `e:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `dist(v:real^1,lift s0) < e` THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
        EXPAND_TAC "O" THEN SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s0` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `J:real^1->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "ode_solution")) (concl th)))) THEN
      ASM_REWRITE_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  (* ODE uniqueness in chart c1 on J *)
  MP_TAC(ISPECL
   [`IMAGE (phi1:A->real^N) (U1 INTER W1)`; `s0 - d1`; `s0 + d1`;
    `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W1 b1 (U1 INTER W1,phi1)`; `tt:real`; `J:real^1->bool`; `J:real^1->bool`;
    `\u:real^1. (phi1:A->real^N)((gamma1:real->A)(drop u pow 2))`; `A1:real^1->real^N`;
    `\u:real^1. (h:real^N->real^N)((phi2:A->real^N)((gamma2:real->A)(drop u pow 2)))`;
    `\u:real^1. frechet_derivative (h:real^N->real^N)
                  (at ((phi2:A->real^N)((gamma2:real->A)(drop u pow 2))))
                  ((A2:real^1->real^N) u)`;
    `lift s0`] P2A_LSOL_UNIQUE) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ODE_SOLUTION_SUBINTERVAL THEN
      EXISTS_TAC `{u:real^1 | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d1}` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "J" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LTE_TRANS];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `A1:real^1->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
    can (find_term ((=) `J:real^1->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN EXPAND_TAC "J" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(gamma1:real->A)(s pow 2) IN O /\ (gamma2:real->A)(s pow 2) IN O`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `O:A->bool`)) (concl th) &&
      (can (find_term ((=) `e1:real`)) (concl th) || can (find_term ((=) `e2:real`)) (concl th)) )) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^N)((phi2:A->real^N)((gamma2:real->A)(s pow 2))) =
                phi1(gamma2(s pow 2))` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(gamma2:real->A)(s pow 2) IN O` THEN
    EXPAND_TAC "O" THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b1`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b1`;
                 `U1:A->bool`; `phi1:A->real^N`; `W1:A->bool`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `(gamma1:real->A)(s pow 2)` th) THEN
                       MP_TAC(SPEC `(gamma2:real->A)(s pow 2)` th)) THEN
  UNDISCH_TAC `(gamma1:real->A)(s pow 2) IN O` THEN
  UNDISCH_TAC `(gamma2:real->A)(s pow 2) IN O` THEN
  EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;


(* ========================================================================= *)
(* Global uniqueness of L-geodesics (clause 1 of P2A_LGEOD_FLOW_STATEMENT,   *)
(* generic in N): an open-closed argument on [0, sqrt b]                     *)
(* (P2A_REAL_CONT_INDUCT) with the local uniqueness, Hausdorff slices        *)
(* (P2A_LGEOD_CLOSED_STEP) and the velocity in a slice chart                 *)
(* (P2A_LGEOD_SLICE_VEL, P2A_LGEOD_OPEN_STEP).                               *)
(* ========================================================================= *)

let P2A_LGEOD_SLICE_VEL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s0 (c0:(A->bool)#(A->real^N)).
     &0 < b /\ &0 <= s0 /\ s0 pow 2 <= b /\ p2a_Lgeod V tt gamma b /\
     c0 IN p2a_vatlas V (tt - s0 pow 2) /\ gamma(s0 pow 2) IN FST c0
     ==> ?w. ((\v. SND c0 (gamma(drop v pow 2))) has_vector_derivative w)
               (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`]
                P2A_LGEOD_PIECE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W1:A->bool` (X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `b1:real`
    (X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N` (X_CHOOSE_THEN `d1:real`
    (X_CHOOSE_THEN `A1:real^1->real^N` STRIP_ASSUME_TAC))))))) THEN
  ABBREV_TAC `t0 = tt - s0 pow 2` THEN
  SUBGOAL_THEN `a1 < t0 /\ t0 <= b1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s0 pow 2) IN U1 INTER W1` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) t0`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) t0`; `c0:(A->bool)#(A->real^N)`]
                MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) t0) (FST(c0:(A->bool)#(A->real^N)) INTER (U1 INTER W1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
    MAP_EVERY EXISTS_TAC [`W1:A->bool`; `a1:real`; `b1:real`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b1`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b1`;
                   `(U1:A->bool,phi1:A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[FST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`;
                 `FST(c0:(A->bool)#(A->real^N)) INTER (U1 INTER W1)`] P2A_LGEOD_CONT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `frechet_derivative (chart_trans (U1 INTER W1:A->bool,phi1:A->real^N) c0)
                (at (phi1((gamma:real->A)(s0 pow 2)))) ((A1:real^1->real^N)(lift s0))` THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC
   [`chart_trans (U1 INTER W1:A->bool,phi1:A->real^N) c0 o
     (\v:real^1. phi1((gamma:real->A)(drop v pow 2)))`; `min e1 d1`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; IN_ELIM_THM; LIFT_DROP] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM; chart_trans; SND] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(gamma:real->A)(drop v pow 2) IN U1 INTER W1` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `drop v` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `e1:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `dist(v:real^1,lift s0) < e1` THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
        SIMP_TAC[IN_INTER]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b1`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b1`;
                   `U1:A->bool`; `phi1:A->real^N`; `W1:A->bool`;
                   `(gamma:real->A)(drop v pow 2)`] MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `lift s0` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u" &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
    ASM_SIMP_TAC[LIFT_DROP; REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC P2A_DIFFEO_ON_DIFFERENTIABLE THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi1:A->real^N) ((U1 INTER W1) INTER FST(c0:(A->bool)#(A->real^N)))`;
    `IMAGE (SND(c0:(A->bool)#(A->real^N))) ((U1 INTER W1) INTER FST c0)`;
    `chart_trans (c0:(A->bool)#(A->real^N)) (U1 INTER W1,phi1)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SLICE_CHART THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)`; `a1:real`; `b1:real`; `t0:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]]);;

let P2A_REAL_CONT_INDUCT = prove
 (`!(E:real->bool) Sb.
     &0 <= Sb /\
     (?e. &0 < e /\ !s. &0 <= s /\ s <= Sb /\ s < e ==> E s) /\
     (!Tm. &0 < Tm /\ Tm <= Sb /\ (!s. &0 <= s /\ s < Tm ==> E s) ==> E Tm) /\
     (!Tm. &0 <= Tm /\ Tm < Sb /\ (!s. &0 <= s /\ s <= Tm ==> E s)
          ==> ?e. &0 < e /\ !s. &0 <= s /\ s <= Sb /\ abs(s - Tm) < e ==> E s)
     ==> !s. &0 <= s /\ s <= Sb ==> E s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "cl") (LABEL_TAC "op")))) THEN
  ABBREV_TAC `P = {t | &0 <= t /\ t <= Sb /\ !s. &0 <= s /\ s <= t ==> (E:real->bool) s}` THEN
  SUBGOAL_THEN `!t. t IN P <=> &0 <= t /\ t <= Sb /\
                               !s. &0 <= s /\ s <= t ==> (E:real->bool) s`
  (LABEL_TAC "P") THENL [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real->bool) (&0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `e0:real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0) IN P` ASSUME_TAC THENL
   [USE_THEN "P" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s = &0` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `P:real->bool` SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `Sb:real` THEN USE_THEN "P" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  ABBREV_TAC `Tm = sup P` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  SUBGOAL_THEN `&0 <= Tm /\ Tm <= Sb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "lub" MATCH_MP_TAC THEN USE_THEN "P" (fun th -> SIMP_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < Tm ==> (E:real->bool) s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?t. t IN P /\ s < t` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
     [REMOVE_THEN "lub" (MP_TAC o SPEC `s:real`) THEN
      ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN MESON_TAC[REAL_NOT_LT];
      ALL_TAC] THEN
    UNDISCH_TAC `(t:real) IN P` THEN USE_THEN "P" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= Tm ==> (E:real->bool) s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < Tm` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s:real = Tm` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `Tm = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Tm:real = Sb` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    REMOVE_THEN "op" (MP_TAC o SPEC `Tm:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `min (Tm + e / &2) Sb IN P` MP_TAC THENL
     [USE_THEN "P" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `s <= Tm` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `min (Tm + e / &2) Sb <= Tm` MP_TAC THENL
       [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let P2A_LGEOD_CLOSED_STEP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma1 gamma2 b Tm.
     p2a_svs V /\ p2a_Lgeod V tt gamma1 b /\ p2a_Lgeod V tt gamma2 b /\
     &0 < Tm /\ Tm pow 2 <= b /\
     (!s. &0 <= s /\ s < Tm ==> gamma1(s pow 2) = gamma2(s pow 2))
     ==> gamma1(Tm pow 2) = gamma2(Tm pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(gamma1:real->A)(Tm pow 2) IN
      topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) (tt - Tm pow 2)) /\
    (gamma2:real->A)(Tm pow 2) IN topspace(p2a_vtop V (tt - Tm pow 2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt gamma1 b`;
      UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt gamma2 b`] THEN
    REWRITE_TAC[p2a_Lgeod] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - Tm pow 2))`
  MP_TAC THENL [ASM_MESON_TAC[p2a_svs]; ALL_TAC] THEN
  REWRITE_TAC[hausdorff_space] THEN
  DISCH_THEN(MP_TAC o SPECL [`(gamma1:real->A)(Tm pow 2)`; `(gamma2:real->A)(Tm pow 2)`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O1:A->bool` (X_CHOOSE_THEN `O2:A->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `b:real`; `Tm:real`;
                 `O1:A->bool`] P2A_LGEOD_CONT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma2:real->A`; `b:real`; `Tm:real`;
                 `O2:A->bool`] P2A_LGEOD_CONT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = Tm - min (min e1 e2) Tm / &2` THEN
  SUBGOAL_THEN `&0 <= s /\ s < Tm /\ s pow 2 <= b /\ abs(s - Tm) < e1 /\ abs(s - Tm) < e2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    SUBGOAL_THEN `&0 < min (min e1 e2) Tm` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Tm pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma1:real->A)(s pow 2) IN O1 /\ (gamma2:real->A)(s pow 2) IN O2`
  MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma1:real->A)(s pow 2) = gamma2(s pow 2)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]);;

let P2A_LGEOD_OPEN_STEP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma1 gamma2 b Tm.
     p2a_svs V /\ p2a_Lgeod V tt gamma1 b /\ p2a_Lgeod V tt gamma2 b /\
     &0 < Tm /\ Tm pow 2 <= b /\
     (!s. &0 <= s /\ s <= Tm ==> gamma1(s pow 2) = gamma2(s pow 2))
     ==> ?e. &0 < e /\
             !s. &0 <= s /\ s pow 2 <= b /\ abs(s - Tm) < e
                 ==> gamma1(s pow 2) = gamma2(s pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  ABBREV_TAC `t0 = tt - Tm pow 2` THEN
  ABBREV_TAC `p = (gamma1:real->A)(Tm pow 2)` THEN
  SUBGOAL_THEN `(gamma2:real->A)(Tm pow 2) = p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(gamma1:real->A)(Tm pow 2) IN
                    topspace(p2a_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - Tm pow 2))`
    MP_TAC THENL
     [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt gamma1 b` THEN
      REWRITE_TAC[p2a_Lgeod] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0)
                  (p2a_vatlas V t0)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o SPEC `t0:real`) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0) (p:A)` THEN
  SUBGOAL_THEN `(c0:(A->bool)#(A->real^N)) IN p2a_vatlas V t0 /\ (p:A) IN FST c0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) t0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `b:real`; `Tm:real`;
                 `c0:(A->bool)#(A->real^N)`] P2A_LGEOD_SLICE_VEL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N` ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma2:real->A`; `b:real`; `Tm:real`;
                 `c0:(A->bool)#(A->real^N)`] P2A_LGEOD_SLICE_VEL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^N` ASSUME_TAC) THEN
  SUBGOAL_THEN `interval[vec 0,lift Tm] SUBSET {v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC; LIFT_DROP] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Tm pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w2:real^N = w1` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC
     [`\v:real^1. SND(c0:(A->bool)#(A->real^N)) ((gamma2:real->A)(drop v pow 2))`;
      `vec 0:real^1`; `lift Tm`; `lift Tm`] THEN
    ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
      MAP_EVERY EXISTS_TAC
       [`\v:real^1. SND(c0:(A->bool)#(A->real^N)) ((gamma1:real->A)(drop v pow 2))`;
        `&1`] THEN
      REWRITE_TAC[REAL_LT_01; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_LGEOD_LOCAL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)`; `tt:real`; `c0:(A->bool)#(A->real^N)`;
                        `w1:real^N`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `((\v:real^1. SND(c0:(A->bool)#(A->real^N)) ((gamma2:real->A)(drop v pow 2)))
                has_vector_derivative w2)
               (at (lift Tm) within {v | &0 <= drop v /\ drop v pow 2 <= b})` THEN
  ASM_REWRITE_TAC[]);;

let P2A_SQRT_LE_IMP = prove
 (`!s b. &0 <= b /\ &0 <= s /\ s <= sqrt b ==> s pow 2 <= b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]]);;

let P2A_LGEOD_UNIQUE_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma1 gamma2 b (c0:(A->bool)#(A->real^N)) w.
     p2a_svs V /\ p2a_Lgeod V tt gamma1 b /\ p2a_Lgeod V tt gamma2 b /\
     gamma1(&0) = gamma2(&0) /\ c0 IN p2a_vatlas V tt /\ gamma1(&0) IN FST c0 /\
     ((\v. SND c0 (gamma1(drop v pow 2))) has_vector_derivative w)
       (at (vec 0) within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
     ((\v. SND c0 (gamma2(drop v pow 2))) has_vector_derivative w)
       (at (vec 0) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> !tau. &0 <= tau /\ tau <= b ==> gamma1 tau = gamma2 tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma2:real->A)(&0) IN FST(c0:(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* the start *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `gamma2:real->A`;
                 `b:real`; `&0`; `c0:(A->bool)#(A->real^N)`; `w:real^N`]
                P2A_LGEOD_LOCAL_UNIQUE) THEN
  ASM_REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_SUB_RZERO; REAL_LE_REFL; LIFT_NUM] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\s. (gamma1:real->A)(s pow 2) = gamma2(s pow 2)`; `sqrt b`]
                P2A_REAL_CONT_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `e0:real`)) (concl th))) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2A_SQRT_LE_IMP THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LGEOD_CLOSED_STEP THEN
      MAP_EVERY EXISTS_TAC
       [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`;
        `tt:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A_SQRT_LE_IMP THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `Tm = &0` THENL
       [EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `e0:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC P2A_SQRT_LE_IMP THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `gamma2:real->A`;
                     `b:real`; `Tm:real`] P2A_LGEOD_OPEN_STEP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC P2A_SQRT_LE_IMP THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2A_SQRT_LE_IMP THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau`) THEN
  ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE; SQRT_POW_2]);;

let P2A_LGEOD_UNIQUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z b gamma1 gamma2.
     p2a_svs V /\ p2a_Lgeod_from V tt x Z b gamma1 /\ p2a_Lgeod_from V tt x Z b gamma2
     ==> !tau. &0 <= tau /\ tau <= b ==> gamma1 tau = gamma2 tau`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2A_LGEOD_UNIQUE_GEN THEN
  MAP_EVERY EXISTS_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`;
    `tt:real`; `chart_at (p2a_vatlas (V:(real->A topology)#
       (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A)`;
    `&2 % (Z:real^N)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CHART_AT THEN
  EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) tt` THEN
  SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt gamma1 b` THEN
    REWRITE_TAC[p2a_Lgeod] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; REAL_SUB_RZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N))` THEN
  REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `tt:real`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;


(* ========================================================================= *)
(* Restriction (clause 2 of P2A_LGEOD_FLOW_STATEMENT: P2A_LDOM_RESTRICT) and *)
(* local existence from a backward-smooth base point (clause 3:              *)
(* P2A_LGEOD_EXISTS_LOCAL), generic in N.                                    *)
(* ========================================================================= *)

let P2A_LGEOD_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b b1.
     p2a_Lgeod V tt gamma b /\ &0 < b1 /\ b1 <= b ==> p2a_Lgeod V tt gamma b1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Lgeod] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u")) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LE_TRANS]]);;

let P2A_LGEOD_FROM_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z gamma b b1.
     p2a_Lgeod_from V tt x Z b gamma /\ &0 < b1 /\ b1 <= b
     ==> p2a_Lgeod_from V tt x Z b1 gamma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2A_LGEOD_RESTRICT THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LE_TRANS]]);;

let P2A_LGEO_PROP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z b.
     Z IN p2a_Ldom V tt x b ==> p2a_Lgeod_from V tt x Z b (p2a_Lgeo V tt x Z b)`,
  REWRITE_TAC[p2a_Ldom; p2a_Lgeo; IN_ELIM_THM] THEN MESON_TAC[]);;

let P2A_LDOM_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z b b1.
     p2a_svs V /\ Z IN p2a_Ldom V tt x b /\ &0 < b1 /\ b1 <= b
     ==> Z IN p2a_Ldom V tt x b1 /\
         !tau. &0 <= tau /\ tau <= b1
               ==> p2a_Lgeo V tt x Z b1 tau = p2a_Lgeo V tt x Z b tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LGEO_PROP) THEN
  SUBGOAL_THEN `p2a_Lgeod_from (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x Z b1 (p2a_Lgeo V tt x Z b)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_LGEOD_FROM_RESTRICT THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b1`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2a_Ldom; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A_LGEOD_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`] THEN
  ASM_SIMP_TAC[P2A_LGEO_PROP; ETA_AX]);;

let P2A_LSOL_AT = prove
 (`!(Gt:real->real^N->real^N^N) tt D J (Y:real^1->real^N) (A:real^1->real^N) u.
     ode_solution (p2a_lfield Gt tt) D J (\t. pastecart (Y t) (A t)) /\ open J /\ u IN J
     ==> (Y has_vector_derivative A u) (at u) /\
         (A has_vector_derivative p2a_lacc Gt tt (drop u) (Y u) (A u)) (at u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_lfield (Gt:real->real^N->real^N^N) tt`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`; `J:real^1->bool`;
                 `\t:real^1. pastecart ((Y:real^1->real^N) t) ((A:real^1->real^N) t)`;
                 `u:real^1`] ODE_SOLUTION_AT) THEN
  ASM_REWRITE_TAC[p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART;
                  P2A_HVD_PASTECART_EQ; ETA_AX]);;

let P2A_LGEOD_EXISTS_LOCAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> ?b. &0 < b /\ Z IN p2a_Ldom V tt x b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_bsmooth] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A)` THEN
  SUBGOAL_THEN `(c0:(A->bool)#(A->real^N)) IN p2a_vatlas V tt /\ (x:A) IN FST c0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `U = FST(c0:(A->bool)#(A->real^N))` THEN
  ABBREV_TAC `phi = SND(c0:(A->bool)#(A->real^N))` THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN ASM_REWRITE_TAC[PAIR]; ALL_TAC] THEN
  ABBREV_TAC `c = (U INTER W:A->bool,phi:A->real^N)` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN
                restrict_atlas (p2a_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) W`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the s-family on (-r,r) *)
  ABBREV_TAC `r = sqrt(tt - a)` THEN
  SUBGOAL_THEN `&0 < r /\ r pow 2 = tt - a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT; SQRT_POW_2;
                                     REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (--r) r
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) W tt c (tt - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt) W`;
      `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt) W`;
      `a:real`; `tt:real`; `p2a_rmetric (V:(real->A topology)#
                               (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt`;
      `c:(A->bool)#(A->real^N)`; `tt:real`; `--r`; `r:real`] P2A_UPTO_SFAMILY) THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[p2a_rlocal; FST; SND] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) W a tt` THEN
    REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:(A->bool)#(A->real^N)) IN
                 restrict_atlas (p2a_vatlas (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) W` THEN
    EXPAND_TAC "c" THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 < r pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      REWRITE_TAC[REAL_ABS_POS; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* chart facts for c in the restricted manifold *)
  MP_TAC(ISPECL [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) W`;
                 `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) W`; `c:(A->bool)#(A->real^N)`]
                MFDM_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "c" THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN U INTER W` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  (* local solution of the system from (0, phi x, 2 Z) *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `--r`; `r:real`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (c:(A->bool)#(A->real^N))`; `tt:real`; `&0`;
                 `(phi:A->real^N) x`; `&2 % (Z:real^N)`] P2A_LSOL_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^1->bool` (X_CHOOSE_THEN `Y:real^1->real^N`
    (X_CHOOSE_THEN `A:real^1->real^N` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIFT_NUM]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t:real^1. t IN J ==> --r < drop t /\ drop t < r /\
                                       (Y:real^1->real^N) t IN
                                       IMAGE (phi:A->real^N) (U INTER W:A->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    UNDISCH_TAC `ode_solution (p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (c:(A->bool)#(A->real^N))) tt)
        (interval(lift(--r),lift r) PCROSS (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N)))
        J (\t. pastecart ((Y:real^1->real^N) t) ((A:real^1->real^N) t))` THEN
    REWRITE_TAC[P2A_LSOL_ODE] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^1` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `b = (d / &2) pow 2` THEN
  SUBGOAL_THEN `&0 < b /\ sqrt b = d / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^1. &0 <= drop v /\ drop v pow 2 <= b ==> v IN J` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
    REWRITE_TAC[IN_BALL; DIST_0; NORM_REAL; GSYM drop] THEN
    SUBGOAL_THEN `drop v <= d / &2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM(ASSUME `sqrt b = d / &2`)] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[p2a_Ldom; IN_ELIM_THM] THEN
  EXISTS_TAC `\tau. chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^1->real^N)(lift(sqrt tau)))` THEN
  (* basic facts about the curve *)
  SUBGOAL_THEN `d / &2 < r` ASSUME_TAC THENL
   [SUBGOAL_THEN `lift(d / &2) IN (J:real^1->bool)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
      REWRITE_TAC[IN_BALL; DIST_0; NORM_LIFT] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th' ->
        can (find_term ((=) `--r`)) (concl th') && is_forall (concl th')))) THEN
      REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `b < tt - a` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `r pow 2 = tt - a`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^1. &0 <= drop v /\ drop v pow 2 <= b
               ==> chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^1->real^N)(lift(sqrt(drop v pow 2)))) =
                   chart_inv c (Y v) /\
                   chart_inv c (Y v) IN U INTER W /\
                   (phi:A->real^N)(chart_inv c (Y v)) = Y v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[POW_2_SQRT; LIFT_DROP] THEN
    SUBGOAL_THEN `(Y:real^1->real^N) v IN IMAGE (phi:A->real^N) (U INTER W)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "c" THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_Lgeod_from; p2a_Lgeod] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!v:real^1. &0 <= drop v /\ drop v pow 2 <= b
                           ==> ((Y:real^1->real^N) has_vector_derivative (A:real^1->real^N) v)
                                 (at v within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
                               (A has_vector_derivative
                                  p2a_lacc (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (c:(A->bool)#(A->real^N))) tt
                                           (drop v) (Y v) (A v))
                                 (at v within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (c:(A->bool)#(A->real^N))`; `tt:real`;
                   `interval(lift(--r),lift r) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `J:real^1->bool`; `Y:real^1->real^N`; `A:real^1->real^N`; `v:real^1`]
                  P2A_LSOL_AT) THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s pow 2 <= b ==> a < tt - s pow 2 /\ tt - s pow 2 <= tt`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN TRY(MP_TAC(SPEC `s:real` REAL_LE_POW_2)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* in the slices *)
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(sqrt tau)` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_SIMP_TAC[LIFT_DROP; SQRT_POS_LE; SQRT_POW_2] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`; `tt - tau`] P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    (* smooth points *)
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[p2a_smooth] THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `tt:real`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(sqrt tau)` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_SIMP_TAC[LIFT_DROP; SQRT_POS_LE; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    (* the chart pieces *)
    X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `tt:real`; `c:(A->bool)#(A->real^N)`;
                          `&1`; `A:real^1->real^N`] THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) = U INTER W` SUBST1_TAC THENL
       [EXPAND_TAC "c" THEN REWRITE_TAC[FST]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `SND(c:(A->bool)#(A->real^N)) = phi` SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[SND]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!v:real^1. &0 <= drop v /\ drop v pow 2 <= b
                 ==> (phi:A->real^N) (chart_inv (c:(A->bool)#(A->real^N))
                        ((Y:real^1->real^N) (lift (sqrt (drop v pow 2))))) = Y v`
    ASSUME_TAC THENL
     [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    TRY(MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
        MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `&1`] THEN
        ASM_SIMP_TAC[REAL_LT_01; IN_ELIM_THM]);
    (* gamma 0 = x *)
    REWRITE_TAC[SQRT_0; LIFT_NUM] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "c" THEN ASM_SIMP_TAC[];
    (* the initial vector *)
    SUBGOAL_THEN `&2 % (Z:real^N) = (A:real^1->real^N)(vec 0)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `&1`] THEN
    REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; DROP_VEC] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^1` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
      is_forall (concl th))) THEN
    REWRITE_TAC[DROP_VEC] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;


