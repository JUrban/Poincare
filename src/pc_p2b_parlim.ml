(* ========================================================================= *)
(* pc_p2b_parlim (Part 2B): the limit vector and the limit geodesics used by *)
(* SPLIT_ROUND, the two statements of pc_p2b_parlimreq:                      *)
(*   P2BPL_POINT_LIMIT: unit vectors with Ric = 0 at the base points of a   *)
(*     slice limit give, along a subsequence, a unit v at xl with           *)
(*     Ric_g0(v,v) = 0 and convergence of the rescaled pulled-back vectors; *)
(*   P2BPL_ORBIT_LIMIT: the rescaled slice geodesics converge to the        *)
(*     geodesics of the limit for |s| <= d.                                 *)
(* ========================================================================= *)

needs "src/pc_p2b_parlimreq.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_lrg_scale.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_p2a_lgeo2.ml";;
needs "src/pc_rf_basic.ml";;
needs "src/pc_mfd_restrict.ml";;
needs "src/pc_geo_local.ml";;
needs "src/pc_geo_max.ml";;
needs "src/pc_geo_hr.ml";;
needs "src/pc_geo_lisom.ml";;
needs "src/pc_ode_c1.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Preliminaries: chart independence of the C^m distance of two metrics, the *)
(* rescaled pullback metric field, and smoothness of continuous parallel     *)
(* fields.                                                                   *)
(* ========================================================================= *)

(* Chart independence of the C^m distance of two Riemannian metrics        *)
(* (manifold-level, chart_at convention) on an open set W: lck_dist2 is     *)
(* invariant under the chart transition (LCK_DIST2_PULLBACK on the overlap, *)
(* METRIC_LOCAL_TRANS, LCK_DIST2_LOCAL).                                    *)

let P2BPL_DIFFEO_ON_SUBSET = prove
 (`!s t (f:real^N->real^N) g s'.
     diffeomorphism_on s t f g /\ open s' /\ s' SUBSET s
     ==> diffeomorphism_on s' (IMAGE f s') f g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) s' = {y | y IN t /\ g y IN s'}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[] THEN NO_TAC) THEN
  ASM SET_TAC[]);;


let P2BPL_LCK_CHART_INDEP = prove
 (`!top atlas (h0:A->real^N^N) h1 W c c' y m.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     (!c. c IN atlas
          ==> metric_field (IMAGE (SND c) (FST c INTER W)) (metric_local atlas c h0) /\
              metric_field (IMAGE (SND c) (FST c INTER W)) (metric_local atlas c h1)) /\
     c IN atlas /\ c' IN atlas /\ y IN FST c /\ y IN FST c' /\ y IN W
     ==> lck_dist2 m (metric_local atlas c h0) (metric_local atlas c h1) (SND c y) =
         lck_dist2 m (metric_local atlas c' h0) (metric_local atlas c' h1) (SND c' y)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> SUBST1_TAC(GSYM(ISPEC t PAIR)))
    [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`] THEN
  MAP_EVERY (fun (v,t) -> SPEC_TAC(t,v))
   [(`psi:A->real^N`,`SND(c':(A->bool)#(A->real^N))`);
    (`V:A->bool`,`FST(c':(A->bool)#(A->real^N))`);
    (`phi:A->real^N`,`SND(c:(A->bool)#(A->real^N))`);
    (`U:A->bool`,`FST(c:(A->bool)#(A->real^N))`)] THEN
  REWRITE_TAC[FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U INTER V INTER W:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  ABBREV_TAC `O1 = IMAGE (phi:A->real^N) (U INTER V INTER W)` THEN
  ABBREV_TAC `O2 = IMAGE (psi:A->real^N) (U INTER V INTER W)` THEN
  ABBREV_TAC `tau = chart_trans (U:A->bool,phi:A->real^N) (V,psi)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "inv1" o CONJUNCT1) THEN
  SUBGOAL_THEN `!x. x IN U INTER V INTER W ==> (tau:real^N->real^N) ((phi:A->real^N) x) = psi x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "tau" THEN
    REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN
    USE_THEN "inv1" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (O1:real^N->bool) /\ open (O2:real^N->bool) /\
                (phi:A->real^N) y IN O1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O1"; "O2"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `U:A->bool`] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `V:A->bool`] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on O1 O2 (tau:real^N->real^N)
                  (chart_trans (V:A->bool,psi:A->real^N) (U,phi))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `O2 = IMAGE (tau:real^N->real^N) O1` SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["O1"; "O2"] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[o_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BPL_DIFFEO_ON_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (phi:A->real^N) (U INTER V)`;
                          `IMAGE (psi:A->real^N) (U INTER V)`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "tau" THEN MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      EXISTS_TAC `top:A topology` THEN EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "O1" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:A->real^N^N w. w IN O1
       ==> metric_local atlas (U,phi) h w =
           mpullback (tau:real^N->real^N) (metric_local atlas (V:A->bool,psi:A->real^N) h) w`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`h:A->real^N^N`; `w:real^N`] THEN EXPAND_TAC "O1" THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN EXPAND_TAC "tau" THEN
    MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field O2 (metric_local atlas (V:A->bool,psi:A->real^N) h0) /\
                metric_field O2 (metric_local atlas (V,psi) h1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field")) (concl th))) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER W)` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "O2" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 m (mpullback (tau:real^N->real^N)
                             (metric_local atlas (V:A->bool,psi:A->real^N) h0))
                          (mpullback tau (metric_local atlas (V,psi) h1)) ((phi:A->real^N) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `O1:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `O2:real^N->bool`; `O1:real^N->bool`; `tau:real^N->real^N`;
                 `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
                 `metric_local atlas (V:A->bool,psi:A->real^N) h0`;
                 `metric_local atlas (V:A->bool,psi:A->real^N) h1`;
                 `(phi:A->real^N) y`] LCK_DIST2_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* The rescaled pullback metric of a diffeomorphism f on W is a metric       *)
(* field on the chart pieces of W (locally the Euclidean pullback through    *)
(* the chart representative of f, MFDR_DIFFEO_CHART_REP).                   *)

let P2BPL_PULLBACK_METRIC_FIELD = prove
 (`!top atlas top' atlas' W W' (f:A->B) f' (g':B->real^N^N) Q c.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\
     &0 < Q /\ c IN atlas
     ==> metric_field (IMAGE (SND c) (FST c INTER W))
                      (metric_local atlas c (\x. Q %% mfd_pullback_metric atlas atlas' f g' x))`,
  REPEAT GEN_TAC THEN SUBST1_TAC(GSYM(ISPEC `c:(A->bool)#(A->real^N)` PAIR)) THEN
  SPEC_TAC(`SND(c:(A->bool)#(A->real^N))`,`phi:A->real^N`) THEN
  SPEC_TAC(`FST(c:(A->bool)#(A->real^N))`,`U:A->bool`) THEN
  REWRITE_TAC[FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) W
                   (top':B topology) (atlas':((B->bool)#(B->real^N))->bool) W' (f:A->B) f'` THEN
    SIMP_TAC[mfd_diffeo];
    ALL_TAC] THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `U:A->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B) x IN W' /\ (f:A->B) x IN topspace top'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a:B s t. a IN s /\ s SUBSET t ==> a IN s /\ a IN t`) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:A->B) W SUBSET W'` THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBSET THEN
      UNDISCH_TAC `mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) W
                     (top':B topology) (atlas':((B->bool)#(B->real^N))->bool) W' (f:A->B) f'` THEN
      SIMP_TAC[mfd_diffeo]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `(f:A->B) x`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBST1_TAC(GSYM(ISPEC `chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)` PAIR)) THEN
  SPEC_TAC(`SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x))`,`psi:B->real^N`) THEN
  SPEC_TAC(`FST(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x))`,`V:B->bool`) THEN
  REWRITE_TAC[FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W':B->bool`;
                 `f:A->B`; `f':B->A`; `U:A->bool`; `phi:A->real^N`; `V:B->bool`;
                 `psi:B->real^N`] MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) {x' | x' IN U INTER W /\ (f:A->B) x' IN V}` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN SIMP_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `\z. Q %% mpullback ((psi:B->real^N) o (f:A->B) o chart_inv (U,phi:A->real^N))
                                 (metric_local atlas' (V,psi) (g':B->real^N^N)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (psi:B->real^N) {y | y IN V INTER W' /\ (f':B->A) y IN U}`;
                          `(phi:A->real^N) o (f':B->A) o chart_inv (V,psi:B->real^N)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:B->real^N) V` THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas' (g':B->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:B->bool,psi:B->real^N)`) THEN ASM_REWRITE_TAC[FST; SND];
      CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN SIMP_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `x':A` THEN STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P2A_PULLBACK_METRIC_LOCAL_W THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `W:A->bool`; `top':B topology`; `W':B->bool`;
                        `f':B->A`] THEN
  ASM_REWRITE_TAC[]);;

(* A continuous solution of the parallel equation D Y = -Gamma(., Y)        *)
(* of a smooth metric field is smooth (bootstrap: if Y is C^n, the         *)
(* derivative z |-> -Gamma(z)(h, Y z) is C^n, so Y is C^(n+1)).            *)

let P2BPL_PARALLEL_BOOTSTRAP = prove
 (`!U (G:real^N->real^N^N) (Y:real^N->real^N).
     metric_field U G /\ Y continuous_on U /\
     (!z. z IN U ==> (Y has_derivative (\h. --(christoffel G z h (Y z)))) (at z))
     ==> smooth_map_on U Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[smooth_map_on] THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `\z h. --(christoffel (G:real^N->real^N^N) z h ((Y:real^N->real^N) z))` THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `h:real^N` THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_NEG_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `\z. vsum (1..dimindex(:N))
                    (\q. drop(lift(((Y:real^N->real^N) z)$q)) %
                         christoffel (G:real^N->real^N^N) z h (basis q))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LINEAR_APPLY_EXPAND THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]
           LRG_CHRISTOFFEL_LINEAR) THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\z. lift(((Y:real^N->real^N) z)$q)) = (\y:real^N. lift(y$q)) o Y`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
    ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `h:real^N`; `basis q:real^N`]
           LRG_CHRISTOFFEL_SMOOTH) THEN
    ASM_REWRITE_TAC[smooth_map_on] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Pullback metrics of a diffeomorphism at a point: surjective differential, *)
(* the metric and the Ricci tensor of the pullback in the preferred chart.   *)
(* ========================================================================= *)

let P2BPL_DIFF_SURJ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' x.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas W top' atlas' W' f f' /\ x IN W
     ==> linear (mfd_differential atlas atlas' f x) /\
         !y. ?z. mfd_differential atlas atlas' f x z = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `linear (mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                        (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `W:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(f:A->B) x IN W' /\ (x:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET; FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `W':B->bool`; `f:A->B`; `f':B->A`; `x:A`] GEOI_DIFF_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_differential (atlas:((A->bool)#(A->real^N))->bool) atlas ((f':B->A) o (f:A->B)) x =
                (\h:real^N. h)` SUBST1_TAC THENL
   [REWRITE_TAC[mfd_differential] THEN
    SUBGOAL_THEN `((f':B->A) o (f:A->B)) x = x` SUBST1_TAC THENL
     [REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) x`, `c:(A->bool)#(A->real^N)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`U0:A->bool`; `phi0:A->real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U0:A->bool`; `phi0:A->real^N`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `frechet_derivative (\y:real^N. y) (at ((phi0:A->real^N) x))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN
      EXISTS_TAC `IMAGE (phi0:A->real^N) (U0 INTER W)` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                              `U0:A->bool`] THEN
        ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
        REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
        ASM_SIMP_TAC[]];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC LINEAR_INJECTIVE_IMP_SURJECTIVE THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MAP_EVERY X_GEN_TAC [`w1:real^N`; `w2:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(AP_THM th `w1:real^N`) THEN MP_TAC(AP_THM th `w2:real^N`)) THEN
  ASM_REWRITE_TAC[o_THM] THEN MESON_TAC[]);;

(* The pullback metric at a point is the congruence of the target metric by *)
(* the matrix of the differential.                                           *)

let P2BPL_PB_METRIC_AT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    (f:A->B) (g':B->real^N^N) x.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     x IN topspace top /\ f x IN topspace top'
     ==> mfd_pullback_metric atlas atlas' f g' x =
         transp(matrix(mfd_differential atlas atlas' f x)) ** g'(f x) **
         matrix(mfd_differential atlas atlas' f x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_pullback_metric; mpullback; mfd_differential; o_DEF] THEN
  SUBGOAL_THEN `chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x)
                  (SND(chart_at atlas x) x) = (x:A)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) x`, `c:(A->bool)#(A->real^N)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`U0:A->bool`; `phi0:A->real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U0:A->bool`; `phi0:A->real^N`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `(f:A->B) x`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* A variant of P2B9S_PB_LOCAL_REP (pc_p2b_979s) with the local           *)
(* diffeomorphism named explicitly: the chart representative of psi,      *)
(* whose derivative is the differential.                                  *)

let P2BPL_PB_LOCAL_REP = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U
     ==> ?P P' K'.
           open P /\ SND(chart_at atlas y) y IN P /\
           diffeomorphism_on P P'
             (SND(chart_at atlas' (psi y)) o psi o chart_inv(chart_at atlas y)) K' /\
           metric_field P' (metric_local atlas' (chart_at atlas' (psi y)) g') /\
           (SND(chart_at atlas' (psi y)) o psi o chart_inv(chart_at atlas y))
             (SND(chart_at atlas y) y) = SND(chart_at atlas' (psi y)) (psi y) /\
           (!z. z IN P
                ==> metric_local atlas (chart_at atlas y)
                                 (mfd_pullback_metric atlas atlas' psi g') z =
                    mpullback (SND(chart_at atlas' (psi y)) o psi o chart_inv(chart_at atlas y))
                              (metric_local atlas' (chart_at atlas' (psi y)) g') z)`,
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


(* Naturality of the Ricci tensor under the pullback by a diffeomorphism.   *)

let P2BPL_PB_RICCI = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) y u v.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U
     ==> mfd_ricci atlas (mfd_pullback_metric atlas atlas' psi g') y u v =
         mfd_ricci atlas' g' (psi y) (mfd_differential atlas atlas' psi y u)
                                     (mfd_differential atlas atlas' psi y v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BPL_PB_LOCAL_REP) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `P':real^N->bool`
    (X_CHOOSE_THEN `K':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_ricci] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lricci (mpullback (SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((psi:A->B) y)) o psi o
                                 chart_inv(chart_at (atlas:((A->bool)#(A->real^N))->bool) y))
                       (metric_local atlas' (chart_at atlas' (psi y)) (g':B->real^N^N)))
                     (SND(chart_at atlas y) y) u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `P:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P':real^N->bool`; `P:real^N->bool`;
                 `SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((psi:A->B) y)) o psi o
                  chart_inv(chart_at (atlas:((A->bool)#(A->real^N))->bool) y)`;
                 `K':real^N->real^N`;
                 `metric_local (atlas':((B->bool)#(B->real^N))->bool) (chart_at atlas' ((psi:A->B) y))
                    (g':B->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) y) y`;
                 `u:real^N`; `v:real^N`] LRICCI_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mfd_differential; o_DEF]);;

(* ========================================================================= *)
(* The per-slice algebra of P2BPL_POINT_LIMIT and the uniform closeness of   *)
(* the rescaled pullbacks on compact sets.                                   *)
(* ========================================================================= *)

let P2BPL_LRICCI_CMUL2 = prove
 (`!U (G:real^N->real^N^N) y c u.
     metric_field U G /\ y IN U ==> lricci G y (c % u) (c % u) = c * c * lricci G y u u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lift(lricci (G:real^N->real^N^N) y (c % u) (c % u)) =
                c % lift(lricci G y u (c % u))` MP_TAC THENL
   [MP_TAC(ISPEC `\a. lift(lricci (G:real^N->real^N^N) y a (c % u))` LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lift(lricci (G:real^N->real^N^N) y u (c % u)) = c % lift(lricci G y u u)`
  MP_TAC THENL
   [MP_TAC(ISPEC `\b. lift(lricci (G:real^N->real^N^N) y u b)` LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P2BPL_QUAD_PULLBACK = prove
 (`!(M:real^N^N) G z. z dot ((transp M ** G ** M) ** z) = (M ** z) dot (G ** (M ** z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM VECTOR_MATRIX_MUL_TRANSP] THEN
  GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN REWRITE_TAC[DOT_LMUL_MATRIX] THEN
  MATCH_ACCEPT_TAC DOT_SYM);;

let P2BPL_QUAD_SCALE = prove
 (`!c Q (A:real^N^N) w. (c % w) dot ((Q %% A) ** (c % w)) = (c * c * Q) * (w dot (A ** w))`,
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

(* One slice: the vector z with D z = U, rescaled by 1/sqrt Q, is a unit    *)
(* null vector of the Ricci tensor of the rescaled pullback at the base.   *)

let P2BPL_POINT_ONE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' (g':B->real^N^N) Q x0 U.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\
     &0 < Q /\ x0 IN W /\
     U dot (g'(f x0) ** U) = &1 /\ mfd_ricci atlas' g' (f x0) U U = &0
     ==> ?z. mfd_differential atlas atlas' f x0 z = U /\
             (inv(sqrt Q) % z) dot
               (metric_local atlas (chart_at atlas x0)
                  (\y. Q %% mfd_pullback_metric atlas atlas' f g' y)
                  (SND(chart_at atlas x0) x0) ** (inv(sqrt Q) % z)) = &1 /\
             lricci (metric_local atlas (chart_at atlas x0)
                       (\y. Q %% mfd_pullback_metric atlas atlas' f g' y))
                    (SND(chart_at atlas x0) x0) (inv(sqrt Q) % z) (inv(sqrt Q) % z) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(x0:A) IN topspace top /\ (f:A->B) x0 IN topspace top'` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET; FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `W:A->bool`; `W':B->bool`; `f:A->B`; `f':B->A`; `x0:A`] P2BPL_DIFF_SURJ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `z:real^N` o SPEC `U:real^N`)) THEN
  EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas' (f:A->B) (g':B->real^N^N)`; `x0:A`]
                METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g':B->real^N^N`; `x0:A`] P2BPL_PB_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[P2BPL_QUAD_SCALE; P2BPL_QUAD_PULLBACK; MATRIX_WORKS; REAL_MUL_RID] THEN
    MP_TAC(SPEC `Q:real` SQRT_POW_2) THEN MP_TAC(SPEC `Q:real` SQRT_POS_LT) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `W:A->bool`; `W':B->bool`; `f:A->B`; `f':B->A`; `g':B->real^N^N`; `x0:A`]
                P2B9S_PB_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `P0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`P0:real^N->bool`;
                 `metric_local atlas (chart_at atlas x0)
                    (mfd_pullback_metric (atlas:((A->bool)#(A->real^N))->bool) atlas' (f:A->B)
                                         (g':B->real^N^N))`;
                 `Q:real`; `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x0) x0`;
                 `inv(sqrt Q) % z:real^N`; `inv(sqrt Q) % z:real^N`] LRICCI_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`P0:real^N->bool`;
                 `metric_local atlas (chart_at atlas x0)
                    (mfd_pullback_metric (atlas:((A->bool)#(A->real^N))->bool) atlas' (f:A->B)
                                         (g':B->real^N^N))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x0) x0`;
                 `inv(sqrt Q)`; `z:real^N`] P2BPL_LRICCI_CMUL2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM mfd_ricci] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `W:A->bool`; `W':B->bool`; `f:A->B`; `f':B->A`; `g':B->real^N^N`; `x0:A`;
                 `z:real^N`; `z:real^N`] P2BPL_PB_RICCI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

(* The slice limit in the manifold form: uniform C^m closeness of g0 and   *)
(* the rescaled pullbacks of the slice metrics on a compact set K.         *)

let P2BPL_SLICE_CLOSE = prove
 (`!V x t Q (top:B topology) atlas g0 xl W phi K m eta.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                        (real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (t n))
                                (rfs_vatlas (V n) (t n)) /\
          riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))) /\
     compact_in top K /\ &0 < eta
     ==> ?n0. !n. n0 <= n
             ==> K SUBSET W n /\
                 !y. y IN K
                     ==> lck_dist2 m (metric_local atlas (chart_at atlas y) g0)
                           (metric_local atlas (chart_at atlas y)
                              (\z. Q n %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                           (rfs_vmetric (V n) (t n)) z))
                           (SND(chart_at atlas y) y) < eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  SUBGOAL_THEN `&0 < &2 pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`K:B->bool`; `m:num`; `eta / &2 pow m`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `n:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) n) (t n)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) n) (t n)`;
                 `(W:num->B->bool) n`; `IMAGE ((phi:num->B->A) n) (W n)`; `(phi:num->B->A) n`;
                 `psi:A->B`; `g0:B->real^3^3`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) n) (t n)`;
                 `&1`; `(Q:num->real) n`; `m:num`; `y:B`] P2BL_LCK_CHART_CONVERT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_CMUL_LID; ETA_AX; REAL_MUL_LID; REAL_INV_1;
              REAL_ARITH `&1 + &1 = &2`] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REAL_ARITH `!a b c e:real. a <= c * b ==> c * b < e ==> a < e`)) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
  USE_THEN "sl" (MP_TAC o SPEC `y:B`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The limit at the base point (Euclidean form) and the main theorem         *)
(* P2BPL_POINT_LIMIT.                                                        *)
(* ========================================================================= *)

let P2BPL_LE_ONE_PLUS_SQUARE = prove
 (`!a. a <= &1 + a pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `a - &1 / &2` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

(* A limit of the quadratic forms of a fixed matrix along a convergent      *)
(* sequence of vectors.                                                      *)

let P2BPL_QUAD_LIM = prove
 (`!(A:real^N^N) (f:num->real^N) v.
     (f --> v) sequentially
     ==> ((\k. lift(f k dot (A ** f k))) --> lift(v dot (A ** v))) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sequentially`; `\x y:real^N. lift(x dot y)`; `f:num->real^N`;
                 `\k. (A:real^N^N) ** (f:num->real^N) k`; `v:real^N`; `(A:real^N^N) ** v`]
                LIM_BILINEAR) THEN
  REWRITE_TAC[BILINEAR_DOT] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`sequentially`; `\x:real^N. (A:real^N^N) ** x`; `f:num->real^N`; `v:real^N`]
                  LIM_LINEAR) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    REWRITE_TAC[]]);;

(* The Ricci quadratic form as the quadratic form of its matrix.           *)

let P2BPL_LRICCI_QUAD = prove
 (`!U (G:real^N->real^N^N) y u.
     metric_field U G /\ y IN U
     ==> lricci G y u u = u dot ((lambda i j. lricci G y (basis i) (basis j)):real^N^N ** u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:real^N`; `u:real^N`]
                LRG_LRICCI_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot; LAMBDA_BETA] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

(* Metrics converging in C^2 at a point p, with unit vectors that are null *)
(* for the Ricci tensors: a subsequence of the vectors converges to a unit  *)
(* null vector of the limit.                                                 *)

let P2BPL_ABSTRACT_LIMIT = prove
 (`!(G0:real^N->real^N^N) (G:num->real^N->real^N^N) s p (w:num->real^N).
     (!n. metric_field (s n) G0 /\ metric_field (s n) (G n) /\ p IN s n) /\
     (!eta. &0 < eta ==> ?n0. !n. n0 <= n ==> lck_dist2 2 G0 (G n) p < eta) /\
     (!n. w n dot (G n p ** w n) = &1 /\ lricci (G n) p (w n) (w n) = &0)
     ==> ?sub v. p3_subseq sub /\ v dot (G0 p ** v) = &1 /\ lricci G0 p v v = &0 /\
                 ((\n. w(sub n)) --> v) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mf") (CONJUNCTS_THEN2 (LABEL_TAC "cl") (LABEL_TAC "wn"))) THEN
  (* coercivity of G0 at p *)
  SUBGOAL_THEN `?m0. &0 < m0 /\ !v. m0 * norm v pow 2 <= v dot ((G0:real^N->real^N^N) p ** v)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_POSDEF_LOWER THEN
    USE_THEN "mf" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[metric_field] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= (w:num->real^N) n dot ((G0:real^N->real^N^N) p ** w n)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_NONNEG THEN
    EXISTS_TAC `(s:num->real^N->bool) n` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* C^0 closeness of the quadratic forms *)
  SUBGOAL_THEN `!n eta. &0 < eta /\ lck_dist2 2 (G0:real^N->real^N^N) (G n) p < eta pow 2
                ==> abs(&1 - (w:num->real^N) n dot (G0 p ** w n)) <= eta * (w n dot (G0 p ** w n))`
  (LABEL_TAC "eta") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`2`; `(s:num->real^N->bool) n`; `G0:real^N->real^N^N`;
                   `(G:num->real^N->real^N^N) n`; `p:real^N`; `(w:num->real^N) n`] LCK_DIST_C0) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "wn" (MP_TAC o SPEC `n:num`) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 2 (G0:real^N->real^N^N) (G n) p) *
                ((w:num->real^N) n dot (G0 p ** w n))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* eventually the quadratic forms are at most 2 *)
  USE_THEN "cl" (MP_TAC o SPEC `&1 / &4`) THEN REWRITE_TAC[REAL_ARITH `&0 < &1 / &4`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  SUBGOAL_THEN `!n. N1 <= n ==> (w:num->real^N) n dot ((G0:real^N->real^N^N) p ** w n) <= &2`
  (LABEL_TAC "le2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "eta" (MP_TAC o SPECL [`n:num`; `&1 / &2`]) THEN
    ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* a convergent subsequence *)
  MP_TAC(ISPECL [`vec 0:real^N`; `&1 + &2 / m0`] COMPACT_CBALL) THEN
  REWRITE_TAC[compact] THEN DISCH_THEN(MP_TAC o SPEC `\k. (w:num->real^N) (N1 + k)`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_CBALL_0] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + norm((w:num->real^N)(N1 + k)) pow 2` THEN
    REWRITE_TAC[P2BPL_LE_ONE_PLUS_SQUARE; REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(w:num->real^N)(N1 + k) dot ((G0:real^N->real^N^N) p ** w(N1 + k))` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
      USE_THEN "le2" MATCH_MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `((\k. (w:num->real^N)(N1 + (r:num->num) k)) --> v) sequentially` (LABEL_TAC "conv") THENL
   [UNDISCH_TAC `((\k. (w:num->real^N)(N1 + k)) o r --> v) sequentially` THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `!eta. &0 < eta
                ==> ?k0. !k. k0 <= k
                         ==> lck_dist2 2 (G0:real^N->real^N^N) (G(N1 + (r:num->num) k)) p < eta`
  (LABEL_TAC "clsub") THENL
   [X_GEN_TAC `eta:real` THEN DISCH_TAC THEN USE_THEN "cl" (MP_TAC o SPEC `eta:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPEC `r:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `n0:num <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\k. N1 + (r:num->num) k`; `v:real^N`] THEN
  ASM_REWRITE_TAC[p3_subseq; LT_ADD_LCANCEL] THEN CONJ_TAC THENL
   [(* the unit length *)
    MP_TAC(ISPECL [`sequentially`;
                   `\k. lift((w:num->real^N)(N1 + (r:num->num) k) dot ((G0:real^N->real^N^N) p ** w(N1 + r k)))`;
                   `lift(v dot ((G0:real^N->real^N^N) p ** v))`; `lift(&1)`] LIM_UNIQUE) THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIFT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BPL_QUAD_LIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "clsub" (MP_TAC o SPEC `(e / &3) pow 2`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN DISCH_TAC THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "eta" (MP_TAC o SPECL [`N1 + (r:num->num) k`; `e / &3`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "le2" (MP_TAC o SPEC `N1 + (r:num->num) k`) THEN REWRITE_TAC[LE_ADD] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `e / &3 * ((w:num->real^N)(N1 + (r:num->num) k) dot ((G0:real^N->real^N^N) p ** w(N1 + r k)))
                  <= e / &3 * &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the Ricci tensor *)
  SUBGOAL_THEN `!u. lricci (G0:real^N->real^N^N) p u u =
                    u dot ((lambda i j. lricci G0 p (basis i) (basis j)):real^N^N ** u)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BPL_LRICCI_QUAD THEN
    EXISTS_TAC `(s:num->real^N->bool) 0` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\k. lift(lricci (G0:real^N->real^N^N) p ((w:num->real^N)(N1 + (r:num->num) k))
                                   (w(N1 + r k)))`;
                 `lift(lricci (G0:real^N->real^N^N) p v v)`; `lift(&0)`] LIM_UNIQUE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIFT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BPL_QUAD_LIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sqrt(abs(lrm_deriv_norm2 0 (G0:real^N->real^N^N) p))`; `e / &3`]
                LCK_CURVATURE_STABILITY) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "stab"))) THEN
  USE_THEN "clsub" (MP_TAC o SPEC `eta0 pow 2`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN DISCH_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "stab" (MP_TAC o SPECL [`(s:num->real^N->bool)(N1 + (r:num->num) k)`;
                                   `G0:real^N->real^N^N`;
                                   `(G:num->real^N->real^N^N)(N1 + (r:num->num) k)`; `p:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_ABS_POS] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(w:num->real^N)(N1 + (r:num->num) k)` o CONJUNCT1 o CONJUNCT2) THEN
  USE_THEN "wn" (MP_TAC o SPEC `N1 + (r:num->num) k`) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  USE_THEN "le2" (MP_TAC o SPEC `N1 + (r:num->num) k`) THEN REWRITE_TAC[LE_ADD] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `e / &3 * ((w:num->real^N)(N1 + (r:num->num) k) dot
                          ((G0:real^N->real^N^N) p ** w(N1 + r k))) <= e / &3 * &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The headline POINT.                                                        *)
(* ------------------------------------------------------------------------- *)

let P2BPL_POINT_LIMIT = prove
 (`!(u:A->bool) (w:B->bool). P2BPL_POINT_LIMIT_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BPL_POINT_LIMIT_STATEMENT] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `psi:num->A->B` o GEN_REWRITE_RULE I [SKOLEM_THM] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* one slice at a time *)
  SUBGOAL_THEN
   `!n. ?z. mfd_differential atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) ((phi:num->B->A) n) xl z =
            (U:num->real^3) n /\
            (inv(sqrt((Q:num->real) n)) % z) dot
              (metric_local atlas (chart_at atlas xl)
                 (\y. Q n %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                (rfs_vmetric (V n) (t n)) y)
                 (SND(chart_at atlas xl) xl) ** (inv(sqrt(Q n)) % z)) = &1 /\
            lricci (metric_local atlas (chart_at atlas xl)
                      (\y. Q n %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                     (rfs_vmetric (V n) (t n)) y))
                   (SND(chart_at atlas xl) xl) (inv(sqrt(Q n)) % z) (inv(sqrt(Q n)) % z) = &0`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                   `(W:num->B->bool) n`; `IMAGE ((phi:num->B->A) n) (W n)`; `(phi:num->B->A) n`;
                   `(psi:num->A->B) n`; `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`; `(Q:num->real) n`; `xl:B`;
                   `(U:num->real^3) n`] P2BPL_POINT_ONE) THEN
    ANTS_TAC THENL [USE_THEN "sl" (MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `zz:num->real^3` (LABEL_TAC "zz") o GEN_REWRITE_RULE I [SKOLEM_THM]) THEN
  (* the Euclidean limit at the chart point of xl *)
  MP_TAC(ISPECL
   [`metric_local atlas (chart_at atlas xl) (g0:B->real^3^3)`;
    `\n. metric_local atlas (chart_at atlas xl)
           (\y. Q n %% mfd_pullback_metric atlas (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)) ((phi:num->B->A) n)
                          (rfs_vmetric (V n) (t n)) y)`;
    `\n. IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B))) (FST(chart_at atlas xl) INTER (W:num->B->bool) n)`;
    `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B)) xl`;
    `\n. inv(sqrt((Q:num->real) n)) % (zz:num->real^3) n`] P2BPL_ABSTRACT_LIMIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      SUBGOAL_THEN `open_in top (FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B)) INTER (W:num->B->bool) n)` ASSUME_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[] THEN
        MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B)`] MFDM_CHART) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `open (IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B))) (FST(chart_at atlas xl) INTER
                                                             (W:num->B->bool) n))` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B))`; `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B))`;
                       `FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B)) INTER (W:num->B->bool) n`] CHART_IMAGE_OPEN) THEN
        ASM_REWRITE_TAC[PAIR; INTER_SUBSET];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
        EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B))) (FST(chart_at atlas xl))` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `riemannian_metric atlas (g0:B->real^3^3)` THEN
          REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
        MATCH_MP_TAC P2BPL_PULLBACK_METRIC_FIELD THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`; `IMAGE ((phi:num->B->A) n) (W n)`;
                              `(psi:num->A->B) n`] THEN
        USE_THEN "sl" (MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[IN_INTER]];
      X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                     `W:num->B->bool`; `phi:num->B->A`; `{xl:B}`; `2`; `eta:real`]
                    P2BPL_SLICE_CLOSE) THEN
      ASM_REWRITE_TAC[COMPACT_IN_SING] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN
      DISCH_THEN(fun th -> X_GEN_TAC `n:num` THEN DISCH_TAC THEN MP_TAC(SPEC `n:num` th)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `xl:B` o CONJUNCT2) THEN
      REWRITE_TAC[IN_SING] THEN DISCH_THEN ACCEPT_TAC;
      X_GEN_TAC `n:num` THEN USE_THEN "zz" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `v:real^3`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  REPEAT CONJ_TAC THENL
   [ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[mfd_ricci];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "-->")) (concl th))) THEN
  ASM_REWRITE_TAC[dist] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  EXISTS_TAC `(zz:num->real^3)((sub:num->num) n)` THEN
  USE_THEN "zz" (MP_TAC o SPEC `(sub:num->num) n`) THEN SIMP_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The geodesic equation under a chart representative that pulls the metric  *)
(* back (a generalization of GEOI_GEODESIC_REP of pc_geo_lisom, with the     *)
(* same proof: the metric of the target need only be a metric field near the *)
(* image of the representative, not a Riemannian metric of the whole         *)
(* target).                                                                  *)
(* ========================================================================= *)

let P2BPL_GEODESIC_REP = prove
 (`!top atlas (g:A->real^N^N) (atlas':((B->bool)#(B->real^N))->bool) (g':B->real^N^N)
    W (f:A->B) (gamma:real->A) J c c' v t D Fr O'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ real_open J /\
     continuous_map (subtopology euclideanreal J,top) gamma /\
     (!t. t IN J ==> gamma t IN W) /\
     (!t. t IN J /\ gamma t IN FST c
          ==> ((\s. SND c (gamma(drop s))) has_vector_derivative v t) (at (lift t)) /\
              ((\s. v(drop s)) has_vector_derivative
               --(christoffel (metric_local atlas c g) (SND c (gamma t)) (v t) (v t)))
              (at (lift t))) /\
     open_in top {x | x IN FST c INTER W /\ f x IN FST c'} /\
     IMAGE (SND c) {x | x IN FST c INTER W /\ f x IN FST c'} = D /\
     SND c' o f o chart_inv c = Fr /\
     open D /\ smooth_map_on D Fr /\
     (!y. y IN D
          ==> metric_local atlas c g y = mpullback Fr (metric_local atlas' c' g') y /\
              Fr y IN O' /\ ~(det(matrix(frechet_derivative Fr (at y))) = &0)) /\
     metric_field O' (metric_local atlas' c' g') /\
     t IN J /\ gamma t IN FST c /\ f(gamma t) IN FST c'
     ==> ((\s. SND c' (f(gamma(drop s)))) has_vector_derivative
          frechet_derivative Fr (at (SND c (gamma t))) (v t)) (at (lift t)) /\
         ((\s. frechet_derivative Fr (at (SND c (gamma(drop s)))) (v(drop s)))
          has_vector_derivative
          --(christoffel (metric_local atlas' c' g') (SND c' (f(gamma t)))
               (frechet_derivative Fr (at (SND c (gamma t))) (v t))
               (frechet_derivative Fr (at (SND c (gamma t))) (v t))))
         (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP
   (CONJ (ASSUME `(t:real) IN J`)
         (ASSUME `(gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))`))) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "pt" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mpullback")) (concl th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t) IN D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the curve stays in the chart domains near t *)
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `{x | x IN FST (c:(A->bool)#(A->real^N)) INTER W /\
                       (f:A->B) x IN FST (c':(B->bool)#(B->real^N))}`;
                 `t:real`] GEOL_CURVE_NEAR) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Fr:real^N->real^N) differentiable at
                (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(Fr:real^N->real^N) o (\s. SND (c:(A->bool)#(A->real^N))
                                              ((gamma:real->A)(drop s)))` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs(drop s - t) < d` ASSUME_TAC THENL
       [UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
        ALL_TAC] THEN
      EXPAND_TAC "Fr" THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x:A. x IN FST (c:(A->bool)#(A->real^N)) ==> chart_inv c (SND c x) = x`)
        (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
    MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN
    ASM_REWRITE_TAC[WITHIN_UNIV; LIFT_DROP] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  (* the second order equation *)
  MP_TAC(ISPECL
   [`D:real^N->bool`; `Fr:real^N->real^N`;
    `\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
    `\s. (v:real->real^N)(drop s)`; `(v:real->real^N) t`;
    `--(christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                    (SND c ((gamma:real->A) t)) ((v:real->real^N) t) (v t))`;
    `lift t`] GEOL_FRECHET_ALONG) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Fr:real^N->real^N)
                         (at (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* invert Fr near the point *)
  MP_TAC(ISPECL [`Fr:real^N->real^N`; `D:real^N->bool`;
                 `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` (X_CHOOSE_THEN `u0:real^N->bool`
    (X_CHOOSE_THEN `Fi:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(u0:real^N->bool) SUBSET O'`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `diffeomorphism_on t0 u0 (Fr:real^N->real^N) Fi`) THEN
    REWRITE_TAC[diffeomorphism_on] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[SYM(CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "pt" (MP_TAC o SPEC `z:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (Fr:real^N->real^N)
      (at (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)))
      (christoffel (metric_local atlas c (g:A->real^N^N))
                   (SND c (gamma t)) ((v:real->real^N) t) (v t)) =
    christoffel (metric_local atlas' (c':(B->bool)#(B->real^N)) (g':B->real^N^N))
                (Fr (SND c (gamma t)))
                (frechet_derivative Fr (at (SND c (gamma t))) (v t))
                (frechet_derivative Fr (at (SND c (gamma t))) (v t)) +
    dd2 Fr (SND c (gamma t)) (v t) (v t)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                  (SND c ((gamma:real->A) t)) ((v:real->real^N) t) (v t) =
      christoffel (mpullback (Fr:real^N->real^N)
                     (metric_local atlas' (c':(B->bool)#(B->real^N)) (g':B->real^N^N)))
                  (SND c (gamma t)) (v t) (v t)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `D:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      USE_THEN "pt" (MP_TAC o SPEC `z:real^N`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LCHRISTOFFEL_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`u0:real^N->bool`; `t0:real^N->bool`; `Fi:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `O':real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Fr:real^N->real^N) (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)) =
    SND (c':(B->bool)#(B->real^N)) ((f:A->B)(gamma t))`
  SUBST1_TAC THENL
   [EXPAND_TAC "Fr" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[dd2] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[LINEAR_NEG] THEN
  MATCH_MP_TAC(MESON[] `(a:real^N) = b ==> (f has_vector_derivative a) net
                                         ==> (f has_vector_derivative b) net`) THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* A geodesic of the target, pulled back by the inverse of a diffeomorphism  *)
(* f, solves in a chart c0 of the source the geodesic equation of the        *)
(* pullback metric of f.                                                     *)
(* ========================================================================= *)

let P2BPL_MPULLBACK_LOCAL_ID = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N) z s.
     open s /\ z IN s /\ (!x. x IN s ==> h x = x) ==> mpullback h G z = G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (h:real^N->real^N) (at z) = (\x. x)` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `frechet_derivative (\x:real^N. x) (at z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID]];
    ASM_SIMP_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]]);;

let P2BPL_DIFFEO_DET = prove
 (`!U V (h:real^N->real^N) k x.
     diffeomorphism_on U V h k /\ x IN U
     ==> ~(det(matrix(frechet_derivative h (at x))) = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at x))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    UNDISCH_TAC `diffeomorphism_on U V (h:real^N->real^N) k` THEN
    SIMP_TAC[diffeomorphism_on] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `det(matrix(frechet_derivative (h:real^N->real^N) (at x))) = &0` THEN
  REWRITE_TAC[GSYM INVERTIBLE_DET_NZ; INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`;
                 `x:real^N`] ODE_DIFFEO_DERIVATIVE_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `frechet_derivative (k:real^N->real^N) (at ((h:real^N->real^N) x))` o
    check (fun th -> is_eq(concl th) && not(is_forall(concl th)))) THEN
  ASM_REWRITE_TAC[]);;

let P2BPL_PULLBACK_GEODESIC = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' (g':B->real^N^N) (gamma:real->B) J c0 t.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\
     mfd_geodesic (top',atlas') g' gamma J /\ (!s. s IN J ==> gamma s IN W') /\
     c0 IN atlas /\ t IN J /\ f'(gamma t) IN FST c0
     ==> ((\s. SND c0 (f'(gamma(drop s)))) has_vector_derivative
          vector_derivative (\s. SND c0 (f'(gamma(drop s)))) (at (lift t))) (at (lift t)) /\
         ((\s. vector_derivative (\r. SND c0 (f'(gamma(drop r)))) (at s)) has_vector_derivative
          --(christoffel (metric_local atlas c0 (mfd_pullback_metric atlas atlas' f g'))
                (SND c0 (f'(gamma t)))
                (vector_derivative (\s. SND c0 (f'(gamma(drop s)))) (at (lift t)))
                (vector_derivative (\s. SND c0 (f'(gamma(drop s)))) (at (lift t)))))
         (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (W':B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->B) t IN topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?c1. c1 IN atlas' /\ (gamma:real->B) t IN FST (c1:(B->bool)#(B->real^N))`
  (X_CHOOSE_THEN `c1:(B->bool)#(B->real^N)` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[CHART_AT]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_geodesic] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_geodesic")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `c1:(B->bool)#(B->real^N)`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `vv:real->real^N`) THEN
  (* the chart data *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^N))->bool`; `c1:(B->bool)#(B->real^N)`;
                 `c0:(A->bool)#(A->real^N)`; `W':B->bool`; `f':B->A`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W':B->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `f':B->A`; `f:A->B`; `FST(c1:(B->bool)#(B->real^N))`; `SND(c1:(B->bool)#(B->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "diffeomorphism_on")) (concl th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`; `f:A->B`;
                 `f':B->A`; `g':B->real^N^N`; `&1`; `c0:(A->bool)#(A->real^N)`]
                P2BPL_PULLBACK_METRIC_FIELD) THEN
  ASM_REWRITE_TAC[REAL_LT_01; METRIC_LOCAL_CMUL; MATRIX_CMUL_LID; ETA_AX] THEN DISCH_TAC THEN
  (* the metric of the target is the pullback of the pullback metric *)
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND (c1:(B->bool)#(B->real^N))) {x | x IN FST c1 INTER W' /\ (f':B->A) x IN FST (c0:(A->bool)#(A->real^N))}
        ==> metric_local atlas' (c1:(B->bool)#(B->real^N)) (g':B->real^N^N) y =
            mpullback (SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) (metric_local atlas (c0:(A->bool)#(A->real^N)) (mfd_pullback_metric atlas atlas' (f:A->B) (g':B->real^N^N))) y /\
            (SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) y IN IMAGE (SND c0) (FST c0 INTER W) /\
            ~(det(matrix(frechet_derivative (SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) (at y))) = &0)`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) y IN IMAGE (SND (c0:(A->bool)#(A->real^N))) {y | y IN FST c0 INTER W /\ (f:A->B) y IN FST (c1:(B->bool)#(B->real^N))}` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `(SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) y IN IMAGE (SND (c0:(A->bool)#(A->real^N))) {y | y IN FST c0 INTER W /\ (f:A->B) y IN FST (c1:(B->bool)#(B->real^N))}` THEN SET_TAC[];
      MATCH_MP_TAC P2BPL_DIFFEO_DET THEN MAP_EVERY EXISTS_TAC [`IMAGE (SND (c1:(B->bool)#(B->real^N))) {x | x IN FST c1 INTER W' /\ (f':B->A) x IN FST (c0:(A->bool)#(A->real^N))}`; `IMAGE (SND (c0:(A->bool)#(A->real^N))) {y | y IN FST c0 INTER W /\ (f:A->B) y IN FST (c1:(B->bool)#(B->real^N))}`; `SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))`] THEN
      ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mpullback (SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) (mpullback (SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))) (metric_local atlas' (c1:(B->bool)#(B->real^N))
                                           (g':B->real^N^N))) y` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))`; `metric_local atlas' (c1:(B->bool)#(B->real^N)) (g':B->real^N^N)`;
                     `y:real^N`] P2A_MPULLBACK_COMPOSE) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
         [EXISTS_TAC `IMAGE (SND (c1:(B->bool)#(B->real^N))) {x | x IN FST c1 INTER W' /\ (f':B->A) x IN FST (c0:(A->bool)#(A->real^N))}` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) {y | y IN FST c0 INTER W /\ (f:A->B) y IN FST (c1:(B->bool)#(B->real^N))}` THEN ASM_REWRITE_TAC[]];
        DISCH_THEN SUBST1_TAC] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BPL_MPULLBACK_LOCAL_ID THEN
      EXISTS_TAC `IMAGE (SND (c1:(B->bool)#(B->real^N))) {x | x IN FST c1 INTER W' /\ (f':B->A) x IN FST (c0:(A->bool)#(A->real^N))}` THEN ASM_SIMP_TAC[o_THM];
      ALL_TAC] THEN
    UNDISCH_TAC `y IN IMAGE (SND (c1:(B->bool)#(B->real^N))) {x | x IN FST c1 INTER W' /\ (f':B->A) x IN FST (c0:(A->bool)#(A->real^N))}` THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `c1:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N)))
                    (SND c1 (x:B)) = SND (c0:(A->bool)#(A->real^N)) ((f':B->A) x)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W':B->bool`;
                   `f:A->B`; `f':B->A`; `g':B->real^N^N`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `FST(c1:(B->bool)#(B->real^N))`; `SND(c1:(B->bool)#(B->real^N))`;
                   `(f':B->A) x`] P2A_PULLBACK_METRIC_LOCAL_W) THEN
    ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mpullback] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the representative at every time near t *)
  SUBGOAL_THEN
   `!s0. s0 IN J /\ (gamma:real->B) s0 IN FST (c1:(B->bool)#(B->real^N)) /\
         (f':B->A)(gamma s0) IN FST (c0:(A->bool)#(A->real^N))
         ==> ((\s. SND c0 (f'(gamma(drop s)))) has_vector_derivative
              frechet_derivative (SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) (at (SND c1 (gamma s0))) ((vv:real->real^N) s0))
             (at (lift s0)) /\
             ((\s. frechet_derivative (SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) (at (SND c1 (gamma(drop s)))) (vv(drop s)))
              has_vector_derivative
              --(christoffel (metric_local atlas c0 (mfd_pullback_metric atlas atlas' (f:A->B) (g':B->real^N^N))) (SND c0 (f'(gamma s0)))
                   (frechet_derivative (SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) (at (SND c1 (gamma s0))) (vv s0))
                   (frechet_derivative (SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) (at (SND c1 (gamma s0))) (vv s0))))
             (at (lift s0))`
  (LABEL_TAC "loc") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2BPL_GEODESIC_REP THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                          `g':B->real^N^N`; `W':B->bool`; `J:real->bool`; `IMAGE (SND (c1:(B->bool)#(B->real^N))) {x | x IN FST c1 INTER W' /\ (f':B->A) x IN FST (c0:(A->bool)#(A->real^N))}`;
                          `IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0 INTER W)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP VECTOR_DERIVATIVE_AT o check (fun th ->
    can (find_term ((=) `f':B->A`)) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "christoffel")) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top':B topology`; `gamma:real->B`; `J:real->bool`;
                 `{x | x IN FST (c1:(B->bool)#(B->real^N)) INTER W' /\
                       (f':B->A) x IN FST (c0:(A->bool)#(A->real^N))}`;
                 `t:real`] GEOL_CURVE_NEAR) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. frechet_derivative (SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) (at (SND c1 ((gamma:real->B)(drop s))))
                                    ((vv:real->real^N)(drop s))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(drop s - t) < d` ASSUME_TAC THENL
   [UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
    ALL_TAC] THEN
  USE_THEN "near" (MP_TAC o SPEC `drop s`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN STRIP_TAC] THEN
  USE_THEN "loc" (MP_TAC o SPEC `drop s`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[LIFT_DROP]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP VECTOR_DERIVATIVE_AT o CONJUNCT1) THEN
  SIMP_TAC[]);;

(* ========================================================================= *)
(* Christoffel symbols of C^1-close metrics are close (pointwise, in         *)
(* Euclidean norms), and the geodesic spray of a metric field is Lipschitz   *)
(* on compact sets.                                                          *)
(* ========================================================================= *)

let P2BPL_CHRISTOFFEL_CLOSE = prove
 (`!s (G0:real^N->real^N^N) G y lam Lam delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ &0 < lam /\
     (!v. lam * norm v pow 2 <= v dot (G0 y ** v) /\ v dot (G0 y ** v) <= Lam * norm v pow 2) /\
     &0 <= delta /\ delta <= &1 / &10 /\ lck_dist2 1 G0 G y <= delta pow 2
     ==> !a b. norm(christoffel G y a b - christoffel G0 y a b) <=
               &2 * delta * Lam / sqrt lam * norm a * norm b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(lck_dist2 1 (G0:real^N->real^N^N) G y) <= delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(delta pow 2)` THEN
    ASM_SIMP_TAC[SQRT_MONO_LE; POW_2_SQRT; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. abs(a dot ((G:real^N->real^N^N) y ** b) - a dot (G0 y ** b)) <=
          delta * norm((M:real^N^N) ** a) * norm(M ** b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 1 (G0:real^N->real^N^N) G y) *
                norm((M:real^N^N) ** a) * norm(M ** b)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                     `y:real^N`; `M:real^N^N`; `\m. if m = 1 then (a:real^N) else b`;
                     `lck_dist2 1 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MP_TAC(ISPECL [`1`; `0`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                       `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
        ASM_REWRITE_TAC[LE_0; lnabla_iter; ADD_CLAUSES];
        REWRITE_TAC[PRODUCT_2; lmetric2; ARITH; REAL_MUL_ASSOC]];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lnabla 2 (G0:real^N->real^N^N)
              (\x u. lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u) y u) <=
        delta * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 1 (G0:real^N->real^N^N) G y) *
                norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `lnabla 2 (G0:real^N->real^N^N)
                        (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
                     `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                     `lck_dist2 1 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
      ASM_REWRITE_TAC[PRODUCT_3] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`1`; `1`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
      REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_A) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Euclidean norms *)
  SUBGOAL_THEN `!v:real^N. norm((M:real^N^N) ** v) pow 2 = v dot ((G0:real^N->real^N^N) y ** v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(G0:real^N->real^N^N) y = transp (M:real^N^N) ** M` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[NORM_POW_2; GSYM MATRIX_VECTOR_MUL_ASSOC; GSYM VECTOR_MATRIX_MUL_TRANSP] THEN
    GEN_REWRITE_TAC RAND_CONV [DOT_SYM] THEN REWRITE_TAC[DOT_LMUL_MATRIX];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Lam` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `basis 1:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Lam:real`)) (concl th))) THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_POW_ONE; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. norm((M:real^N^N) ** v) <= sqrt Lam * norm v /\
                           sqrt lam * norm v <= norm(M ** v)` ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_LT_IMP_LE; NORM_POS_LE; REAL_POW_MUL;
                 SQRT_POW_2; ARITH];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((M:real^N^N) ** (christoffel G y a b - christoffel G0 y a b)) / sqrt lam` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; SQRT_POS_LT] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * delta * Lam * norm(a:real^N) * norm(b:real^N)) / sqrt lam` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; SQRT_POS_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * delta * norm((M:real^N^N) ** a) * norm(M ** b)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(sqrt Lam * norm(a:real^N)) * (sqrt Lam * norm(b:real^N))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MP_TAC(SPEC `Lam:real` SQRT_POW_2) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `sqrt Lam pow 2 = Lam` THEN CONV_TAC REAL_RING];
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

let P2BPL_SPRAY_LIPSCHITZ = prove
 (`!U (G:real^N->real^N^N) S.
     metric_field U G /\ compact S /\ S SUBSET U PCROSS (:real^N)
     ==> ?L. &0 < L /\
             !Y Y'. Y IN S /\ Y' IN S
                    ==> norm(geo_spray G Y - geo_spray G Y') <= L * norm(Y - Y')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `open((:real^1) PCROSS ((U:real^N->bool) PCROSS (:real^N)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^(1,(N,N)finite_sum)finite_sum. geo_spray (G:real^N->real^N^N) (sndcart z)`;
                 `(:real^1) PCROSS ((U:real^N->bool) PCROSS (:real^N))`]
                ODE_SMOOTH_IMP_LOCALLY_LIPSCHITZ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\z:real^(1,(N,N)finite_sum)finite_sum. geo_spray (G:real^N->real^N^N) (sndcart z)) =
                  geo_spray G o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(U:real^N->bool) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; GEOL_SPRAY_SMOOTH] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[PASTECART_IN_PCROSS];
      MP_TAC(ISPECL [`(:real^1) PCROSS ((U:real^N->bool) PCROSS (:real^N))`;
                     `\x:real^(1,(N,N)finite_sum)finite_sum. x`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`\z:real^(1,(N,N)finite_sum)finite_sum. geo_spray (G:real^N->real^N^N) (sndcart z)`;
                 `(:real^1) PCROSS ((U:real^N->bool) PCROSS (:real^N))`;
                 `{lift(&0)} PCROSS (S:real^(N,N)finite_sum->bool)`] ODE_LOCALLY_LIPSCHITZ_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_SING] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; IN_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SNDCART_PASTECART] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `L + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `L * norm(Y - Y':real^(N,N)finite_sum)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `lift(&0)` THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING];
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC]);;

(* The limit geodesic in the preferred chart at its base point.              *)

let P2BPL_LIMIT_GEO_CHART = prove
 (`!(top:B topology) atlas (g0:B->real^N^N) xl v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     xl IN topspace top
     ==> ?d0 q0. &0 < d0 /\
            (!s. abs s < d0
                 ==> s IN mfd_geo_maxint (top,atlas) g0 xl v /\
                     mfd_geo (top,atlas) g0 xl v s IN FST (chart_at atlas xl)) /\
            (!s. abs s < d0
                 ==> ((\r. SND (chart_at atlas xl) (mfd_geo (top,atlas) g0 xl v (drop r)))
                      has_vector_derivative q0 s) (at (lift s)) /\
                     ((\r. q0(drop r)) has_vector_derivative
                      --(christoffel (metric_local atlas (chart_at atlas xl) g0)
                            (SND (chart_at atlas xl) (mfd_geo (top,atlas) g0 xl v s))
                            (q0 s) (q0 s))) (at (lift s))) /\
            q0 (&0) = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g0:B->real^N^N`;
                 `xl:B`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `xl:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_geodesic] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_geodesic")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `chart_at (atlas:((B->bool)#(B->real^N))->bool) (xl:B)`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q0:real->real^N` (LABEL_TAC "ode")) THEN
  MP_TAC(ISPECL [`top:B topology`; `mfd_geo (top,atlas) (g0:B->real^N^N) xl v`;
                 `mfd_geo_maxint (top,atlas) (g0:B->real^N^N) xl v`;
                 `FST(chart_at (atlas:((B->bool)#(B->real^N))->bool) (xl:B))`; `&0`]
                GEOL_CURVE_NEAR) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `chart_at (atlas:((B->bool)#(B->real^N))->bool) (xl:B)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC)] THEN
  MAP_EVERY EXISTS_TAC [`d0:real`; `q0:real->real^N`] THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\r. SND (chart_at (atlas:((B->bool)#(B->real^N))->bool) (xl:B))
                    (mfd_geo (top,atlas) (g0:B->real^N^N) xl v (drop r))` THEN
  EXISTS_TAC `lift(&0)` THEN CONJ_TAC THENL
   [USE_THEN "ode" (MP_TAC o SPEC `&0`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g0:B->real^N^N`;
                 `mfd_geo (top,atlas) (g0:B->real^N^N) xl v`;
                 `mfd_geo_maxint (top,atlas) (g0:B->real^N^N) xl v`; `chart_at (atlas:((B->bool)#(B->real^N))->bool) (xl:B)`;
                 `&0`] MFD_GEODESIC_VEL_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `FST(chart_at (atlas:((B->bool)#(B->real^N))->bool) (xl:B))`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) (xl:B))`; `xl:B`]
                CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

(* Riemannian distance between chart points of a convex part of a chart     *)
(* image, by the chart segment.                                              *)

let P2BPL_CHART_DIST = prove
 (`!(top:B topology) atlas (g:B->real^N^N) c K C y1 y2.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
     convex K /\ K SUBSET IMAGE (SND c) (FST c) /\ y1 IN K /\ y2 IN K /\
     (!y v. y IN K ==> v dot (metric_local atlas c g y ** v) <= C * norm v pow 2)
     ==> mfd_dist (top,atlas) g (chart_inv c y1) (chart_inv c y2) <= sqrt C * dist(y1,y2)`,
  REPEAT GEN_TAC THEN SUBST1_TAC(GSYM(ISPEC `c:(B->bool)#(B->real^N)` PAIR)) THEN
  SPEC_TAC(`SND(c:(B->bool)#(B->real^N))`,`phi:B->real^N`) THEN
  SPEC_TAC(`FST(c:(B->bool)#(B->real^N))`,`U:B->bool`) THEN
  REWRITE_TAC[FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[y1:real^N,y2] SUBSET K` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `U:B->bool`; `phi:B->real^N`; `y1:real^N`; `y2:real^N`] GRGD_CHART_SEGMENT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g:B->real^N^N`;
                 `\t. chart_inv (U:B->bool,phi:B->real^N) (y1 + t % (y2 - y1))`;
                 `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                  VECTOR_ARITH `y1 + (y2 - y1):real^N = y2`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas (g:B->real^N^N)
                (\t. chart_inv (U:B->bool,phi:B->real^N) (y1 + t % (y2 - y1))) (&0) (&1)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_SEGMENT_LENGTH_UPPER THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `&0`; `K:real^N->bool`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_NONNEG THEN EXISTS_TAC `IMAGE (phi:B->real^N) U` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric; FST; SND]; ASM SET_TAC[]];
    ASM_SIMP_TAC[]]);;

(* The pulled-back curve of a geodesic through f x0 with velocity D f (w)   *)
(* has chart velocity w at time 0 in the preferred chart at x0.              *)

let P2BPL_PULLBACK_VEL0 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' (g':B->real^N^N) (gamma:real->B) J x0 w.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\ x0 IN W /\
     mfd_geodesic (top',atlas') g' gamma J /\ (!s. s IN J ==> gamma s IN W') /\ &0 IN J /\
     gamma(&0) = f x0 /\ mfd_vel atlas' gamma (&0) = mfd_differential atlas atlas' f x0 w
     ==> ((\s. SND (chart_at atlas x0) (f'(gamma(drop s)))) has_vector_derivative w)
         (at (lift(&0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (W':B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN topspace top /\ (f:A->B) x0 IN topspace top' /\ f x0 IN W' /\
                (f':B->A)(f x0) = x0`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET; FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x0:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `(f:A->B) x0`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)` THEN
  ABBREV_TAC `c1 = chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x0)` THEN
  (* the chart velocity of gamma in c1 at 0 is D w *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `gamma:real->B`; `J:real->bool`; `c1:(B->bool)#(B->real^N)`; `&0`]
                MFD_GEODESIC_VEL_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `FST(c1:(B->bool)#(B->real^N))`; `SND(c1:(B->bool)#(B->real^N))`; `(f:A->B) x0`]
                CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the chart representatives *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W':B->bool`;
                 `f:A->B`; `f':B->A`; `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(c1:(B->bool)#(B->real^N))`; `SND(c1:(B->bool)#(B->real^N))`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "diffeomorphism_on")) (concl th))) THEN
  MP_TAC(ISPECL [`IMAGE (SND (c0:(A->bool)#(A->real^N))) {x | x IN FST c0 INTER W /\
                                                              (f:A->B) x IN FST (c1:(B->bool)#(B->real^N))}`;
                 `IMAGE (SND (c1:(B->bool)#(B->real^N))) {y | y IN FST c1 INTER W' /\
                                                              (f':B->A) y IN FST (c0:(A->bool)#(A->real^N))}`;
                 `SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))`;
                 `SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))`;
                 `SND (c0:(A->bool)#(A->real^N)) (x0:A)`; `w:real^N`] ODE_DIFFEO_DERIVATIVE_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c1:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(SND (c1:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c0:(A->bool)#(A->real^N)))
                  (SND c0 (x0:A)) = SND c1 (f x0) /\
                frechet_derivative (SND c1 o f o chart_inv c0) (at (SND c0 x0)) =
                mfd_differential atlas atlas' f x0`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[o_THM] THEN EXPAND_TAC "c0" THEN EXPAND_TAC "c1" THEN
    REWRITE_TAC[mfd_differential; o_DEF];
    DISCH_TAC] THEN
  (* the curve near 0 *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^N))->bool`; `c1:(B->bool)#(B->real^N)`;
                 `c0:(A->bool)#(A->real^N)`; `W':B->bool`; `f':B->A`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_geodesic] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_geodesic")) (concl th))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `gamma:real->B`; `J:real->bool`;
                 `{x | x IN FST (c1:(B->bool)#(B->real^N)) INTER W' /\
                       (f':B->A) x IN FST (c0:(A->bool)#(A->real^N))}`; `&0`] GEOL_CURVE_NEAR) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `(SND (c0:(A->bool)#(A->real^N)) o (f':B->A) o chart_inv (c1:(B->bool)#(B->real^N))) o
              (\s. SND c1 ((gamma:real->B)(drop s)))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(drop s) < d` ASSUME_TAC THENL
     [UNDISCH_TAC `dist(s:real^1,lift(&0)) < d` THEN
      REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP; REAL_SUB_RZERO];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM th]) o
    check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "frechet_derivative")) (lhs(concl th)))) THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN
  ASM_REWRITE_TAC[WITHIN_UNIV; LIFT_DROP] THEN
  REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND (c1:(B->bool)#(B->real^N))) {y | y IN FST c1 INTER W' /\
                                                       (f':B->A) y IN FST (c0:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]);;

(* ========================================================================= *)
(* An abstract first-exit Gronwall argument: a solution Yn of Y' = Fn(Y),    *)
(* defined while a time is "good" (an open condition, closed along good      *)
(* times with the bound), stays good and close to a solution Y0 of           *)
(* Y' = F0(Y) on [0,d] when Fn is close to F0 and F0 is Lipschitz on a       *)
(* region containing the eps-tube around Y0.                                 *)
(* ========================================================================= *)

let P2BPL_EXIT_GRONWALL = prove
 (`!(inO:real->bool) (Yn:real->real^M) Y0 Fn F0 S d eps L K delta.
     &0 <= d /\ &0 < L /\ &0 <= K /\ &0 <= delta /\
     (delta + K / L) * exp(&3 * L * d) < eps /\
     inO(&0) /\ norm(Yn(&0) - Y0(&0)) <= delta /\
     (!s. inO s ==> ?e. &0 < e /\ !s'. abs(s' - s) < e ==> inO s') /\
     (!Tm. &0 < Tm /\ Tm <= d /\ (!s. &0 <= s /\ s < Tm ==> inO s /\ norm(Yn s - Y0 s) <= eps)
          ==> inO Tm) /\
     (!s. inO s ==> ((\t. Yn(drop t)) has_vector_derivative Fn(Yn s)) (at (lift s))) /\
     (!s. &0 <= s /\ s <= d
          ==> ((\t. Y0(drop t)) has_vector_derivative F0(Y0 s)) (at (lift s))) /\
     (!Y Y'. Y IN S /\ Y' IN S ==> norm(F0 Y - F0 Y') <= L * norm(Y - Y')) /\
     (!Y. Y IN S ==> norm(Fn Y - F0 Y) <= K) /\
     (!s Y. &0 <= s /\ s <= d /\ norm(Y - Y0 s) <= eps ==> Y IN S /\ Y0 s IN S)
     ==> !s. &0 <= s /\ s <= d
             ==> inO s /\ norm(Yn s - Y0 s) <= (delta + K / L) * exp(&3 * L * d)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ABBREV_TAC `Gb = (delta + K / L) * exp(&3 * L * d)` THEN
  SUBGOAL_THEN `delta <= Gb` ASSUME_TAC THENL
   [EXPAND_TAC "Gb" THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(delta + K / L) * &1` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a <= a + b`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  (* continuity of the difference at good times *)
  SUBGOAL_THEN `!t0. inO t0 /\ &0 <= t0 /\ t0 <= d
                     ==> (\t. (Yn:real->real^M)(drop t) - Y0(drop t)) continuous (at (lift t0))`
  (LABEL_TAC "cont") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* Gronwall on every good initial interval *)
  SUBGOAL_THEN
   `!Tm. &0 <= Tm /\ Tm <= d /\
        (!s. &0 <= s /\ s <= Tm ==> inO s /\ norm((Yn:real->real^M) s - Y0 s) <= eps)
        ==> !s. &0 <= s /\ s <= Tm ==> norm(Yn s - Y0 s) <= Gb`
  (LABEL_TAC "gron") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!s. &0 <= s /\ s <= Tm
          ==> ((\t. (Yn:real->real^M)(drop t) - Y0(drop t)) has_vector_derivative
               ((Fn:real^M->real^M)(Yn s) - F0((Y0:real->real^M) s))) (at (lift s))`
    (LABEL_TAC "rder") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\t. (Yn:real->real^M)(drop t) - Y0(drop t)`;
                   `\t. (Fn:real^M->real^M)((Yn:real->real^M)(drop t)) - F0((Y0:real->real^M)(drop t))`;
                   `interval[lift(&0),lift Tm]`; `lift(&0)`; `L:real`; `K:real`]
                  ODE_GRONWALL_INHOM) THEN
    REWRITE_TAC[IS_INTERVAL_INTERVAL; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
     [X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
        USE_THEN "rder" (MP_TAC o SPEC `drop t`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LIFT_DROP]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(Yn:real->real^M)(drop t) IN S /\ (Y0:real->real^M)(drop t) IN S`
      STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((Fn:real^M->real^M)((Yn:real->real^M)(drop t)) - F0(Yn(drop t))) +
                  norm((F0:real^M->real^M)(Yn(drop t)) - F0((Y0:real->real^M)(drop t)))` THEN
      CONJ_TAC THENL [REWRITE_TAC[NORM_ARITH `norm(a - c:real^M) <= norm(a - b) + norm(b - c)`];
                      ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= K /\ b <= L * n ==> a + b <= L * n + K`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    EXPAND_TAC "Gb" THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_DIV; REAL_LT_IMP_LE];
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_EXP_POS_LE];
      REWRITE_TAC[REAL_EXP_MONO_LE; REAL_SUB_RZERO] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the induction on [0,d] *)
  SUBGOAL_THEN `!s. &0 <= s /\ s <= d ==> inO s /\ norm((Yn:real->real^M) s - Y0 s) <= eps`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s. inO s /\ norm((Yn:real->real^M) s - Y0 s) <= eps`; `d:real`]
                  P2A_REAL_CONT_INDUCT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(* near 0 *)
      FIRST_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
        is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_SUB_RZERO]] THEN
      DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "cont" (MP_TAC o SPEC `&0`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `eps - delta`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `e1:real`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
          can (find_term ((=) `e2:real`)) (concl th))) THEN
        REWRITE_TAC[DIST_LIFT; LIFT_DROP; REAL_SUB_RZERO] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `norm((Yn:real->real^M)(&0) - Y0(&0)) <= delta` THEN
        REWRITE_TAC[dist] THEN NORM_ARITH_TAC];
      (* closedness *)
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(inO:real->bool) Tm` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `eps:real`)) (concl th) &&
          is_comb(snd(dest_imp(snd(strip_forall(concl th))))) &&
          not(is_conj(snd(dest_imp(snd(strip_forall(concl th)))))))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Gb:real` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `~(Gb < x) ==> x <= Gb`) THEN DISCH_TAC THEN
      USE_THEN "cont" (MP_TAC o SPEC `Tm:real`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      REWRITE_TAC[continuous_at] THEN
      DISCH_THEN(MP_TAC o SPEC `norm((Yn:real->real^M) Tm - Y0 Tm) - Gb`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `&0 <= Tm - min Tm e2 / &2 /\ Tm - min Tm e2 / &2 < Tm /\
                    abs((Tm - min Tm e2 / &2) - Tm) < e2` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `lift(Tm - min Tm e2 / &2)` o check (fun th ->
        can (find_term ((=) `e2:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[DIST_LIFT; LIFT_DROP] THEN
      USE_THEN "gron" (MP_TAC o SPEC `Tm - min Tm e2 / &2`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `Tm:real`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `Tm - min Tm e2 / &2`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
      (* openness *)
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(inO:real->bool) Tm /\ norm((Yn:real->real^M) Tm - Y0 Tm) <= Gb`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
        USE_THEN "gron" (MP_TAC o SPEC `Tm:real`) THEN ANTS_TAC THENL
         [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `Tm:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `Tm:real` o check (fun th -> is_forall(concl th) &&
        is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "cont" (MP_TAC o SPEC `Tm:real`) THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `eps - Gb`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `e1:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
          can (find_term ((=) `e2:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[DIST_LIFT; LIFT_DROP] THEN
        UNDISCH_TAC `norm((Yn:real->real^M) Tm - Y0 Tm) <= Gb` THEN
        REWRITE_TAC[dist] THEN NORM_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "gron" (MP_TAC o SPEC `d:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The pulled-back geodesic of one slice in the fixed chart c0: its state    *)
(* solves the spray equation of the pullback metric while it stays in the    *)
(* chart piece, and it stays close to the limit state on [0,d]               *)
(* (P2BPL_EXIT_GRONWALL).                                                    *)
(* ========================================================================= *)

let P2BPL_PULLBACK_STATE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' (g':B->real^N^N) (sigma:real->B) c0 s.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\
     mfd_geodesic (top',atlas') g' sigma (:real) /\ c0 IN atlas /\
     sigma s IN W' /\ f'(sigma s) IN FST c0
     ==> (?e. &0 < e /\ !s'. abs(s' - s) < e ==> sigma s' IN W' /\ f'(sigma s') IN FST c0) /\
         ((\t. pastecart (SND c0 (f'(sigma(drop t))))
                         (vector_derivative (\r. SND c0 (f'(sigma(drop r)))) (at (lift(drop t)))))
          has_vector_derivative
          geo_spray (metric_local atlas c0 (mfd_pullback_metric atlas atlas' f g'))
            (pastecart (SND c0 (f'(sigma s)))
                       (vector_derivative (\r. SND c0 (f'(sigma(drop r)))) (at (lift s)))))
         (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (W':B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(sigma:real->B) s IN topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?c'. c' IN atlas' /\ (sigma:real->B) s IN FST (c':(B->bool)#(B->real^N))`
  (X_CHOOSE_THEN `c':(B->bool)#(B->real^N)` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[CHART_AT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^N))->bool`; `c':(B->bool)#(B->real^N)`;
                 `c0:(A->bool)#(A->real^N)`; `W':B->bool`; `f':B->A`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_geodesic] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_geodesic")) (concl th))) THEN
  MP_TAC(ISPECL [`top':B topology`; `sigma:real->B`; `(:real)`;
                 `{x | x IN FST (c':(B->bool)#(B->real^N)) INTER W' /\
                       (f':B->A) x IN FST (c0:(A->bool)#(A->real^N))}`; `s:real`] GEOL_CURVE_NEAR) THEN
  ASM_REWRITE_TAC[IN_UNIV; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`; `f:A->B`;
                 `f':B->A`; `g':B->real^N^N`; `sigma:real->B`; `real_interval(s - e,s + e)`;
                 `c0:(A->bool)#(A->real^N)`; `s:real`] P2BPL_PULLBACK_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `(:real)` THEN
      ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL; REAL_OPEN_REAL_INTERVAL; SUBSET_UNIV];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `abs(s' - s) < e` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas' (f:A->B) (g':B->real^N^N)`;
                 `\s. (f':B->A)((sigma:real->B) s)`; `c0:(A->bool)#(A->real^N)`;
                 `\s. vector_derivative (\r. SND (c0:(A->bool)#(A->real^N))
                                               ((f':B->A)((sigma:real->B)(drop r)))) (at (lift s))`;
                 `s:real`] GEOL_GEODESIC_CHART_STATE) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; SIMP_TAC[]]);;

(* One slice: the pulled-back geodesic stays in the chart piece and close  *)
(* to the limit chart geodesic on [0,d].                                    *)

let P2BPL_FWD_ONE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W W' (f:A->B) f' (g':B->real^N^N) (sigma:real->B) xl c0 p (G0:real^N->real^N^N)
    (y0:real->real^N) q0 v w r B d L eta delta eps.
     hausdorff_space top' /\ smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\ xl IN W /\
     chart_at atlas xl = c0 /\ SND c0 xl = p /\
     &0 < r /\ cball(p,&2 * r) SUBSET IMAGE (SND c0) (FST c0) /\
     IMAGE (chart_inv c0) (cball(p,&2 * r)) SUBSET W /\
     mfd_geodesic (top',atlas') g' sigma (:real) /\ sigma(&0) = f xl /\
     mfd_vel atlas' sigma (&0) = mfd_differential atlas atlas' f xl w /\
     (!s. &0 <= s /\ s <= d
          ==> ((\t. pastecart (y0(drop t)) (q0(drop t))) has_vector_derivative
               geo_spray G0 (pastecart (y0 s) (q0 s))) (at (lift s)) /\
              norm(y0 s - p) <= r / &2 /\ norm(q0 s) <= B) /\
     y0(&0) = p /\ q0(&0) = v /\
     &0 <= d /\ &0 < L /\ &0 <= eta /\ &0 <= delta /\ &0 < eps /\ eps <= r / &2 /\ eps <= &1 /\
     (delta + (eta * (B + &1) pow 2) / L) * exp(&3 * L * d) < eps /\
     (!Y Y'. Y IN cball(p,&2 * r) PCROSS cball(vec 0,B + &1) /\
             Y' IN cball(p,&2 * r) PCROSS cball(vec 0,B + &1)
             ==> norm(geo_spray G0 Y - geo_spray G0 Y') <= L * norm(Y - Y')) /\
     (!y a b. y IN cball(p,&2 * r)
              ==> norm(christoffel (metric_local atlas c0 (mfd_pullback_metric atlas atlas' f g'))
                         y a b - christoffel G0 y a b) <= eta * norm a * norm b) /\
     norm(w - v) <= delta
     ==> !s. &0 <= s /\ s <= d
             ==> sigma s IN W' /\ f'(sigma s) IN FST c0 /\
                 norm(SND c0 (f'(sigma s)) - y0 s) <=
                 (delta + (eta * (B + &1) pow 2) / L) * exp(&3 * L * d)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (W':B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(xl:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `xl:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\s. (sigma:real->B) s IN W' /\ (f':B->A)(sigma s) IN FST (c0:(A->bool)#(A->real^N)) /\
         SND c0 (f'(sigma s)) IN ball(p:real^N,&2 * r)`;
    `\s. pastecart (SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s)))
                   (vector_derivative (\r. SND c0 (f'(sigma(drop r)))) (at (lift s)))`;
    `\s. pastecart ((y0:real->real^N) s) ((q0:real->real^N) s)`;
    `geo_spray (metric_local atlas (c0:(A->bool)#(A->real^N))
                 (mfd_pullback_metric atlas atlas' (f:A->B) (g':B->real^N^N)))`;
    `geo_spray (G0:real^N->real^N^N)`;
    `cball(p:real^N,&2 * r) PCROSS cball(vec 0:real^N,B + &1)`;
    `d:real`; `eps:real`; `L:real`; `eta * (B + &1) pow 2`; `delta:real`] P2BPL_EXIT_GRONWALL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(* 1 *) MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      (* 2 *) ASM SET_TAC[];
      (* 3 *) ASM_SIMP_TAC[];
      (* 4 *) ASM_SIMP_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      (* 5: the initial velocity *)
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                     `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`; `f:A->B`;
                     `f':B->A`; `g':B->real^N^N`; `sigma:real->B`; `c0:(A->bool)#(A->real^N)`;
                     `&0:real`] P2BPL_PULLBACK_STATE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o CONJUNCT1) THEN
      SUBGOAL_THEN
       `mfd_geodesic (top',atlas') (g':B->real^N^N) (sigma:real->B) (real_interval(--e,e)) /\
        (!s. s IN real_interval(--e,e) ==> sigma s IN W') /\ &0 IN real_interval(--e,e)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `(:real)` THEN
          ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL; REAL_OPEN_REAL_INTERVAL; SUBSET_UNIV];
          REPEAT STRIP_TAC THEN
          SUBGOAL_THEN `abs(s - &0) < e` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                     `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`; `f:A->B`;
                     `f':B->A`; `g':B->real^N^N`; `sigma:real->B`; `real_interval(--e,e)`;
                     `xl:A`; `w:real^N`] P2BPL_PULLBACK_VEL0) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP VECTOR_DERIVATIVE_AT th]) THEN
      ASM_SIMP_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART; NORM_0;
                   REAL_ARITH `&0 pow 2 + x = x`; POW_2_SQRT; NORM_POS_LE];
      (* 6: openness *)
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`; `f:A->B`;
                       `f':B->A`; `g':B->real^N^N`; `sigma:real->B`; `c0:(A->bool)#(A->real^N)`;
                       `s:real`] P2BPL_PULLBACK_STATE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) MP_TAC) THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT o
                 MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE) THEN
      REWRITE_TAC[continuous_at] THEN
      DISCH_THEN(MP_TAC o SPEC `&2 * r - dist(p:real^N,SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s)))`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s)) IN ball(p:real^N,&2 * r)` THEN
        REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      X_GEN_TAC `s':real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s':real` o check (fun th ->
        can (find_term ((=) `e1:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s'` o check (fun th ->
        can (find_term ((=) `e2:real`)) (concl th))) THEN
      REWRITE_TAC[DIST_LIFT; LIFT_DROP] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s)) IN ball(p:real^N,&2 * r)` THEN
      REWRITE_TAC[IN_BALL; dist] THEN
      MP_TAC(ISPEC `pastecart (SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s')))
                      (vector_derivative (\r. SND (c0:(A->bool)#(A->real^N)) (f'(sigma(drop r)))) (at (lift s'))) -
                    pastecart (SND (c0:(A->bool)#(A->real^N)) (f'(sigma s)))
                      (vector_derivative (\r. SND (c0:(A->bool)#(A->real^N)) (f'(sigma(drop r)))) (at (lift s)))`
             NORM_FSTCART) THEN
      REWRITE_TAC[FSTCART_SUB; FSTCART_PASTECART] THEN NORM_ARITH_TAC;
      (* 7: closedness *)
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `compact_in top' (IMAGE ((f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))) (cball(p:real^N,r)))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
        EXISTS_TAC `subtopology euclidean (cball(p:real^N,r))` THEN
        REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL; SUBSET_REFL] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `subtopology top (W:A->bool)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_INTO_SUBTOPOLOGY THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                         `FST (c0:(A->bool)#(A->real^N))`; `SND (c0:(A->bool)#(A->real^N))`] GRGD_CHART_INV_CONTINUOUS) THEN
          ASM_REWRITE_TAC[PAIR] THEN
          DISCH_THEN(MP_TAC o SPEC `cball(p:real^N,r)` o MATCH_MP CONTINUOUS_MAP_FROM_SUBTOPOLOGY) THEN
          REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
          SUBGOAL_THEN `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST (c0:(A->bool)#(A->real^N))) INTER cball(p:real^N,r) = cball(p,r)` SUBST1_TAC THENL
           [MP_TAC(ISPECL [`p:real^N`; `r:real`; `&2 * r`] SUBSET_CBALL) THEN
            ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
            REWRITE_TAC[]];
          REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
          MP_TAC(ISPECL [`p:real^N`; `r:real`; `&2 * r`] SUBSET_CBALL) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `closed_in top' (IMAGE ((f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))) (cball(p:real^N,r))) /\
        IMAGE ((f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))) (cball(p:real^N,r)) SUBSET topspace top'`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE];
        ALL_TAC] THEN
      SUBGOAL_THEN `!s. &0 <= s /\ s < Tm
                        ==> (sigma:real->B) s IN IMAGE ((f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))) (cball(p:real^N,r))`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `Tm:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        REWRITE_TAC[IN_IMAGE; o_THM] THEN
        EXISTS_TAC `SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s))` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `B:real`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "geo_spray")) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
        UNDISCH_TAC `norm(pastecart (SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s)))
                       (vector_derivative (\r. SND (c0:(A->bool)#(A->real^N)) (f'(sigma(drop r)))) (at (lift s))) -
                       pastecart ((y0:real->real^N) s) ((q0:real->real^N) s)) <= eps` THEN
        MP_TAC(ISPEC `pastecart (SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s)))
                       (vector_derivative (\r. SND (c0:(A->bool)#(A->real^N)) (f'(sigma(drop r)))) (at (lift s))) -
                       pastecart ((y0:real->real^N) s) ((q0:real->real^N) s)` NORM_FSTCART) THEN
        REWRITE_TAC[FSTCART_SUB; FSTCART_PASTECART; IN_CBALL; dist] THEN
        UNDISCH_TAC `norm((y0:real->real^N) s - p) <= r / &2` THEN
        UNDISCH_TAC `eps <= r / &2` THEN NORM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(sigma:real->B) Tm IN IMAGE ((f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))) (cball(p:real^N,r))`
      MP_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_geodesic] o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_geodesic")) (concl th))) THEN
        MP_TAC(ISPECL [`top':B topology`; `sigma:real->B`; `(:real)`;
                       `topspace top' DIFF IMAGE ((f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))) (cball(p:real^N,r))`;
                       `Tm:real`] GEOL_CURVE_NEAR) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[IN_UNIV; OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF] THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
          REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `e3:real` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `Tm - min Tm e3 / &2` o check (fun th ->
          can (find_term ((=) `e3:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[IN_DIFF] THEN
        SUBGOAL_THEN `&0 <= Tm - min Tm e3 / &2 /\ Tm - min Tm e3 / &2 < Tm` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; o_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `y IN cball(p:real^N,&2 * r)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`p:real^N`; `r:real`; `&2 * r`] SUBSET_CBALL) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `chart_inv (c0:(A->bool)#(A->real^N)) (y:real^N) IN W /\ chart_inv (c0:(A->bool)#(A->real^N)) y IN FST (c0:(A->bool)#(A->real^N)) /\
                    SND (c0:(A->bool)#(A->real^N)) (chart_inv (c0:(A->bool)#(A->real^N)) y) = y` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `y IN cball(p:real^N,r)` THEN REWRITE_TAC[IN_CBALL; IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      (* 8 *)
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `W':B->bool`; `f:A->B`;
                       `f':B->A`; `g':B->real^N^N`; `sigma:real->B`; `c0:(A->bool)#(A->real^N)`;
                       `s:real`] P2BPL_PULLBACK_STATE) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      (* 9 *)
      ASM_SIMP_TAC[];
      (* 10 *)
      REWRITE_TAC[FORALL_IN_PCROSS; IN_CBALL_0] THEN
      MAP_EVERY X_GEN_TAC [`y:real^N`; `q:real^N`] THEN STRIP_TAC THEN
      REWRITE_TAC[geo_spray; FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_SUB; VECTOR_SUB_REFL;
                  NORM_PASTECART; NORM_0; REAL_ARITH `&0 pow 2 + x = x`] THEN
      SIMP_TAC[POW_2_SQRT; NORM_POS_LE] THEN
      REWRITE_TAC[VECTOR_ARITH `--a - --b:real^N = --(a - b)`; NORM_NEG] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eta * norm(q:real^N) * norm q` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      (* 11 *)
      MAP_EVERY X_GEN_TAC [`s:real`; `Y:real^(N,N)finite_sum`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `B:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "geo_spray")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                  IN_CBALL; IN_CBALL_0; dist] THEN
      UNDISCH_TAC `norm(Y - pastecart ((y0:real->real^N) s) ((q0:real->real^N) s)) <= eps` THEN
      MP_TAC(ISPEC `Y - pastecart ((y0:real->real^N) s) ((q0:real->real^N) s)` NORM_FSTCART) THEN
      MP_TAC(ISPEC `Y - pastecart ((y0:real->real^N) s) ((q0:real->real^N) s)` NORM_SNDCART) THEN
      REWRITE_TAC[FSTCART_SUB; SNDCART_SUB; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      UNDISCH_TAC `norm((y0:real->real^N) s - p) <= r / &2` THEN
      UNDISCH_TAC `norm((q0:real->real^N) s) <= B` THEN
      UNDISCH_TAC `eps <= r / &2` THEN UNDISCH_TAC `eps <= &1` THEN UNDISCH_TAC `&0 < r` THEN
      NORM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(pastecart (SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s)))
                   (vector_derivative (\r. SND c0 (f'(sigma(drop r)))) (at (lift s))) -
                   pastecart ((y0:real->real^N) s) ((q0:real->real^N) s))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `pastecart (SND (c0:(A->bool)#(A->real^N)) ((f':B->A)((sigma:real->B) s)))
                   (vector_derivative (\r. SND c0 (f'(sigma(drop r)))) (at (lift s))) -
                   pastecart ((y0:real->real^N) s) ((q0:real->real^N) s)` NORM_FSTCART) THEN
  REWRITE_TAC[FSTCART_SUB; FSTCART_PASTECART]);;

(* ========================================================================= *)
(* Closeness of the slices in the fixed chart c0 = chart_at atlas xl         *)
(* (metrics and Christoffel symbols), two arithmetic lemmas, geodesics of    *)
(* complete slices, and the data of the limit geodesic in the chart c0.      *)
(* ========================================================================= *)

let P2BPL_SLICE_CLOSE_C0 = prove
 (`!V x t Q (top:B topology) atlas g0 xl W phi c0 D m eta.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                        (real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (t n))
                                (rfs_vatlas (V n) (t n)) /\
          riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))) /\
     c0 IN atlas /\ compact D /\ D SUBSET IMAGE (SND c0) (FST c0) /\ &0 < eta
     ==> ?n0. !n. n0 <= n
             ==> IMAGE (chart_inv c0) D SUBSET W n /\
                 !y. y IN D
                     ==> lck_dist2 m (metric_local atlas c0 g0)
                           (metric_local atlas c0
                              (\z. Q n %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                           (rfs_vmetric (V n) (t n)) z)) y < eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact_in top (IMAGE (chart_inv (c0:(B->bool)#(B->real^3))) D)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (SND (c0:(B->bool)#(B->real^3))) (FST c0))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST (c0:(B->bool)#(B->real^3))`; `SND (c0:(B->bool)#(B->real^3))`]
           GRGD_CHART_INV_CONTINUOUS) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `IMAGE (chart_inv (c0:(B->bool)#(B->real^3))) D`; `m:num`; `eta:real`]
         P2BPL_SLICE_CLOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN
  DISCH_THEN(fun th -> X_GEN_TAC `n:num` THEN DISCH_TAC THEN MP_TAC(SPEC `n:num` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (c0:(B->bool)#(B->real^3)) y IN FST c0 /\
                SND c0 (chart_inv c0 y) = y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c0:(B->bool)#(B->real^3)) y IN topspace top /\
                chart_inv c0 y IN (W:num->B->bool) n`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ASM SET_TAC[]]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `chart_inv (c0:(B->bool)#(B->real^3)) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `n:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> metric_field (IMAGE (SND c) (FST c INTER (W:num->B->bool) n))
                         (metric_local atlas c (g0:B->real^3^3)) /\
            metric_field (IMAGE (SND c) (FST c INTER W n))
                         (metric_local atlas c
                            (\z. (Q:num->real) n %%
                                 mfd_pullback_metric atlas
                                   (rfs_vatlas ((V:num->(real->A topology)#
                                                 (real->((A->bool)#(A->real^3))->bool)#
                                                 (real->A->real^3^3)) n) (t n))
                                   ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)) z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlas (g0:B->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `FST (c:(B->bool)#(B->real^3))`; `SND (c:(B->bool)#(B->real^3))`;
                       `FST (c:(B->bool)#(B->real^3)) INTER (W:num->B->bool) n`]
               CHART_IMAGE_OPEN) THEN
        ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
      MATCH_MP_TAC P2BPL_PULLBACK_METRIC_FIELD THEN
      MAP_EVERY EXISTS_TAC
       [`top:B topology`;
        `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) n) (t n)`;
        `IMAGE ((phi:num->B->A) n) (W n)`; `psi:A->B`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `\z. (Q:num->real) n %%
                      mfd_pullback_metric atlas
                        (rfs_vatlas ((V:num->(real->A topology)#
                                      (real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) n) (t n))
                        ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)) z`;
                 `(W:num->B->bool) n`;
                 `chart_at (atlas:((B->bool)#(B->real^3))->bool)
                           (chart_inv (c0:(B->bool)#(B->real^3)) y)`;
                 `c0:(B->bool)#(B->real^3)`; `chart_inv (c0:(B->bool)#(B->real^3)) y`; `m:num`]
         P2BPL_LCK_CHART_INDEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  USE_THEN "cl" MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

(* Christoffel symbols of the (unscaled) pulled-back slice metrics in the   *)
(* chart c0 converge uniformly on compacts to those of the limit metric.    *)

let P2BPL_CHRIST_C0 = prove
 (`!V x t Q (top:B topology) atlas g0 xl W phi c0 D eta.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                        (real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (t n))
                                (rfs_vatlas (V n) (t n)) /\
          riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))) /\
     c0 IN atlas /\ compact D /\ D SUBSET IMAGE (SND c0) (FST c0) /\ &0 < eta
     ==> ?n0. !n. n0 <= n
             ==> IMAGE (chart_inv c0) D SUBSET W n /\
                 !y a b. y IN D
                         ==> norm(christoffel (metric_local atlas c0
                                    (mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n)
                                       (rfs_vmetric (V n) (t n)))) y a b -
                                  christoffel (metric_local atlas c0 g0) y a b)
                             <= eta * norm a * norm b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `FST (c0:(B->bool)#(B->real^3))`; `SND (c0:(B->bool)#(B->real^3))`;
                 `D:real^3->bool`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < sqrt lam /\ &0 < Lam` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * Lam / sqrt lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `delta = min (&1 / &10) (eta / (&2 * Lam / sqrt lam))` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= &1 / &10 /\ &2 * delta * Lam / sqrt lam <= eta`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < eta / (&2 * Lam / sqrt lam)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "delta" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "delta" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&2 * delta * Lam / sqrt lam = delta * (&2 * Lam / sqrt lam)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN EXPAND_TAC "delta" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c0:(B->bool)#(B->real^3)`;
                 `D:real^3->bool`; `1`; `delta pow 2`] P2BPL_SLICE_CLOSE_C0) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN
  DISCH_THEN(fun th -> X_GEN_TAC `n:num` THEN DISCH_TAC THEN MP_TAC(SPEC `n:num` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `a:real^3`; `b:real^3`] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `n:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  ABBREV_TAC `O = IMAGE (SND (c0:(B->bool)#(B->real^3))) (FST c0 INTER (W:num->B->bool) n)` THEN
  SUBGOAL_THEN `(y:real^3) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `chart_inv (c0:(B->bool)#(B->real^3)) y` THEN
    SUBGOAL_THEN `chart_inv (c0:(B->bool)#(B->real^3)) y IN FST c0 /\
                  SND c0 (chart_inv c0 y) = y`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (O:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST (c0:(B->bool)#(B->real^3))`; `SND (c0:(B->bool)#(B->real^3))`;
                   `FST (c0:(B->bool)#(B->real^3)) INTER (W:num->B->bool) n`]
           CHART_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field O (metric_local atlas (c0:(B->bool)#(B->real^3)) (g0:B->real^3^3)) /\
    metric_field O (metric_local atlas c0
      (\z. (Q:num->real) n %%
           mfd_pullback_metric atlas
             (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) n) (t n))
             ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)) z)) /\
    metric_field O (metric_local atlas c0
      (mfd_pullback_metric atlas (rfs_vatlas (V n) (t n)) (phi n) (rfs_vmetric (V n) (t n))))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c0:(B->bool)#(B->real^3))) (FST c0)` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlas (g0:B->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "O" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
      EXPAND_TAC "O" THEN MATCH_MP_TAC P2BPL_PULLBACK_METRIC_FIELD THEN
      MAP_EVERY EXISTS_TAC
       [`top:B topology`;
        `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) n) (t n)`;
        `IMAGE ((phi:num->B->A) n) (W n)`; `psi:A->B`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) n) (t n)`;
                     `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) n) (t n)`;
                     `(W:num->B->bool) n`; `IMAGE ((phi:num->B->A) n) (W n)`;
                     `(phi:num->B->A) n`; `psi:A->B`;
                     `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) n) (t n)`;
                     `&1`; `c0:(B->bool)#(B->real^3)`] P2BPL_PULLBACK_METRIC_FIELD) THEN
      ASM_REWRITE_TAC[REAL_LT_01; MATRIX_CMUL_LID; ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `metric_local atlas (c0:(B->bool)#(B->real^3)) (g0:B->real^3^3)`;
                 `metric_local atlas (c0:(B->bool)#(B->real^3))
                    (\z. (Q:num->real) n %%
                         mfd_pullback_metric atlas
                           (rfs_vatlas ((V:num->(real->A topology)#
                                         (real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) n) (t n))
                           ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)) z)`;
                 `y:real^3`; `lam:real`; `Lam:real`; `delta:real`] P2BPL_CHRISTOFFEL_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`O:real^3->bool`;
                 `metric_local atlas (c0:(B->bool)#(B->real^3))
                    (mfd_pullback_metric atlas
                      (rfs_vatlas ((V:num->(real->A topology)#
                                    (real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n))
                      ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)))`;
                 `(Q:num->real) n`; `y:real^3`; `a:real^3`; `b:real^3`] CHRISTOFFEL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]);;

(* Arithmetic: the Gronwall bound can be made smaller than eps.             *)

let P2BPL_EPS_SPLIT = prove
 (`!K L E eps. &0 < K /\ &0 < L /\ &0 < E /\ &0 < eps
     ==> ?delta eta. &0 < delta /\ &0 < eta /\ (delta + (eta * K) / L) * E < eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &4 * E /\ &0 < &4 * K * E` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `eps / (&4 * E)` THEN EXISTS_TAC `eps * L / (&4 * K * E)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL] THEN
  SUBGOAL_THEN `(eps / (&4 * E) + ((eps * L / (&4 * K * E)) * K) / L) * E = eps / &2`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~(K = &0) /\ ~(L = &0) /\ ~(E = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ASM_REAL_ARITH_TAC]);;

let P2BPL_EPS_SMALL = prove
 (`!a e. &0 <= a /\ &0 < e ==> &0 < e / (a + &1) /\ a * e / (a + &1) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Geodesics of a complete Hausdorff manifold: defined for all times, and   *)
(* rescaling the initial velocity rescales the time.                        *)

let P2BPL_SLICE_GEO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g x (U:real^N) a.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ x IN topspace top
     ==> mfd_geodesic (top,atlas) g (mfd_geo (top,atlas) g x (a % U)) (:real) /\
         mfd_geo (top,atlas) g x (a % U) (&0) = x /\
         mfd_vel atlas (mfd_geo (top,atlas) g x (a % U)) (&0) = a % U /\
         !s. mfd_geo (top,atlas) g x (a % U) s = mfd_geo (top,atlas) g x U (a * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^N. mfd_geo_maxint (top,atlas) (g:A->real^N^N) x w = (:real)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
           MFD_COMPLETE_GEO_COMPLETE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[MFD_COMPLETE_IMP_MCOMPLETE]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `a % (U:real^N)`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `U:real^N`; `a:real`] MFD_GEO_RESCALE) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(MATCH_ACCEPT_TAC o CONJUNCT2));;

(* The limit side: in the chart c0 at xl, a doubled ball around p in the    *)
(* chart image, a time d, the chart velocity q0 of the limit geodesic with  *)
(* its state equation and bounds on [-d,d], a Lipschitz constant of the     *)
(* limit spray and an upper bound of the limit metric on the doubled ball.  *)

let P2BPL_LIMIT_DATA = prove
 (`!(top:B topology) atlas (g0:B->real^N^N) xl c0 p v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     xl IN topspace top /\ chart_at atlas xl = c0 /\ SND c0 xl = p
     ==> ?r d (q0:real->real^N) B L Lam.
           &0 < r /\ &0 < d /\ &0 <= B /\ &0 < L /\ &0 < Lam /\
           cball(p,&2 * r) SUBSET IMAGE (SND c0) (FST c0) /\
           (!s. abs s <= d
                ==> mfd_geo (top,atlas) g0 xl v s IN FST c0 /\
                    ((\t. pastecart (SND c0 (mfd_geo (top,atlas) g0 xl v (drop t))) (q0(drop t)))
                     has_vector_derivative
                     geo_spray (metric_local atlas c0 g0)
                       (pastecart (SND c0 (mfd_geo (top,atlas) g0 xl v s)) (q0 s))) (at (lift s)) /\
                    norm(SND c0 (mfd_geo (top,atlas) g0 xl v s) - p) <= r / &2 /\
                    norm(q0 s) <= B) /\
           SND c0 (mfd_geo (top,atlas) g0 xl v (&0)) = p /\ q0(&0) = v /\
           (!Y Y'. Y IN cball(p,&2 * r) PCROSS cball(vec 0,B + &1) /\
                   Y' IN cball(p,&2 * r) PCROSS cball(vec 0,B + &1)
                   ==> norm(geo_spray (metric_local atlas c0 g0) Y -
                            geo_spray (metric_local atlas c0 g0) Y') <= L * norm(Y - Y')) /\
           (!y u. y IN cball(p,&2 * r)
                  ==> u dot (metric_local atlas c0 g0 y ** u) <= Lam * norm u pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `xl:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c0:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?r. &0 < r /\
                    cball(p:real^N,&2 * r) SUBSET IMAGE (SND (c0:(B->bool)#(B->real^N))) (FST c0)`
  (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THENL
   [FIRST_ASSUM(MP_TAC o SPEC `p:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_ARITH `&2 * e / &2 = e`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g0:B->real^N^N`;
                 `xl:B`; `v:real^N`] P2BPL_LIMIT_GEO_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `q0:real->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g0:B->real^N^N`;
                 `xl:B`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "christoffel")) (concl th))) THEN
  REWRITE_TAC[REAL_ABS_NUM] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dy") (LABEL_TAC "dq")) THEN
  SUBGOAL_THEN
   `?d1. &0 < d1 /\
         !s. abs s < d1
             ==> norm(SND (c0:(B->bool)#(B->real^N)) (mfd_geo (top,atlas) (g0:B->real^N^N) xl v s) - p)
                 <= r / &2`
  (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THENL
   [USE_THEN "dy" (MP_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT o
                   MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE) THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `r / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN
    ASM_REWRITE_TAC[DIST_LIFT; LIFT_DROP; REAL_SUB_RZERO; dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d2. &0 < d2 /\ !s. abs s < d2 ==> norm((q0:real->real^N) s) <= norm(v:real^N) + &1`
  (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THENL
   [USE_THEN "dq" (MP_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT o
                   MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE) THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d2:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN
    ASM_REWRITE_TAC[DIST_LIFT; LIFT_DROP; REAL_SUB_RZERO; dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c0:(B->bool)#(B->real^N))) (FST c0)`;
                 `metric_local atlas (c0:(B->bool)#(B->real^N)) (g0:B->real^N^N)`;
                 `cball(p:real^N,&2 * r) PCROSS cball(vec 0:real^N,(norm(v:real^N) + &1) + &1)`]
         P2BPL_SPRAY_LIPSCHITZ) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g0:B->real^N^N)` THEN REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_CBALL];
      MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
    DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^N))->bool`; `g0:B->real^N^N`;
                 `FST (c0:(B->bool)#(B->real^N))`; `SND (c0:(B->bool)#(B->real^N))`;
                 `cball(p:real^N,&2 * r)`] GRGD_METRIC_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PAIR; COMPACT_CBALL]; REWRITE_TAC[PAIR]] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `min d0 (min d1 d2) / &2`; `q0:real->real^N`;
                        `norm(v:real^N) + &1`; `L:real`; `Lam:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs s < d0 /\ abs s < d1 /\ abs s < d2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "christoffel")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC GEOL_GEODESIC_CHART_STATE THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* One slice (the pulled-back rescaled geodesic is close to the limit        *)
(* geodesic at a time s in [0,d]), the forward orbit limit, and the main     *)
(* theorem P2BPL_ORBIT_LIMIT (time reversal).                                *)
(* ========================================================================= *)

let P2BPL_FWD_SLICE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    W (f:A->B) f' (g':B->real^N^N) (g0:A->real^N^N) (gamma0:real->A) xl c0 p
    (q0:real->real^N) v z U' Qk r B d L Lam eta delta eps s e.
     hausdorff_space top' /\ smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\ riemannian_metric atlas g0 /\
     mfd_diffeo top atlas W top' atlas' (IMAGE f W) f f' /\ xl IN W /\
     chart_at atlas xl = c0 /\ SND c0 xl = p /\ &0 < Qk /\
     mfd_differential atlas atlas' f xl z = U' /\ norm(inv(sqrt Qk) % z - v) <= delta /\
     &0 < r /\ cball(p,&2 * r) SUBSET IMAGE (SND c0) (FST c0) /\
     IMAGE (chart_inv c0) (cball(p,&2 * r)) SUBSET W /\
     (!s. abs s <= d
          ==> gamma0 s IN FST c0 /\
              ((\t. pastecart (SND c0 (gamma0(drop t))) (q0(drop t))) has_vector_derivative
               geo_spray (metric_local atlas c0 g0) (pastecart (SND c0 (gamma0 s)) (q0 s)))
              (at (lift s)) /\
              norm(SND c0 (gamma0 s) - p) <= r / &2 /\ norm(q0 s) <= B) /\
     SND c0 (gamma0(&0)) = p /\ q0(&0) = v /\
     &0 <= d /\ &0 < L /\ &0 <= Lam /\ &0 <= eta /\ &0 <= delta /\ &0 < eps /\
     eps <= r / &2 /\ eps <= &1 /\
     (delta + (eta * (B + &1) pow 2) / L) * exp(&3 * L * d) < eps /\
     (!Y Y'. Y IN cball(p,&2 * r) PCROSS cball(vec 0,B + &1) /\
             Y' IN cball(p,&2 * r) PCROSS cball(vec 0,B + &1)
             ==> norm(geo_spray (metric_local atlas c0 g0) Y -
                      geo_spray (metric_local atlas c0 g0) Y') <= L * norm(Y - Y')) /\
     (!y a b. y IN cball(p,&2 * r)
              ==> norm(christoffel (metric_local atlas c0 (mfd_pullback_metric atlas atlas' f g'))
                         y a b - christoffel (metric_local atlas c0 g0) y a b)
                  <= eta * norm a * norm b) /\
     (!y u. y IN cball(p,&2 * r)
            ==> u dot (metric_local atlas c0 g0 y ** u) <= Lam * norm u pow 2) /\
     sqrt Lam * eps < e /\ &0 <= s /\ s <= d
     ==> ?y. y IN W /\ f y = mfd_geo (top',atlas') g' (f xl) U' (s / sqrt Qk) /\
             mfd_dist (top,atlas) g0 y (gamma0 s) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (IMAGE (f:A->B) W)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(xl:A) IN topspace top /\ (f:A->B) xl IN topspace top'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET; FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `xl:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(gamma0:real->A) s IN FST (c0:(A->bool)#(A->real^N)) /\ norm(SND c0 (gamma0 s) - p) <= r / &2`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `q0:real->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= d
        ==> ((\t. pastecart (SND (c0:(A->bool)#(A->real^N)) ((gamma0:real->A)(drop t)))
                            ((q0:real->real^N)(drop t)))
             has_vector_derivative
             geo_spray (metric_local atlas c0 (g0:A->real^N^N))
               (pastecart (SND c0 (gamma0 s)) (q0 s))) (at (lift s)) /\
            norm(SND c0 (gamma0 s) - p) <= r / &2 /\ norm(q0 s) <= B`
  ASSUME_TAC THENL
   [X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s':real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `q0:real->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `(f:A->B) xl`; `U':real^N`; `inv(sqrt Qk)`] P2BPL_SLICE_GEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `IMAGE (f:A->B) W`;
                 `f:A->B`; `f':B->A`; `xl:A`] P2BPL_DIFF_SURJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                  (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) xl (inv(sqrt Qk) % (z:real^N)) =
                inv(sqrt Qk) % (U':real^N)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LINEAR_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `W:A->bool`; `IMAGE (f:A->B) W`;
                 `f:A->B`; `f':B->A`; `g':B->real^N^N`;
                 `mfd_geo (top',atlas') (g':B->real^N^N) ((f:A->B) xl) (inv(sqrt Qk) % U')`;
                 `xl:A`; `c0:(A->bool)#(A->real^N)`; `p:real^N`;
                 `metric_local atlas (c0:(A->bool)#(A->real^N)) (g0:A->real^N^N)`;
                 `\s. SND (c0:(A->bool)#(A->real^N)) ((gamma0:real->A) s)`; `q0:real->real^N`;
                 `v:real^N`; `inv(sqrt Qk) % (z:real^N)`; `r:real`; `B:real`; `d:real`; `L:real`;
                 `eta:real`; `delta:real`; `eps:real`] P2BPL_FWD_ONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `(f':B->A)(mfd_geo (top',atlas') (g':B->real^N^N) ((f:A->B) xl) (inv(sqrt Qk) % U') s)` THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                   `(f:A->B) xl`; `U':real^N`; `inv(sqrt Qk)`] P2BPL_SLICE_GEO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 th))]) THEN
    AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(SND (c0:(A->bool)#(A->real^N))
          ((f':B->A)(mfd_geo (top',atlas') (g':B->real^N^N) ((f:A->B) xl) (inv(sqrt Qk) % U') s)) -
         SND c0 ((gamma0:real->A) s)) < eps`
  ASSUME_TAC THENL [ASM_MESON_TAC[REAL_LET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g0:A->real^N^N`;
                 `c0:(A->bool)#(A->real^N)`; `cball(p:real^N,&2 * r)`; `Lam:real`;
                 `SND (c0:(A->bool)#(A->real^N))
                    ((f':B->A)(mfd_geo (top',atlas') (g':B->real^N^N) ((f:A->B) xl)
                                 (inv(sqrt Qk) % U') s))`;
                 `SND (c0:(A->bool)#(A->real^N)) ((gamma0:real->A) s)`] P2BPL_CHART_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CBALL; IN_CBALL] THEN
    UNDISCH_TAC
     `norm(SND (c0:(A->bool)#(A->real^N))
            ((f':B->A)(mfd_geo (top',atlas') (g':B->real^N^N) ((f:A->B) xl)
                         (inv(sqrt Qk) % U') s)) -
           SND c0 ((gamma0:real->A) s)) < eps` THEN
    UNDISCH_TAC `norm(SND (c0:(A->bool)#(A->real^N)) ((gamma0:real->A) s) - p) <= r / &2` THEN
    UNDISCH_TAC `eps <= r / &2` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt Lam * eps` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH `a <= b ==> b <= c ==> a <= c`)) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; dist; REAL_LT_IMP_LE]);;

(* The forward half of the orbit limit: times s in [0,d].                   *)

let P2BPL_ORBIT_FORWARD = prove
 (`!V x t Q top atlas g0 xl W phi (U:num->real^3) sub v.
       p2c_slice_limit_with V x t Q (top:B topology,atlas) g0 xl W phi /\
       (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                          (real->((A->bool)#(A->real^3))->bool)#
                                          (real->A->real^3^3)) (t n))
                                  (rfs_vatlas (V n) (t n)) /\
            hausdorff_space (rfs_vtop (V n) (t n)) /\
            riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
            mfd_complete (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                         (rfs_vmetric (V n) (t n))) /\
       p3_subseq sub /\
       (!e. &0 < e
            ==> ?n0. !n. n0 <= n
                         ==> ?z. mfd_differential atlas (rfs_vatlas (V (sub n)) (t (sub n)))
                                   (phi (sub n)) xl z = U (sub n) /\
                                 norm(inv(sqrt(Q(sub n))) % z - v) < e)
       ==> ?d. &0 < d /\
               !s e. &0 <= s /\ s <= d /\ &0 < e
                     ==> ?n0. !n. n0 <= n
                                  ==> ?y. y IN W (sub n) /\
                                          phi (sub n) y =
                                          mfd_geo (rfs_vtop (V (sub n)) (t (sub n)),
                                                   rfs_vatlas (V (sub n)) (t (sub n)))
                                                  (rfs_vmetric (V (sub n)) (t (sub n)))
                                                  (x (sub n)) (U (sub n))
                                                  (s / sqrt(Q(sub n))) /\
                                          mfd_dist (top,atlas) g0 y
                                                   (mfd_geo (top,atlas) g0 xl v s) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B)`;
                 `SND (chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B)) xl`; `v:real^3`]
         P2BPL_LIMIT_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((B->bool)#(B->real^3))->bool) (xl:B)` THEN
  ABBREV_TAC `p = SND (c0:(B->bool)#(B->real^3)) xl` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `q0:real->real^3`
    (X_CHOOSE_THEN `B:real` (X_CHOOSE_THEN `L:real` (X_CHOOSE_THEN `Lam:real`
      STRIP_ASSUME_TAC)))))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `e:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt Lam` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt Lam`; `e:real`] P2BPL_EPS_SMALL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
  ABBREV_TAC `eps = min (min (r / &2) (&1)) (e / (sqrt Lam + &1))` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= r / &2 /\ eps <= &1 /\ eps <= e / (sqrt Lam + &1)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt Lam * eps < e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt Lam * e / (sqrt Lam + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(B + &1) pow 2`; `L:real`; `exp(&3 * L * d)`; `eps:real`] P2BPL_EPS_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `delta:real` (X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `c0:(B->bool)#(B->real^3)`;
                 `cball(p:real^3,&2 * r)`; `eta:real`] P2BPL_CHRIST_C0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_MESON_TAC[CHART_AT];
    DISCH_THEN(X_CHOOSE_THEN `n1:num` (LABEL_TAC "chr"))] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `delta:real` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_differential")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n2:num` (LABEL_TAC "zz")) THEN
  EXISTS_TAC `MAX n1 n2` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `n <= (sub:num->num) n` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_subseq sub` THEN REWRITE_TAC[p3_subseq] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "zz" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "chr" (MP_TAC o SPEC `(sub:num->num) n`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `(sub:num->num) n` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) ((sub:num->num) n)) (t (sub n))`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) ((sub:num->num) n)) (t (sub n))`;
                 `(W:num->B->bool) ((sub:num->num) n)`; `(phi:num->B->A) ((sub:num->num) n)`; `psi:A->B`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) ((sub:num->num) n)) (t (sub n))`;
                 `g0:B->real^3^3`; `mfd_geo (top,atlas) (g0:B->real^3^3) xl v`; `xl:B`;
                 `c0:(B->bool)#(B->real^3)`; `p:real^3`; `q0:real->real^3`; `v:real^3`;
                 `z:real^3`; `(U:num->real^3) ((sub:num->num) n)`; `(Q:num->real) ((sub:num->num) n)`;
                 `r:real`; `B:real`; `d:real`; `L:real`; `Lam:real`; `eta:real`; `delta:real`;
                 `eps:real`; `s:real`; `e:real`] P2BPL_FWD_SLICE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Headline: the orbit limit for |s| <= d, by the forward result for        *)
(* (U,v) and for (--U,--v) with geodesic time reversal.                     *)

let P2BPL_ORBIT_LIMIT = prove
 (`!(u:A->bool) (w:B->bool). P2BPL_ORBIT_LIMIT_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BPL_ORBIT_LIMIT_STATEMENT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `U:num->real^3`; `sub:num->num`;
                 `v:real^3`] P2BPL_ORBIT_FORWARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f1"))) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `\n. --((U:num->real^3) n)`; `sub:num->num`;
                 `--(v:real^3)`] P2BPL_ORBIT_FORWARD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_differential")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `--(z:real^3)` THEN CONJ_TAC THENL
     [FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `(sub:num->num) n` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) ((sub:num->num) n)) (t (sub n))`;
                     `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) ((sub:num->num) n)) (t (sub n))`;
                     `(W:num->B->bool) ((sub:num->num) n)`; `IMAGE ((phi:num->B->A) ((sub:num->num) n)) (W (sub n))`;
                     `(phi:num->B->A) ((sub:num->num) n)`; `psi:A->B`; `xl:B`] P2BPL_DIFF_SURJ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_SIMP_TAC[LINEAR_NEG];
      REWRITE_TAC[VECTOR_ARITH `!c z v:real^N. c % --z - --v = --(c % z - v)`; NORM_NEG] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f2")))] THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `e:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [USE_THEN "f1" (MP_TAC o SPECL [`s:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
  USE_THEN "f2" (MP_TAC o SPECL [`--s:real`; `e:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k s. mfd_geo (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (t k),
                   rfs_vatlas (V k) (t k))
                  (rfs_vmetric (V k) (t k)) ((x:num->A) k) (--((U:num->real^3) k)) s =
          mfd_geo (rfs_vtop (V k) (t k),rfs_vatlas (V k) (t k))
                  (rfs_vmetric (V k) (t k)) (x k) (U k) (--s)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) k) (t k)`;
                   `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) k) (t k)`;
                   `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) k) (t k)`;
                   `(x:num->A) k`; `(U:num->real^3) k`; `-- &1`] P2BPL_SLICE_GEO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `k:num` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      MATCH_MP_TAC(SET_RULE `!x:A s t. x IN s ==> s SUBSET t ==> x IN t`) THEN
      SUBGOAL_THEN `(x:num->A) k = (phi:num->B->A) k xl` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID; REAL_MUL_LNEG; REAL_MUL_LID] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. mfd_geo (top,atlas) (g0:B->real^3^3) xl (--(v:real^3)) s =
        mfd_geo (top,atlas) g0 xl v (--s)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                   `xl:B`; `v:real^3`; `-- &1`] P2BPL_SLICE_GEO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID; REAL_MUL_LNEG; REAL_MUL_LID] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_NEG; real_div; REAL_MUL_LNEG] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

