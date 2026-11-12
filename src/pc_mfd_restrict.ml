(* ========================================================================= *)
(* pc_mfd_restrict: metrics on open submanifolds and pullbacks of metrics    *)
(* along diffeomorphisms.  A metric g of an atlas is a field of matrices in  *)
(* the preferred charts (pc_mfd_riem); restrict_metric atlas W g is g        *)
(* transported to the preferred charts of restrict_atlas atlas W             *)
(* (pc_mfd_maps); mfd_pullback_metric atlas atlas' f g' is f^* g' in the     *)
(* preferred charts of atlas.  Results: representatives in restricted        *)
(* charts, riemannian metrics of open submanifolds, locality of scalar,      *)
(* Ricci and sectional curvature (and of mfd_sec_min, mfd_rm_norm), the      *)
(* pullback metric of a diffeomorphism and its isometry (mfd_isometry of     *)
(* pc_grg_dist), naturality of curvature under isometries.                   *)
(*                                                                           *)
(* First: the definitions.                                                   *)
(* ========================================================================= *)

needs "src/pc_mfd_riem.ml";;
needs "src/pc_mfd_maps.ml";;
needs "src/pc_grg_dist.ml";;

prioritize_real();;
type_invention_error := true;;

(* A metric g of atlas transported to the preferred charts of the restricted *)
(* atlas on an open set W: its representative in the restricted chart chosen *)
(* at x, evaluated at x.                                                     *)

let restrict_metric = new_definition
 `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool)
                  (g:A->real^N^N) =
    \x. metric_local atlas (chart_at (restrict_atlas atlas W) x) g
                     (SND(chart_at (restrict_atlas atlas W) x) x)`;;

(* The pullback f^* g' of a metric g' of atlas' by a map f, in the preferred *)
(* charts of atlas: the pullback (mpullback) of the representative of g' in  *)
(* the preferred chart at f x by the chart representative of f, at x.        *)

let mfd_pullback_metric = new_definition
 `mfd_pullback_metric (atlas:((A->bool)#(A->real^N))->bool)
                      (atlas':((B->bool)#(B->real^N))->bool)
                      (f:A->B) (g':B->real^N^N) =
    \x. mpullback (SND(chart_at atlas' (f x)) o f o chart_inv(chart_at atlas x))
                  (metric_local atlas' (chart_at atlas' (f x)) g')
                  (SND(chart_at atlas x) x)`;;

(* ------------------------------------------------------------------------- *)
(* Restricted charts (U INTER W,phi) behave as (U,phi) on the points of W;   *)
(* the preferred restricted chart; representatives of the restricted metric; *)
(* riemannian metrics of open submanifolds.                                  *)
(* ------------------------------------------------------------------------- *)

let MFDR_CHART_INV_RESTRICT = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) W x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ x IN U INTER W
        ==> chart_inv (U INTER W,phi) (phi x) = x /\
            chart_inv (U,phi) (phi x) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[chart_inv; FST; SND] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_INTER] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART_INJ];
    ASM_MESON_TAC[CHART_INV]]);;

let MFDR_RESTRICT_IMAGE_OPEN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) W.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ open_in top W
        ==> open (IMAGE phi (U INTER W))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
  ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]);;

let MFDR_CHART_JAC_RESTRICT_L = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) W c' x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ open_in top W /\
        x IN U INTER W
        ==> chart_jac (U INTER W,phi) c' x = chart_jac (U,phi) c' x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_jac; SND] THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MFDR_RESTRICT_IMAGE_OPEN];
    ASM SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; chart_trans] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `z:A`]
           MFDR_CHART_INV_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MFDR_CHART_JAC_RESTRICT_R = prove
 (`!c (U:A->bool) (phi:A->real^N) W x.
        chart_jac c (U INTER W,phi) x = chart_jac c (U,phi) x`,
  REWRITE_TAC[chart_jac; chart_trans; SND]);;

let MFDR_METRIC_LOCAL_RESTRICT_CHART = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) W (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ open_in top W /\
        x IN U INTER W
        ==> metric_local atlas (U INTER W,phi) g (phi x) =
            metric_local atlas (U,phi) g (phi x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_local] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `x:A`]
         MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `chart_jac (U INTER W,phi) (chart_at atlas (x:A)) x =
    chart_jac (U,(phi:A->real^N)) (chart_at atlas x) x`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MFDR_CHART_JAC_RESTRICT_L THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MFDR_CHART_AT_RESTRICT = prove
 (`!top atlas (W:A->bool) x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        open_in top W /\ x IN W
        ==> ?U phi. (U,phi) IN atlas /\ x IN U /\
                    chart_at (restrict_atlas atlas W) x = (U INTER W,phi)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                 `x:A`] CHART_AT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY;
                 IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  SPEC_TAC(`chart_at (restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W)
                     (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS; FST] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)
                             ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `psi:A->real^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The central representation lemma: in a restricted chart (U INTER W,phi)  *)
(* the restricted metric has the representative of g in (U,phi).            *)

let METRIC_LOCAL_RESTRICT = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) W (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ open_in top W /\
        x IN U INTER W
        ==> metric_local (restrict_atlas atlas W) (U INTER W,phi)
                         (restrict_metric atlas W g) (phi x) =
            metric_local atlas (U,phi) g (phi x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `x:A`] MFDR_CHART_AT_RESTRICT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `phi':A->real^N`
    STRIP_ASSUME_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [metric_local] THEN BETA_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `x:A`]
         MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  ASM_REWRITE_TAC[restrict_metric; SND; MFDR_CHART_JAC_RESTRICT_R] THEN
  SUBGOAL_THEN
   `chart_jac (U INTER W,phi) (U',phi') (x:A) =
    chart_jac (U,(phi:A->real^N)) (U',phi') x`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_CHART_JAC_RESTRICT_L THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_local atlas (U' INTER W,phi') (g:A->real^N^N) (phi' x) =
    metric_local atlas (U',phi') g ((phi':A->real^N) x)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_METRIC_LOCAL_RESTRICT_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC METRIC_LOCAL_JAC THEN
  EXISTS_TAC `top:A topology` THEN ASM SET_TAC[]);;

let MFDR_METRIC_FIELD_EQ = prove
 (`!s (G:real^N->real^N^N) G'.
        metric_field s G /\ (!y. y IN s ==> G' y = G y) ==> metric_field s G'`,
  REWRITE_TAC[metric_field] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)` THEN
  ASM_SIMP_TAC[o_THM]);;

let RIEMANNIAN_METRIC_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        open_in top W
        ==> riemannian_metric (restrict_atlas atlas W) (restrict_metric atlas W g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `metric_local atlas (U,phi) (g:A->real^N^N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric; FST; SND]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFDR_RESTRICT_IMAGE_OPEN]; ALL_TAC] THEN
    SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Locality of curvature.  Scalar curvature, mfd_sec_min and mfd_rm_norm of  *)
(* the restricted metric are those of g; Ricci and sectional curvature agree *)
(* after the Jacobian J from the preferred restricted chart to the preferred *)
(* chart of atlas (a linear isomorphism).                                    *)
(* ------------------------------------------------------------------------- *)

let MFDR_LRICCI_CHART_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) x u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
        ==> lricci (metric_local atlas (U,phi) g) (phi x) u v =
            lricci (metric_local atlas (V,psi) g) (psi x)
                   (chart_jac (U,phi) (V,psi) x u) (chart_jac (U,phi) (V,psi) x v)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `lricci (mpullback (chart_trans (U:A->bool,phi:A->real^N) (V,psi))
                      (metric_local atlas (V,psi) (g:A->real^N^N)))
           (phi x) u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_TRANS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
    `metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
    `(phi:A->real^N) x`; `u:real^N`; `v:real^N`] LRICCI_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN
      MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[chart_jac; SND]]);;

let MFDR_LSECTIONAL_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y u v.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
        ==> lsectional G1 y u v = lsectional G2 y u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN
  SUBGOAL_THEN `(G1:real^N->real^N^N) y = G2 y` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lriemann (G1:real^N->real^N^N) y u v v = lriemann G2 y u v v`
   SUBST1_TAC THENL
   [MATCH_MP_TAC LRIEMANN_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REFL_TAC]);;

(* The restricted representation at a point of W, packaged. *)

let MFDR_RESTRICT_REP = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W
        ==> ?U phi. (U,phi) IN atlas /\ x IN U /\
                    chart_at (restrict_atlas atlas W) x = (U INTER W,phi) /\
                    open (IMAGE phi (U INTER W)) /\ phi x IN IMAGE phi (U INTER W) /\
                    !z. z IN IMAGE phi (U INTER W)
                        ==> metric_local (restrict_atlas atlas W) (U INTER W,phi)
                                         (restrict_metric atlas W g) z =
                            metric_local atlas (U,phi) g z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `x:A`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MFDR_RESTRICT_IMAGE_OPEN];
    ASM SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

let MFD_SCALAR_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        open_in top W /\ x IN W
        ==> mfd_scalar (restrict_atlas atlas W) (restrict_metric atlas W g) x =
            mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `g:A->real^N^N`; `x:A`] MFDR_RESTRICT_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [mfd_scalar] THEN ASM_REWRITE_TAC[SND] THEN
  TRANS_TAC EQ_TRANS
   `lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) ((phi:A->real^N) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFD_SCALAR_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MFD_RICCI_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        open_in top W /\ x IN W
        ==> mfd_ricci (restrict_atlas atlas W) (restrict_metric atlas W g) x u v =
            mfd_ricci atlas g x
              (chart_jac (chart_at (restrict_atlas atlas W) x) (chart_at atlas x) x u)
              (chart_jac (chart_at (restrict_atlas atlas W) x) (chart_at atlas x) x v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `g:A->real^N^N`; `x:A`] MFDR_RESTRICT_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[mfd_ricci] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SND] THEN
  SUBGOAL_THEN
   `chart_jac (U INTER W,phi) (V,psi) (x:A) =
    chart_jac (U,(phi:A->real^N)) (V,psi) x`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_CHART_JAC_RESTRICT_L THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lricci (metric_local atlas (U,phi) (g:A->real^N^N)) ((phi:A->real^N) x) u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFDR_LRICCI_CHART_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER]]);;

let MFD_SECTIONAL_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        open_in top W /\ x IN W
        ==> mfd_sectional (restrict_atlas atlas W) (restrict_metric atlas W g) x u v =
            mfd_sectional atlas g x
              (chart_jac (chart_at (restrict_atlas atlas W) x) (chart_at atlas x) x u)
              (chart_jac (chart_at (restrict_atlas atlas W) x) (chart_at atlas x) x v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `g:A->real^N^N`; `x:A`] MFDR_RESTRICT_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[mfd_sectional] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SND] THEN
  SUBGOAL_THEN
   `chart_jac (U INTER W,phi) (V,psi) (x:A) =
    chart_jac (U,(phi:A->real^N)) (V,psi) x`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_CHART_JAC_RESTRICT_L THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lsectional (metric_local atlas (U,phi) (g:A->real^N^N)) ((phi:A->real^N) x) u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LSECTIONAL_CHART_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER]]);;

(* The Jacobian between the two preferred charts is a linear isomorphism. *)

let MFDR_RESTRICT_JAC_ISO = prove
 (`!top atlas (W:A->bool) x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        open_in top W /\ x IN W
        ==> ?K. linear(chart_jac (chart_at (restrict_atlas atlas W) x)
                                 (chart_at atlas x) x) /\
                linear K /\
                (!w. K(chart_jac (chart_at (restrict_atlas atlas W) x)
                                 (chart_at atlas x) x w) = w) /\
                (!w. chart_jac (chart_at (restrict_atlas atlas W) x)
                               (chart_at atlas x) x (K w) = w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `x:A`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `chart_jac (U INTER W,phi) (V,psi) (x:A) =
    chart_jac (U,(phi:A->real^N)) (V,psi) x`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_CHART_JAC_RESTRICT_L THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `chart_jac (V,psi) (U,phi) (x:A):real^N->real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_JAC_LINEAR THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER];
    MATCH_MP_TAC CHART_JAC_LINEAR THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER];
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                  `x:A`] CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[IN_INTER; FUN_EQ_THM; o_THM];
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `V:A->bool`; `psi:A->real^N`; `U:A->bool`; `phi:A->real^N`;
                  `x:A`] CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[IN_INTER; FUN_EQ_THM; o_THM]]);;

(* The set of sectional curvatures at x is the same for both metrics. *)

let MFDR_SECTIONAL_SET_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        open_in top W /\ x IN W
        ==> {mfd_sectional (restrict_atlas atlas W) (restrict_metric atlas W g) x u v |
             u,v | ~collinear {vec 0,u,v}} =
            {mfd_sectional atlas g x u v | u,v | ~collinear {vec 0,u,v}}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `x:A`] MFDR_RESTRICT_JAC_ISO) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `J = chart_jac (chart_at (restrict_atlas atlas W) x)
                            (chart_at (atlas:((A->bool)#(A->real^N))->bool) x)
                            (x:A)` THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!u v. collinear {vec 0,(J:real^N->real^N) u,J v} <=> collinear {vec 0,u,v}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `{vec 0,(J:real^N->real^N) u,J v} = IMAGE J {vec 0,u,v}`
     SUBST1_TAC THENL
     [MP_TAC(MATCH_MP LINEAR_0 (ASSUME `linear (J:real^N->real^N)`)) THEN
      SIMP_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC COLLINEAR_LINEAR_IMAGE_EQ THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. collinear {vec 0,(K:real^N->real^N) u,K v} <=> collinear {vec 0,u,v}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `{vec 0,(K:real^N->real^N) u,K v} = IMAGE K {vec 0,u,v}`
     SUBST1_TAC THENL
     [MP_TAC(MATCH_MP LINEAR_0 (ASSUME `linear (K:real^N->real^N)`)) THEN
      SIMP_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC COLLINEAR_LINEAR_IMAGE_EQ THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. mfd_sectional (restrict_atlas atlas W) (restrict_metric atlas W g) x u v =
          mfd_sectional atlas (g:A->real^N^N) x ((J:real^N->real^N) u) (J v)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "J" THEN
    MATCH_MP_TAC MFD_SECTIONAL_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(J:real^N->real^N) u`; `(J:real^N->real^N) v`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`(K:real^N->real^N) u`; `(K:real^N->real^N) v`] THEN
    ASM_REWRITE_TAC[]]);;

let MFD_SEC_MIN_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        open_in top W /\ x IN W
        ==> mfd_sec_min (restrict_atlas atlas W) (restrict_metric atlas W g) x =
            mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sec_min] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MFDR_SECTIONAL_SET_RESTRICT THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

let MFD_RM_NORM_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        open_in top W /\ x IN W
        ==> mfd_rm_norm (restrict_atlas atlas W) (restrict_metric atlas W g) x =
            mfd_rm_norm atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `g:A->real^N^N`; `x:A`] MFDR_SECTIONAL_SET_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Chart representatives of a diffeomorphism; the pullback metric in an      *)
(* arbitrary chart pair.                                                     *)
(* ------------------------------------------------------------------------- *)

(* The chart representative of a diffeomorphism of open sets W, W' in charts *)
(* (U,phi), (V,psi) is a diffeomorphism of open subsets of real^N.           *)

let MFDR_DIFFEO_CHART_REP = prove
 (`!top atlas W top' atlas' W' (f:A->B) f' (U:A->bool) (phi:A->real^N)
    (V:B->bool) (psi:B->real^N).
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_diffeo top atlas W top' atlas' W' f f' /\
        (U,phi) IN atlas /\ (V,psi) IN atlas'
        ==> diffeomorphism_on
              (IMAGE phi {x | x IN U INTER W /\ f x IN V})
              (IMAGE psi {y | y IN V INTER W' /\ f' y IN U})
              (psi o f o chart_inv (U,phi)) (phi o f' o chart_inv (V,psi))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  UNDISCH_TAC `mfd_diffeo (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) W
                (top':B topology) (atlas':((B->bool)#(B->real^N))->bool) W' (f:A->B) f'` THEN
  REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(V:B->bool,psi:B->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  REWRITE_TAC[diffeomorphism_on] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`;
                   `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_REWRITE_TAC[FST; SND] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(V:B->bool,psi:B->real^N)`; `(U:A->bool,phi:A->real^N)`;
                   `W':B->bool`; `f':B->A`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_REWRITE_TAC[FST; SND] THEN SIMP_TAC[];
    SUBGOAL_THEN `(!x. x IN W ==> (f:A->B) x IN W') /\
                  (!y. y IN W' ==> (f':B->A) y IN W)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; o_THM; IN_INTER] THEN
    ASM_MESON_TAC[];
    SUBGOAL_THEN `(!x. x IN W ==> (f:A->B) x IN W') /\
                  (!y. y IN W' ==> (f':B->A) y IN W)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; o_THM; IN_INTER] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_THM; IN_INTER] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_THM; IN_INTER] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`(U:A->bool,phi:A->real^N)`;
                                  `(V:B->bool,psi:B->real^N)`] o
                  REWRITE_RULE[mfd_smooth_map] o
                  check (fun th -> can (find_term ((=) `f:A->B`)) (concl th) &&
                                   can (find_term (fun t -> is_const t &&
                                     fst(dest_const t) = "mfd_smooth_map")) (concl th))) THEN
    ASM_REWRITE_TAC[FST; SND];
    FIRST_X_ASSUM(MP_TAC o SPECL [`(V:B->bool,psi:B->real^N)`;
                                  `(U:A->bool,phi:A->real^N)`] o
                  REWRITE_RULE[mfd_smooth_map] o
                  check (fun th -> can (find_term ((=) `f':B->A`)) (concl th) &&
                                   can (find_term (fun t -> is_const t &&
                                     fst(dest_const t) = "mfd_smooth_map")) (concl th))) THEN
    ASM_REWRITE_TAC[FST; SND]]);;

(* The pullback metric in an arbitrary chart pair: the pullback of the       *)
(* representative of g' by the chart representative of f.                   *)

let MFD_PULLBACK_METRIC_LOCAL = prove
 (`!top atlas top' atlas' (f:A->B) f' (g':B->real^N^N) (U:A->bool)
    (phi:A->real^N) (V:B->bool) (psi:B->real^N) x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') f f' /\
        (U,phi) IN atlas /\ (V,psi) IN atlas' /\ x IN U /\ f x IN V
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
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:A->B) (topspace top) SUBSET topspace top'` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
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
                 `topspace top:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `topspace top':B->bool`; `f:A->B`; `f':B->A`;
                 `U0:A->bool`; `phi0:A->real^N`; `V0:B->bool`; `psi0:B->real^N`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `h0 = (psi0:B->real^N) o (f:A->B) o chart_inv (U0:A->bool,phi0:A->real^N)` THEN
  SUBGOAL_THEN `(h0:real^N->real^N) differentiable at ((phi0:A->real^N) x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi0:A->real^N)
                      {z | z IN U0 INTER topspace top /\ (f:A->B) z IN V0}`;
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
    SUBGOAL_THEN `continuous_map (top,top') (f:A->B)` ASSUME_TAC THENL
     [UNDISCH_TAC `continuous_map (subtopology top (topspace top),top') (f:A->B)` THEN
      REWRITE_TAC[SUBTOPOLOGY_TOPSPACE];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `frechet_derivative
        (\y. chart_trans (V0:B->bool,psi0:B->real^N) (V,psi)
               ((h0:real^N->real^N)
                  (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)))
        (at ((phi:A->real^N) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `IMAGE (phi:A->real^N)
                    {z | z IN U INTER {z | z IN U0 /\ (f:A->B) z IN V0} /\
                         f z IN V}` THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                       `(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`;
                       `{z | z IN U0 /\ (f:A->B) z IN V0}`; `f:A->B`]
                      MFDM_CHART_DOMAIN_OPEN) THEN
        REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
          MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN EXISTS_TAC `top':B topology` THEN
          ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY];
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

(* ------------------------------------------------------------------------- *)
(* The pullback metric of a diffeomorphism is a riemannian metric and makes  *)
(* f an isometry (mfd_isometry of pc_grg_dist); scalar and sectional         *)
(* curvature are natural under isometries.                                   *)
(* ------------------------------------------------------------------------- *)

let MFDR_METRIC_FIELD_LOCAL = prove
 (`!s (G:real^N->real^N^N).
        open s /\
        (!y. y IN s ==> ?t. open t /\ y IN t /\ metric_field t G)
        ==> metric_field s G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_field] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[metric_field];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[metric_field]]);;

let RIEMANNIAN_METRIC_PULLBACK = prove
 (`!top atlas top' atlas' (f:A->B) f' (g':B->real^N^N).
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') f f' /\
        riemannian_metric atlas' g'
        ==> riemannian_metric atlas (mfd_pullback_metric atlas atlas' f g')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:A->B) (topspace top) SUBSET topspace top'` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) x`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)`,
           `c':(B->bool)#(B->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`V:B->bool`; `psi:B->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `topspace top':B->bool`; `f:A->B`; `f':B->A`;
                 `U:A->bool`; `phi:A->real^N`; `V:B->bool`; `psi:B->real^N`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE (phi:A->real^N)
                {z | z IN U INTER topspace top /\ (f:A->B) z IN V}` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on];
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `mpullback ((psi:B->real^N) o (f:A->B) o chart_inv (U:A->bool,phi:A->real^N))
                        (metric_local atlas' (V,psi) (g':B->real^N^N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (psi:B->real^N) {y | y IN V INTER topspace top' /\ (f':B->A) y IN U}`;
      `(phi:A->real^N) o (f':B->A) o chart_inv (V:B->bool,psi:B->real^N)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:B->real^N) V` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric; FST; SND]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PULLBACK_METRIC_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `f':B->A`] THEN
    ASM_REWRITE_TAC[]]);;

let MFD_ISOMETRY_PULLBACK = prove
 (`!top atlas top' atlas' (f:A->B) f' (g':B->real^N^N).
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') f f'
        ==> mfd_isometry (top,atlas) (mfd_pullback_metric atlas atlas' f g')
                         (top',atlas') g' f f'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_isometry] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PULLBACK_METRIC_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `f':B->A`] THEN
  ASM_REWRITE_TAC[]);;

let MFDR_LSECTIONAL_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y u v.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> lsectional (mpullback h G) y u v =
            lsectional G (h y) (frechet_derivative h (at y) u)
                               (frechet_derivative h (at y) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[lsectional] THEN ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `v:real^N`; `v:real^N`] LRIEMANN_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* An isometry is, near each point and in the preferred charts, the pullback *)
(* by a diffeomorphism of open subsets of real^N.                            *)

let MFDR_ISOMETRY_REP = prove
 (`!top atlas top' atlas' (g:A->real^N^N) (g':B->real^N^N) f f' x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ x IN topspace top
        ==> ?t t' h'.
              open t /\ SND(chart_at atlas x) x IN t /\
              diffeomorphism_on t t'
                (SND(chart_at atlas' (f x)) o f o chart_inv (chart_at atlas x)) h' /\
              metric_field t' (metric_local atlas' (chart_at atlas' (f x)) g') /\
              (!z. z IN t
                   ==> metric_local atlas (chart_at atlas x) g z =
                       mpullback (SND(chart_at atlas' (f x)) o f o
                                  chart_inv (chart_at atlas x))
                                 (metric_local atlas' (chart_at atlas' (f x)) g') z) /\
              (SND(chart_at atlas' (f x)) o f o chart_inv (chart_at atlas x))
                (SND(chart_at atlas x) x) = SND(chart_at atlas' (f x)) (f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_isometry] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:A->B) (topspace top) SUBSET topspace top'` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) x`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)`,
           `c':(B->bool)#(B->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:B->bool`; `psi:B->real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `topspace top':B->bool`; `f:A->B`; `f':B->A`;
                 `U:A->bool`; `phi:A->real^N`; `V:B->bool`; `psi:B->real^N`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi:A->real^N) {z | z IN U INTER topspace top /\ (f:A->B) z IN V}`;
    `IMAGE (psi:B->real^N) {y | y IN V INTER topspace top' /\ (f':B->A) y IN U}`;
    `(phi:A->real^N) o (f':B->A) o chart_inv (V:B->bool,psi:B->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on];
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:B->real^N) V` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric; FST; SND]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(U:A->bool,phi:A->real^N)`;
                                  `(V:B->bool,psi:B->real^N)`] o
      check (fun th -> can (find_term (fun t -> is_const t &&
                         fst(dest_const t) = "mpullback")) (concl th))) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]]);;

let MFD_ISOMETRY_SCALAR = prove
 (`!top atlas top' atlas' (g:A->real^N^N) (g':B->real^N^N) f f' x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ x IN topspace top
        ==> mfd_scalar atlas g x = mfd_scalar atlas' g' (f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                `g:A->real^N^N`; `g':B->real^N^N`; `f:A->B`; `f':B->A`; `x:A`]
               MFDR_ISOMETRY_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `t':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_scalar] THEN
  TRANS_TAC EQ_TRANS
   `lscalar (mpullback (SND(chart_at atlas' ((f:A->B) x)) o f o
                        chart_inv (chart_at atlas x))
                       (metric_local atlas' (chart_at atlas' (f x))
                                     (g':B->real^N^N)))
            (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    MATCH_MP_TAC LSCALAR_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`t':real^N->bool`; `t:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let MFD_ISOMETRY_SECTIONAL = prove
 (`!top atlas top' atlas' (g:A->real^N^N) (g':B->real^N^N) f f' x u v.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ x IN topspace top
        ==> mfd_sectional atlas g x u v =
            mfd_sectional atlas' g' (f x)
              (frechet_derivative (SND(chart_at atlas' (f x)) o f o
                                   chart_inv (chart_at atlas x))
                                  (at (SND(chart_at atlas x) x)) u)
              (frechet_derivative (SND(chart_at atlas' (f x)) o f o
                                   chart_inv (chart_at atlas x))
                                  (at (SND(chart_at atlas x) x)) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                `g:A->real^N^N`; `g':B->real^N^N`; `f:A->B`; `f':B->A`; `x:A`]
               MFDR_ISOMETRY_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `t':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_sectional] THEN
  TRANS_TAC EQ_TRANS
   `lsectional (mpullback (SND(chart_at atlas' ((f:A->B) x)) o f o
                           chart_inv (chart_at atlas x))
                          (metric_local atlas' (chart_at atlas' (f x))
                                        (g':B->real^N^N)))
               (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x) u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
      (RAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [SYM th]) THEN
    MATCH_MP_TAC MFDR_LSECTIONAL_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`t':real^N->bool`; `t:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

(* Constant sectional curvature is carried along isometries (space forms). *)

let MFD_ISOMETRY_SECTIONAL_CONST = prove
 (`!top atlas top' atlas' (g:A->real^N^N) (g':B->real^N^N) f f' k.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        (!y u v. y IN topspace top' /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas' g' y u v = k)
        ==> !x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> mfd_sectional atlas g x u v = k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                `g:A->real^N^N`; `g':B->real^N^N`; `f:A->B`; `f':B->A`; `x:A`;
                `u:real^N`; `v:real^N`] MFD_ISOMETRY_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                `g:A->real^N^N`; `g':B->real^N^N`; `f:A->B`; `f':B->A`; `x:A`]
               MFDR_ISOMETRY_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `t':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `mfd_isometry (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                   (g:A->real^N^N)
                   (top':B topology,atlas':((B->bool)#(B->real^N))->bool)
                   (g':B->real^N^N) (f:A->B) f'` THEN
    REWRITE_TAC[mfd_isometry] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t':real^N->bool`; `t:real^N->bool`;
                 `SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)) o f o
                  chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x)`;
                 `h':real^N->real^N`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x`]
                LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative
                    (SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)) o f o
                     chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                    (at (SND(chart_at atlas x) x))` THEN
  SUBGOAL_THEN `{vec 0,(D:real^N->real^N) u,D v} = IMAGE D {vec 0,u,v}`
   SUBST1_TAC THENL
   [MP_TAC(MATCH_MP LINEAR_0 (ASSUME `linear (D:real^N->real^N)`)) THEN
    SIMP_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL [`D:real^N->real^N`; `{vec 0:real^N,u,v}`]
                               COLLINEAR_LINEAR_IMAGE_EQ)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sanity check: restricting to the whole space changes nothing.             *)
(* ------------------------------------------------------------------------- *)

let RESTRICT_ATLAS_TOPSPACE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool).
        smooth_manifold_atlas top atlas
        ==> restrict_atlas atlas (topspace top) = atlas`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SET_RULE `(s:A->bool) SUBSET t ==> s INTER t = s`];
    DISCH_TAC THEN EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(V:A->bool) SUBSET topspace top` MP_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET]; SET_TAC[]]]);;

let RESTRICT_METRIC_TOPSPACE = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ x IN topspace top
        ==> restrict_metric atlas (topspace top) g x = g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[restrict_metric] THEN
  ASM_SIMP_TAC[RESTRICT_ATLAS_TOPSPACE] THEN
  MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

