(* ========================================================================= *)
(* Unit pc_rfs_history: finite Ricci flow histories with surgery on ONE      *)
(* carrier type A (for the top statement A is replaced by A + num#num#real^3: *)
(* old points stay where they are, cap points are new).                      *)
(*                                                                           *)
(* A history has stages k = 0..n (closed 3-manifolds, the empty stage        *)
(* allowed), times tm 0 = 0 < tm 1 < ... < tm n < tm (n+1) (the horizon),    *)
(* slab k = a Ricci flow on stage k over [tm k, tm (k+1)), and events        *)
(* k = 1..n at tm k turning stage k-1 into stage k by cutting along neck     *)
(* spheres, capping both sides with balls and discarding components.  The   *)
(* retained old points are literally the same points in both stages (the     *)
(* identity is the flow identification of MT), so MT's space-time is the     *)
(* view t |-> (stage at t, its atlas, its metric) and flow lines are         *)
(* constant points.  The cut-and-cap data come from pc_mfd_cut and          *)
(* restrict_metric from pc_mfd_restrict.                                     *)
(* ========================================================================= *)

needs "src/pc_rfs_geom.ml";;
needs "src/pc_mfd_cut.ml";;
needs "src/pc_mfd_restrict.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* H1. Events.  Fields: Omega (open set of the old stage where the slab      *)
(* converges, MT Thm 11.19), the limit metric on Omega (old atlas), the      *)
(* finite index set of surgery necks, the necks (strong delta-necks of the   *)
(* limit flow; their restrictions to annulus 1/2 2 are the cut charts), the  *)
(* ball charts of the caps on the plus side (discarded) and on the minus     *)
(* side (retained), the cut-and-capped manifold Z (topology, atlas) and its  *)
(* discarded part D (a union of components of Z).                            *)
(* ------------------------------------------------------------------------- *)

let rfs_event_INDUCT,rfs_event_RECURSION = define_type
 "rfs_event = RfsEvent (A->bool) (A->real^3^3) (num->bool) (num->real^3->A)
                       (num->real^3->A) (num->real^3->A) (A topology)
                       (((A->bool)#(A->real^3))->bool) (A->bool)";;

let ev_omega = new_recursive_definition rfs_event_RECURSION
 `ev_omega (RfsEvent (om:A->bool) gl ix ne cp cm zt za ds) = om`;;
let ev_limit = new_recursive_definition rfs_event_RECURSION
 `ev_limit (RfsEvent (om:A->bool) gl ix ne cp cm zt za ds) = gl`;;
let ev_index = new_recursive_definition rfs_event_RECURSION
 `ev_index (RfsEvent (om:A->bool) gl ix ne cp cm zt za ds) = ix`;;
let ev_neck = new_recursive_definition rfs_event_RECURSION
 `ev_neck (RfsEvent (om:A->bool) gl ix ne cp cm zt za ds) = ne`;;
let ev_capp = new_recursive_definition rfs_event_RECURSION
 `ev_capp (RfsEvent (om:A->bool) gl ix ne cp cm zt za ds) = cp`;;
let ev_capm = new_recursive_definition rfs_event_RECURSION
 `ev_capm (RfsEvent (om:A->bool) gl ix ne cp cm zt za ds) = cm`;;
let ev_ztop = new_recursive_definition rfs_event_RECURSION
 `ev_ztop (RfsEvent (om:A->bool) gl ix ne cp cm zt za ds) = zt`;;
let ev_zatlas = new_recursive_definition rfs_event_RECURSION
 `ev_zatlas (RfsEvent (om:A->bool) gl ix ne cp cm zt za ds) = za`;;
let ev_disc = new_recursive_definition rfs_event_RECURSION
 `ev_disc (RfsEvent (om:A->bool) gl ix ne cp cm zt za ds) = ds`;;

(* ------------------------------------------------------------------------- *)
(* H2. Histories.  Fields: the number n of events, the times, the stage      *)
(* topologies and atlases, the slab metrics (hs_metric hs k t = metric of    *)
(* slab k at time t, preferred charts of stage k), the events.               *)
(* ------------------------------------------------------------------------- *)

let rfs_history_INDUCT,rfs_history_RECURSION = define_type
 "rfs_history = RfsHistory num (num->real) (num->A topology)
                           (num->((A->bool)#(A->real^3))->bool)
                           (num->real->A->real^3^3) (num->(A)rfs_event)";;

let hs_count = new_recursive_definition rfs_history_RECURSION
 `hs_count (RfsHistory n tm (st:num->A topology) sa gm ev) = n`;;
let hs_time = new_recursive_definition rfs_history_RECURSION
 `hs_time (RfsHistory n tm (st:num->A topology) sa gm ev) = tm`;;
let hs_top = new_recursive_definition rfs_history_RECURSION
 `hs_top (RfsHistory n tm (st:num->A topology) sa gm ev) = st`;;
let hs_atlas = new_recursive_definition rfs_history_RECURSION
 `hs_atlas (RfsHistory n tm (st:num->A topology) sa gm ev) = sa`;;
let hs_metric = new_recursive_definition rfs_history_RECURSION
 `hs_metric (RfsHistory n tm (st:num->A topology) sa gm ev) = gm`;;
let hs_event = new_recursive_definition rfs_history_RECURSION
 `hs_event (RfsHistory n tm (st:num->A topology) sa gm ev) = ev`;;

(* ------------------------------------------------------------------------- *)
(* H3. Cut-and-cap data: mfd_cut_cap of unit pc_mfd_cut (with                *)
(* mfd_cut_spheres and mfd_cut_cores), in exactly the form of the endgame    *)
(* sphere-system statement.                                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* H4. Analytic glue at an event: smooth convergence of the slab on compact  *)
(* subsets of Omega to the limit metric (MT Thm 11.19, Def 11.22), measured  *)
(* with lck_dist2 (all orders k); equality of two metrics given in two       *)
(* atlases on a common open set W (the identity is an isometry there; the    *)
(* clause of mfd_isometry).                                                  *)
(* ------------------------------------------------------------------------- *)

let rfs_limit_metric = new_definition
 `rfs_limit_metric (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (Om:A->bool) (ts:real) (g:real->A->real^3^3)
                   (gl:A->real^3^3) <=>
    (!c. c IN atlas
         ==> metric_field (IMAGE (SND c) (FST c INTER Om)) (metric_local atlas c gl)) /\
    (!K k e. compact_in top K /\ K SUBSET Om /\ &0 < e
             ==> ?d. &0 < d /\
                     !t x. ts - d < t /\ t < ts /\ x IN K
                           ==> lck_dist2 k (metric_local atlas (chart_at atlas x) gl)
                                           (metric_local atlas (chart_at atlas x) (g t))
                                           (SND(chart_at atlas x) x) < e)`;;

let rfs_same_metric_on = new_definition
 `rfs_same_metric_on (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
                     (atlas':((A->bool)#(A->real^3))->bool) (g':A->real^3^3)
                     (W:A->bool) <=>
    !c c' y. c IN atlas /\ c' IN atlas' /\
             y IN IMAGE (SND c) (FST c INTER FST c' INTER W)
             ==> metric_local atlas c g y =
                 mpullback (SND c' o chart_inv c) (metric_local atlas' c' g') y`;;

(* ------------------------------------------------------------------------- *)
(* H5. One event (k-1 -> k) at time ts: X = old stage with slab metric gX,   *)
(* Y = new stage with slab metric gY.  Cut-and-cap with the identity map,    *)
(* cap cores are new points (disjoint from X), cuts inside Omega, Z closed,  *)
(* D clopen in Z with all plus caps discarded and all minus caps retained,   *)
(* Y = Z minus D (subtopology and restricted atlas), retained old points     *)
(* lie in Omega and carry the limit metric at time ts.                       *)
(* ------------------------------------------------------------------------- *)

let rfs_event_ok = new_definition
 `rfs_event_ok (topX:A topology,atlasX:((A->bool)#(A->real^3))->bool)
               (gX:real->A->real^3^3) (ts:real)
               (topY:A topology,atlasY:((A->bool)#(A->real^3))->bool)
               (gY:real->A->real^3^3) (ev:(A)rfs_event) <=>
    open_in topX (ev_omega ev) /\
    rfs_limit_metric (topX,atlasX) (ev_omega ev) ts gX (ev_limit ev) /\
    hausdorff_space (ev_ztop ev) /\
    smooth_manifold_atlas (ev_ztop ev) (ev_zatlas ev) /\
    compact_space (ev_ztop ev) /\
    mfd_cut_cap topX atlasX (ev_ztop ev) (ev_zatlas ev) (ev_index ev)
                (ev_neck ev) (ev_capp ev) (ev_capm ev) (\x. x) (\x. x) /\
    DISJOINT (topspace topX) (mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm ev)) /\
    (!i. i IN ev_index ev
         ==> IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)) SUBSET ev_omega ev) /\
    ev_disc ev SUBSET topspace(ev_ztop ev) /\
    open_in (ev_ztop ev) (ev_disc ev) /\ closed_in (ev_ztop ev) (ev_disc ev) /\
    (!i. i IN ev_index ev
         ==> IMAGE (ev_capp ev i) (cball(vec 0,&1)) SUBSET ev_disc ev /\
             DISJOINT (IMAGE (ev_capm ev i) (cball(vec 0,&1))) (ev_disc ev)) /\
    topY = subtopology (ev_ztop ev) (topspace(ev_ztop ev) DIFF ev_disc ev) /\
    atlasY = restrict_atlas (ev_zatlas ev) (topspace(ev_ztop ev) DIFF ev_disc ev) /\
    topspace topY INTER topspace topX SUBSET ev_omega ev /\
    rfs_same_metric_on atlasX (ev_limit ev) atlasY (gY ts)
                       (topspace topY INTER topspace topX)`;;

(* ------------------------------------------------------------------------- *)
(* H6. Structural conditions on a history: times, closed stages, Ricci flow  *)
(* slabs smooth up to their initial times (ricci_flow_from), events.         *)
(* ------------------------------------------------------------------------- *)

let rfs_history_ok = new_definition
 `rfs_history_ok (hs:(A)rfs_history) <=>
    hs_time hs 0 = &0 /\
    (!k. k <= hs_count hs ==> hs_time hs k < hs_time hs (k + 1)) /\
    (!k. k <= hs_count hs
         ==> hausdorff_space (hs_top hs k) /\
             smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
             compact_space (hs_top hs k) /\
             ricci_flow_from (hs_top hs k,hs_atlas hs k) (hs_time hs k)
                             (hs_time hs (k + 1)) (hs_metric hs k)) /\
    (!k. 1 <= k /\ k <= hs_count hs
         ==> rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1))
                          (hs_metric hs (k - 1)) (hs_time hs k)
                          (hs_top hs k,hs_atlas hs k) (hs_metric hs k)
                          (hs_event hs k))`;;

(* ------------------------------------------------------------------------- *)
(* H7. The space-time view of a history: the slab containing t, the slice    *)
(* at t (empty outside [0, horizon), with the metric mat 1 there, so that   *)
(* views of a history and of its extensions agree literally before the      *)
(* earlier horizon), and the pre-surgery view at event k:                    *)
(* MT's maximal extension to time tm k (the slice at tm k is the open        *)
(* submanifold Omega of the old stage with the limit metric, transported to  *)
(* the restricted atlas; earlier times as in the history).                   *)
(* ------------------------------------------------------------------------- *)

let rfs_slab = new_definition
 `rfs_slab (hs:(A)rfs_history) (t:real) =
    @k. k <= hs_count hs /\ hs_time hs k <= t /\ t < hs_time hs (k + 1)`;;

let rfs_live = new_definition
 `rfs_live (hs:(A)rfs_history) (t:real) <=>
    &0 <= t /\ t < hs_time hs (hs_count hs + 1)`;;

let rfs_top_at = new_definition
 `rfs_top_at (hs:(A)rfs_history) (t:real) =
    if rfs_live hs t then hs_top hs (rfs_slab hs t) else discrete_topology {}`;;

let rfs_atlas_at = new_definition
 `rfs_atlas_at (hs:(A)rfs_history) (t:real) =
    if rfs_live hs t then hs_atlas hs (rfs_slab hs t) else {}`;;

let rfs_metric_at = new_definition
 `rfs_metric_at (hs:(A)rfs_history) (t:real) =
    if rfs_live hs t then hs_metric hs (rfs_slab hs t) t else (\x:A. mat 1)`;;

let rfs_view = new_definition
 `rfs_view (hs:(A)rfs_history) =
    rfs_top_at hs,rfs_atlas_at hs,rfs_metric_at hs`;;

let rfs_preview = new_definition
 `rfs_preview (hs:(A)rfs_history) (k:num) =
    (\t. if t = hs_time hs k
         then subtopology (hs_top hs (k - 1)) (ev_omega(hs_event hs k))
         else if t < hs_time hs k then rfs_top_at hs t
         else discrete_topology {}),
    (\t. if t = hs_time hs k
         then restrict_atlas (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k))
         else if t < hs_time hs k then rfs_atlas_at hs t else {}),
    (\t. if t = hs_time hs k
         then restrict_metric (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k))
                                  (ev_limit(hs_event hs k))
         else rfs_metric_at hs t)`;;

(* ------------------------------------------------------------------------- *)
(* H8. Surgery parameters (MT Def 15.5, 15.7; Qin et al.: they may depend on *)
(* the initial manifold): canonical neighbourhood parameter rp, surgery      *)
(* control dl, noncollapsing kp, surgery scale h <= dl^2 rp (h = h(rho,dl)   *)
(* of MT Thm 11.31, rho = dl rp).                                            *)
(* ------------------------------------------------------------------------- *)

let rfs_params = new_definition
 `rfs_params (rp:real->real,dl:real->real,kp:real->real,h:real->real) <=>
    (!t. &0 <= t
         ==> &0 < rp t /\ &0 < dl t /\ &0 < kp t /\ &0 < h t /\
             h t <= dl t pow 2 * rp t) /\
    (!s t. &0 <= s /\ s <= t ==> rp t <= rp s /\ dl t <= dl s /\ kp t <= kp s)`;;

(* ------------------------------------------------------------------------- *)
(* H9. Control at event k (MT Assumptions (5), (6) and the surgery scale of  *)
(* Def 15.5): every cut neck is a strong dl(ts)-neck of the maximal          *)
(* extension centred at a point y with R(y) = h(ts)^-2, and for t' < ts      *)
(* close to ts every point of the disappearing region D_t' (old points not   *)
(* retained) has a strong (C,eps)-canonical neighbourhood at time t'.        *)
(* ------------------------------------------------------------------------- *)

let rfs_surgery_ok = new_definition
 `rfs_surgery_ok (hs:(A)rfs_history) (C:real) (eps:real) (dl:real->real)
                 (h:real->real) (k:num) <=>
    (!i. i IN ev_index(hs_event hs k)
         ==> ?y. rfs_strong_neck (rfs_preview hs k) (dl(hs_time hs k)) y
                                 (hs_time hs k) (ev_neck(hs_event hs k) i) /\
                 rfs_vscalar (rfs_preview hs k) (hs_time hs k) y =
                 inv(h(hs_time hs k) pow 2)) /\
    (?t1. hs_time hs (k - 1) <= t1 /\ t1 < hs_time hs k /\
          !t x. t1 < t /\ t < hs_time hs k /\
                x IN topspace(hs_top hs (k - 1)) DIFF topspace(hs_top hs k)
                ==> ?U. rfs_strong_canonical (rfs_view hs) C eps x t U)`;;

(* MT Assumption (7): a slab that ends at an event is maximal (its curvature *)
(* is unbounded near the event time).                                        *)

let rfs_slab_maximal = new_definition
 `rfs_slab_maximal (hs:(A)rfs_history) (k:num) <=>
    !B. ?t x. hs_time hs k <= t /\ t < hs_time hs (k + 1) /\
              x IN topspace(hs_top hs k) /\
              B < mfd_rm_norm (hs_atlas hs k) (hs_metric hs k t) x`;;

(* ------------------------------------------------------------------------- *)
(* H10. Controlled histories: MT Assumptions (1)-(7) (Assumption (1)'s       *)
(* RP^2 clause replaced by orientable stages; (2) and (4) are built in),     *)
(* pinching toward positive, the strong (C,eps)-canonical neighbourhood      *)
(* assumption with parameter rp, kp-noncollapsing on scales <= eps (the      *)
(* conclusions of MT Thm 15.9 / Cor 15.10).                                  *)
(* ------------------------------------------------------------------------- *)

let rfs_controlled = new_definition
 `rfs_controlled (C:real,eps:real) (rp:real->real,dl:real->real,kp:real->real,
                                    h:real->real) (hs:(A)rfs_history) <=>
    rfs_history_ok hs /\ rfs_params (rp,dl,kp,h) /\
    (!k. k <= hs_count hs ==> mfd_orientable (hs_top hs k) (hs_atlas hs k)) /\
    (!k. 1 <= k /\ k <= hs_count hs ==> rfs_surgery_ok hs C eps dl h k) /\
    (!k. k < hs_count hs ==> rfs_slab_maximal hs k) /\
    rfs_pinched (rfs_view hs) /\
    rfs_canonical_assumption (rfs_view hs) C eps rp /\
    rfs_noncollapsed (rfs_view hs) kp eps`;;

(* ------------------------------------------------------------------------- *)
(* H11. Initial identification with a Riemannian manifold on another type    *)
(* (a diffeomorphism which is an isometry onto stage 0 at time 0), and       *)
(* extinction (the last stage is empty).                                     *)
(* ------------------------------------------------------------------------- *)

let rfs_initial = new_definition
 `rfs_initial (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
              (g:A->real^3^3) (hs:(B)rfs_history) (iota:A->B) (iota':B->A) <=>
    mfd_diffeo top atlas (topspace top) (hs_top hs 0) (hs_atlas hs 0)
               (topspace(hs_top hs 0)) iota iota' /\
    mfd_isometry (top,atlas) g (hs_top hs 0,hs_atlas hs 0) (hs_metric hs 0 (&0))
                 iota iota'`;;

let rfs_extinct = new_definition
 `rfs_extinct (hs:(A)rfs_history) <=> topspace(hs_top hs (hs_count hs)) = {}`;;

(* ------------------------------------------------------------------------- *)
(* H11b. Horizon and extension (for the continuation form of MT Thm 15.9:    *)
(* a controlled history on [0,T) extends to a controlled history with a      *)
(* later horizon; Lemma 17.12 bounds the number of events on bounded time    *)
(* intervals).  hs' extends hs: same events, times, stages and slab metrics  *)
(* up to the horizon of hs.                                                  *)
(* ------------------------------------------------------------------------- *)

let rfs_horizon = new_definition
 `rfs_horizon (hs:(A)rfs_history) = hs_time hs (hs_count hs + 1)`;;

let rfs_extends = new_definition
 `rfs_extends (hs:(A)rfs_history) (hs':(A)rfs_history) <=>
    hs_count hs <= hs_count hs' /\
    rfs_horizon hs <= hs_time hs' (hs_count hs + 1) /\
    (!k. k <= hs_count hs
         ==> hs_time hs' k = hs_time hs k /\
             hs_top hs' k = hs_top hs k /\ hs_atlas hs' k = hs_atlas hs k /\
             (!t. hs_time hs k <= t /\ t < hs_time hs (k + 1)
                  ==> hs_metric hs' k t = hs_metric hs k t)) /\
    (!k. 1 <= k /\ k <= hs_count hs ==> hs_event hs' k = hs_event hs k)`;;

(* ------------------------------------------------------------------------- *)
(* H12. Components: all simply connected, all diffeomorphic to S^3.          *)
(* ------------------------------------------------------------------------- *)

let rfs_components_sc = new_definition
 `rfs_components_sc (top:A topology) <=>
    !U. U IN connected_components_of top ==> simply_connected_space (subtopology top U)`;;

let rfs_components_s3 = new_definition
 `rfs_components_s3 (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) <=>
    !U. U IN connected_components_of top
        ==> mfd_diffeomorphic (subtopology top U) (restrict_atlas atlas U)
              (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas`;;

(* ------------------------------------------------------------------------- *)
(* H13. Space-time curves parametrized by backward time tau in [a,b] from    *)
(* the time tt (MT Ch 6 and Ch 16): gamma tau lies in the slice at           *)
(* tt - tau, is continuous in the slice topology at each tau (so near a      *)
(* surgery time it runs through retained points), and is C^1 in every chart  *)
(* of each stage on the times in (a,b] spent in that stage (not at tau = a: *)
(* L-geodesics behave like sqrt tau there, MT Def 6.9 as corrected).  Used  *)
(* by the L-geometry of Part 3.                                             *)
(* ------------------------------------------------------------------------- *)

let rfs_st_curve = new_definition
 `rfs_st_curve (hs:(A)rfs_history) (tt:real) (gamma:real->A) (a:real) (b:real) <=>
    a <= b /\
    (!tau. a <= tau /\ tau <= b ==> gamma tau IN topspace(rfs_top_at hs (tt - tau))) /\
    (!tau0 O. a <= tau0 /\ tau0 <= b /\ open_in (rfs_top_at hs (tt - tau0)) O /\
              gamma tau0 IN O
              ==> ?d. &0 < d /\
                      !tau. a <= tau /\ tau <= b /\ abs(tau - tau0) < d
                            ==> gamma tau IN O) /\
    (!k c. k <= hs_count hs /\ c IN hs_atlas hs k
           ==> continuously_differentiable 1
                 {s | a < drop s /\ drop s <= b /\
                      hs_time hs k <= tt - drop s /\ tt - drop s < hs_time hs (k + 1) /\
                      gamma(drop s) IN FST c}
                 (\s. SND c (gamma(drop s))))`;;

