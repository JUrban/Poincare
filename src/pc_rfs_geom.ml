(* ========================================================================= *)
(* Unit pc_rfs_geom: the geometric notions of Morgan-Tian (MT) used by the   *)
(* top statements of the surgery layer, for one Riemannian 3-manifold and    *)
(* for time-dependent families of manifolds and metrics on one carrier type  *)
(* (views, used for flows and for the space-time of a surgery history):      *)
(* closeness, necks, twisted charts, caps, C-components, round components,   *)
(* canonical neighbourhoods, pinching, normalized metrics, noncollapsing,    *)
(* the listed pieces of MT Prop 15.3.  Metrics are matrix fields in the      *)
(* preferred charts of their atlas (as in pc_mfd_riem); a metric is only     *)
(* ever used together with its own atlas.  Curvature conventions: sectional  *)
(* normalization, nu = mfd_sec_min, |Rm| = mfd_rm_norm.                      *)
(* ========================================================================= *)

needs "src/pc_rf_basic.ml";;
needs "src/pc_lrg_tensor.ml";;
needs "src/pc_lrg_lap.ml";;
needs "src/pc_grg_dist.ml";;
needs "src/pc_grg_dist_in.ml";;
needs "src/pc_grg_voldefs.ml";;
needs "src/pc_mfd_maps.ml";;
needs "src/pc_mfd_examples.ml";;
needs "src/pc_smt_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* G0. Helpers: the order k = [1/eps] of MT Def 2.16, strict bounds on sup   *)
(* and inf of sets of reals (sup S < c is encoded as a strict bound d < c of *)
(* all elements, which also excludes unbounded S).                           *)
(* ------------------------------------------------------------------------- *)

let rfs_kreg = new_definition
 `rfs_kreg (eps:real) = @k:num. &k <= inv eps /\ inv eps < &k + &1`;;

let rfs_sup_lt = new_definition
 `rfs_sup_lt (S:real->bool) (c:real) <=> ?d. d < c /\ !x. x IN S ==> x <= d`;;

let rfs_inf_gt = new_definition
 `rfs_inf_gt (S:real->bool) (c:real) <=> ?d. c < d /\ !x. x IN S ==> d <= x`;;

(* ------------------------------------------------------------------------- *)
(* G1. Pullback of a metric g (preferred coordinates of atlas) by a smooth   *)
(* map e from an open subset of real^N into the manifold.  At y the          *)
(* representative is taken in the preferred chart at e y; by the             *)
(* transformation law (METRIC_LOCAL_TRANS) any chart containing e y gives    *)
(* the same matrix.                                                          *)
(* ------------------------------------------------------------------------- *)

let rfs_pullback = new_definition
 `rfs_pullback (atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A)
               (g:A->real^N^N) =
    \y. mpullback (SND(chart_at atlas (e y)) o e)
                  (metric_local atlas (chart_at atlas (e y)) g) y`;;

(* ------------------------------------------------------------------------- *)
(* G2. eps-closeness in the C^[1/eps] topology (MT Def 2.16): the sup of     *)
(* |G - G0|^2 + sum |nabla^l G|^2 (G0-norms, G0-connection) is < eps^2.      *)
(* rfs_close_on: on an open set of real^N; rfs_close_fam: for families over *)
(* a time set J, spatial derivatives only (MT's convention); rfs_mclose: on  *)
(* a region W of a manifold, two metrics of the same atlas, computed in the  *)
(* preferred charts (chart independent by the naturality of lck_dist2).      *)
(* ------------------------------------------------------------------------- *)

let rfs_close_on = new_definition
 `rfs_close_on k (eps:real) (s:real^N->bool) (G0:real^N->real^N^N)
               (G:real^N->real^N^N) <=>
    ?d. d < eps pow 2 /\ !y. y IN s ==> lck_dist2 k G0 G y <= d`;;

let rfs_close_fam = new_definition
 `rfs_close_fam k (eps:real) (J:real->bool) (s:real^N->bool)
                (G0:real->real^N->real^N^N) (G:real->real^N->real^N^N) <=>
    ?d. d < eps pow 2 /\
        !t y. t IN J /\ y IN s ==> lck_dist2 k (G0 t) (G t) y <= d`;;

let rfs_mclose = new_definition
 `rfs_mclose k (eps:real) (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool)
             (g0:A->real^N^N) (g:A->real^N^N) <=>
    ?d. d < eps pow 2 /\
        !x. x IN W
            ==> lck_dist2 k (metric_local atlas (chart_at atlas x) g0)
                            (metric_local atlas (chart_at atlas x) g)
                            (SND(chart_at atlas x) x) <= d`;;

(* ------------------------------------------------------------------------- *)
(* G3. Derived scalar quantities in the preferred chart: |grad R|^2, the     *)
(* Laplacian of R and |Ric|^2 (needed by MT Def 9.72(8)), from the local     *)
(* operators lgrad2 and llap (unit pc_lrg_lap).                             *)
(* ------------------------------------------------------------------------- *)

let rfs_scalar_grad2 = new_definition
 `rfs_scalar_grad2 (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    lgrad2 (metric_local atlas (chart_at atlas x) g)
               (lscalar (metric_local atlas (chart_at atlas x) g))
               (SND(chart_at atlas x) x)`;;

let rfs_scalar_lap = new_definition
 `rfs_scalar_lap (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    llap (metric_local atlas (chart_at atlas x) g)
             (lscalar (metric_local atlas (chart_at atlas x) g))
             (SND(chart_at atlas x) x)`;;

let rfs_ric_norm2 = new_definition
 `rfs_ric_norm2 (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    ltnorm2 2 (metric_local atlas (chart_at atlas x) g)
            (\z u. lricci (metric_local atlas (chart_at atlas x) g) z (u 1) (u 2))
            (SND(chart_at atlas x) x)`;;

(* ------------------------------------------------------------------------- *)
(* G4. eps-necks as charts of the cylinder model (MT Def 2.18).  The model   *)
(* is real^3 minus the origin with the metric 2|y|^-2 delta =                *)
(* cylinder_flow 0, isometric to S^2(radius sqrt 2) x R with s = sqrt 2      *)
(* log|y|; s in (-1/eps,1/eps) is the annulus rfs_neck_dom eps.  An          *)
(* eps-neck centred at x is a smooth parametrization e of that annulus with  *)
(* x on the central sphere e(|y| = 1) and R(x) times the pullback of g       *)
(* eps-close in C^[1/eps] to the model.  Central sphere e(sphere 1),         *)
(* s_N(e y) = sqrt 2 log|y|, positive side |y| > 1, scale R(x)^(-1/2).       *)
(* ------------------------------------------------------------------------- *)

let rfs_neck_dom = new_definition
 `rfs_neck_dom (eps:real) =
    (annulus (exp(--(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps)))
     :real^3->bool)`;;

let rfs_neck = new_definition
 `rfs_neck (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
           (g:A->real^3^3) (eps:real) (x:A) (e:real^3->A) <=>
    smooth_manifold_atlas top atlas /\ &0 < eps /\
    mfd_param top atlas (rfs_neck_dom eps) e /\
    x IN IMAGE e (sphere(vec 0,&1)) /\
    &0 < mfd_scalar atlas g x /\
    rfs_close_on (rfs_kreg eps) eps (rfs_neck_dom eps) (cylinder_flow (&0))
                 (\y. mfd_scalar atlas g x %% rfs_pullback atlas e g y)`;;

(* ------------------------------------------------------------------------- *)
(* G5. Views: a time-dependent family (TM t, AT t, G t) of manifolds,        *)
(* atlases and metrics on one carrier type.  An ordinary Ricci flow on a     *)
(* time set J is rfs_flow_view; a surgery history gives rfs_view            *)
(* (pc_rfs_history).                                                         *)
(* A set W persists over (a,b] when every slice there is a smooth manifold   *)
(* and W is open in it: this is MT's embedding W x (a,b] -> M compatible     *)
(* with time and the vector field (flow lines are constant points; Defs      *)
(* 3.38, 14.3, 14.14).  Every notion below that reads preferred charts is    *)
(* guarded by smooth_manifold_atlas (chart_at is arbitrary off the atlas).   *)
(* ------------------------------------------------------------------------- *)

let rfs_flow_view = new_definition
 `rfs_flow_view (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                (J:real->bool) (g:real->A->real^3^3) =
    (\t. if t IN J then top else discrete_topology {}),
    (\t:real. atlas),g`;;

let rfs_persists = new_definition
 `rfs_persists (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
                G:real->A->real^3^3) (W:A->bool) (a:real) (b:real) <=>
    !s. a < s /\ s <= b
        ==> smooth_manifold_atlas (TM s) (AT s) /\ open_in (TM s) W`;;

(* Evolving eps-neck of normalized length len centred at (x,t) (MT Def 3.6, *)
(* 9.78): an eps-neck in the slice at t whose image persists over           *)
(* (t - len/R(x), t], with the rescaled family R(x) G(t + s/R(x)),          *)
(* -len < s <= 0, eps-close to the shrinking cylinder cylinder_flow s       *)
(* (round S^2 factor of scalar curvature 1/(1 - s)).  Strong: len = 1.       *)

let rfs_evolving_neck = new_definition
 `rfs_evolving_neck (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
                     G:real->A->real^3^3)
                    (eps:real) (x:A) (t:real) (len:real) (e:real^3->A) <=>
    rfs_neck (TM t,AT t) (G t) eps x e /\ &0 < len /\
    rfs_persists (TM,AT,G) (IMAGE e (rfs_neck_dom eps))
                 (t - len / mfd_scalar (AT t) (G t) x) t /\
    rfs_close_fam (rfs_kreg eps) eps {s | --len < s /\ s <= &0}
                  (rfs_neck_dom eps) cylinder_flow
                  (\s y. mfd_scalar (AT t) (G t) x %%
                         rfs_pullback (AT(t + s / mfd_scalar (AT t) (G t) x)) e
                                      (G(t + s / mfd_scalar (AT t) (G t) x)) y)`;;

let rfs_strong_neck = new_definition
 `rfs_strong_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3))
                  (eps:real) (x:A) (t:real) (e:real^3->A) <=>
    rfs_evolving_neck V eps x t (&1) e`;;

(* ------------------------------------------------------------------------- *)
(* G6. Twisted charts: open copies of RP^3 minus a point (the twisted        *)
(* I-bundle over RP^2), as 2-to-1 local parametrizations of an annulus that  *)
(* identify y with -y/|y|^2.  Used for the RP^3 alternatives of MT Defs      *)
(* 9.72(1) and 9.75(1), and for the listed types of Prop 15.3.               *)
(* ------------------------------------------------------------------------- *)

let rfs_twist = new_definition
 `rfs_twist (y:real^3) = --(inv(norm y pow 2) % y)`;;

let rfs_twisted_chart = new_definition
 `rfs_twisted_chart (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
                    (p:real^3->A) <=>
    (!y z. y IN annulus (&1 / &4) (&4) /\ z IN annulus (&1 / &4) (&4)
           ==> (p y = p z <=> z = y \/ z = rfs_twist y)) /\
    (!y. y IN annulus (&1 / &4) (&4)
         ==> ?r. &0 < r /\ ball(y,r) SUBSET annulus (&1 / &4) (&4) /\
                 mfd_param top atlas (ball(y,r)) p)`;;

let rfs_has_twisted = new_definition
 `rfs_has_twisted (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) <=>
    ?p. rfs_twisted_chart top atlas p`;;

(* ------------------------------------------------------------------------- *)
(* G7. (C,eps)-caps (MT Def 9.72) with a chart of the closed core (the       *)
(* smooth-topology part needs this to avoid smooth Schoenflies): either a    *)
(* ball chart b (core b(ball 1), closed core b(cball 1)) or a twisted chart  *)
(* p (core p(annulus 1/2 2), closed core RP^3 minus a ball), with the        *)
(* boundary neck e' radially matched to the core chart on the collar up to a *)
(* diffeomorphism f of S^2, and the end neck e = U minus the closed core.  U *)
(* is the cap, Y its (open) core.  Clauses (4)-(8) as in MT.  The volume     *)
(* clause (7) is guarded by boundedness of R on the ball (HOL's sup of an    *)
(* unbounded set is the fixed unspecified value of the empty sup, so in      *)
(* incomplete manifolds such as Omega an unguarded clause would be           *)
(* junk-sensitive); the other sups are over U, where the ratio clause bounds *)
(* R.  The diameter clause (5) names its binders y1, y2 explicitly; without  *)
(* the binder list U would occur on both sides of the bar and be bound too.  *)
(* ------------------------------------------------------------------------- *)

let rfs_cap = new_definition
 `rfs_cap (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
          (g:A->real^3^3) (C:real) (eps:real) (U:A->bool) (Y:A->bool) <=>
    smooth_manifold_atlas top atlas /\ open_in top U /\
    ((?b e e' z z' f f'.
        mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
        Y = IMAGE b (ball(vec 0,&1)) /\
        rfs_neck (top,atlas) g eps z e /\
        IMAGE e (rfs_neck_dom eps) = U DIFF IMAGE b (cball(vec 0,&1)) /\
        rfs_neck (top,atlas) g eps z' e' /\
        IMAGE e' (rfs_neck_dom eps) SUBSET U /\
        IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
        sphere_diffeo f f' /\
        (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) \/
     (?p e e' z z' f f'.
        rfs_twisted_chart top atlas p /\
        IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\
        Y = IMAGE p (annulus (&1 / &2) (&2)) /\
        rfs_neck (top,atlas) g eps z e /\
        IMAGE e (rfs_neck_dom eps) =
          U DIFF IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
        rfs_neck (top,atlas) g eps z' e' /\
        IMAGE e' (rfs_neck_dom eps) SUBSET U /\
        IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
        sphere_diffeo f f' /\
        (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y))))) /\
    (!y. y IN U ==> &0 < mfd_scalar atlas g y) /\
    rfs_sup_lt {mfd_dist_in (top,atlas) g U y1 y2 | y1,y2 | y1 IN U /\ y2 IN U}
               (C * inv(sqrt(sup(IMAGE (mfd_scalar atlas g) U)))) /\
    rfs_sup_lt {mfd_scalar atlas g y2 / mfd_scalar atlas g y1 |
                y1 IN U /\ y2 IN U} C /\
    (?v. mfd_has_volume (top,atlas) g U v /\
         v < C * inv(sqrt(sup(IMAGE (mfd_scalar atlas g) U)) pow 3)) /\
    (?d. inv C < d /\
         !y r. y IN Y /\ &0 < r /\
               (?B. !z. z IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g z <= B) /\
               sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y r)) =
               inv(r pow 2)
               ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                   top closure_of mfd_ball (top,atlas) g y r SUBSET U /\
                   ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                       d <= v / r pow 3) /\
    rfs_sup_lt {sqrt(rfs_scalar_grad2 atlas g y) /
                (mfd_scalar atlas g y * sqrt(mfd_scalar atlas g y)) | y IN U} C /\
    rfs_sup_lt {abs(rfs_scalar_lap atlas g y + &2 * rfs_ric_norm2 atlas g y) /
                mfd_scalar atlas g y pow 2 | y IN U} C`;;

(* ------------------------------------------------------------------------- *)
(* G8. C-components (MT Def 9.75) and eps-round components (Def 9.76) of a   *)
(* Riemannian manifold, as connected components U.  Def 9.75(1), S^3 or      *)
(* RP^3, is read as S^3 or containing an RP^3 minus a point (implied by      *)
(* MT's clause; all that the topology needs).  Def 9.76 is transported to    *)
(* the component: a metric g1 of constant sectional curvature 1 with         *)
(* q g eps-close to g1 (equivalent to MT's form with a diffeomorphism).      *)
(* Distances inside a component are those of the manifold.  C-components    *)
(* carry the derivative bounds of Def 9.72(8) (MT's Def 9.75 has none, but   *)
(* Lemma 11.2 and Assumption 11.18(c) need them; true for kappa-solutions by *)
(* (9.33)-(9.34)).                                                           *)
(* ------------------------------------------------------------------------- *)

let rfs_c_component = new_definition
 `rfs_c_component (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                  (g:A->real^3^3) (C:real) (U:A->bool) <=>
    smooth_manifold_atlas top atlas /\
    U IN connected_components_of top /\ compact_in top U /\
    (mfd_diffeomorphic (subtopology top U) (restrict_atlas atlas U)
       (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas \/
     rfs_has_twisted (subtopology top U) (restrict_atlas atlas U)) /\
    (!x u v. x IN U /\ ~collinear {vec 0,u,v}
             ==> &0 < mfd_sectional atlas g x u v) /\
    rfs_inf_gt {mfd_sectional atlas g x u v | x,u,v |
                x IN U /\ ~collinear {vec 0,u,v}}
               (inv C * sup(IMAGE (mfd_scalar atlas g) U)) /\
    inv C * inv(sqrt(sup(IMAGE (mfd_scalar atlas g) U))) <
    sup {mfd_dist (top,atlas) g x y | x IN U /\ y IN U} /\
    sup {mfd_dist (top,atlas) g x y | x IN U /\ y IN U} <
    C * inv(sqrt(inf(IMAGE (mfd_scalar atlas g) U))) /\
    rfs_sup_lt {sqrt(rfs_scalar_grad2 atlas g y) /
                (mfd_scalar atlas g y * sqrt(mfd_scalar atlas g y)) | y IN U} C /\
    rfs_sup_lt {abs(rfs_scalar_lap atlas g y + &2 * rfs_ric_norm2 atlas g y) /
                mfd_scalar atlas g y pow 2 | y IN U} C`;;

let rfs_round_component = new_definition
 `rfs_round_component (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                      (g:A->real^3^3) (eps:real) (U:A->bool) <=>
    smooth_manifold_atlas top atlas /\
    U IN connected_components_of top /\ compact_in top U /\
    ?q g1. &0 < q /\ riemannian_metric atlas g1 /\
           (!x u v. x IN U /\ ~collinear {vec 0,u,v}
                    ==> mfd_sectional atlas g1 x u v = &1) /\
           rfs_mclose (rfs_kreg eps) eps atlas U g1 (\x. q %% g x)`;;

(* ------------------------------------------------------------------------- *)
(* G9. (C,eps)-canonical neighbourhoods (MT Def 9.77) and strong ones in a   *)
(* view at time t (MT p. 232, Def 14.18: only the neck alternative looks     *)
(* backward in time).                                                        *)
(* ------------------------------------------------------------------------- *)

let rfs_canonical_nbhd = new_definition
 `rfs_canonical_nbhd (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                     (g:A->real^3^3) (C:real) (eps:real) (x:A) (U:A->bool) <=>
    (?e. rfs_neck (top,atlas) g eps x e /\ U = IMAGE e (rfs_neck_dom eps)) \/
    (?Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y) \/
    (x IN U /\ rfs_c_component (top,atlas) g C U) \/
    (x IN U /\ rfs_round_component (top,atlas) g eps U)`;;

let rfs_strong_canonical = new_definition
 `rfs_strong_canonical (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
                        G:real->A->real^3^3)
                       (C:real) (eps:real) (x:A) (t:real) (U:A->bool) <=>
    (?e. rfs_strong_neck (TM,AT,G) eps x t e /\ U = IMAGE e (rfs_neck_dom eps)) \/
    (?Y. rfs_cap (TM t,AT t) (G t) C eps U Y /\ x IN Y) \/
    (x IN U /\ rfs_c_component (TM t,AT t) (G t) C U) \/
    (x IN U /\ rfs_round_component (TM t,AT t) (G t) eps U)`;;

(* ------------------------------------------------------------------------- *)
(* G10. Curvature pinched toward positive at time t (MT Def 4.34, 14.17),    *)
(* with X = max(0,-nu), nu the least sectional curvature (sectional          *)
(* normalization); normalized metrics (MT Def 4.10, for all r <= 1;          *)
(* omega_3 / 2 = 2 pi / 3).                                                  *)
(* ------------------------------------------------------------------------- *)

let rfs_pinched_at = new_definition
 `rfs_pinched_at (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
                 (t:real) (x:A) <=>
    --(&6) / (&4 * t + &1) <= mfd_scalar atlas g x /\
    (&0 < --(mfd_sec_min atlas g x)
     ==> &2 * --(mfd_sec_min atlas g x) *
         (log(--(mfd_sec_min atlas g x)) + log(&1 + t) - &3)
         <= mfd_scalar atlas g x)`;;

let rfs_normalized = new_definition
 `rfs_normalized (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                 (g:A->real^3^3) <=>
    smooth_manifold_atlas top atlas /\
    (!x. x IN topspace top ==> mfd_rm_norm atlas g x <= &1) /\
    (!x r. x IN topspace top /\ &0 < r /\ r <= &1
           ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\
                   &2 / &3 * pi * r pow 3 <= v)`;;

(* ------------------------------------------------------------------------- *)
(* G11. Views: balls, parabolic neighbourhoods, pinching, the strong         *)
(* canonical neighbourhood assumption with parameter function rp (MT Def     *)
(* 14.18, 15.7) and kappa-noncollapsing on scales <= r0 with the             *)
(* positive-curvature exemption of MT p. 360.  CONVENTION:                   *)
(* backward parabolic neighbourhoods are HALF-OPEN, B(x,t,r) x (t - dt, t]   *)
(* (MT Defs 9.1, 14.14, 14.15); MT Thm 8.1 uses the closed form and is       *)
(* applied with r' < r.                                                      *)
(* ------------------------------------------------------------------------- *)

let rfs_vball = new_definition
 `rfs_vball (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
             G:real->A->real^3^3) (t:real) (x:A) (r:real) =
    mfd_ball (TM t,AT t) (G t) x r`;;

let rfs_vscalar = new_definition
 `rfs_vscalar (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
               G:real->A->real^3^3) (t:real) (x:A) =
    mfd_scalar (AT t) (G t) x`;;

let rfs_parabolic_exists = new_definition
 `rfs_parabolic_exists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3))
                       (t:real) (x:A) (r:real) (dt:real) <=>
    rfs_persists V (rfs_vball V t x r) (t - dt) t`;;

let rfs_pos_component = new_definition
 `rfs_pos_component (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                    (g:A->real^3^3) (x:A) <=>
    smooth_manifold_atlas top atlas /\
    ?U. U IN connected_components_of top /\ x IN U /\
        !y u v. y IN U /\ ~collinear {vec 0,u,v}
                ==> &0 < mfd_sectional atlas g y u v`;;

let rfs_pinched = new_definition
 `rfs_pinched (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
               G:real->A->real^3^3) <=>
    !t x. &0 <= t /\ x IN topspace(TM t) ==> rfs_pinched_at (AT t) (G t) t x`;;

let rfs_canonical_assumption = new_definition
 `rfs_canonical_assumption
    (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,G:real->A->real^3^3)
    (C:real) (eps:real) (rp:real->real) <=>
    !t x. &0 <= t /\ x IN topspace(TM t) /\
          inv(rp t pow 2) <= mfd_scalar (AT t) (G t) x
          ==> ?U. rfs_strong_canonical (TM,AT,G) C eps x t U`;;

let rfs_noncollapsed = new_definition
 `rfs_noncollapsed
    (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,G:real->A->real^3^3)
    (kappa:real->real) (r0:real) <=>
    !t x r. &0 <= t /\ x IN topspace(TM t) /\
            ~rfs_pos_component (TM t,AT t) (G t) x /\
            &0 < r /\ r <= r0 /\
            rfs_parabolic_exists (TM,AT,G) t x r (r pow 2) /\
            (!s y. t - r pow 2 < s /\ s <= t /\ y IN rfs_vball (TM,AT,G) t x r
                   ==> mfd_rm_norm (AT s) (G s) y <= inv(r pow 2))
            ==> ?v. mfd_has_volume (TM t,AT t) (G t) (rfs_vball (TM,AT,G) t x r) v /\
                    kappa t * r pow 3 <= v`;;

(* Plain kappa-noncollapsing on scales <= r0 (MT Def 9.1 for an ordinary   *)
(* flow view, Def 14.15 for a history view): no exemption, constant kappa.  *)
(* For rfs_flow_view (top,atlas) J g with J = (a,b], persistence over       *)
(* (t - r^2, t] is MT's requirement a <= t - r^2.                           *)

let rfs_kappa_noncollapsed = new_definition
 `rfs_kappa_noncollapsed
    (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,G:real->A->real^3^3)
    (kappa:real) (r0:real) <=>
    !t x r. x IN topspace(TM t) /\ &0 < r /\ r <= r0 /\
            rfs_parabolic_exists (TM,AT,G) t x r (r pow 2) /\
            (!s y. t - r pow 2 < s /\ s <= t /\ y IN rfs_vball (TM,AT,G) t x r
                   ==> mfd_rm_norm (AT s) (G s) y <= inv(r pow 2))
            ==> ?v. mfd_has_volume (TM t,AT t) (G t) (rfs_vball (TM,AT,G) t x r) v /\
                    kappa * r pow 3 <= v`;;

(* ------------------------------------------------------------------------- *)
(* G12. The listed types of MT Prop 15.3, for a closed connected 3-manifold: *)
(* S^3; a space form (a metric of constant sectional curvature 1); an S^2-   *)
(* bundle over S^1 (mapping torus of a diffeomorphism f of S^2: the          *)
(* complement of the central sphere of a neck chart e is an open product     *)
(* E(annulus 1 4) whose ends approach the sphere from both sides);           *)
(* containing an RP^3 minus a point (RP^3, RP^3 # RP^3 and every piece with  *)
(* an RP^3 cap core).                                                        *)
(* ------------------------------------------------------------------------- *)

let rfs_space_form = new_definition
 `rfs_space_form (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) <=>
    smooth_manifold_atlas top atlas /\
    ?g. riemannian_metric atlas g /\
        !x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> mfd_sectional atlas g x u v = &1`;;

let rfs_s2_bundle = new_definition
 `rfs_s2_bundle (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) <=>
    ?e E f f'.
        mfd_neck_chart top atlas e /\
        mfd_param top atlas (annulus (&1) (&4)) E /\
        sphere_diffeo f f' /\
        topspace top DIFF IMAGE e (sphere(vec 0,&1)) = IMAGE E (annulus (&1) (&4)) /\
        (!x. x IN annulus (&1) (&2) ==> E x = e x) /\
        (!x. x IN annulus (&2) (&4) ==> E x = e(radial_ext f (inv(&4) % x)))`;;

let rfs_listed_piece = new_definition
 `rfs_listed_piece (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) <=>
    mfd_diffeomorphic top atlas
      (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas \/
    rfs_space_form top atlas \/
    rfs_s2_bundle top atlas \/
    rfs_has_twisted top atlas`;;

