(* ========================================================================= *)
(* pc_apx_defs: vocabulary and statement constants of the Appendix layer     *)
(* (Morgan-Tian Appendix A, corrected, separating case) and of the topology  *)
(* of one surgery event (MT Prop 15.3), and the reduction                    *)
(* APX_EVENT_TOPOLOGY_FROM_PARTS of EVENT_TOPOLOGY_STATEMENT to the event    *)
(* statements E1 and E2.  The separation notions are those of pc_apx_sep,    *)
(* restrict_metric is that of pc_mfd_restrict.                               *)
(*                                                                           *)
(* The definitions rfs_neck, rfs_cap and the history records come from the   *)
(* units pc_rfs_geom, pc_rfs_history and pc_rfs_top; the cut-and-cap data    *)
(* are mfd_cut_cap, mfd_cut_spheres and mfd_cut_cores of pc_mfd_cut.         *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;
needs "src/pc_mfd_base.ml";;
needs "src/pc_lrg.ml";;
needs "src/pc_mfd_riem.ml";;
needs "src/pc_audit_sanity.ml";;
needs "src/pc_mfd_examples.ml";;
needs "src/pc_mfd_maps.ml";;
needs "src/pc_ode_defs.ml";;
needs "src/pc_smt_defs.ml";;
needs "src/pc_rf_basic.ml";;
needs "src/pc_lrg_tensor.ml";;
needs "src/pc_lrg_lap.ml";;
needs "src/pc_grg_dist.ml";;
needs "src/pc_grg_dist_in.ml";;
needs "src/pc_mfd_restrict.ml";;
needs "src/pc_apx_sep.ml";;
needs "src/pc_rfs_top.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* X1. The neck model.  apx_slab a b is the region a < s < b of the model    *)
(* cylinder (real^3 minus 0 with 2|y|^-2 delta, s = sqrt 2 log|y|), so that  *)
(* rfs_neck_dom eps = apx_slab (-1/eps) (1/eps) (APX_SLAB_NECK_DOM).  MT's   *)
(* quarters, halves, middle thirds are slabs.  apx_rev e reverses the        *)
(* s-direction (y -> y/|y|^2 is an isometry of the model, s -> -s).          *)
(* ------------------------------------------------------------------------- *)

let apx_slab = new_definition
 `apx_slab (a:real) (b:real) =
    (annulus (exp(a / sqrt(&2))) (exp(b / sqrt(&2))):real^3->bool)`;;

let apx_sval = new_definition
 `apx_sval (y:real^3) = sqrt(&2) * log(norm y)`;;

let apx_rev = new_definition
 `apx_rev (e:real^3->A) = \y:real^3. e(inv(norm y pow 2) % y)`;;

(* The s-function of a neck on its image (inverse by choice; e is injective  *)
(* on its domain when it is a parametrization).                              *)

let apx_sfun = new_definition
 `apx_sfun (s:real^3->bool) (e:real^3->A) (p:A) =
    apx_sval (@y. y IN s /\ e y = p)`;;

(* |df|_g^2 at p for a real function f on an open set of the manifold,      *)
(* computed in the preferred chart at p (lgrad2 of the local layer).         *)

let apx_dnorm2 = new_definition
 `apx_dnorm2 (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (f:A->real) (p:A) =
    lgrad2 (metric_local atlas (chart_at atlas p) g)
           (\z. f(chart_inv (chart_at atlas p) z))
           (SND(chart_at atlas p) p)`;;

(* X2. Separation: apx_separates and apx_sphere_sep come from pc_apx_sep.     *)

(* ------------------------------------------------------------------------- *)
(* X3. Sections: S is a smooth radial graph in the coordinates of the        *)
(* parametrization E of annulus r1 r2 (MT A.11(4), Cor A.3: a section of     *)
(* the projection to S^2, isotopic to the spheres of the product             *)
(* structure).  apx_csection: the same with a continuous graph (Lemma A.10,  *)
(* metric spheres).                                                          *)
(* ------------------------------------------------------------------------- *)

let apx_section = new_definition
 `apx_section (E:real^3->A) (r1:real) (r2:real) (S:A->bool) <=>
    ?u. smooth_near (sphere(vec 0,&1)) (\x:real^3. lift(u x)) /\
        (!x. x IN sphere(vec 0,&1) ==> r1 < u x /\ u x < r2) /\
        S = IMAGE (\x. E(u x % x)) (sphere(vec 0,&1))`;;

let apx_csection = new_definition
 `apx_csection (E:real^3->A) (r1:real) (r2:real) (S:A->bool) <=>
    ?u. (\x:real^3. lift(u x)) continuous_on sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> r1 < u x /\ u x < r2) /\
        S = IMAGE (\x. E(u x % x)) (sphere(vec 0,&1))`;;

(* ------------------------------------------------------------------------- *)
(* X4. Points covered by the Appendix hypotheses: centre of an eps-neck or   *)
(* in the core of a (C,eps)-cap (MT A.21, A.25).                             *)
(* ------------------------------------------------------------------------- *)

let apx_neck_or_core = new_definition
 `apx_neck_or_core (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:A->real^3^3) (C:real) (eps:real) (x:A) <=>
    (?e. rfs_neck (top,atlas) g eps x e) \/
    (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y)`;;

(* ------------------------------------------------------------------------- *)
(* X5. Chains of eps-necks (MT Def A.12) indexed by an integer interval I    *)
(* (finite, half-infinite or bi-infinite), and balanced chains (A.1).        *)
(* Clause (1): consecutive necks overlap in the positive quarter of N_i and  *)
(* the negative quarter of N_(i+1), inside the positive 3/4 of N_i and the   *)
(* negative 3/4 of N_(i+1).  Clause (2), in the form MT's infinite chains    *)
(* require of every finite subinterval, and symmetrically: a later neck      *)
(* misses the negative quarter of an earlier one, an earlier neck misses the *)
(* positive quarter of a later one (no wrap-around).                         *)
(* ------------------------------------------------------------------------- *)

let apx_int_interval = new_definition
 `apx_int_interval (Ix:int->bool) <=>
    !i j k. i IN Ix /\ k IN Ix /\ i <= j /\ j <= k ==> j IN Ix`;;

let apx_chain = new_definition
 `apx_chain (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
            (eps:real) (Ix:int->bool) (x:int->A) (e:int->real^3->A) <=>
    apx_int_interval Ix /\ ~(Ix = {}) /\
    (!i. i IN Ix ==> rfs_neck (top,atlas) g eps (x i) (e i)) /\
    (!i. i IN Ix /\ (i + &1) IN Ix
         ==> IMAGE (e i) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
             IMAGE (e(i + &1)) (apx_slab (--inv eps) (--inv(&2 * eps)))
             SUBSET IMAGE (e i) (rfs_neck_dom eps) INTER
                    IMAGE (e(i + &1)) (rfs_neck_dom eps) /\
             IMAGE (e i) (rfs_neck_dom eps) INTER
             IMAGE (e(i + &1)) (rfs_neck_dom eps)
             SUBSET IMAGE (e i) (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
                    IMAGE (e(i + &1)) (apx_slab (--inv eps) (inv(&2 * eps)))) /\
    (!a i. a IN Ix /\ i IN Ix /\ a < i
           ==> DISJOINT (IMAGE (e i) (rfs_neck_dom eps))
                        (IMAGE (e a) (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
               DISJOINT (IMAGE (e a) (rfs_neck_dom eps))
                        (IMAGE (e i) (apx_slab (inv(&2 * eps)) (inv eps))))`;;

let apx_balanced = new_definition
 `apx_balanced (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
               (eps:real) (Ix:int->bool) (x:int->A) (e:int->real^3->A) <=>
    apx_chain (top,atlas) g eps Ix x e /\
    (!i. i IN Ix /\ (i + &1) IN Ix
         ==> mfd_joinable (top,atlas) (x i) (x(i + &1)) /\
             &99 / &100 * inv(sqrt(mfd_scalar atlas g (x i))) * inv eps
             <= mfd_dist (top,atlas) g (x i) (x(i + &1)) /\
             mfd_dist (top,atlas) g (x i) (x(i + &1))
             <= &101 / &100 * inv(sqrt(mfd_scalar atlas g (x i))) * inv eps)`;;

let apx_chain_union = new_definition
 `apx_chain_union (eps:real) (Ix:int->bool) (e:int->real^3->A) =
    UNIONS {IMAGE (e i) (rfs_neck_dom eps) | i IN Ix}`;;

(* ------------------------------------------------------------------------- *)
(* X6. Tubes, capped tubes, two-ball components (MT Def 9.81, made explicit: *)
(* product charts instead of diffeomorphic to S^2 x (0,1), sections          *)
(* instead of isotopic to the S^2-factors).                                  *)
(*                                                                           *)
(* apx_tube: an open eps-tube with product chart E of annulus r1 r2: every   *)
(* point lies in an eps-neck inside the tube, and the central sphere of      *)
(* every eps-neck that lies in the tube separates its two ends               *)
(* (apx_ends_sep; MT: isotopic to the S^2-factors).  The separation form    *)
(* is what the uses need (Claim 10.4, Lemma 11.30, the sides of surgery      *)
(* spheres) and is provable for the charts of A.13 (whose radial field is    *)
(* not controlled by SMT_PRODUCT2_STATEMENT).                                *)

let apx_ends_sep = new_definition
 `apx_ends_sep (top:A topology) (E:real^3->A) (r1:real) (r2:real) (S:A->bool) <=>
    ?rho1 rho2.
        r1 < rho1 /\ rho1 < rho2 /\ rho2 < r2 /\
        S SUBSET IMAGE E (annulus rho1 rho2) /\
        !p q. p IN IMAGE E (annulus r1 rho1) /\ q IN IMAGE E (annulus rho2 r2)
              ==> apx_separates top S p q`;;

let apx_tube = new_definition
 `apx_tube (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
           (eps:real) (E:real^3->A) (r1:real) (r2:real) <=>
    &0 < r1 /\ r1 < r2 /\
    mfd_param top atlas (annulus r1 r2) E /\
    (!p. p IN IMAGE E (annulus r1 r2)
         ==> ?x e. rfs_neck (top,atlas) g eps x e /\
                   p IN IMAGE e (rfs_neck_dom eps) /\
                   IMAGE e (rfs_neck_dom eps) SUBSET IMAGE E (annulus r1 r2)) /\
    (!x e. rfs_neck (top,atlas) g eps x e /\
           IMAGE e (sphere(vec 0,&1)) SUBSET IMAGE E (annulus r1 r2)
           ==> apx_ends_sep top E r1 r2 (IMAGE e (sphere(vec 0,&1))))`;;

(* A C-capped eps-tube of ball type with one chart B of ball(0,r): the cap   *)
(* core is B(ball 1) (so its closed core is the closed ball B(cball 1)), and *)
(* B(annulus 1 r) is an open eps-tube with chart B (it contains the end neck *)
(* of the cap, MT Def 9.81: cap and tube overlap in a product containing an  *)
(* end of each).  A single ball-type cap, with its end neck as the tube, is  *)
(* the case of MT A.21(3).                                                   *)

let apx_ball_tube = new_definition
 `apx_ball_tube (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                (g:A->real^3^3) (C:real) (eps:real) (B:real^3->A) (r:real) <=>
    &2 < r /\
    mfd_param top atlas (ball(vec 0,r)) B /\
    (?U. rfs_cap (top,atlas) g C eps U (IMAGE B (ball(vec 0,&1))) /\
         IMAGE B (ball(vec 0,&2)) SUBSET U) /\
    apx_tube (top,atlas) g eps B (&1) r`;;

(* A C-capped eps-tube of twisted type: a cap with a twisted chart p of its  *)
(* core (an RP^3 minus a ball) and an open eps-tube that meets the cap but   *)
(* not near its outer end (so V has one end, MT Def 9.81).                   *)

let apx_twisted_tube = new_definition
 `apx_twisted_tube (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:A->real^3^3) (C:real) (eps:real) (V:A->bool) (Y:A->bool) <=>
    ?U p E r1 rho r2.
        rfs_cap (top,atlas) g C eps U Y /\
        rfs_twisted_chart top atlas p /\
        IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\
        Y = IMAGE p (annulus (&1 / &2) (&2)) /\
        apx_tube (top,atlas) g eps E r1 r2 /\ r1 < rho /\ rho < r2 /\
        V = U UNION IMAGE E (annulus r1 r2) /\
        ~(U INTER IMAGE E (annulus r1 r2) = {}) /\
        DISJOINT U (IMAGE E (annulus rho r2)) /\
        DISJOINT (top closure_of Y) (IMAGE E (annulus r1 r2))`;;

(* Two closed balls glued radially: exactly the hypotheses of the twisted    *)
(* sphere statement SMT_TWISTED_SPHERE_STATEMENT (so S^3).  This is the form *)
(* in which the compact alternatives of MT A.21(1),(2) and A.25(1) are       *)
(* delivered (two caps, or a double C-capped tube), for both caps of ball    *)
(* type; with a twisted cap the component contains a twisted chart.         *)

let apx_two_balls = new_definition
 `apx_two_balls (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) <=>
    ?b1 b2 f f' r.
        mfd_ball_chart top atlas b1 /\ mfd_ball_chart top atlas b2 /\
        sphere_diffeo f f' /\ &1 < r /\
        topspace top = IMAGE b1 (cball(vec 0,&1)) UNION IMAGE b2 (cball(vec 0,&1)) /\
        DISJOINT (IMAGE b1 (ball(vec 0,&1))) (IMAGE b2 (ball(vec 0,&1))) /\
        (!x. x IN annulus (&1) r
             ==> b1 x = b2(inv(norm x) % f(inv(norm x) % x)))`;;

(* ------------------------------------------------------------------------- *)
(* X7. Shortest curves (minimal geodesics up to parametrization, MT A.4,     *)
(* A.6-A.8; used in layer P): a C^1 curve whose length between               *)
(* any two of its parameters is the distance of the two points.             *)
(* ------------------------------------------------------------------------- *)

let apx_shortest = new_definition
 `apx_shortest (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
               (g:A->real^3^3) (gamma:real->A) (a:real) (b:real) <=>
    mfd_c1_curve (top,atlas) gamma a b /\
    !s t. a <= s /\ s <= t /\ t <= b
          ==> mfd_length atlas g gamma s t =
              mfd_dist (top,atlas) g (gamma s) (gamma t)`;;

(* ------------------------------------------------------------------------- *)
(* X8. The situation of MT Prop 15.3 at a time t' just before the surgery    *)
(* time, as pure data (no history): X = the old stage with the metric at     *)
(* t', the cut-and-capped Z with discarded part D (union of components),     *)
(* plus caps on the outer sides (discarded), minus caps retained, every cut  *)
(* neck an eps1-neck at t' (eps1 = 2 delta(T)), every old point that is not  *)
(* retained with a (C,eps)-canonical neighbourhood (Assumption (6), where    *)
(* MT's text says (5)), all neck spheres separating.                         *)
(* ------------------------------------------------------------------------- *)

let apx_cut_situation = new_definition
 `apx_cut_situation (topX:A topology,atlasX:((A->bool)#(A->real^3))->bool)
                    (g:A->real^3^3) (C:real) (eps:real) (dl:real)
                    (topZ:A topology,atlasZ:((A->bool)#(A->real^3))->bool)
                    (J:num->bool) (e:num->real^3->A) (cp:num->real^3->A)
                    (cm:num->real^3->A) (D:A->bool) <=>
    hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
    compact_space topX /\ riemannian_metric atlasX g /\
    apx_sphere_sep topX atlasX /\
    hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
    compact_space topZ /\
    mfd_cut_cap topX atlasX topZ atlasZ J e cp cm (\x. x) (\x. x) /\
    DISJOINT (topspace topX) (mfd_cut_cores J cp cm) /\
    D SUBSET topspace topZ /\ open_in topZ D /\ closed_in topZ D /\
    (!i. i IN J
         ==> IMAGE (cp i) (cball(vec 0,&1)) SUBSET D /\
             DISJOINT (IMAGE (cm i) (cball(vec 0,&1))) D /\
             (?y. rfs_neck (topX,atlasX) g dl y (e i))) /\
    (!x. x IN topspace topX DIFF (topspace topZ DIFF D)
         ==> ?U. rfs_canonical_nbhd (topX,atlasX) g C eps x U)`;;


prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Layer N: metric facts about eps-necks.                                    *)
(* ========================================================================= *)

(* N0. A delta-neck is an eps-neck for delta <= eps (restriction to the      *)
(* smaller annulus, fewer derivatives, larger bound).                        *)

let APX_NECK_MONO_STATEMENT = new_definition
 `APX_NECK_MONO_STATEMENT (u:A->bool) <=>
    !top atlas g dl eps x e.
        &0 < dl /\ dl <= eps /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g dl x (e:real^3->A)
        ==> rfs_neck (top,atlas) g eps x e`;;

(* N1. MT Lemma A.2 in model coordinates: on an eps-neck centred at x the    *)
(* rescaled pullback G = R(x) times e-pullback of g has scalar curvature    *)
(* within alpha of 1,                                                        *)
(* Ricci form and sectional curvatures within alpha of the cylinder's        *)
(* (Ric0 = (G0 - ds^2)/2: the s-direction is the null direction of Ric0).    *)

let APX_NECK_CURV_STATEMENT = new_definition
 `APX_NECK_CURV_STATEMENT (u:A->bool) <=>
    !alpha. &0 < alpha
      ==> ?eps1. &0 < eps1 /\
            !top atlas g eps x e y.
               &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
               rfs_neck (top,atlas) g eps x (e:real^3->A) /\ y IN rfs_neck_dom eps
               ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y
                       - &1) <= alpha /\
                   (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z)
                                   y w w -
                            lricci (cylinder_flow (&0)) y w w)
                        <= alpha * (w dot (cylinder_flow (&0) y ** w))) /\
                   (!v w. ~collinear {vec 0,v,w}
                          ==> abs(lsectional
                                    (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z)
                                    y v w -
                                  lsectional (cylinder_flow (&0)) y v w) <= alpha)`;;

(* N1b. The manifold reading of N1 (naturality, a foundations fact):         *)
(* scalar curvature of g at e y = scalar curvature of the pullback at y.     *)

let APX_PULLBACK_SCALAR_STATEMENT = new_definition
 `APX_PULLBACK_SCALAR_STATEMENT (u:A->bool) <=>
    !top atlas g s e y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        riemannian_metric atlas g /\ mfd_param top atlas s (e:real^3->A) /\ y IN s
        ==> mfd_scalar atlas g (e y) = lscalar (rfs_pullback atlas e g) y`;;

(* N2. MT Lemma A.4 (diameter of the neck spheres) and Cor A.5: the          *)
(* s-coordinate is almost a distance function on the neck, at the scale      *)
(* h = R(x)^(-1/2); curves leaving the neck from level s have length at      *)
(* least (1-alpha) h (1/eps - |s|) (so B(x,(1-alpha)h/eps) lies in N).       *)
(* The lower bound allows the exit and re-enter route of non-separating      *)
(* necks (2/eps - |s y| - |s z|).                                            *)

let APX_NECK_DIST_STATEMENT = new_definition
 `APX_NECK_DIST_STATEMENT (u:A->bool) <=>
    !alpha. &0 < alpha
      ==> ?eps1. &0 < eps1 /\
            !top atlas g eps x e y z.
               &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
               riemannian_metric atlas g /\
               rfs_neck (top,atlas) g eps x (e:real^3->A) /\
               y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps
               ==> mfd_joinable (top,atlas) (e y) (e z) /\
                   mfd_dist (top,atlas) g (e y) (e z)
                   <= (&1 + alpha) * inv(sqrt(mfd_scalar atlas g x)) *
                      (abs(apx_sval y - apx_sval z) + sqrt(&2) * pi) /\
                   (&1 - alpha) * inv(sqrt(mfd_scalar atlas g x)) *
                   min (abs(apx_sval y - apx_sval z))
                       (&2 * inv eps - abs(apx_sval y) - abs(apx_sval z))
                   <= mfd_dist (top,atlas) g (e y) (e z) /\
                   (!gamma a b.
                       mfd_c1_curve (top,atlas) gamma a b /\ gamma a = e y /\
                       ~(gamma b IN IMAGE e (rfs_neck_dom eps))
                       ==> (&1 - alpha) * inv(sqrt(mfd_scalar atlas g x)) *
                           (inv eps - abs(apx_sval y))
                           <= mfd_length atlas g gamma a b)`;;

(* N3. MT Prop A.11(1),(3): overlapping eps-necks have comparable scales,    *)
(* and their normalized s-differentials agree up to sign: at every common    *)
(* point p, |R(x)^(-1/2) ds_N -+ R(x')^(-1/2) ds_N'|_g <= alpha.  (Proof via *)
(* N1: Ric is (R/2)(g - h^2 ds^2) up to alpha on both necks, so the two rank *)
(* one forms ds_N^2, ds_N'^2 agree up to scale; no geodesics needed.)        *)

let APX_NECK_OVERLAP_STATEMENT = new_definition
 `APX_NECK_OVERLAP_STATEMENT (u:A->bool) <=>
    !alpha. &0 < alpha
      ==> ?eps1. &0 < eps1 /\
            !top atlas g eps x e x' e' p.
               &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
               rfs_neck (top,atlas) g eps x (e:real^3->A) /\
               rfs_neck (top,atlas) g eps x' e' /\
               p IN IMAGE e (rfs_neck_dom eps) INTER IMAGE e' (rfs_neck_dom eps)
               ==> abs(mfd_scalar atlas g x' / mfd_scalar atlas g x - &1) <= alpha /\
                   ?sg. (sg = &1 \/ sg = -- &1) /\
                        apx_dnorm2 atlas g
                          (\q. inv(sqrt(mfd_scalar atlas g x)) *
                               apx_sfun (rfs_neck_dom eps) e q -
                               sg * inv(sqrt(mfd_scalar atlas g x')) *
                               apx_sfun (rfs_neck_dom eps) e' q) p
                        <= alpha pow 2`;;

(* N4. MT Prop A.11(4), Cor A.3: a level sphere of an eps-neck N' that lies  *)
(* in an eps-neck N is a (smooth radial) section of N.  (Proof: N3 gives     *)
(* transversality to the radial lines of N, so radial projection is a local  *)
(* diffeomorphism of S^2, a diffeomorphism by SMT_SPHERE_COVERING.)  The    *)
(* guard 0 < r is needed: for r < 0 the sphere is empty, the                 *)
(* hypotheses hold vacuously, and no section is empty.                       *)

let APX_NECK_SECTION_STATEMENT = new_definition
 `APX_NECK_SECTION_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !top atlas g eps x e x' e' r.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         rfs_neck (top,atlas) g eps x (e:real^3->A) /\
         rfs_neck (top,atlas) g eps x' e' /\ &0 < r /\
         sphere(vec 0,r) SUBSET rfs_neck_dom eps /\
         IMAGE e' (sphere(vec 0,r)) SUBSET IMAGE e (rfs_neck_dom eps)
         ==> apx_section e (exp(--(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps)))
                         (IMAGE e' (sphere(vec 0,r)))`;;

(* N5. A section bounds no compact region of the tube (point-set core of     *)
(* N5b, Claim 16.10 and the proof of Thm 11.31): a compact K inside          *)
(* the image of E whose frontier lies in an E-section has empty interior.    *)
(* The inner radius must be nonnegative (for r1 < 0 the annulus is a ball   *)
(* and a section through 0 can bound a compact region).                     *)

let APX_SECTION_NOT_BOUNDING_STATEMENT = new_definition
 `APX_SECTION_NOT_BOUNDING_STATEMENT (u:A->bool) <=>
    !top atlas E r1 r2 S K.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        &0 <= r1 /\
        mfd_param top atlas (annulus r1 r2) E /\ apx_section E r1 r2 S /\
        compact_in top K /\ K SUBSET IMAGE E (annulus r1 r2) /\
        top frontier_of K SUBSET S
        ==> top interior_of K = {}`;;

(* N5b. The closed core of a (C,eps)-cap never lies in an eps-neck (its      *)
(* boundary sphere would be a section bounding it; N4 + N5).  The first case *)
(* of MT's proof of Claim A.22 (p. 510) needs this fact without proving it.  *)

let APX_NO_CAP_IN_NECK_STATEMENT = new_definition
 `APX_NO_CAP_IN_NECK_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !C top atlas g eps x e U Y.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         rfs_neck (top,atlas) g eps x (e:real^3->A) /\
         rfs_cap (top,atlas) g C eps U Y
         ==> ~(top closure_of Y SUBSET IMAGE e (rfs_neck_dom eps))`;;

(* N6. Caps keep away from the middle half of a delta-neck when delta is     *)
(* small relative to 1/C (diameter clause of Def 9.72 + N2 + N5b).  Used in  *)
(* the region theorem: surgery spheres are far from all cap cores.           *)

let APX_CAP_FAR_STATEMENT = new_definition
 `APX_CAP_FAR_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps. &0 < C /\ &0 < eps /\ eps <= eps0
        ==> ?dl1. &0 < dl1 /\
              !top atlas g dl x e U Y.
                 &0 < dl /\ dl <= dl1 /\ hausdorff_space top /\
                 riemannian_metric atlas g /\
                 rfs_neck (top,atlas) g dl x (e:real^3->A) /\
                 rfs_cap (top,atlas) g C eps U Y
                 ==> DISJOINT U (IMAGE e (apx_slab (--inv(&2 * dl)) (inv(&2 * dl))))`;;

(* N7. A component containing a delta-neck (delta small relative to 1/C) is  *)
(* neither a C-component nor an eps-round component (a neck has a plane of   *)
(* sectional curvature about 0 next to one of about R/2, by N1; C-components *)
(* have all sectional curvatures above R/C, round components almost constant *)
(* ones).  MT's proof of Prop 15.3 (p. 357) does not exclude these           *)
(* components.                                                               *)

let APX_EXCLUDE_STATEMENT = new_definition
 `APX_EXCLUDE_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps. &0 < C /\ &0 < eps /\ eps <= eps0
        ==> ?dl1. &0 < dl1 /\
              !top atlas g dl x e W.
                 &0 < dl /\ dl <= dl1 /\ hausdorff_space top /\
                 riemannian_metric atlas g /\
                 rfs_neck (top,atlas) g dl x (e:real^3->A) /\ x IN W
                 ==> ~rfs_c_component (top,atlas) g C W /\
                     ~rfs_round_component (top,atlas) g eps W`;;

(* N8. A strong delta-neck at time t (MT Def 9.78) is a K delta-neck with   *)
(* the same parametrization and centre at all slightly earlier times of a    *)
(* fixed stage, K universal (closeness to cylinder_flow s for s near 0, and  *)
(* the factor R(y,t')/R(y,t) = 1 + O(delta + |s|) from the curvature         *)
(* stability constant).  Used to move the surgery spheres to the time t' of  *)
(* Prop 15.3.                                                                *)

let APX_STRONG_NECK_EARLIER_STATEMENT = new_definition
 `APX_STRONG_NECK_EARLIER_STATEMENT (u:A->bool) <=>
    ?K. &1 <= K /\
      !TM AT G dl y t e top atlas t0.
          &0 < dl /\ K * dl <= &1 / &2 /\ t0 < t /\
          rfs_strong_neck (TM,AT,G) dl y t (e:real^3->A) /\
          (!s. t0 < s /\ s < t
               ==> TM s = top /\ AT s = atlas /\ riemannian_metric atlas (G s) /\
                   mfd_param top atlas (rfs_neck_dom dl) e)
          ==> ?d. &0 < d /\
                  !s. t - d < s /\ s < t ==> rfs_neck (top,atlas) (G s) (K * dl) y e`;;



(* ========================================================================= *)
(* Layer P: shortest curves and necks, MT A.1-A.10 (used by Prop 2.19, Ch 9  *)
(* and Thm 10.2).                                                            *)
(* ========================================================================= *)

(* The positive side of the central sphere of e (component of the            *)
(* complement containing the outer half).                                    *)

let apx_pos_side = new_definition
 `apx_pos_side (top:A topology) (e:real^3->A) =
    connected_component_of
      (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
      (e(&4 / &3 % basis 1))`;;

let apx_neg_side = new_definition
 `apx_neg_side (top:A topology) (e:real^3->A) =
    connected_component_of
      (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
      (e(&3 / &4 % basis 1))`;;

(* P1. MT Lemma A.1 (shortening across a separating neck): a curve from the  *)
(* centre to a point y on the closed positive side that dips into the        *)
(* negative quarter can be replaced by one on the closed positive side that  *)
(* is shorter by eps^-1 R(x)^(-1/2) / 2.                                     *)

let APX_A1_STATEMENT = new_definition
 `APX_A1_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !top atlas g eps x e y gamma a b.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
         riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
         rfs_neck (top,atlas) g eps x (e:real^3->A) /\
         (y IN IMAGE e (sphere(vec 0,&1)) \/ apx_pos_side top e y) /\
         mfd_c1_curve (top,atlas) gamma a b /\ gamma a = x /\ gamma b = y /\
         (?t. a <= t /\ t <= b /\
              gamma t IN IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps))))
         ==> ?gamma'. mfd_c1_curve (top,atlas) gamma' (&0) (&1) /\
                      gamma'(&0) = x /\ gamma'(&1) = y /\
                      (!t. &0 <= t /\ t <= &1
                           ==> gamma' t IN IMAGE e (sphere(vec 0,&1)) \/
                               apx_pos_side top e (gamma' t)) /\
                      mfd_length atlas g gamma' (&0) (&1) <=
                      mfd_length atlas g gamma a b -
                      inv(&2 * eps) * inv(sqrt(mfd_scalar atlas g x))`;;

(* P2. MT Lemma A.4 (first part, scalar form): a long shortest curve inside  *)
(* an eps-neck moves almost purely in the s-direction: (d/dt) s(gamma t) >=  *)
(* (1 - alpha) R(x)^(1/2) |gamma'(t)|_g when s increases from start to end.  *)

let APX_A4_STATEMENT = new_definition
 `APX_A4_STATEMENT (u:A->bool) <=>
    !alpha. &0 < alpha
      ==> ?eps1. &0 < eps1 /\
            !top atlas g eps x e gamma a b.
               &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
               riemannian_metric atlas g /\
               rfs_neck (top,atlas) g eps x (e:real^3->A) /\
               apx_shortest (top,atlas) g gamma a b /\ a < b /\
               (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
               inv(&100 * eps) * inv(sqrt(mfd_scalar atlas g x))
               < mfd_length atlas g gamma a b /\
               apx_sfun (rfs_neck_dom eps) e (gamma a) <
               apx_sfun (rfs_neck_dom eps) e (gamma b)
               ==> !t. a <= t /\ t <= b
                       ==> (&1 - alpha) * sqrt(mfd_scalar atlas g x) *
                           mfd_speed atlas g gamma a b t
                           <= drop(vector_derivative
                                    (\s. lift(apx_sfun (rfs_neck_dom eps) e (gamma(drop s))))
                                    (at (lift t) within interval[lift a,lift b]))`;;

(* P3. MT Cor A.6: such a curve meets each level sphere of the neck domain   *)
(* in at most one point.  Corrected form: the conclusion is gamma t1 = gamma *)
(* t2 (shortest curves may stop), and the level sphere must lie in the neck  *)
(* domain (outside it e is arbitrary).                                       *)

let APX_A6_STATEMENT = new_definition
 `APX_A6_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !top atlas g eps x e gamma a b r.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         rfs_neck (top,atlas) g eps x (e:real^3->A) /\
         apx_shortest (top,atlas) g gamma a b /\
         (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
         inv(&100 * eps) * inv(sqrt(mfd_scalar atlas g x))
         < mfd_length atlas g gamma a b /\
         sphere(vec 0,r) SUBSET rfs_neck_dom eps
         ==> !t1 t2. a <= t1 /\ t1 <= b /\ a <= t2 /\ t2 <= b /\
                     gamma t1 IN IMAGE e (sphere(vec 0,r)) /\
                     gamma t2 IN IMAGE e (sphere(vec 0,r))
                     ==> gamma t1 = gamma t2`;;

(* P3b. MT Lemma A.7: a shortest curve                                       *)
(* of M whose pieces in the neck are long (at least R(x)^(-1/2)/(8 eps))   *)
(* meets each level sphere of the neck domain in at most one point.  A      *)
(* piece is a maximal subinterval mapped into the neck.                     *)

let APX_A7_STATEMENT = new_definition
 `APX_A7_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !top atlas g eps x e gamma a b r.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         rfs_neck (top,atlas) g eps x (e:real^3->A) /\
         apx_shortest (top,atlas) g gamma a b /\
         (!c d. a <= c /\ c < d /\ d <= b /\
                (!t. c < t /\ t < d ==> gamma t IN IMAGE e (rfs_neck_dom eps)) /\
                (c = a \/ ~(gamma c IN IMAGE e (rfs_neck_dom eps))) /\
                (d = b \/ ~(gamma d IN IMAGE e (rfs_neck_dom eps)))
                ==> inv(&8 * eps) * inv(sqrt(mfd_scalar atlas g x))
                    <= mfd_length atlas g gamma c d) /\
         sphere(vec 0,r) SUBSET rfs_neck_dom eps
         ==> !t1 t2. a <= t1 /\ t1 <= b /\ a <= t2 /\ t2 <= b /\
                     gamma t1 IN IMAGE e (sphere(vec 0,r)) /\
                     gamma t2 IN IMAGE e (sphere(vec 0,r))
                     ==> gamma t1 = gamma t2`;;

(* P4. MT Cor A.8: a shortest curve that meets the core of a cap meets the   *)
(* extended core (closed core plus the closed half of the end neck next to  *)
(* it) in an interval containing an end point.  The end neck e is oriented   *)
(* so that its negative end abuts the core (MT Remark after Def 9.72).       *)

let APX_A8_STATEMENT = new_definition
 `APX_A8_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !C top atlas g eps U Y x e gamma a b.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         rfs_cap (top,atlas) g C eps U Y /\
         rfs_neck (top,atlas) g eps x (e:real^3->A) /\
         IMAGE e (rfs_neck_dom eps) = U DIFF top closure_of Y /\
         ~(top closure_of (IMAGE e (apx_slab (--inv eps) (&0))) INTER
           top closure_of Y = {}) /\
         apx_shortest (top,atlas) g gamma a b /\
         (?t. a <= t /\ t <= b /\ gamma t IN Y)
         ==> ?c d. a <= c /\ c <= d /\ d <= b /\ (c = a \/ d = b) /\
                   !t. a <= t /\ t <= b
                       ==> (gamma t IN top closure_of Y UNION
                                       IMAGE e {y | y IN rfs_neck_dom eps /\ norm y <= &1}
                            <=> c <= t /\ t <= d)`;;

(* P5. MT Lemma A.9 with the scale factor R(x)^(-1/2) that MT's statement    *)
(* omits (proved by a separating level sphere instead of MT's continuity     *)
(* argument): z off the middle two thirds on the negative side, p in the     *)
(* middle half, q further along the same s-line: d(z,.) grows like h s.      *)

let APX_A9_STATEMENT = new_definition
 `APX_A9_STATEMENT (u:A->bool) <=>
    !alpha. &0 < alpha /\ alpha < &1
      ==> ?eps1. &0 < eps1 /\
            !top atlas g eps x e z w r1 r2.
               &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
               riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
               rfs_neck (top,atlas) g eps x (e:real^3->A) /\
               apx_neg_side top e z /\
               ~(z IN IMAGE e (apx_slab (--(&2 / &3 * inv eps)) (&2 / &3 * inv eps))) /\
               w IN sphere(vec 0,&1) /\ r1 <= r2 /\
               r1 % w IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\
               r2 % w IN rfs_neck_dom eps /\
               mfd_joinable (top,atlas) z (e(r1 % w))
               ==> (&1 - alpha) * inv(sqrt(mfd_scalar atlas g x)) *
                   (apx_sval(r2 % w) - apx_sval(r1 % w))
                   <= mfd_dist (top,atlas) g z (e(r2 % w)) -
                      mfd_dist (top,atlas) g z (e(r1 % w)) /\
                   mfd_dist (top,atlas) g z (e(r2 % w)) -
                   mfd_dist (top,atlas) g z (e(r1 % w))
                   <= (&1 + alpha) * inv(sqrt(mfd_scalar atlas g x)) *
                      (apx_sval(r2 % w) - apx_sval(r1 % w))`;;

(* P6. MT Lemma A.10 (used by Lemma 2.20, Prop 9.85): the metric sphere      *)
(* around such a z through a point p of the middle sixth meets N in a        *)
(* continuous section inside the middle quarter, within alpha/eps of s(p).   *)

let APX_A10_STATEMENT = new_definition
 `APX_A10_STATEMENT (u:A->bool) <=>
    !alpha. &0 < alpha
      ==> ?eps1. &0 < eps1 /\
            !top atlas g eps x e z y.
               &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
               riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
               rfs_neck (top,atlas) g eps x (e:real^3->A) /\
               apx_neg_side top e z /\
               ~(z IN IMAGE e (apx_slab (--(&2 / &3 * inv eps)) (&2 / &3 * inv eps))) /\
               y IN apx_slab (--inv(&6 * eps)) (inv(&6 * eps)) /\
               mfd_joinable (top,atlas) z (e y)
               ==> apx_csection e (exp(--inv(&4 * eps) / sqrt(&2)))
                                  (exp(inv(&4 * eps) / sqrt(&2)))
                     ({q | mfd_joinable (top,atlas) z q /\
                           mfd_dist (top,atlas) g z q = mfd_dist (top,atlas) g z (e y)}
                      INTER IMAGE e (rfs_neck_dom eps)) /\
                   (!y'. y' IN rfs_neck_dom eps /\
                         mfd_dist (top,atlas) g z (e y') = mfd_dist (top,atlas) g z (e y)
                         ==> abs(apx_sval y' - apx_sval y) < alpha * inv eps)`;;



(* ========================================================================= *)
(* Layer T: topology of regions covered by necks and caps (separating case). *)
(* ========================================================================= *)

(* T0, T0b: APX_SC_SPHERE_SEP_STATEMENT and APX_SEP_OPEN_STATEMENT come from  *)
(* pc_apx_sep.                                                                *)

(* T1. MT Lemma A.13 (with A.16), corrected (MT's proof applies A.11(5), a   *)
(* statement about two necks, to unions of necks) and made explicit: the     *)
(* union of a finite chain N_0..N_n is an eps-tube whose product chart E is  *)
(* exactly e_0 up to the middle of N_0 and e_n (up to a diffeomorphism f of  *)
(* S^2 and the shift of s by L) from the middle of N_n on.  Proof: splice    *)
(* the s-functions of the necks (cutoffs in s, N3) into a function without   *)
(* critical points, SMT_PRODUCT2_STATEMENT (M6b) between a level in N_0 and  *)
(* a level in N_n, and e_0, e_n beyond those levels.  The exact end          *)
(* conditions keep all later gluings radial (no uniqueness of collars        *)
(* needed).  The hypothesis apx_sphere_sep is needed (the sections clause of *)
(* apx_tube fails without it, e.g. on S^2 x (R/LZ) with L > 4/eps), and both *)
(* exact-end regions have length 1/(8 eps) (with 1/(4 eps) they can be       *)
(* forced to overlap).                                                       *)

let APX_A13_STATEMENT = new_definition
 `APX_A13_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !top atlas g eps n x e.
         &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
         apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x
                   (e:int->real^3->A)
         ==> ?E L f f'.
               &0 <= L /\ sphere_diffeo f f' /\
               mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
               (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
               (!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
                    ==> E y = e (&n) (radial_ext f (exp(--L / sqrt(&2)) % y))) /\
               IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
               apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e /\
               apx_tube (top,atlas) g eps E (exp(--inv eps / sqrt(&2)))
                        (exp((L + inv eps) / sqrt(&2)))`;;

(* T2. MT Lemma A.15 (used in Ch 11): the frontier of the union of a         *)
(* chain infinite in the positive direction lies in the closure of the       *)
(* negative quarter of its first neck.                                       *)

let APX_A15_STATEMENT = new_definition
 `APX_A15_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !top atlas g eps x e.
         &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         apx_chain (top,atlas) g eps {i:int | &0 <= i} x (e:int->real^3->A)
         ==> top frontier_of (apx_chain_union eps {i:int | &0 <= i} e) SUBSET
             top closure_of (IMAGE (e (&0)) (apx_slab (--inv eps) (--inv(&2 * eps))))`;;

(* T3. MT Lemmas A.17-A.18 (extension of a balanced chain at its positive    *)
(* end by a neck centred at a frontier point), with separation of all neck   *)
(* spheres (A.17 needs it for N_b and N too).                                *)

let APX_A18_STATEMENT = new_definition
 `APX_A18_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !top atlas g eps a b x e z ez.
         &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas g /\ apx_sphere_sep top atlas /\ a <= b /\
         apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x
                      (e:int->real^3->A) /\
         z IN top closure_of (IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps))) /\
         ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e) /\
         rfs_neck (top,atlas) g eps z ez
         ==> ?ez'. (ez' = ez \/ ez' = apx_rev ez) /\
                   apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b + &1}
                     (\i. if i = b + &1 then z else x i)
                     (\i. if i = b + &1 then ez' else e i)`;;

(* T3b. Termination: a balanced chain centred in a compact set is finite.    *)

let APX_CHAIN_FINITE_STATEMENT = new_definition
 `APX_CHAIN_FINITE_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !top atlas g eps Ix x e K.
         &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         apx_balanced (top,atlas) g eps Ix x (e:int->real^3->A) /\
         compact_in top K /\ (!i. i IN Ix ==> x i IN K)
         ==> FINITE Ix`;;

(* T4. MT Prop A.19, corrected (the central spheres SEPARATE: MT's text      *)
(* assumes that they do not, but its proof uses Lemma A.18, which needs      *)
(* separation; compact X here, the Ch 11 noncompact form uses T2): a compact *)
(* connected set all of whose points are centres of necks from a class NK    *)
(* lies in the union of a finite balanced chain of NK-necks (possibly        *)
(* reversed) centred in X, and that union is an eps-tube.  NK = strong necks *)
(* gives MT's strong tubes.                                                  *)

let APX_A19_STATEMENT = new_definition
 `APX_A19_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !top atlas g eps NK X.
         &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
         compact_in top X /\ connected_in top X /\ ~(X = {}) /\
         (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
         (!x. x IN X ==> ?e. NK x e)
         ==> ?a b x e.
               a <= b /\
               apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
               (!i. a <= i /\ i <= b
                    ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
               X SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e /\
               ?E r1 r2. apx_tube (top,atlas) g eps E r1 r2 /\
                         IMAGE E (annulus r1 r2) =
                         apx_chain_union eps {i:int | a <= i /\ i <= b} e`;;

(* T5. MT Claim A.22 (with the quantitative repair recorded by FrenzyMath):  *)
(* no infinite increasing sequence of caps each of whose closed cores meets  *)
(* the frontier of the previous cap.  Gives the maximal cap of A.21 Case I.  *)

let APX_A22_STATEMENT = new_definition
 `APX_A22_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas g U Y.
         &0 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas (g:A->real^3^3)
         ==> ~(!n. rfs_cap (top,atlas) g C eps (U n) (Y n) /\
                   U n SUBSET U(SUC n) /\
                   ~(top frontier_of (U n) INTER top closure_of (Y(SUC n)) = {}))`;;

(* T6. MT Prop A.21, corrected, separating case, compact X, with a class NK  *)
(* of necks as in T4. X lies in (1),(2) a compact component V of M that is   *)
(* the union of two (C,eps)-caps, or of two caps and an eps-tube; (3) a      *)
(* single (C,eps)-cap; (4) a C-capped eps-tube: a cap U and an eps-tube that *)
(* meets U, leaves U at its outer end and misses the closed core; (5) the    *)
(* union of a balanced chain of NK-necks centred in X, an eps-tube. In every *)
(* cap alternative the closed core meets X. The non-separating alternative   *)
(* (6) does not occur.  Every end comes with a neck (the cap neck in         *)
(* rfs_cap, the tube chart E).  The extra information (closed cores meet X;  *)
(* necks from NK centred in X) is used by Lemma 11.30 but is not in the      *)
(* statement of MT (only in its proof): the maximal-cap iteration ends with  *)
(* a cap whose closed core contains a point of X.  MT's alternative (3) is   *)
(* kept (a single twisted cap is no capped tube), capped tubes have no       *)
(* global chart, and the compact component comes without its diffeomorphism  *)
(* type (S^3, RP^3, RP^3 # RP^3 is the business of A25, proved separately);  *)
(* A21 then needs no Schoenflies theorem.                                    *)

let APX_A21_STATEMENT = new_definition
 `APX_A21_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas g NK X.
         &0 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas (g:A->real^3^3) /\ apx_sphere_sep top atlas /\
         compact_in top X /\ connected_in top X /\ ~(X = {}) /\
         (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
         (!x. x IN X
              ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y))
         ==> (?V U1 Y1 U2 Y2.
                  V IN connected_components_of top /\ compact_in top V /\
                  X SUBSET V /\
                  rfs_cap (top,atlas) g C eps U1 Y1 /\ ~DISJOINT X (top closure_of Y1) /\
                  rfs_cap (top,atlas) g C eps U2 Y2 /\ ~DISJOINT X (top closure_of Y2) /\
                  (V = U1 UNION U2 \/
                   (?E r1 r2. apx_tube (top,atlas) g eps E r1 r2 /\
                              V = U1 UNION IMAGE E (annulus r1 r2) UNION U2))) \/
             (?U Y. rfs_cap (top,atlas) g C eps U Y /\ X SUBSET U /\
                    ~DISJOINT X (top closure_of Y)) \/
             (?U Y E r1 rho r2.
                  rfs_cap (top,atlas) g C eps U Y /\
                  apx_tube (top,atlas) g eps E r1 r2 /\ r1 < rho /\ rho < r2 /\
                  ~(U INTER IMAGE E (annulus r1 r2) = {}) /\
                  DISJOINT U (IMAGE E (annulus rho r2)) /\
                  DISJOINT (top closure_of Y) (IMAGE E (annulus r1 r2)) /\
                  X SUBSET U UNION IMAGE E (annulus r1 r2) /\
                  ~DISJOINT X (top closure_of Y)) \/
             (?a b x e E r1 r2.
                 a <= b /\
                 apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
                 (!i. a <= i /\ i <= b
                      ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
                 apx_tube (top,atlas) g eps E r1 r2 /\
                 IMAGE E (annulus r1 r2) =
                 apx_chain_union eps {i:int | a <= i /\ i <= b} e /\
                 X SUBSET IMAGE E (annulus r1 r2))`;;

(* T7. MT Prop A.25 (stated in MT without proof), separating case, for a     *)
(* compact component V of M all of whose points are neck centres or cap     *)
(* cores (relative form: no metric has to be restricted): two closed balls   *)
(* glued radially (S^3 by SMT_TWISTED_SPHERE_STATEMENT) or a twisted chart   *)
(* (RP^3, RP^3 # RP^3).  The S^2-bundle case (4) needs non-separating        *)
(* spheres.  Follows from T6 with X = V (APX_A25_FROM_A21).                  *)

let APX_A25_STATEMENT = new_definition
 `APX_A25_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas g V.
         &0 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas (g:A->real^3^3) /\ apx_sphere_sep top atlas /\
         V IN connected_components_of top /\ compact_in top V /\
         (!x. x IN V ==> apx_neck_or_core (top,atlas) g C eps x)
         ==> apx_two_balls (subtopology top V) (restrict_atlas atlas V) \/
             rfs_has_twisted (subtopology top V) (restrict_atlas atlas V)`;;

(* T7b. Noncompact form of A.25 (used in Ch 11, Lemma 11.28; needs the       *)
(* infinite chains of T2): an open ball, a twisted capped tube, or S^2 x R. *)

let APX_A25_NC_STATEMENT = new_definition
 `APX_A25_NC_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas g.
         &0 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas (g:A->real^3^3) /\ apx_sphere_sep top atlas /\
         connected_space top /\ ~compact_space top /\
         (!x. x IN topspace top ==> apx_neck_or_core (top,atlas) g C eps x)
         ==> mfd_diffeomorphic top atlas
               (subtopology euclidean (ball(vec 0:real^3,&1)))
               (open_set_atlas (ball(vec 0:real^3,&1))) \/
             rfs_has_twisted top atlas \/
             mfd_diffeomorphic top atlas
               (subtopology euclidean (annulus (&1) (&2):real^3->bool))
               (open_set_atlas (annulus (&1) (&2):real^3->bool))`;;

(* ========================================================================= *)
(* Layer R: the region theorem (the corrected core of the proof of MT Prop   *)
(* 15.3, which applies A.19 without checking separation).  P is the old part *)
(* of a discarded piece: open, connected, compact closure P + the cut        *)
(* spheres S_i (i in J, delta-necks e_i), P on the outer side of each S_i,   *)
(* every point of the closure a neck centre or a cap core.  Then |J| <= 2    *)
(* and, unless P contains a twisted chart, P is a product E(annulus 1 L)     *)
(* starting exactly at e_i and ending radially either at a closed ball       *)
(* b2(cball 1) in P (J = {i}) or at the outer side of e_j (J = {i,j}, b2 =   *)
(* e_j).  Capping (APX_GLUE_CAPPED) then gives S^3.  delta <= dl1(C,eps)     *)
(* keeps caps away from the S_i (N6).                                        *)
(* ========================================================================= *)

let APX_REGION_STATEMENT = new_definition
 `APX_REGION_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps. &0 < C /\ &0 < eps /\ eps <= eps0
        ==> ?dl1. &0 < dl1 /\
              !top atlas g dl J e P.
                 hausdorff_space top /\
                 smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                 riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
                 &0 < dl /\ dl <= dl1 /\ FINITE J /\ ~(J = {}) /\
                 (!i:num. i IN J ==> ?y. rfs_neck (top,atlas) g dl y (e i)) /\
                 (!i j. i IN J /\ j IN J /\ ~(i = j)
                        ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                                     (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
                 open_in top P /\ connected_in top P /\
                 compact_in top (top closure_of P) /\
                 top closure_of P =
                 P UNION UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i IN J} /\
                 (!i. i IN J
                      ==> P INTER IMAGE (e i) (annulus (&1 / &2) (&2)) =
                          IMAGE (e i) (annulus (&1) (&2))) /\
                 (!x. x IN top closure_of P ==> apx_neck_or_core (top,atlas) g C eps x)
                 ==> rfs_has_twisted (subtopology top P) (restrict_atlas atlas P) \/
                     ?i E L f f' b2.
                        i IN J /\ &1 < L /\ sphere_diffeo f f' /\
                        mfd_param top atlas (annulus (&1) L) E /\
                        (!x. x IN annulus (&1) (&3 / &2) ==> E x = e i x) /\
                        (!x. x IN annulus (L / &2) L
                             ==> E x = b2((L / norm x) % f(inv(norm x) % x))) /\
                        ((J = {i} /\ mfd_ball_chart top atlas b2 /\
                          IMAGE b2 (ball(vec 0,&2)) SUBSET P /\
                          P = IMAGE E (annulus (&1) L) UNION IMAGE b2 (cball(vec 0,&1)) /\
                          DISJOINT (IMAGE E (annulus (&1) L)) (IMAGE b2 (cball(vec 0,&1)))) \/
                         (?j. j IN J /\ ~(j = i) /\ J = {i,j} /\ b2 = e j /\
                              P = IMAGE E (annulus (&1) L)))`;;



(* ========================================================================= *)
(* Layer E: the chain from EVENT_TOPOLOGY_STATEMENT (MT Prop 15.3).          *)
(* ========================================================================= *)

(* E1. From the history to the situation at a time t' just before the        *)
(* surgery time: canonical neighbourhoods (Assumption (6); a strong          *)
(* canonical neighbourhood is a canonical one at its time), the cut necks    *)
(* as K delta(T)-necks at t' (N8, same universal K), separation (T0).        *)

let APX_EVENT_SLICE_STATEMENT = new_definition
 `APX_EVENT_SLICE_STATEMENT (u:A->bool) <=>
    ?K. &1 <= K /\
      !(hs:(A)rfs_history) C eps rp dl kp h k.
          rfs_history_ok hs /\ rfs_params (rp,dl,kp,h) /\ &0 < C /\ &0 < eps /\
          (!t. &0 <= t ==> K * dl t <= &1 / &2) /\
          1 <= k /\ k <= hs_count hs /\
          rfs_surgery_ok hs C eps dl h k /\
          rfs_components_sc (hs_top hs (k - 1))
          ==> ?t'. hs_time hs (k - 1) <= t' /\ t' < hs_time hs k /\
                   apx_cut_situation (hs_top hs (k - 1),hs_atlas hs (k - 1))
                     (hs_metric hs (k - 1) t') C eps (K * dl(hs_time hs k))
                     (ev_ztop(hs_event hs k),ev_zatlas(hs_event hs k))
                     (ev_index(hs_event hs k)) (ev_neck(hs_event hs k))
                     (ev_capp(hs_event hs k)) (ev_capm(hs_event hs k))
                     (ev_disc(hs_event hs k))`;;

(* E2. MT Prop 15.3 (separating case) for the situation: every discarded     *)
(* component of Z is a listed piece.                                          *)

let APX_EVENT_PIECES_STATEMENT = new_definition
 `APX_EVENT_PIECES_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps. &0 < C /\ &0 < eps /\ eps <= eps0
        ==> ?dl1. &0 < dl1 /\
              !topX atlasX g dl topZ atlasZ J e cp cm D.
                 &0 < dl /\ dl <= dl1 /\
                 apx_cut_situation (topX,atlasX) g C eps dl (topZ,atlasZ)
                                   J e cp cm (D:A->bool)
                 ==> !U. U IN connected_components_of topZ /\ U SUBSET D
                         ==> rfs_listed_piece (subtopology topZ U)
                                              (restrict_atlas atlasZ U)`;;

(* E3. Point-set structure of a discarded component U of Z: J_U = the plus   *)
(* caps in U, P = U minus the cap cores.  If J_U is empty, U is a component  *)
(* of X; in all cases P satisfies the topological hypotheses of the region  *)
(* theorem and its closure consists of old points that are not retained.    *)

let APX_CUTCAP_PIECE_STATEMENT = new_definition
 `APX_CUTCAP_PIECE_STATEMENT (u:A->bool) <=>
    !topX atlasX topZ atlasZ J e cp cm D U JU P.
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        compact_space topX /\
        hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
        compact_space topZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm (\x. x) (\x. x) /\
        DISJOINT (topspace topX) (mfd_cut_cores J cp cm) /\
        D SUBSET topspace topZ /\ open_in topZ D /\ closed_in topZ D /\
        (!i. i IN J
             ==> IMAGE (cp i) (cball(vec 0,&1)) SUBSET D /\
                 DISJOINT (IMAGE (cm i) (cball(vec 0,&1))) D) /\
        U IN connected_components_of topZ /\ U SUBSET D /\
        JU = {i | i IN J /\ cp i (vec 0) IN U} /\
        P = U DIFF mfd_cut_cores J cp cm
        ==> (JU = {} ==> P = U /\ U IN connected_components_of topX) /\
            U = P UNION UNIONS {IMAGE (cp i) (cball(vec 0,&1)) | i IN JU} /\
            open_in topX P /\ connected_in topX P /\ ~(P = {}) /\
            compact_in topX (topX closure_of P) /\
            topX closure_of P =
            P UNION UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i IN JU} /\
            topX closure_of P SUBSET topspace topX DIFF (topspace topZ DIFF D) /\
            (!i. i IN JU
                 ==> P INTER IMAGE (e i) (annulus (&1 / &2) (&2)) =
                     IMAGE (e i) (annulus (&1) (&2))) /\
            (!i. i IN J /\ ~(i IN JU)
                 ==> DISJOINT P (IMAGE (e i) (annulus (&1 / &2) (&2))))`;;

(* E4. Capping a product by two balls gives S^3 (in Z; from the twisted      *)
(* sphere theorem M2 by assembling one ball chart from c, E and b2).  Both   *)
(* outcomes of the region theorem have this form after capping.             *)

let APX_GLUE_CAPPED_STATEMENT = new_definition
 `APX_GLUE_CAPPED_STATEMENT (u:A->bool) <=>
    !top atlas c E L b2 f f'.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        mfd_ball_chart top atlas c /\ mfd_ball_chart top atlas b2 /\
        &1 < L /\ sphere_diffeo f f' /\
        mfd_param top atlas (annulus (&1) L) E /\
        (!x. x IN annulus (&1) (&3 / &2) ==> E x = c x) /\
        (!x. x IN annulus (L / &2) L ==> E x = b2((L / norm x) % f(inv(norm x) % x))) /\
        topspace top = IMAGE c (cball(vec 0,&1)) UNION IMAGE E (annulus (&1) L) UNION
                       IMAGE b2 (cball(vec 0,&1)) /\
        DISJOINT (IMAGE c (cball(vec 0,&1))) (IMAGE E (annulus (&1) L)) /\
        DISJOINT (IMAGE c (cball(vec 0,&1))) (IMAGE b2 (cball(vec 0,&1))) /\
        DISJOINT (IMAGE E (annulus (&1) L)) (IMAGE b2 (cball(vec 0,&1)))
        ==> mfd_diffeomorphic top atlas
              (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas`;;

(* E5. Twisted charts and listed pieces are invariant under diffeomorphisms  *)
(* (S^3 by transitivity, space forms by pulling back the metric, S^2-bundles *)
(* and twisted charts by composition).                                       *)

let APX_LISTED_DIFFEO_STATEMENT = new_definition
 `APX_LISTED_DIFFEO_STATEMENT (u:A->bool) (v:B->bool) <=>
    !top atlas top' atlas'.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        hausdorff_space top' /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
        mfd_diffeomorphic top atlas top' atlas'
        ==> (rfs_has_twisted top atlas ==> rfs_has_twisted top' atlas') /\
            (rfs_listed_piece top atlas ==> rfs_listed_piece top' atlas')`;;

(* E6. A twisted chart of an open subset is one of every larger open subset. *)

let APX_TWISTED_MONO_STATEMENT = new_definition
 `APX_TWISTED_MONO_STATEMENT (u:A->bool) <=>
    !top atlas W W'.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        open_in top W /\ open_in top W' /\ W SUBSET W' /\
        rfs_has_twisted (subtopology top W) (restrict_atlas atlas W)
        ==> rfs_has_twisted (subtopology top W') (restrict_atlas atlas W')`;;

(* ------------------------------------------------------------------------- *)
(* E7-E10. Manifold-level bookkeeping used by the E2 assembly (facts about   *)
(* the notions of pc_mfd_maps and pc_mfd_riem, stated here).                 *)
(* ------------------------------------------------------------------------- *)

(* E7. A diffeomorphism of open subsets is a diffeomorphism of the open      *)
(* submanifolds (identity of X minus the cut spheres and Z minus the cores). *)

let APX_DIFFEO_SUBSPACE_STATEMENT = new_definition
 `APX_DIFFEO_SUBSPACE_STATEMENT (u:A->bool) (v:B->bool) <=>
    !top atlas W top' atlas' W' f f'.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
        mfd_diffeo top atlas W top' atlas' W' f f'
        ==> mfd_diffeomorphic (subtopology top W) (restrict_atlas atlas W)
                              (subtopology top' W') (restrict_atlas atlas' W')`;;

(* E8. Parametrizations are carried by diffeomorphisms and restrict to open  *)
(* submanifolds containing their images.                                     *)

let APX_PARAM_TRANSFER_STATEMENT = new_definition
 `APX_PARAM_TRANSFER_STATEMENT (u:A->bool) (v:B->bool) <=>
    !top atlas W top' atlas' W' f f' s e.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
        mfd_diffeo top atlas W top' atlas' W' f f' /\
        mfd_param top atlas s e /\ IMAGE e s SUBSET W
        ==> mfd_param top' atlas' s (f o e)`;;

let APX_PARAM_RESTRICT_STATEMENT = new_definition
 `APX_PARAM_RESTRICT_STATEMENT (u:A->bool) <=>
    !top atlas W s e.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        open_in top W /\ IMAGE e s SUBSET W
        ==> (mfd_param (subtopology top W) (restrict_atlas atlas W) s e <=>
             mfd_param top atlas s e)`;;

(* E9. An eps-round component is a space form (its metric of curvature 1,    *)
(* transported to the restricted atlas by restrict_metric).                  *)

let APX_ROUND_SPACE_FORM_STATEMENT = new_definition
 `APX_ROUND_SPACE_FORM_STATEMENT (u:A->bool) <=>
    !top atlas g eps U.
        hausdorff_space top /\
        rfs_round_component (top,atlas) (g:A->real^3^3) eps U
        ==> rfs_space_form (subtopology top U) (restrict_atlas atlas U)`;;

(* The top of the event chain and sanity theorems.                           *)

prioritize_real();;
type_invention_error := true;;

(* Event times are nonnegative. *)

let APX_HS_TIME_POS = prove
 (`!hs:(A)rfs_history k.
        rfs_history_ok hs /\ k <= hs_count hs + 1 ==> &0 <= hs_time hs k`,
  SUBGOAL_THEN
   `!hs:(A)rfs_history. rfs_history_ok hs
       ==> !k. k <= hs_count hs + 1 ==> &0 <= hs_time hs k`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[rfs_history_ok]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[rfs_history_ok] o
                check (fun th -> concl th = `rfs_history_ok (hs:(A)rfs_history)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD1] THEN ASM_REAL_ARITH_TAC]);;

(* EVENT_TOPOLOGY_STATEMENT from E1 and E2: eps0 from E2; for (C,eps) the   *)
(* surgery control bound dl0 = min(dl1/K, 1/(2K)), so that the cut necks are *)
(* K delta(T)-necks with K delta(T) <= dl1 at the time t' given by E1.       *)

let APX_EVENT_TOPOLOGY_FROM_PARTS = prove
 (`!u:A->bool. APX_EVENT_SLICE_STATEMENT u /\ APX_EVENT_PIECES_STATEMENT u
               ==> EVENT_TOPOLOGY_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[APX_EVENT_SLICE_STATEMENT; APX_EVENT_PIECES_STATEMENT;
              EVENT_TOPOLOGY_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `eps0:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`C:real`; `eps:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (dl1 / K) (&1 / (&2 * K))` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `rp:real->real`; `dl:real->real`;
                       `kp:real->real`; `h:real->real`; `k:num`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. &0 <= t ==> K * (dl:real->real) t <= dl1 /\ K * dl t <= &1 / &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < K ==> &0 < &2 * K`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= hs_time (hs:(A)rfs_history) k` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_HS_TIME_POS THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (dl:real->real)(hs_time (hs:(A)rfs_history) k) /\
    K * dl(hs_time hs k) <= dl1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[rfs_params]) THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`hs:(A)rfs_history`; `C:real`; `eps:real`; `rp:real->real`;
    `dl:real->real`; `kp:real->real`; `h:real->real`; `k:num`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
    `hs_metric (hs:(A)rfs_history) (k - 1) t'`;
    `K * (dl:real->real)(hs_time (hs:(A)rfs_history) k)`;
    `ev_ztop(hs_event (hs:(A)rfs_history) k)`;
    `ev_zatlas(hs_event (hs:(A)rfs_history) k)`;
    `ev_index(hs_event (hs:(A)rfs_history) k)`;
    `ev_neck(hs_event (hs:(A)rfs_history) k)`;
    `ev_capp(hs_event (hs:(A)rfs_history) k)`;
    `ev_capm(hs_event (hs:(A)rfs_history) k)`;
    `ev_disc(hs_event (hs:(A)rfs_history) k)`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; REWRITE_TAC[]]);;

prioritize_real();;
type_invention_error := true;;

(* The neck domain rfs_neck_dom is the model slab -1/eps < s < 1/eps. *)

let APX_SLAB_NECK_DOM = prove
 (`!eps. rfs_neck_dom eps = apx_slab (--inv eps) (inv eps)`,
  REWRITE_TAC[rfs_neck_dom; apx_slab; real_div; REAL_INV_MUL; REAL_MUL_LNEG] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

(* Reversal is an involution (also at the origin, as inv 0 = 0). *)

let APX_REV_REV = prove
 (`!e:real^3->A. apx_rev (apx_rev e) = e`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; apx_rev] THEN X_GEN_TAC `y:real^3` THEN
  AP_TERM_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_CASES_TAC `y:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  SUBGOAL_THEN `inv(norm(inv(norm(y:real^3) pow 2) % y) pow 2) *
                inv(norm y pow 2) = &1`
   (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  UNDISCH_TAC `~(y:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
  CONV_TAC REAL_FIELD);;

(* Reversal changes the sign of s. *)

let APX_SVAL_INVERSION = prove
 (`!y:real^3. ~(y = vec 0)
              ==> apx_sval(inv(norm y pow 2) % y) = --(apx_sval y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sval] THEN
  SUBGOAL_THEN `norm(inv(norm(y:real^3) pow 2) % y) = inv(norm y)` SUBST1_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    UNDISCH_TAC `~(y:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[LOG_INV; NORM_POS_LT] THEN REAL_ARITH_TAC]);;

(* Level spheres of a product chart are sections (constant radial graph). *)

let APX_SECTION_LEVEL = prove
 (`!E:real^3->A r1 r2 r.
        r1 < r /\ r < r2 /\ &0 < r
        ==> apx_section E r1 r2 (IMAGE E (sphere(vec 0,r)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_section] THEN
  EXISTS_TAC `\x:real^3. r:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[smooth_near] THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_CONST];
    MP_TAC(ISPECL [`vec 0:real^3`; `&1`]
                  (MATCH_MP SPHERE_SCALING (ASSUME `&0 < r`))) THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; REAL_MUL_RID] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF]]);;

(* Integer segments are integer intervals. *)

let APX_INT_INTERVAL_SEGMENT = prove
 (`!a b:int. apx_int_interval {i | a <= i /\ i <= b}`,
  REWRITE_TAC[apx_int_interval; IN_ELIM_THM] THEN INT_ARITH_TAC);;

(* The positive and negative quarters and the 3/4 slabs of Def A.12 lie in  *)
(* the neck domain (so clause (1) of apx_chain compares subsets of the two   *)
(* necks).                                                                   *)

let APX_SLAB_SUBSET = prove
 (`!a b c d. c <= a /\ b <= d ==> apx_slab a b SUBSET apx_slab c d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exp(c / sqrt(&2)) <= exp(a / sqrt(&2)) /\
                exp(b / sqrt(&2)) <= exp(d / sqrt(&2))` MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    SIMP_TAC[REAL_LE_DIV2_EQ; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[apx_slab; annulus; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

