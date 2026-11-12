(* ========================================================================= *)
(* Unit pc_p4_defs: the history-free definitions and statement constants of  *)
(* Part 4 (finite extinction through the Colding-Minicozzi width of          *)
(* sweepouts by 2-spheres).  Areas, energies and Ricci tangential traces of  *)
(* maps of S^2 into a manifold (through the radial extension), C^1           *)
(* sweepouts, the induced map of S^3 and essential maps (nonzero on H_3),    *)
(* the sweepout width of a component, the monotone quantity Q, pinch maps,   *)
(* width systems, harmonic spheres.  The history parts (p4_pinch_ok,         *)
(* FINITE_EXTINCTION_STATEMENT) are in pc_p4_top.                            *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;
needs "src/pc_mfd_base.ml";;
needs "src/pc_mfd_riem.ml";;
needs "src/pc_mfd_maps.ml";;
needs "src/pc_rf_basic.ml";;
needs "src/pc_grg_dist.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* D1. Second elementary symmetric function of a 3x3 matrix (sum of the    *)
(* principal 2x2 minors) and its polarization (d/ds e2(a + s b) at s = 0).   *)
(* ------------------------------------------------------------------------- *)

let p4_e2 = new_definition
 `p4_e2 (m:real^3^3) = ((trace m) pow 2 - trace(m ** m)) / &2`;;

let p4_e2_pol = new_definition
 `p4_e2_pol (a:real^3^3) (b:real^3^3) = trace a * trace b - trace(a ** b)`;;

(* ------------------------------------------------------------------------- *)
(* D2. C^1 maps from S^2 into a manifold, and the chart Jacobian of the     *)
(* radial extension at y in the preferred chart at u y.                     *)
(* ------------------------------------------------------------------------- *)

let p4_s2_c1 = new_definition
 `p4_s2_c1 (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (u:real^3->A) <=>
    continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top) u /\
    !c. c IN atlas
        ==> continuously_differentiable 1
              {z:real^3 | ~(z = vec 0) /\ u(inv(norm z) % z) IN FST c}
              (\z. SND c (u(inv(norm z) % z)))`;;

let p4_s2_jac = new_definition
 `p4_s2_jac (atlas:((A->bool)#(A->real^N))->bool) (u:real^3->A) (y:real^3) =
    jacobian (\z. SND (chart_at atlas (u y)) (u(inv(norm z) % z))) (at y)`;;

(* The Gram matrix of u at y for the metric g (a 3x3 matrix with y in its  *)
(* kernel), the area density sqrt(e2), the energy density (half the trace)  *)
(* and the tangential trace of a symmetric 2-tensor field Q (given, like g, *)
(* by matrices in preferred charts) times the area density.                 *)

let p4_s2_gram = new_definition
 `p4_s2_gram (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (u:real^3->A) (y:real^3) =
    transp(p4_s2_jac atlas u y) ** g(u y) ** p4_s2_jac atlas u y`;;

let p4_s2_density = new_definition
 `p4_s2_density (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                (u:real^3->A) (y:real^3) =
    sqrt(p4_e2(p4_s2_gram atlas g u y))`;;

let p4_s2_edensity = new_definition
 `p4_s2_edensity (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                 (u:real^3->A) (y:real^3) =
    trace(p4_s2_gram atlas g u y) / &2`;;

let p4_s2_trdensity = new_definition
 `p4_s2_trdensity (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                  (Q:A->real^N^N) (u:real^3->A) (y:real^3) =
    if p4_e2(p4_s2_gram atlas g u y) = &0 then &0
    else p4_e2_pol (p4_s2_gram atlas g u y) (p4_s2_gram atlas Q u y) /
         sqrt(p4_e2(p4_s2_gram atlas g u y))`;;

(* ------------------------------------------------------------------------- *)
(* D3. Area, energy and tangential trace integral of a map of S^2 (surface  *)
(* integrals as 3 times ball integrals of radial extensions).               *)
(* ------------------------------------------------------------------------- *)

let p4_s2_integral = new_definition
 `p4_s2_integral (f:real^3->real) =
    &3 * drop(integral (ball(vec 0:real^3,&1)) (\z. lift(f(inv(norm z) % z))))`;;

let p4_s2_area = new_definition
 `p4_s2_area (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (u:real^3->A) =
    p4_s2_integral (p4_s2_density atlas g u)`;;

let p4_s2_energy = new_definition
 `p4_s2_energy (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (u:real^3->A) =
    p4_s2_integral (p4_s2_edensity atlas g u)`;;

let p4_s2_trint = new_definition
 `p4_s2_trint (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
              (Q:A->real^N^N) (u:real^3->A) =
    p4_s2_integral (p4_s2_trdensity atlas g Q u)`;;

(* ------------------------------------------------------------------------- *)
(* D4. Sweepouts (CM 2008 Sec 1.1, with C^1 slices; equivalent widths by    *)
(* CM Lemma D.1): sigma y t for y in S^2 and t in [0,1], jointly C^1 in     *)
(* (y,t) through the radial extension in y, constant on S^2 at t = 0, 1.    *)
(* ------------------------------------------------------------------------- *)

let p4_sweepout = new_definition
 `p4_sweepout (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
              (sigma:real^3->real->A) <=>
    continuous_map
      (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                     (subtopology euclideanreal (real_interval[&0,&1])),top)
      (\(y,t). sigma y t) /\
    (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
            ==> sigma y (&0) = sigma y' (&0) /\ sigma y (&1) = sigma y' (&1)) /\
    (!c. c IN atlas
         ==> continuously_differentiable 1
               {x:real^(3,1)finite_sum |
                  ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
                  sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) IN FST c}
               (\x. SND c (sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))))`;;

(* The induced map on S^3: the point (r y, 2t - 1) with r = sqrt(1-(2t-1)^2) *)
(* goes to sigma y t; the two poles go to the constant end slices.          *)

let p4_susp = new_definition
 `p4_susp (sigma:real^3->real->A) =
    \x:real^4. if (lambda i. x$i):real^3 = vec 0
               then sigma (basis 1) ((x$4 + &1) / &2)
               else sigma (inv(norm((lambda i. x$i):real^3)) % (lambda i. x$i))
                          ((x$4 + &1) / &2)`;;

(* Essential maps of S^3 into a space: the induced map on H_3 (singular    *)
(* homology, integer coefficients) is not zero (a degree condition that     *)
(* needs no choice of generator).                                            *)

let p4_essential = new_definition
 `p4_essential (top:A topology) (f:real^4->A) <=>
    continuous_map (subtopology euclidean (sphere(vec 0:real^4,&1)),top) f /\
    ?z. z IN group_carrier
               (homology_group(&3,subtopology euclidean (sphere(vec 0:real^4,&1)))) /\
        ~(hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{})
                           (top,{}) f z =
          group_id(homology_group(&3,top)))`;;

(* Sweepouts with values in a subset U (in use: a connected component),     *)
(* their maximal slice area, admissibility (an essential sweepout of U      *)
(* exists) and the width of U: CM's W_A over all nontrivial classes at once *)
(* (the union is harmless: CM Thm 1.14 and Thm 1.7 never fix the class).    *)

let p4_sweepout_in = new_definition
 `p4_sweepout_in (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (U:A->bool)
                 (sigma:real^3->real->A) <=>
    p4_sweepout (top,atlas) sigma /\
    (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> sigma y t IN U) /\
    p4_essential (subtopology top U) (p4_susp sigma)`;;

let p4_sweep_area = new_definition
 `p4_sweep_area (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                (sigma:real^3->real->A) =
    sup {p4_s2_area atlas g (\y. sigma y t) | t IN real_interval[&0,&1]}`;;

let p4_cm_adm = new_definition
 `p4_cm_adm (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (U:A->bool) <=>
    ?sigma. p4_sweepout_in (top,atlas) U sigma`;;

let p4_cm_width = new_definition
 `p4_cm_width (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
              (U:A->bool) =
    inf {p4_sweep_area atlas g sigma | sigma | p4_sweepout_in (top,atlas) U sigma}`;;

(* ------------------------------------------------------------------------- *)
(* D5. The monotone quantity of MT Sec 18.3.2 / CM (1.9) for the scalar     *)
(* lower bound R >= -6/(4t+1): Q = w (4t+1)^(-3/4) + c (4t+1)^(1/4), with   *)
(* c = 4 pi on the Colding-Minicozzi route (c = 2 pi for MT's discs).       *)
(* ------------------------------------------------------------------------- *)

let p4_q = new_definition
 `p4_q (c:real) (w:real) (t:real) =
    w / ((&4 * t + &1) rpow (&3 / &4)) + c * (&4 * t + &1) rpow (&1 / &4)`;;

(* ------------------------------------------------------------------------- *)
(* D6. Pinch maps (MT Prop 15.12 as used in Claim 18.22, in a corrected      *)
(* form: a degree-one map with Lipschitz constant L, in place of the         *)
(* distance-decreasing homotopy equivalence stated by MT): a smooth map      *)
(* p from the component X (metric gX) to the component Y (metric gY) with    *)
(* |dp v|_gY <= L |v|_gX, which is a homeomorphism from a nonempty open      *)
(* U onto an open set and is injective over it (the degree-one witness: in   *)
(* a history p is the identity on the retained points away from the caps).   *)
(* ------------------------------------------------------------------------- *)

let p4_pinch_map = new_definition
 `p4_pinch_map (topX:A topology,atlasX:((A->bool)#(A->real^3))->bool)
               (gX:A->real^3^3) (X:A->bool)
               (topY:B topology,atlasY:((B->bool)#(B->real^3))->bool)
               (gY:B->real^3^3) (Y:B->bool) (L:real) (p:A->B) <=>
    continuous_map (subtopology topX X,subtopology topY Y) p /\
    mfd_smooth_map atlasX atlasY X p /\
    (!x v. x IN X
           ==> (jacobian (\y. SND (chart_at atlasY (p x)) (p (chart_inv (chart_at atlasX x) y)))
                         (at (SND (chart_at atlasX x) x)) ** v) dot
               (gY(p x) **
                (jacobian (\y. SND (chart_at atlasY (p x)) (p (chart_inv (chart_at atlasX x) y)))
                          (at (SND (chart_at atlasX x) x)) ** v))
               <= L pow 2 * (v dot (gX x ** v))) /\
    (?U. open_in topX U /\ ~(U = {}) /\ U SUBSET X /\
         open_in topY (IMAGE p U) /\
         homeomorphic_map (subtopology topX U,subtopology topY (IMAGE p U)) p /\
         !x. x IN X /\ p x IN IMAGE p U ==> x IN U)`;;

(* ------------------------------------------------------------------------- *)
(* D7. Width systems: the route-agnostic interface of the extinction        *)
(* argument (MT Sec 18.3.2 with Prop 18.18 and Claim 18.22; CM Thm 1.7 and  *)
(* Cor 1.11).  WA, aA: width and admissibility on the type of the initial   *)
(* manifold; WB, aB: the same on the type of the history.  Conditions:      *)
(* nonnegativity; the slab inequality (Q non-increasing on surgery-free      *)
(* intervals under R >= -6/(4t+1)); transport by pinch maps; an admissible  *)
(* class on closed simply connected manifolds; isometry invariance.         *)
(* ------------------------------------------------------------------------- *)

let p4_width_system = new_definition
 `p4_width_system
    (WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real,
     aA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->bool)->bool)
    (WB:(B topology#(((B->bool)#(B->real^3))->bool))->(B->real^3^3)->(B->bool)->real,
     aB:(B topology#(((B->bool)#(B->real^3))->bool))->(B->bool)->bool)
    (c:real) <=>
    &0 < c /\
    (!top atlas g U.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        riemannian_metric atlas g /\ aB (top,atlas) U
        ==> &0 <= WB (top,atlas) g U) /\
    (!top atlas g a b t0 t1 U.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        mfd_orientable top atlas /\
        ricci_flow_from (top,atlas) a b g /\
        &0 <= a /\ a <= t0 /\ t0 <= t1 /\ t1 < b /\
        U IN connected_components_of top /\ aB (top,atlas) U /\
        (!t x. t0 <= t /\ t <= t1 /\ x IN U
               ==> --(&6) / (&4 * t + &1) <= mfd_scalar atlas (g t) x)
        ==> p4_q c (WB (top,atlas) (g t1) U) t1 <= p4_q c (WB (top,atlas) (g t0) U) t0) /\
    (!topX atlasX gX X topY atlasY gY Y L p.
        hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
        compact_space topX /\ mfd_orientable topX atlasX /\ riemannian_metric atlasX gX /\
        hausdorff_space topY /\ smooth_manifold_atlas topY atlasY /\
        compact_space topY /\ mfd_orientable topY atlasY /\ riemannian_metric atlasY gY /\
        X IN connected_components_of topX /\ Y IN connected_components_of topY /\
        &1 <= L /\ p4_pinch_map (topX,atlasX) gX X (topY,atlasY) gY Y L p /\
        aB (topX,atlasX) X
        ==> aB (topY,atlasY) Y /\ WB (topY,atlasY) gY Y <= L pow 2 * WB (topX,atlasX) gX X) /\
    (!top atlas.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        ~(topspace top = {}) /\ simply_connected_space top
        ==> aA (top,atlas) (topspace top)) /\
    (!top atlas g top' atlas' g' iota iota'.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        riemannian_metric atlas g /\
        hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ compact_space top' /\
        mfd_isometry (top,atlas) g (top',atlas') g' iota iota' /\
        aA (top,atlas) (topspace top)
        ==> aB (top',atlas') (topspace top') /\
            WB (top',atlas') g' (topspace top') <= WA (top,atlas) g (topspace top))`;;

(* ------------------------------------------------------------------------- *)
(* D8. Smooth maps of S^2, smooth variations, harmonic spheres (critical    *)
(* points of the energy among smooth variations; nonconstant, values in U). *)
(* By Hopf they are conformal, hence branched minimal immersions (CM 2008   *)
(* Sec 2.1, Sacks-Uhlenbeck Cor 1.7).                                        *)
(* ------------------------------------------------------------------------- *)

let p4_s2_smooth = new_definition
 `p4_s2_smooth (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (u:real^3->A) <=>
    continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top) u /\
    !c. c IN atlas
        ==> smooth_map_on {z:real^3 | ~(z = vec 0) /\ u(inv(norm z) % z) IN FST c}
                          (\z. SND c (u(inv(norm z) % z)))`;;

let p4_s2_variation = new_definition
 `p4_s2_variation (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (u:real^3->A)
                  (V:real->real^3->A) <=>
    (!y. y IN sphere(vec 0,&1) ==> V (&0) y = u y) /\
    continuous_map
      (prod_topology (subtopology euclideanreal (real_interval(--(&1),&1)))
                     (subtopology euclidean (sphere(vec 0:real^3,&1))),top)
      (\(s,y). V s y) /\
    !c. c IN atlas
        ==> smooth_map_on
              {x:real^(1,3)finite_sum |
                 drop(fstcart x) IN real_interval(--(&1),&1) /\ ~(sndcart x = vec 0) /\
                 V (drop(fstcart x)) (inv(norm(sndcart x)) % sndcart x) IN FST c}
              (\x. SND c (V (drop(fstcart x)) (inv(norm(sndcart x)) % sndcart x)))`;;

let p4_harmonic_sphere = new_definition
 `p4_harmonic_sphere (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                     (g:A->real^N^N) (U:A->bool) (u:real^3->A) <=>
    p4_s2_smooth (top,atlas) u /\
    (!y. y IN sphere(vec 0,&1) ==> u y IN U) /\
    ~(?x. !y. y IN sphere(vec 0,&1) ==> u y = x) /\
    !V. p4_s2_variation (top,atlas) u V
        ==> ((\s. p4_s2_energy atlas g (V s)) has_real_derivative &0) (atreal (&0))`;;

(* ------------------------------------------------------------------------- *)
(* The history-free statement constants: the CM slab inequality, the         *)
(* topology statements, the elementary area and width facts (proved in       *)
(* pc_p4_width), and the level CM1 statements (CM Thm 1.7,                   *)
(* Thm 1.14 + Prop 1.5, Lemma 1.22).                                         *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* CM0. The width of sweepouts is a width system with c = 4 pi.  The slab   *)
(* inequality (CM Thm 1.7 integrated, CM (1.9)-(1.10)) is the analytic core *)
(* of Part 4; the other conditions are topology (DEGREE_ONE, SC_DEGREE_ONE, *)
(* SMOOTHING) and elementary facts about areas (PINCH_AREA, NONNEG,          *)
(* ISOMETRY, proved in unit pc_p4_width).                                    *)
(* ------------------------------------------------------------------------- *)

let CM_SLAB_STATEMENT = new_definition
 `CM_SLAB_STATEMENT (u:A->bool) <=>
    !top atlas g a b t0 t1 U.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ mfd_orientable top atlas /\
        ricci_flow_from (top,atlas) a b g /\
        &0 <= a /\ a <= t0 /\ t0 <= t1 /\ t1 < b /\
        U IN connected_components_of top /\ p4_cm_adm (top,atlas) U /\
        (!t x. t0 <= t /\ t <= t1 /\ x IN U
               ==> --(&6) / (&4 * t + &1) <= mfd_scalar atlas (g t) x)
        ==> p4_q (&4 * pi) (p4_cm_width (top,atlas) (g t1) U) t1
            <= p4_q (&4 * pi) (p4_cm_width (top,atlas) (g t0) U) t0`;;

(* Topology: a degree-one map (a homeomorphism from a nonempty open U onto *)
(* an open set, injective over it) between closed connected orientable      *)
(* 3-manifolds maps essential maps of S^3 to essential maps.  Needs the     *)
(* fundamental class (H_3 = Z, H_3(X) -> H_3(X, X - x) iso) on top of       *)
(* Multivariate/homology.ml (excision, exactness).                           *)

let P4_DEGREE_ONE_STATEMENT = new_definition
 `P4_DEGREE_ONE_STATEMENT (u:A->bool) (v:B->bool) <=>
    !topX atlasX X topY atlasY Y p f.
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        compact_space topX /\ mfd_orientable topX atlasX /\
        hausdorff_space topY /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^3))->bool) /\
        compact_space topY /\ mfd_orientable topY atlasY /\
        X IN connected_components_of topX /\ Y IN connected_components_of topY /\
        continuous_map (subtopology topX X,subtopology topY Y) p /\
        (?U. open_in topX U /\ ~(U = {}) /\ U SUBSET X /\
             open_in topY (IMAGE p U) /\
             homeomorphic_map (subtopology topX U,subtopology topY (IMAGE p U)) p /\
             !x. x IN X /\ p x IN IMAGE p U ==> x IN U) /\
        p4_essential (subtopology topX X) f
        ==> p4_essential (subtopology topY Y) (p o f)`;;

(* Topology: a closed simply connected 3-manifold admits an essential map  *)
(* of S^3 (a degree-one map; Poincare duality H_2 = 0, Hurewicz in degrees  *)
(* 2 and 3; MT Claim 18.19 with T1 = 0).                                     *)

let P4_SC_DEGREE_ONE_STATEMENT = new_definition
 `P4_SC_DEGREE_ONE_STATEMENT (u:A->bool) <=>
    !top atlas.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ ~(topspace top = {}) /\ simply_connected_space top
        ==> ?f. p4_essential top f`;;

(* Smoothing: an essential map of S^3 into a component U of a closed        *)
(* manifold is homotopic to the suspension of a C^1 sweepout of U, hence U  *)
(* is admissible (approximation of continuous maps by smooth ones on        *)
(* manifolds; the slices of a C^1 map of S^3 after a collar reparametrization *)
(* near the poles).                                                          *)

let P4_SMOOTHING_STATEMENT = new_definition
 `P4_SMOOTHING_STATEMENT (u:A->bool) <=>
    !top atlas U f.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ U IN connected_components_of top /\
        p4_essential (subtopology top U) f
        ==> p4_cm_adm (top,atlas) U`;;

(* Areas under pinch maps: composing a sweepout of X with a pinch map with *)
(* constant L gives a sweepout of Y whose slice areas are at most L^2 times *)
(* the old ones (Loewner order of Gram matrices restricted to the image     *)
(* plane), with suspension p o (suspension).                                 *)

let P4_PINCH_AREA_STATEMENT = new_definition
 `P4_PINCH_AREA_STATEMENT (u:A->bool) (v:B->bool) <=>
    !topX atlasX gX X topY atlasY gY Y L p sigma.
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        compact_space topX /\ riemannian_metric atlasX gX /\
        hausdorff_space topY /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^3))->bool) /\
        compact_space topY /\ riemannian_metric atlasY gY /\
        X IN connected_components_of topX /\ Y IN connected_components_of topY /\
        &1 <= L /\ p4_pinch_map (topX,atlasX) gX X (topY,atlasY) gY Y L p /\
        p4_sweepout (topX,atlasX) sigma /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> sigma y t IN X)
        ==> p4_sweepout (topY,atlasY) (\y t. p(sigma y t)) /\
            (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                   ==> p(sigma y t) IN Y) /\
            p4_sweep_area atlasY gY (\y t. p(sigma y t))
            <= L pow 2 * p4_sweep_area atlasX gX sigma`;;

(* Areas are nonnegative and slice areas of a sweepout are bounded (so the *)
(* sup and the inf in p4_cm_width are meaningful).                           *)

let P4_CM_NONNEG_STATEMENT = new_definition
 `P4_CM_NONNEG_STATEMENT (u:A->bool) <=>
    !top atlas g sigma.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ riemannian_metric atlas g /\
        p4_sweepout (top,atlas) sigma
        ==> (!t. t IN real_interval[&0,&1]
                 ==> &0 <= p4_s2_area atlas g (\y. sigma y t)) /\
            (?B. !t. t IN real_interval[&0,&1]
                     ==> p4_s2_area atlas g (\y. sigma y t) <= B)`;;

(* Isometry invariance (initial manifold on A, stage 0 on B).               *)

let P4_CM_ISOMETRY_STATEMENT = new_definition
 `P4_CM_ISOMETRY_STATEMENT (u:A->bool) (v:B->bool) <=>
    !top atlas g top' atlas' g' iota iota'.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ riemannian_metric atlas g /\
        hausdorff_space top' /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
        compact_space top' /\
        mfd_isometry (top,atlas) g (top',atlas') g' iota iota' /\
        p4_cm_adm (top,atlas) (topspace top)
        ==> p4_cm_adm (top',atlas') (topspace top') /\
            p4_cm_width (top',atlas') g' (topspace top') <=
            p4_cm_width (top,atlas) g (topspace top)`;;

(* ------------------------------------------------------------------------- *)
(* CM1. The next level: CM Thm 1.7 in forward-difference form at one time,  *)
(* continuity of the width along a smooth flow (MT Claim 18.21 analogue),   *)
(* CM Thm 1.14 + Prop 1.5 + (1.19) for one metric (good sweepouts; slices   *)
(* of large area are close, in area and in the Ricci tangential trace, to   *)
(* nonempty finite collections of harmonic spheres; includes W > 0), CM     *)
(* Lemma 1.22 (Gauss equation + Gauss-Bonnet with branch points) and the    *)
(* area variation (1.20) with a uniform second-order Taylor bound.          *)
(* ------------------------------------------------------------------------- *)

(* CM_DINI_STATEMENT and P4_AREA_TAYLOR_STATEMENT are stated for times       *)
(* strictly after the initial time a of the flow (the flow equation of       *)
(* ricci_flow_on holds on the open interval only); the slab inequality at    *)
(* t0 = a follows from the continuity of the width at a                      *)
(* (P4_WIDTH_CONTINUITY_STATEMENT, closed at a) in P4_CM_SLAB_FROM_DINI      *)
(* (unit pc_p4_cm).                                                          *)

let CM_DINI_STATEMENT = new_definition
 `CM_DINI_STATEMENT (u:A->bool) <=>
    !top atlas g a b tau U.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ mfd_orientable top atlas /\
        ricci_flow_from (top,atlas) a b g /\ &0 <= a /\ a < tau /\ tau < b /\
        U IN connected_components_of top /\ p4_cm_adm (top,atlas) U /\
        (!x. x IN U ==> --(&6) / (&4 * tau + &1) <= mfd_scalar atlas (g tau) x)
        ==> !e. &0 < e
                ==> ?d. &0 < d /\
                        !h. &0 < h /\ h < d /\ tau + h < b
                            ==> p4_cm_width (top,atlas) (g(tau + h)) U
                                <= p4_cm_width (top,atlas) (g tau) U +
                                   h * (--(&4 * pi) +
                                        &3 / (&4 * tau + &1) *
                                        p4_cm_width (top,atlas) (g tau) U + e)`;;

let P4_WIDTH_CONTINUITY_STATEMENT = new_definition
 `P4_WIDTH_CONTINUITY_STATEMENT (u:A->bool) <=>
    !top atlas g a b t1 U.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\
        ricci_flow_from (top,atlas) a b g /\ a <= t1 /\ t1 < b /\
        U IN connected_components_of top /\ p4_cm_adm (top,atlas) U
        ==> (\t. p4_cm_width (top,atlas) (g t) U) real_continuous_on
            real_interval[a,t1]`;;

let CM_GOOD_SWEEPOUT_STATEMENT = new_definition
 `CM_GOOD_SWEEPOUT_STATEMENT (u:A->bool) <=>
    !top atlas g U.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ mfd_orientable top atlas /\
        riemannian_metric atlas g /\
        U IN connected_components_of top /\ p4_cm_adm (top,atlas) U
        ==> &0 < p4_cm_width (top,atlas) g U /\
            !e. &0 < e
                ==> ?d. &0 < d /\
                        !e'. &0 < e'
                             ==> ?sigma. p4_sweepout_in (top,atlas) U sigma /\
                                         p4_sweep_area atlas g sigma
                                         < p4_cm_width (top,atlas) g U + e' /\
                                         !t. t IN real_interval[&0,&1] /\
                                             p4_cm_width (top,atlas) g U - d
                                             < p4_s2_area atlas g (\y. sigma y t)
                                             ==> ?n v. 1 <= n /\
                                                   (!i. 1 <= i /\ i <= n
                                                        ==> p4_harmonic_sphere (top,atlas) g U (v i)) /\
                                                   abs(p4_s2_area atlas g (\y. sigma y t) -
                                                       sum(1..n) (\i. p4_s2_area atlas g (v i))) < e /\
                                                   abs(p4_s2_trint atlas g (mfd_ricci_matrix atlas g)
                                                         (\y. sigma y t) -
                                                       sum(1..n) (\i. p4_s2_trint atlas g
                                                                   (mfd_ricci_matrix atlas g) (v i)))
                                                   < e`;;

let CM_HARMONIC_SPHERE_STATEMENT = new_definition
 `CM_HARMONIC_SPHERE_STATEMENT (u:A->bool) <=>
    !top atlas g U v r0.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ riemannian_metric atlas g /\
        U IN connected_components_of top /\
        p4_harmonic_sphere (top,atlas) g U v /\
        (!x. x IN U ==> r0 <= mfd_scalar atlas g x)
        ==> &4 * pi + r0 / &2 * p4_s2_area atlas g v
            <= p4_s2_trint atlas g (mfd_ricci_matrix atlas g) v`;;

let P4_AREA_TAYLOR_STATEMENT = new_definition
 `P4_AREA_TAYLOR_STATEMENT (u:A->bool) <=>
    !top atlas g a b t0 t1.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\
        ricci_flow_from (top,atlas) a b g /\ a < t0 /\ t0 <= t1 /\ t1 < b
        ==> ?C. &0 <= C /\
                !sigma s t h.
                   p4_sweepout (top,atlas) sigma /\ s IN real_interval[&0,&1] /\
                   t0 <= t /\ &0 <= h /\ t + h <= t1
                   ==> abs(p4_s2_trint atlas (g t) (mfd_ricci_matrix atlas (g t))
                                       (\y. sigma y s))
                       <= C * p4_s2_area atlas (g t) (\y. sigma y s) /\
                       p4_s2_area atlas (g(t + h)) (\y. sigma y s)
                       <= p4_s2_area atlas (g t) (\y. sigma y s) -
                          h * p4_s2_trint atlas (g t) (mfd_ricci_matrix atlas (g t))
                                          (\y. sigma y s) +
                          C * h pow 2 * p4_s2_area atlas (g t) (\y. sigma y s)`;;

(* ------------------------------------------------------------------------- *)
(* Basic facts used by every later Part 4 unit.                              *)
(* ------------------------------------------------------------------------- *)

let P4_Q_ZERO = prove
 (`!c w. p4_q c w (&0) = w + c`,
  REWRITE_TAC[p4_q; REAL_MUL_RZERO; REAL_ADD_LID; RPOW_ONE; REAL_DIV_1;
              REAL_MUL_RID]);;

let P4_SUSP_COMPOSE = prove
 (`!(p:A->B) (sigma:real^3->real->A).
        p4_susp (\y t. p(sigma y t)) = p o p4_susp sigma`,
  REWRITE_TAC[p4_susp; FUN_EQ_THM; o_THM] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let P4_E2_POL_SYM = prove
 (`!a b. p4_e2_pol a b = p4_e2_pol b a`,
  REWRITE_TAC[p4_e2_pol; TRACE_MUL_SYM] THEN REAL_ARITH_TAC);;

let P4_E2_ADD = prove
 (`!a b. p4_e2(a + b) = p4_e2 a + p4_e2_pol a b + p4_e2 b`,
  REWRITE_TAC[p4_e2; p4_e2_pol; TRACE_ADD; MATRIX_ADD_LDISTRIB;
              MATRIX_ADD_RDISTRIB; TRACE_MUL_SYM] THEN
  REAL_ARITH_TAC);;

let P4_E2_CMUL = prove
 (`!k a. p4_e2(k %% a) = k pow 2 * p4_e2 a`,
  REWRITE_TAC[p4_e2; TRACE_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
              MATRIX_CMUL_ASSOC] THEN REAL_ARITH_TAC);;

