type_invention_error := true;;

(* ========================================================================= *)
(* BLIND independent formalization of the statement of the Poincare          *)
(* conjecture, in a topological and in a smooth form.  Definitions only,     *)
(* nothing is proved.  All auxiliary constants are prefixed blind_.          *)
(*                                                                           *)
(* Sources (the only ones used):                                             *)
(*  [MT] J. Morgan, G. Tian, Ricci Flow and the Poincare Conjecture,         *)
(*       Introduction, pages ix-x:                                           *)
(*       'The Poincare Conjecture: every closed, smooth, simply connected    *)
(*       3-manifold is diffeomorphic to S^3.'  Footnote 1: 'Every            *)
(*       topological 3-manifold admits a differentiable structure and every  *)
(*       homeomorphism between smooth 3-manifolds can be approximated by a   *)
(*       diffeomorphism.  Thus, classification results about topological    *)
(*       3-manifolds up to homeomorphism and about smooth 3-manifolds up to  *)
(*       diffeomorphism are equivalent.  In this book manifold means smooth  *)
(*       manifold.'  Corollary 0.2(a): 'A closed, simply connected           *)
(*       3-manifold is diffeomorphic to S^3.'                                *)
(*  [M]  J. Milnor, The Poincare Conjecture, the official problem            *)
(*       description of the Clay Mathematics Institute:                      *)
(*       'the hypothesis that every simply connected closed 3-manifold is    *)
(*       homeomorphic to the 3-sphere has been known as the Poincare         *)
(*       Conjecture'; the Question: 'If a compact three-dimensional manifold *)
(*       M^3 has the property that every simple closed curve within the      *)
(*       manifold can be deformed continuously to a point, does it follow    *)
(*       that M^3 is homeomorphic to the sphere S^3?'; and the 3-sphere is   *)
(*       'the locus of all points (x, y, z, w) in four-dimensional Euclidean *)
(*       space which have distance exactly 1 from the origin'.               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Choice of carrier.  The sources speak of abstract manifolds, so a         *)
(* manifold here is a topological space top:A topology on an arbitrary type  *)
(* A (its points form topspace top, a subset of A), not a subset of some     *)
(* real^N; this keeps embedding theorems out of the statement.  HOL Light    *)
(* cannot quantify over types inside a formula, so each headline constant    *)
(* takes a dummy argument u:A->bool that only fixes the type A and is        *)
(* otherwise ignored; the intended reading is BLIND_POINCARE_TOP (:A).  A    *)
(* theorem with A a type variable then holds for every carrier type.  Every  *)
(* nonempty closed 3-manifold has the cardinality of the reals, so the       *)
(* instance at any type of at least that cardinality already covers all      *)
(* closed 3-manifolds up to homeomorphism.                                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Topological 3-manifolds.  Standard reading of manifold: Hausdorff, second *)
(* countable and locally Euclidean of dimension 3, i.e. every point has an   *)
(* open neighbourhood homeomorphic to an open subset of real^3.  Charts go   *)
(* to open subsets of real^3, never to a half-space, so these manifolds have *)
(* no boundary.  This is forced by the texts: the closed 3-ball is compact   *)
(* and simply connected but not homeomorphic to S^3, so the compact manifold *)
(* in the Question of [M] must be one without boundary.                      *)
(* ------------------------------------------------------------------------- *)

let blind_locally_euclidean_3 = new_definition
 `blind_locally_euclidean_3 (top:A topology) <=>
    !x. x IN topspace top
        ==> ?u (v:real^3->bool).
              open_in top u /\ x IN u /\ open v /\
              (subtopology top u) homeomorphic_space (subtopology euclidean v)`;;

let blind_topological_3_manifold = new_definition
 `blind_topological_3_manifold (top:A topology) <=>
    hausdorff_space top /\ second_countable top /\
    blind_locally_euclidean_3 top`;;

(* ------------------------------------------------------------------------- *)
(* Closed: standard reading, compact and without boundary (no boundary is    *)
(* built into the charts above).  For compact Hausdorff locally Euclidean    *)
(* spaces second countability is automatic (finitely many charts), so        *)
(* including it in the definition of manifold changes nothing here.          *)
(* ------------------------------------------------------------------------- *)

let blind_closed_topological_3_manifold = new_definition
 `blind_closed_topological_3_manifold (top:A topology) <=>
    blind_topological_3_manifold top /\ compact_space top`;;

(* ------------------------------------------------------------------------- *)
(* Simply connected: standard reading, nonempty and path-connected with      *)
(* trivial fundamental group, i.e. every loop p is homotopic, with both      *)
(* endpoints kept at the base point p(0) throughout, to the constant loop.   *)
(* Paths are the library notion path_in (maps from the real interval from 0  *)
(* to 1), homotopies the library notion homotopic_with.  Nonemptiness must   *)
(* be explicit: the library predicate path_connected_space holds for the     *)
(* empty space, which is also a compact manifold, so without it the          *)
(* statement would be false.  Path-connectedness is part of simply           *)
(* connected; it supplies the connectedness that Theorem 0.1 of [MT] states  *)
(* separately, and without it two disjoint 3-spheres would satisfy the       *)
(* hypothesis of the Question of [M].  That Question speaks of simple closed *)
(* curves deformed to a point; in a 3-manifold every loop is homotopic to a  *)
(* simple one, and a loop that can be deformed to a point freely can also be *)
(* contracted with its base point fixed, so the pi_1 = 0 reading used here   *)
(* is equivalent.                                                            *)
(* ------------------------------------------------------------------------- *)

let blind_simply_connected_space = new_definition
 `blind_simply_connected_space (top:A topology) <=>
    ~(topspace top = {}) /\
    path_connected_space top /\
    !p:real->A.
        path_in top p /\ p(&1) = p(&0)
        ==> homotopic_with (\q. q(&0) = p(&0) /\ q(&1) = p(&0))
              (subtopology euclideanreal (real_interval[&0,&1]),top)
              p (\t:real. p(&0))`;;

(* ------------------------------------------------------------------------- *)
(* Smoothness class: smooth means C-infinity (standard reading; footnote 1   *)
(* of [MT] says differentiable structure without naming a class).            *)
(* blind_ck k s f: f is k times continuously differentiable on the set s,    *)
(* which is open wherever it is used below.  Class 0 means continuous on s;  *)
(* class k+1 means Frechet differentiable at every point of s with every     *)
(* first partial derivative x -> Df(x)(e_i) of class k.  As s is open, the   *)
(* values of the Hilbert-choice frechet_derivative outside s never matter.   *)
(* ------------------------------------------------------------------------- *)

let blind_ck = define
 `(blind_ck 0 (s:real^M->bool) (f:real^M->real^N) <=> f continuous_on s) /\
  (blind_ck (SUC k) s f <=>
     (!x. x IN s ==> f differentiable (at x)) /\
     (!i. 1 <= i /\ i <= dimindex(:M)
          ==> blind_ck k s (\x. frechet_derivative f (at x) (basis i))))`;;

let blind_smooth_on = new_definition
 `blind_smooth_on (s:real^M->bool) (f:real^M->real^N) <=> !k. blind_ck k s f`;;

(* ------------------------------------------------------------------------- *)
(* Smooth structures, represented by smooth atlases.  A chart is a pair      *)
(* (u,c): u is open in top and c maps u homeomorphically onto an open subset *)
(* of real^3.  Two charts are smoothly compatible when the transition map    *)
(* from c(u INTER v) to d(u INTER v) is C-infinity; this is expressed        *)
(* without inverse functions as a smooth g with g(c x) = d x on u INTER v (c *)
(* is injective on u, so g is the transition map on the open set             *)
(* c(u INTER v)).  A smooth 3-manifold is a Hausdorff, second countable      *)
(* space with a smooth atlas: charts covering it, pairwise compatible in     *)
(* both orders.  The atlas need not be maximal: an atlas determines a unique *)
(* maximal one and smoothness of maps (below) is the same for both, so       *)
(* quantifying over all atlases is the same as quantifying over smooth       *)
(* structures.                                                               *)
(* ------------------------------------------------------------------------- *)

let blind_chart_3 = new_definition
 `blind_chart_3 (top:A topology) (u,(c:A->real^3)) <=>
    open_in top u /\ open (IMAGE c u) /\
    homeomorphic_map (subtopology top u,subtopology euclidean (IMAGE c u)) c`;;

let blind_smoothly_compatible_3 = new_definition
 `blind_smoothly_compatible_3 ((u:A->bool),(c:A->real^3)) (v,d) <=>
    ?g:real^3->real^3.
        blind_smooth_on (IMAGE c (u INTER v)) g /\
        !x. x IN u INTER v ==> g(c x) = d x`;;

let blind_smooth_atlas_3 = new_definition
 `blind_smooth_atlas_3 (top:A topology) (atlas:(A->bool)#(A->real^3)->bool) <=>
    (!ch. ch IN atlas ==> blind_chart_3 top ch) /\
    (!x. x IN topspace top ==> ?u c. (u,c) IN atlas /\ x IN u) /\
    (!ch ch'. ch IN atlas /\ ch' IN atlas
              ==> blind_smoothly_compatible_3 ch ch')`;;

let blind_smooth_3_manifold = new_definition
 `blind_smooth_3_manifold (top:A topology)
                          (atlas:(A->bool)#(A->real^3)->bool) <=>
    hausdorff_space top /\ second_countable top /\
    blind_smooth_atlas_3 top atlas`;;

let blind_closed_smooth_3_manifold = new_definition
 `blind_closed_smooth_3_manifold (top:A topology)
                                 (atlas:(A->bool)#(A->real^3)->bool) <=>
    blind_smooth_3_manifold top atlas /\ compact_space top`;;

(* ------------------------------------------------------------------------- *)
(* Smooth maps and diffeomorphisms between smooth 3-manifolds, standard:     *)
(* a smooth map is continuous and C-infinity in every pair of charts, i.e.   *)
(* d o f o c^-1 is smooth on the open set c(u INTER f^-1(v)); a              *)
(* diffeomorphism is a homeomorphism that is smooth with smooth inverse.     *)
(* ------------------------------------------------------------------------- *)

let blind_smooth_map_3 = new_definition
 `blind_smooth_map_3 (top:A topology,atlas:(A->bool)#(A->real^3)->bool)
                     (top':B topology,atlas':(B->bool)#(B->real^3)->bool)
                     (f:A->B) <=>
    continuous_map (top,top') f /\
    !u c v d. (u,c) IN atlas /\ (v,d) IN atlas'
              ==> ?g:real^3->real^3.
                    blind_smooth_on (IMAGE c {x | x IN u /\ f x IN v}) g /\
                    !x. x IN u /\ f x IN v ==> g(c x) = d(f x)`;;

let blind_diffeomorphic_3 = new_definition
 `blind_diffeomorphic_3 (top:A topology,atlas:(A->bool)#(A->real^3)->bool)
                        (top':B topology,atlas':(B->bool)#(B->real^3)->bool) <=>
    ?f g. homeomorphic_maps (top,top') (f,g) /\
          blind_smooth_map_3 (top,atlas) (top',atlas') f /\
          blind_smooth_map_3 (top',atlas') (top,atlas) g`;;

(* ------------------------------------------------------------------------- *)
(* The 3-sphere S^3, following [M]: the unit sphere of real^4, with the      *)
(* subspace topology of the Euclidean topology.  For the smooth form it      *)
(* carries its standard smooth structure, given by the atlas of the two      *)
(* stereographic projections, from the north pole basis 4 = (0,0,0,1) and    *)
(* from the south pole (0,0,0,-1); each maps the sphere minus its pole       *)
(* homeomorphically onto real^3, and the transition map is y -> y / norm(y)  *)
(* squared on real^3 minus the origin.  This atlas generates the smooth      *)
(* structure of S^3 as a smooth submanifold of real^4.  The poles are        *)
(* excluded from the chart domains, so the convention x / 0 = 0 never        *)
(* enters.                                                                   *)
(* ------------------------------------------------------------------------- *)

let blind_sphere3 = new_definition
 `blind_sphere3 = sphere(vec 0:real^4,&1)`;;

let blind_sphere3_topology = new_definition
 `blind_sphere3_topology = subtopology euclidean blind_sphere3`;;

let blind_stereo_north = new_definition
 `blind_stereo_north (x:real^4) = (lambda i. x$i / (&1 - x$4)):real^3`;;

let blind_stereo_south = new_definition
 `blind_stereo_south (x:real^4) = (lambda i. x$i / (&1 + x$4)):real^3`;;

let blind_sphere3_atlas = new_definition
 `blind_sphere3_atlas =
    {(blind_sphere3 DELETE (basis 4),blind_stereo_north),
     (blind_sphere3 DELETE (--(basis 4)),blind_stereo_south)}`;;

(* ------------------------------------------------------------------------- *)
(* Headline statements.  The argument u only fixes the carrier type A.       *)
(* BLIND_POINCARE_TOP, the form stated in [M] (and the topological reading   *)
(* of Corollary 0.2(a) of [MT] given by its footnote 1): every closed,       *)
(* simply connected topological 3-manifold is homeomorphic to S^3.           *)
(* BLIND_POINCARE_SMOOTH, the form stated in [MT], page ix and Corollary     *)
(* 0.2(a): every closed, smooth, simply connected 3-manifold is              *)
(* diffeomorphic to S^3 with its standard smooth structure.  Simple          *)
(* connectivity is a property of the underlying topological space.          *)
(* ------------------------------------------------------------------------- *)

let BLIND_POINCARE_TOP = new_definition
 `BLIND_POINCARE_TOP (u:A->bool) <=>
    !top:A topology.
        blind_closed_topological_3_manifold top /\
        blind_simply_connected_space top
        ==> top homeomorphic_space blind_sphere3_topology`;;

let BLIND_POINCARE_SMOOTH = new_definition
 `BLIND_POINCARE_SMOOTH (u:A->bool) <=>
    !(top:A topology) (atlas:(A->bool)#(A->real^3)->bool).
        blind_closed_smooth_3_manifold top atlas /\
        blind_simply_connected_space top
        ==> blind_diffeomorphic_3 (top,atlas)
              (blind_sphere3_topology,blind_sphere3_atlas)`;;
