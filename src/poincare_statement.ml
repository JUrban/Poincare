(* ========================================================================= *)
(* The Poincare conjecture: headline statements.                             *)
(*                                                                           *)
(* POINCARE_STATEMENT (:A) is the classical topological form: every closed   *)
(* (compact, Hausdorff, locally Euclidean of dimension 3), nonempty, simply  *)
(* connected topological space with carrier type A is homeomorphic to the    *)
(* unit sphere of real^4.                                                    *)
(*                                                                           *)
(* POINCARE_SMOOTH_STATEMENT (:A) is the smooth form: every closed, nonempty,*)
(* simply connected smooth 3-manifold is diffeomorphic to the standard       *)
(* 3-sphere, expressed as the existence of a smooth immersion into real^4    *)
(* that is a homeomorphism onto the unit sphere (by the inverse function     *)
(* theorem this is a diffeomorphism onto the sphere with its standard smooth *)
(* structure as a submanifold of real^4).                                    *)
(*                                                                           *)
(* POINCARE_EMBEDDED_STATEMENT (:N) is the topological form for subsets of   *)
(* real^N, using only notions of the HOL Light library; it follows from      *)
(* POINCARE_STATEMENT (:real^N).                                             *)
(*                                                                           *)
(* The argument of each statement constant only fixes a type: the theorems  *)
(* are |- POINCARE_STATEMENT (:A) etc. for a type variable, hence hold for   *)
(* every type.                                                               *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Smooth (C^infinity) maps on subsets of Euclidean space. The same text as  *)
(* src/ns_smooth.ml (from the Navier_Stokes development,                     *)
(* github.com/hol-light-family/Navier_Stokes), so that both can be loaded.   *)
(* ------------------------------------------------------------------------- *)

let continuously_differentiable = define
 `(continuously_differentiable 0 s (f:real^M->real^N) <=>
   f continuous_on s) /\
  (!n. continuously_differentiable (SUC n) s f <=>
       ?f'. (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
            !h. continuously_differentiable n s (\x. f' x h))`;;

let smooth_map_on = new_definition
 `smooth_map_on M (f:real^M->real^N) <=>
    !n. continuously_differentiable n M f`;;

(* ------------------------------------------------------------------------- *)
(* Simply connected topological spaces: any two loops are homotopic as       *)
(* loops.  This mirrors the library's simply_connected for sets in real^N    *)
(* (paths.ml), to which it is equivalent for subspaces of real^N.  As there, *)
(* it implies path connectedness, and the empty space is simply connected.   *)
(* ------------------------------------------------------------------------- *)

let simply_connected_space = new_definition
 `simply_connected_space (top:A topology) <=>
    !p q. path_in top p /\ p(&1) = p(&0) /\
          path_in top q /\ q(&1) = q(&0)
          ==> homotopic_with (\r. r(&1) = r(&0))
                (subtopology euclideanreal (real_interval[&0,&1]),top) p q`;;

(* ------------------------------------------------------------------------- *)
(* Locally Euclidean spaces of dimension dimindex(:N): every point has an    *)
(* open neighbourhood homeomorphic to real^N.  The argument only fixes the   *)
(* type N, as in dimindex(:N).                                               *)
(* ------------------------------------------------------------------------- *)

let locally_euclidean_space = new_definition
 `locally_euclidean_space (s:N->bool) (top:A topology) <=>
    !x. x IN topspace top
        ==> ?U. open_in top U /\ x IN U /\
                subtopology top U homeomorphic_space (euclidean:(real^N)topology)`;;

(* ------------------------------------------------------------------------- *)
(* Smooth atlases.  A chart is a pair (U,phi): an open set U of the space    *)
(* and a homeomorphism phi of U onto an open subset of real^N.  An atlas     *)
(* covers the space and its transition maps are smooth: on phi(U INTER V)    *)
(* the map psi o inverse(phi) agrees with a smooth map.                      *)
(* ------------------------------------------------------------------------- *)

let smooth_manifold_atlas = new_definition
 `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) <=>
    (!U phi. (U,phi) IN atlas
             ==> open_in top U /\ open (IMAGE phi U) /\
                 homeomorphic_map (subtopology top U,
                                   subtopology euclidean (IMAGE phi U)) phi) /\
    (!x. x IN topspace top ==> ?U phi. (U,phi) IN atlas /\ x IN U) /\
    (!U phi V psi.
         (U,phi) IN atlas /\ (V,psi) IN atlas
         ==> ?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
                 !x. x IN U INTER V ==> g(phi x) = psi x)`;;

(* ------------------------------------------------------------------------- *)
(* A map f from a manifold with the given atlas into real^M is a smooth      *)
(* immersion: in every chart it agrees with a smooth map with injective      *)
(* derivative.                                                               *)
(* ------------------------------------------------------------------------- *)

let smooth_immersion_into = new_definition
 `smooth_immersion_into (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^M) <=>
    !U phi. (U,phi) IN atlas
            ==> ?g. smooth_map_on (IMAGE phi U) g /\
                    (!x. x IN U ==> g(phi x) = f x) /\
                    (!y h. y IN IMAGE phi U /\ frechet_derivative g (at y) h = vec 0
                           ==> h = vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* The headline statements.                                                  *)
(* ------------------------------------------------------------------------- *)

let POINCARE_STATEMENT = new_definition
 `POINCARE_STATEMENT (u:A->bool) <=>
    !top:A topology.
        hausdorff_space top /\ locally_euclidean_space (:3) top /\
        compact_space top /\ ~(topspace top = {}) /\
        simply_connected_space top
        ==> top homeomorphic_space
            subtopology euclidean (sphere(vec 0:real^4,&1))`;;

let POINCARE_SMOOTH_STATEMENT = new_definition
 `POINCARE_SMOOTH_STATEMENT (u:A->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        compact_space top /\ ~(topspace top = {}) /\
        simply_connected_space top
        ==> ?f:A->real^4.
              smooth_immersion_into atlas f /\
              homeomorphic_map (top,subtopology euclidean (sphere(vec 0,&1))) f`;;

let POINCARE_EMBEDDED_STATEMENT = new_definition
 `POINCARE_EMBEDDED_STATEMENT (u:N->bool) <=>
    !M:real^N->bool.
        compact M /\ ~(M = {}) /\ simply_connected M /\
        (!x. x IN M
             ==> ?U. open_in (subtopology euclidean M) U /\ x IN U /\
                     U homeomorphic (:real^3))
        ==> M homeomorphic sphere(vec 0:real^4,&1)`;;
