(* ========================================================================= *)
(* pc_moi_stmt: the statement layer of the Moise track (topological          *)
(* 3-manifolds are smoothable).  PL notions (maps, polyhedra, balls,         *)
(* spheres, locally finite complexes, combinatorial manifolds, PL atlases)   *)
(* and the statement constants of the chain down to the Euclidean core.      *)
(* Route: Moise, Geometric Topology in Dimensions 2 and 3 (GTM 47), with the *)
(* Lean development of Qin et al. (Moise352Producer.lean) as blueprint.      *)
(* ========================================================================= *)

needs "src/pc_interfaces.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. PL notions in real^N.                                                  *)
(* ------------------------------------------------------------------------- *)

(* f is piecewise affine (PL) on s: near each point x of s, finitely many    *)
(* polytopes inside s cover a neighbourhood of x in s, and f agrees with an  *)
(* affine map on each of them.  As in DG's IsPiecewiseAffineOn; the         *)
(* identity is PL on s exactly when s is locally polyhedral.                 *)

let pl_map_on = new_definition
 `pl_map_on (s:real^M->bool) (f:real^M->real^N) <=>
    !x. x IN s
        ==> ?c u. FINITE c /\ open u /\ x IN u /\ s INTER u SUBSET UNIONS c /\
                  !k. k IN c
                      ==> polytope k /\ k SUBSET s /\
                          ?l:real^M->real^N y. linear l /\
                                               !z. z IN k ==> f z = l z + y`;;

(* A PL homeomorphism between subsets of Euclidean spaces.                    *)

let pl_homeomorphism = new_definition
 `pl_homeomorphism (s:real^M->bool,t:real^N->bool) (f,g) <=>
    homeomorphism (s,t) (f,g) /\ pl_map_on s f /\ pl_map_on t g`;;

(* Compact polyhedra in the PL sense (HOL's polyhedron is a convex set).      *)

let pl_polyhedron = new_definition
 `pl_polyhedron (s:real^N->bool) <=>
    ?c. FINITE c /\ (!k. k IN c ==> polytope k) /\ s = UNIONS c`;;

(* PL n-balls and PL n-spheres: PL homeomorphic to an n-simplex, or to the    *)
(* boundary of an (n+1)-simplex, in the same space.                          *)

let pl_ball = new_definition
 `pl_ball n (s:real^N->bool) <=>
    ?k:real^N->bool f g. &n simplex k /\ pl_homeomorphism (k,s) (f,g)`;;

let pl_sphere = new_definition
 `pl_sphere n (s:real^N->bool) <=>
    ?k:real^N->bool f g.
        &(n + 1) simplex k /\ pl_homeomorphism (relative_frontier k,s) (f,g)`;;

(* Locally finite simplicial complexes (possibly infinite): the conditions  *)
(* of HOL's simplicial_complex without FINITE, plus local finiteness at the *)
(* points of the polyhedron UNIONS c (which need not be closed in real^N,   *)
(* e.g. a triangulation of an open set).                                     *)

let lf_simplicial_complex = new_definition
 `lf_simplicial_complex (c:(real^N->bool)->bool) <=>
    (!s. s IN c ==> ?n. n simplex s) /\
    (!f s. s IN c /\ f face_of s ==> f IN c) /\
    (!s s'. s IN c /\ s' IN c
            ==> (s INTER s') face_of s /\ (s INTER s') face_of s') /\
    (!x. x IN UNIONS c
         ==> ?u. open u /\ x IN u /\
                 FINITE {s | s IN c /\ ~(s INTER u = {})})`;;

(* The link of a vertex v in a simplicial complex c.                         *)

let simplicial_link = new_definition
 `simplicial_link (c:(real^N->bool)->bool) (v:real^N) =
    {s | s IN c /\ ~(v IN s) /\ ?t. t IN c /\ v IN t /\ s face_of t}`;;

(* Combinatorial n-manifolds (without boundary): vertex links are PL         *)
(* (n-1)-spheres.  With boundary: PL (n-1)-spheres or PL (n-1)-balls.        *)
(* Locally finite; add FINITE c for compact ones.                            *)

let combinatorial_manifold = new_definition
 `combinatorial_manifold n (c:(real^N->bool)->bool) <=>
    lf_simplicial_complex c /\
    !v. {v} IN c ==> pl_sphere (n - 1) (UNIONS (simplicial_link c v))`;;

let combinatorial_manifold_with_boundary = new_definition
 `combinatorial_manifold_with_boundary n (c:(real^N->bool)->bool) <=>
    lf_simplicial_complex c /\
    !v. {v} IN c ==> pl_sphere (n - 1) (UNIONS (simplicial_link c v)) \/
                     pl_ball (n - 1) (UNIONS (simplicial_link c v))`;;

(* ------------------------------------------------------------------------- *)
(* 2. PL manifolds: atlases with PL transition maps (same shape as           *)
(* smooth_manifold_atlas in poincare_statement.ml).                          *)
(* ------------------------------------------------------------------------- *)

let pl_manifold_atlas = new_definition
 `pl_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) <=>
    (!U phi. (U,phi) IN atlas
             ==> open_in top U /\ open (IMAGE phi U) /\
                 homeomorphic_map (subtopology top U,
                                   subtopology euclidean (IMAGE phi U)) phi) /\
    (!x. x IN topspace top ==> ?U phi. (U,phi) IN atlas /\ x IN U) /\
    (!U phi V psi.
         (U,phi) IN atlas /\ (V,psi) IN atlas
         ==> ?g. pl_map_on (IMAGE phi (U INTER V)) g /\
                 !x. x IN U INTER V ==> g(phi x) = psi x)`;;

(* A map from a PL manifold into real^M is PL: PL in every chart.            *)

let pl_in_charts = new_definition
 `pl_in_charts (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^M) <=>
    !U phi. (U,phi) IN atlas
            ==> ?g. pl_map_on (IMAGE phi U) g /\
                    !x. x IN U ==> g(phi x) = f x`;;

(* ------------------------------------------------------------------------- *)
(* 3. Separation and spherical shells in Euclidean space (for Moise 30.4,    *)
(* 30.5).  b separates s from t: the complement of b is the union of two     *)
(* disjoint open sets containing s and t (DG's Separates).  A spherical      *)
(* shell with ends b0, b1: a homeomorphic image of the closed annulus        *)
(* 1 <= |y| <= 2 in real^3, b0 and b1 the images of its boundary spheres.    *)
(* ------------------------------------------------------------------------- *)

let euclidean_separates = new_definition
 `euclidean_separates (b:real^N->bool) (s:real^N->bool) (t:real^N->bool) <=>
    ?u v. open u /\ open v /\ DISJOINT u v /\
          u UNION v = (:real^N) DIFF b /\ s SUBSET u /\ t SUBSET v`;;

let spherical_shell = new_definition
 `spherical_shell (x:real^3->bool) (b0:real^3->bool) (b1:real^3->bool) <=>
    ?h k. homeomorphism ({y:real^3 | &1 <= norm y /\ norm y <= &2},x) (h,k) /\
          b0 = IMAGE h (sphere(vec 0,&1)) /\ b1 = IMAGE h (sphere(vec 0,&2))`;;

(* ------------------------------------------------------------------------- *)
(* 4. Level 1: the two halves of MOISE_SMOOTHING_STATEMENT.                  *)
(* ------------------------------------------------------------------------- *)

(* The triangulation theorem in atlas form (Moise, Sec 35).                  *)

let MOISE_PL_ATLAS_STATEMENT = new_definition
 `MOISE_PL_ATLAS_STATEMENT (u:A->bool) <=>
    !top:A topology.
        hausdorff_space top /\ compact_space top /\
        locally_euclidean_space (:3) top
        ==> ?atlas:((A->bool)#(A->real^3))->bool. pl_manifold_atlas top atlas`;;

(* Compact PL 3-manifolds are smoothable (no compatibility asked).           *)

let PL_SMOOTHING_STATEMENT = new_definition
 `PL_SMOOTHING_STATEMENT (u:A->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool).
        hausdorff_space top /\ compact_space top /\ pl_manifold_atlas top atlas
        ==> ?atlas':((A->bool)#(A->real^3))->bool.
                smooth_manifold_atlas top atlas'`;;

(* ------------------------------------------------------------------------- *)
(* 5. Level 2, PL side: the approximation theorem and the chart gluing.      *)
(* ------------------------------------------------------------------------- *)

(* Moise's approximation theorem with a PL-manifold source (DG's             *)
(* PLApproximation with target an open set of real^3; Moise Sec 35): an open *)
(* embedding h of a PL 3-manifold into real^3 is approximated, within any    *)
(* positive continuous e, by a PL open embedding with the same image.        *)

let MOISE_APPROX_STATEMENT = new_definition
 `MOISE_APPROX_STATEMENT (u:A->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
     (h:A->real^3) (e:A->real).
        hausdorff_space top /\ second_countable top /\
        pl_manifold_atlas top atlas /\
        embedding_map (top,euclidean) h /\ open (IMAGE h (topspace top)) /\
        continuous_map (top,euclideanreal) e /\
        (!x. x IN topspace top ==> &0 < e x)
        ==> ?f. embedding_map (top,euclidean) f /\
                IMAGE f (topspace top) = IMAGE h (topspace top) /\
                pl_in_charts atlas f /\
                !x. x IN topspace top ==> dist(f x,h x) < e x`;;

(* The same for open subsets of real^3 (Moise's Euclidean form, Sec 35); a  *)
(* corollary of MOISE_352_COMPLEX_STATEMENT (:3) and the image equality.     *)

let MOISE_APPROX_R3_STATEMENT = new_definition
 `MOISE_APPROX_R3_STATEMENT <=>
    !(u:real^3->bool) (h:real^3->real^3) (k:real^3->real^3) (e:real^3->real).
        open u /\ homeomorphism (u,IMAGE h u) (h,k) /\
        (lift o e) continuous_on u /\ (!x. x IN u ==> &0 < e x)
        ==> ?f g. pl_homeomorphism (u,IMAGE h u) (f,g) /\
                  !x. x IN u ==> dist(f x,h x) < e x`;;

(* ------------------------------------------------------------------------- *)
(* 6. Level 2, smooth side: triangulation and smoothing of combinatorial     *)
(* 3-manifolds.  A finite 3-complex has a linear realization in real^7.     *)
(* ------------------------------------------------------------------------- *)

(* The triangulation theorem, simplicial form: a combinatorial              *)
(* triangulation by a finite complex in real^N, N >= 7.                     *)

let MOISE_TRIANGULATION_STATEMENT = new_definition
 `MOISE_TRIANGULATION_STATEMENT (u:A->bool) (v:N->bool) <=>
    7 <= dimindex(:N)
    ==> !top:A topology.
          hausdorff_space top /\ compact_space top /\
          locally_euclidean_space (:3) top
          ==> ?(c:(real^N->bool)->bool) (t:real^N->A).
                FINITE c /\ combinatorial_manifold 3 c /\
                homeomorphic_map (subtopology euclidean (UNIONS c),top) t`;;

(* Compact PL 3-manifolds have finite combinatorial triangulations.         *)

let PL_TRIANGULATION_STATEMENT = new_definition
 `PL_TRIANGULATION_STATEMENT (u:A->bool) (v:N->bool) <=>
    7 <= dimindex(:N)
    ==> !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool).
          hausdorff_space top /\ compact_space top /\
          pl_manifold_atlas top atlas
          ==> ?(c:(real^N->bool)->bool) (t:real^N->A).
                FINITE c /\ combinatorial_manifold 3 c /\
                homeomorphic_map (subtopology euclidean (UNIONS c),top) t /\
                !U phi. (U,phi) IN atlas
                        ==> ?g. pl_map_on {x | x IN UNIONS c /\ t x IN U} g /\
                                !x. x IN UNIONS c /\ t x IN U
                                    ==> g x = phi(t x)`;;

(* The polyhedron of a finite combinatorial 3-manifold is smoothable.        *)

let COMBINATORIAL_SMOOTHING_STATEMENT = new_definition
 `COMBINATORIAL_SMOOTHING_STATEMENT (v:N->bool) <=>
    !c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 3 c
        ==> ?atlas:((real^N->bool)#(real^N->real^3))->bool.
                smooth_manifold_atlas (subtopology euclidean (UNIONS c)) atlas`;;

(* ------------------------------------------------------------------------- *)
(* 7. Level 3, PL side: the rectilinear core and the Euclidean leaves.       *)
(* ------------------------------------------------------------------------- *)

(* Moise 35 in DG's main-chain form (Moise352Open, target real^3): a         *)
(* topological embedding of a PL 3-manifold into real^3 is approximated by   *)
(* a PL embedding within any positive continuous e.  The image equality of   *)
(* MOISE_APPROX_STATEMENT follows by invariance of domain (DG                *)
(* Transition361.lean:284).                                                  *)

let MOISE_352_OPEN_STATEMENT = new_definition
 `MOISE_352_OPEN_STATEMENT (u:A->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
     (h:A->real^3) (e:A->real).
        hausdorff_space top /\ second_countable top /\
        pl_manifold_atlas top atlas /\ embedding_map (top,euclidean) h /\
        continuous_map (top,euclideanreal) e /\
        (!x. x IN topspace top ==> &0 < e x)
        ==> ?f. embedding_map (top,euclidean) f /\ pl_in_charts atlas f /\
                !x. x IN topspace top ==> dist(f x,h x) < e x`;;

(* The core of the PL side, rectilinear form (Moise 35.2 for triangulated    *)
(* 3-manifolds without boundary; DG Moise352Open with the source            *)
(* triangulated): a topological embedding of the polyhedron of a locally    *)
(* finite combinatorial 3-manifold in real^N into real^3 is approximated by *)
(* PL embeddings within any positive continuous e.                           *)

let MOISE_352_COMPLEX_STATEMENT = new_definition
 `MOISE_352_COMPLEX_STATEMENT (v:N->bool) <=>
    !(c:(real^N->bool)->bool) (h:real^N->real^3) (e:real^N->real).
        combinatorial_manifold 3 c /\
        h continuous_on UNIONS c /\
        (!x y. x IN UNIONS c /\ y IN UNIONS c /\ h x = h y ==> x = y) /\
        (lift o e) continuous_on UNIONS c /\ (!x. x IN UNIONS c ==> &0 < e x)
        ==> ?f. pl_map_on (UNIONS c) f /\
                (!x y. x IN UNIONS c /\ y IN UNIONS c /\ f x = f y ==> x = y) /\
                !x. x IN UNIONS c ==> dist(f x,h x) < e x`;;

(* Second countable PL 3-manifolds have locally finite PL triangulations     *)
(* by rectilinear complexes in real^N, N >= 7 (DG LocallyFinitePLPieceIn,   *)
(* ExistsLocallyFinitePLPieceInOfIsOpen; TriangulationExistence).           *)

let PL_TRIANGULATION_LF_STATEMENT = new_definition
 `PL_TRIANGULATION_LF_STATEMENT (u:A->bool) (v:N->bool) <=>
    7 <= dimindex(:N)
    ==> !(top:A topology) (atlas:((A->bool)#(A->real^3))->bool).
          hausdorff_space top /\ second_countable top /\
          pl_manifold_atlas top atlas
          ==> ?(c:(real^N->bool)->bool) (t:real^N->A).
                combinatorial_manifold 3 c /\
                homeomorphic_map (subtopology euclidean (UNIONS c),top) t /\
                !U phi. (U,phi) IN atlas
                        ==> ?g. pl_map_on {x | x IN UNIONS c /\ t x IN U} g /\
                                !x. x IN UNIONS c /\ t x IN U
                                    ==> g x = phi(t x)`;;

(* Moise 34.1 (DG Moise341, MoiseChain.lean:96): an embedding of a PL        *)
(* 3-ball in real^3 is approximated by PL embeddings.                        *)

let MOISE_341_STATEMENT = new_definition
 `MOISE_341_STATEMENT <=>
    !(c:real^3->bool) (h:real^3->real^3) e.
        pl_ball 3 c /\ h continuous_on c /\
        (!x y. x IN c /\ y IN c /\ h x = h y ==> x = y) /\ &0 < e
        ==> ?f g. pl_homeomorphism (c,IMAGE f c) (f,g) /\
                  !x. x IN c ==> dist(f x,h x) < e`;;

(* Alexander's PL Schoenflies theorem in real^3 (Moise Sec 17), and the      *)
(* polygonal Schoenflies theorem in real^2 (Moise Sec 3).                    *)

let PL_SCHOENFLIES_3_STATEMENT = new_definition
 `PL_SCHOENFLIES_3_STATEMENT <=>
    !s:real^3->bool. pl_sphere 2 s ==> pl_ball 3 (s UNION inside s)`;;

let PL_SCHOENFLIES_2_STATEMENT = new_definition
 `PL_SCHOENFLIES_2_STATEMENT <=>
    !s:real^2->bool. pl_sphere 1 s ==> pl_ball 2 (s UNION inside s)`;;

(* The loop theorem (Moise 25.2, DG Moise252) for compact polyhedral         *)
(* 3-manifolds with boundary in real^3 (orientable automatically; this is    *)
(* the form used in Secs 30 and 33).  b is a component of the boundary,      *)
(* which for a 3-manifold in real^3 is its frontier.  The internal version   *)
(* for orientable complexes in real^N is a lower-level statement.            *)

let LOOP_THEOREM_3_STATEMENT = new_definition
 `LOOP_THEOREM_3_STATEMENT <=>
    !(c:(real^3->bool)->bool) b p.
        FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
        b IN components (frontier (UNIONS c)) /\
        path p /\ path_image p SUBSET b /\ pathfinish p = pathstart p /\
        homotopic_loops (UNIONS c) p (linepath(pathstart p,pathstart p)) /\
        ~homotopic_loops b p (linepath(pathstart p,pathstart p))
        ==> ?(k:real^3->bool) d f g.
              &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\
              d SUBSET UNIONS c /\
              d INTER frontier (UNIONS c) = IMAGE f (relative_frontier k) /\
              IMAGE f (relative_frontier k) SUBSET b /\
              ~(?a. homotopic_with (\h. T)
                      (subtopology euclidean (IMAGE f (relative_frontier k)),
                       subtopology euclidean b)
                      (\x. x) (\x. a))`;;

(* Ambient forms of the PL Schoenflies theorems (DG IsSimplyEmbedded,        *)
(* PL/SimplyEmbedded.lean:14 and PL/Schoenflies.lean:69 in R^3, for convex   *)
(* open w; DG PL/PlanarSchoenflies.lean:1260, Moise Ch 3 Thm 7 relative      *)
(* form, in R^2): a PL homeomorphism of the whole space, the identity off w, *)
(* carries s onto the boundary of a simplex.                                 *)

let PL_SCHOENFLIES_3_AMBIENT_STATEMENT = new_definition
 `PL_SCHOENFLIES_3_AMBIENT_STATEMENT <=>
    !s w:real^3->bool.
        pl_sphere 2 s /\ convex w /\ open w /\ s SUBSET w
        ==> ?(k:real^3->bool) f g.
              &3 simplex k /\ pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
              (!x. ~(x IN w) ==> f x = x) /\ IMAGE f s = relative_frontier k`;;

let PL_SCHOENFLIES_2_AMBIENT_STATEMENT = new_definition
 `PL_SCHOENFLIES_2_AMBIENT_STATEMENT <=>
    !s w:real^2->bool.
        pl_sphere 1 s /\ open w /\ s UNION inside s SUBSET w
        ==> ?(k:real^2->bool) f g.
              &2 simplex k /\ pl_homeomorphism ((:real^2),(:real^2)) (f,g) /\
              (!x. ~(x IN w) ==> f x = x) /\ IMAGE f s = relative_frontier k`;;

(* Moise 30.4 (DG Moise304, MoiseChain.lean:83): a topological spherical     *)
(* shell in real^3 contains in its interior a PL 2-sphere separating its     *)
(* two ends.                                                                 *)

let MOISE_304_STATEMENT = new_definition
 `MOISE_304_STATEMENT <=>
    !x b0 b1:real^3->bool.
        spherical_shell x b0 b1
        ==> ?b. pl_sphere 2 b /\ b SUBSET interior x /\
                euclidean_separates b b0 b1`;;

(* Moise 30.5 in the book's form (DG proves only Moise305Tame, with Bd c2    *)
(* bicollared, PL/TameNestedCells.lean:23): between topological 3-cells     *)
(* c1 inside int c2 with a spherical shell between them lies a PL 3-ball.   *)

let MOISE_305_STATEMENT = new_definition
 `MOISE_305_STATEMENT <=>
    !c1 c2:real^3->bool.
        c1 homeomorphic cball(vec 0:real^3,&1) /\
        c2 homeomorphic cball(vec 0:real^3,&1) /\
        c1 SUBSET interior c2 /\
        spherical_shell (closure(c2 DIFF c1)) (frontier c1) (frontier c2)
        ==> ?c. pl_ball 3 c /\ c1 SUBSET interior c /\ c SUBSET interior c2`;;

