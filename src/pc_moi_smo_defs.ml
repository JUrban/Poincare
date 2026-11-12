(* ========================================================================= *)
(* pc_moi_smo_defs (route M): definitions and statement constants for       *)
(* COMBINATORIAL_SMOOTHING_STATEMENT by metric smoothing                    *)
(* (regular-tetrahedron metric, angular rescaling at edges, cones over a    *)
(* smoothing of the vertex links), the glue implications as terms, and the  *)
(* 2D chain.  The statement constants of sections C and D are proved in the *)
(* pc_moi_smo and pc_moi_pd2 files; section F records alternative           *)
(* statements that the proof does not use.                                  *)
(* ========================================================================= *)

needs "src/pc_moi_smb.ml";;
needs "src/pc_moi_tridef.ml";;

needs "src/ns_cutoff.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A. Definitions of the 3D construction.                                    *)
(* ------------------------------------------------------------------------- *)

(* A1. Regular charts of a tetrahedron: affine maps into real^3 sending the *)
(* vertices to a regular tetrahedron with unit edges.  Any two differ by an *)
(* isometry of real^3, so the regular metric of tet is canonical.             *)

let moi_smo_regmap = new_definition
 `moi_smo_regmap (tet:real^N->bool) (A:real^N->real^3) <=>
    (?l:real^N->real^3 y. linear l /\ !x. A x = l x + y) /\
    (!p q. p extreme_point_of tet /\ q extreme_point_of tet /\ ~(p = q)
           ==> dist(A p,A q) = &1)`;;

(* A2. Open star of a simplex s in c: the relative interiors of the         *)
(* simplices having s as a face.                                            *)

let moi_smo_open_star = new_definition
 `moi_smo_open_star (c:(real^N->bool)->bool) (s:real^N->bool) =
    UNIONS {relative_interior t | t IN c /\ s face_of t}`;;

(* A3. The base structure: regular charts of open tetrahedra and isometric  *)
(* unfoldings over open stars of triangles (injectivity puts the two        *)
(* tetrahedra on opposite sides of the common face).  Maximal families.     *)

let moi_smo_tet_atlas = new_definition
 `moi_smo_tet_atlas (c:(real^N->bool)->bool) =
    {(relative_interior tet,A) | tet,A |
       tet IN c /\ aff_dim tet = &3 /\ moi_smo_regmap tet A}`;;

let moi_smo_unfold_atlas = new_definition
 `moi_smo_unfold_atlas (c:(real^N->bool)->bool) =
    {(moi_smo_open_star c t,u) | t,u |
       t IN c /\ aff_dim t = &2 /\
       (!x y. x IN moi_smo_open_star c t /\ y IN moi_smo_open_star c t /\
              (u:real^N->real^3) x = u y ==> x = y) /\
       !tet. tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet
           ==> ?A. moi_smo_regmap tet A /\
                   !x. x IN tet INTER moi_smo_open_star c t ==> u x = A x}`;;

(* A4. Angular rescaling about the third axis (for points with x$2 >= 0,    *)
(* i.e. angle in [0,pi]: (r,phi,z) |-> (r,k phi,z)), rotation about the     *)
(* third axis, the dihedral angle acs(1/3) of the regular tetrahedron and   *)
(* the rescaling factor of an edge (m tetrahedra around it).                *)

let moi_smo_twist = new_definition
 `moi_smo_twist (k:real) (x:real^3) =
    vector[norm(complex(x$1,x$2)) * cos(k * Arg(complex(x$1,x$2)));
           norm(complex(x$1,x$2)) * sin(k * Arg(complex(x$1,x$2)));
           x$3]:real^3`;;

let moi_smo_rotz = new_definition
 `moi_smo_rotz (a:real) (x:real^3) =
    vector[cos a * x$1 - sin a * x$2; sin a * x$1 + cos a * x$2; x$3]:real^3`;;

let moi_smo_dihedral = new_definition
 `moi_smo_dihedral = acs(&1 / &3)`;;

let moi_smo_edge_factor = new_definition
 `moi_smo_edge_factor (c:(real^N->bool)->bool) (e:real^N->bool) =
    &2 * pi /
    (&(CARD {tet | tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet}) * moi_smo_dihedral)`;;

(* A5. Edge charts: on every tetrahedron tet around e = segment[a,b], kappa   *)
(* is a rotation of the angular rescaling of a regular chart A of tet that    *)
(* puts e on the third axis (a to 0, b to basis 3) and tet in the wedge of    *)
(* angles [0,acs(1/3)]; injectivity forces the cyclic arrangement.  The     *)
(* chart is conical at a (homogeneous of degree 1 about a) and preserves    *)
(* the regular distance to a.                                               *)

let moi_smo_edge_atlas = new_definition
 `moi_smo_edge_atlas (c:(real^N->bool)->bool) =
    {(moi_smo_open_star c e,kappa) | e,kappa |
       e IN c /\ aff_dim e = &1 /\
       (!x y. x IN moi_smo_open_star c e /\ y IN moi_smo_open_star c e /\
              (kappa:real^N->real^3) x = kappa y ==> x = y) /\
       ?a b. ~(a = b) /\ e = segment[a,b] /\
             !tet. tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet
                 ==> ?A th. moi_smo_regmap tet A /\ A a = vec 0 /\ A b = basis 3 /\
                            (!p. p extreme_point_of tet /\ ~(p = a) /\ ~(p = b)
                                 ==> &0 <= (A p)$2) /\
                            (?p. p extreme_point_of tet /\ ~(p = a) /\ ~(p = b) /\
                                 (A p)$2 = &0 /\ &0 < (A p)$1) /\
                            !x. x IN tet INTER moi_smo_open_star c e
                                ==> kappa x =
                                    moi_smo_rotz (moi_smo_edge_factor c e * th)
                                      (moi_smo_twist (moi_smo_edge_factor c e)
                                                     (A x))}`;;

(* A6. Regular distance to a vertex v (well defined on the closed star).    *)

let moi_smo_rho = new_definition
 `moi_smo_rho (c:(real^N->bool)->bool) (v:real^N) (x:real^N) =
    @r. ?tet A. tet IN c /\ aff_dim tet = &3 /\ v IN tet /\ x IN tet /\
              moi_smo_regmap tet A /\ r = dist(A x,A v)`;;

(* A7. Gnomonic projection (central projection to the plane x$3 = 1).       *)

let moi_smo_gnom = new_definition
 `moi_smo_gnom (y:real^3) = vector[y$1 / y$3; y$2 / y$3]:real^2`;;

(* A8. Star charts at v: members of the three families that are conical at *)
(* v with apex 0 (homogeneous of degree 1 about v).  Their gnomonic         *)
(* projections, after any rotation R, chart the link of v: the link atlas. *)
(* Straight segments of the link go to straight segments in the charts of  *)
(* tetrahedra and triangles; the edge charts give the cone points.          *)

let moi_smo_star_atlas = new_definition
 `moi_smo_star_atlas (c:(real^N->bool)->bool) (v:real^N) =
    {(U,kappa) | (U,kappa) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                              moi_smo_edge_atlas c /\
                 !x t. x IN U /\ &0 < t /\ t <= &1
                       ==> v + t % (x - v) IN U /\
                           kappa(v + t % (x - v)) = t % kappa x}`;;

let moi_smo_link_atlas = new_definition
 `moi_smo_link_atlas (c:(real^N->bool)->bool) (v:real^N) =
    {({l | l IN UNIONS(simplicial_link c v) /\ v + inv(&2) % (l - v) IN U /\
           &0 < ((R:real^3->real^3)(kappa(v + inv(&2) % (l - v))))$3},
      (\l. moi_smo_gnom(R(kappa(v + inv(&2) % (l - v)))))) |
     U,kappa,R | (U,kappa) IN moi_smo_star_atlas c v /\ orthogonal_transformation R}`;;

(* A9. Vertex charts: x |-> rho(x) d(ray(x)) on the regular ball of radius  *)
(* 1/2 about v, for a homeomorphism d of the link onto S^2.                 *)

let moi_smo_ray = new_definition
 `moi_smo_ray (c:(real^N->bool)->bool) (v:real^N) (x:real^N) =
    @l. l IN UNIONS(simplicial_link c v) /\
        ?s. &0 < s /\ s <= &1 /\ x = v + s % (l - v)`;;

let moi_smo_vertex_dom = new_definition
 `moi_smo_vertex_dom (c:(real^N->bool)->bool) (v:real^N) =
    {x | x IN moi_smo_open_star c {v} /\ moi_smo_rho c v x < inv(&2)}`;;

let moi_smo_vertex_chart = new_definition
 `moi_smo_vertex_chart (c:(real^N->bool)->bool) (v:real^N) (d:real^N->real^3)
                       (x:real^N) =
    moi_smo_rho c v x % d(moi_smo_ray c v x)`;;

(* ------------------------------------------------------------------------- *)
(* B. Definitions of the 2D layer.                                           *)
(* ------------------------------------------------------------------------- *)

(* B1. Planar angular rescaling on the closed half-plane of directions      *)
(* [b,b+pi] (developed angle b + theta |-> k (b + theta)); k = 1 gives the  *)
(* identity (sanity theorem MOI_SMO_ANG_ONE below).                         *)

let moi_smo_ang = new_definition
 `moi_smo_ang (k:real) (b:real) (y:complex) =
    Cx(norm y) * cexp(ii * Cx(k * (b + Arg(cexp(--(ii * Cx b)) * y))))`;;

(* B2. Tangent directions of a cell and smoothness of a map on a closed     *)
(* cell up to the boundary, with injective tangential derivative.           *)

let moi_smo_tangent = new_definition
 `moi_smo_tangent (s:real^N->bool) = span {y - z | y IN s /\ z IN s}`;;

let moi_smo_cell_smooth = new_definition
 `moi_smo_cell_smooth (s:real^N->bool) (f:real^N->real^M) <=>
    ?u g. open u /\ s SUBSET u /\ smooth_map_on u g /\
          (!x. x IN s ==> g x = f x) /\
          (!x w. x IN s /\ w IN moi_smo_tangent s /\
                 frechet_derivative g (at x) w = vec 0 ==> w = vec 0)`;;

(* B3. Conical piecewise smoothness of a homeomorphism h of the polyhedron  *)
(* of a 2-complex L onto S^2 with respect to a 2D atlas sigma (the          *)
(* interface between the link files and the 2D smoothing files):            *)
(* (1) h is smooth on every closed triangle;                                *)
(* (2) at every vertex w there is a chart phi with phi w = 0 which on each  *)
(*     triangle s at w is an angular rescaling (exponent k > 0, developed   *)
(*     offset b s) of a cell-smooth embedding Q s mapping the edges at w    *)
(*     into rays, with equal norms on common faces (the developed pieces    *)
(*     around a cone point agree only up to the rotation by the cone angle  *)
(*     across one seam; k = 1 at ordinary vertices, k = 2 pi / (m acs(1/3)) *)
(*     at the cone points, the vertices of the original link);              *)
(* (3) every open edge lies in a chart in which it is straight and the two  *)
(*     triangles are smooth up to it;                                       *)
(* (4) h is a smooth immersion on open triangles in every chart.            *)

let moi_smo_conical_pd = new_definition
 `moi_smo_conical_pd (L:(real^N->bool)->bool)
                     (sigma:((real^N->bool)#(real^N->real^2))->bool)
                     (h:real^N->real^3) <=>
   (!s. s IN L /\ aff_dim s = &2 ==> moi_smo_cell_smooth s h) /\
   (!w. {w} IN L
        ==> ?U phi k b Q.
              (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < k /\
              !s. s IN L /\ aff_dim s = &2 /\ w IN s
                  ==> moi_smo_cell_smooth s ((Q:(real^N->bool)->real^N->real^2) s) /\
                      (!x y. x IN s /\ y IN s /\ Q s x = Q s y ==> x = y) /\
                      Q s w = vec 0 /\
                      (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx(b s))) * Q s x)) /\
                      (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
                           ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q s x = t % a) /\
                      (!x. x IN s INTER U ==> phi x = moi_smo_ang k (b s) (Q s x)) /\
                      (!s' x. s' IN L /\ aff_dim s' = &2 /\ w IN s' /\ x IN s INTER s'
                              ==> norm(Q s x) = norm(Q s' x))) /\
   (!e. e IN L /\ aff_dim e = &1
        ==> ?U phi. (U,phi) IN sigma /\ relative_interior e SUBSET U /\
                    (?a p. !x. x IN relative_interior e ==> ?t. phi x = a + t % p) /\
                    !s x. s IN L /\ aff_dim s = &2 /\ e SUBSET s /\
                          x IN relative_interior e
                          ==> ?r. &0 < r /\ s INTER cball(x,r) SUBSET U /\
                                  moi_smo_cell_smooth (s INTER cball(x,r)) phi) /\
   (!s U phi. s IN L /\ aff_dim s = &2 /\ (U,phi) IN sigma
              ==> ?g. smooth_map_on (IMAGE phi (U INTER relative_interior s)) g /\
                      (!x. x IN U INTER relative_interior s ==> g(phi x) = h x) /\
                      (!y z. y IN IMAGE phi (U INTER relative_interior s) /\
                             frechet_derivative g (at y) z = vec 0 ==> z = vec 0))`;;

(* ------------------------------------------------------------------------- *)
(* C. Statement constants of the 3D chain (route M).                         *)
(* ------------------------------------------------------------------------- *)

(* C1. Combinatorics of a finite complex whose polyhedron is a 2-sphere     *)
(* (pure, every edge in exactly two triangles, vertex links single cycles); *)
(* by invariance of domain.  Used for vertex links and for the subdivision  *)
(* of the link in the 2D layer.                                             *)

let MOI_SMO_SURFACE_COMPLEX_STATEMENT = new_definition
 `MOI_SMO_SURFACE_COMPLEX_STATEMENT (u:N->bool) <=>
    !L:(real^N->bool)->bool.
        simplicial_complex L /\ (UNIONS L) homeomorphic (sphere(vec 0:real^3,&1))
        ==> (!s. s IN L ==> aff_dim s <= &2) /\
            (!s. s IN L /\ ~(s = {}) ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t) /\
            (!e. e IN L /\ aff_dim e = &1
                 ==> CARD {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = 2) /\
            (!w. {w} IN L
                 ==> ?n S. 3 <= n /\ (!i. S(i + n) = (S:num->real^N->bool) i) /\
                           (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
                           (!i. S i IN L /\ aff_dim(S i) = &2 /\ w IN S i /\
                                aff_dim(S i INTER S(SUC i)) = &1) /\
                           (!t. t IN L /\ aff_dim t = &2 /\ w IN t
                                ==> ?i. i < n /\ t = S i))`;;

(* C2. Combinatorics of a finite combinatorial 3-manifold: pure, every      *)
(* triangle in exactly two tetrahedra, the tetrahedra around an edge form   *)
(* one cycle.  From C1 applied to the vertex links.                         *)

let MOI_SMO_CF_STATEMENT = new_definition
 `MOI_SMO_CF_STATEMENT (u:N->bool) <=>
    !c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 3 c
        ==> (!s. s IN c ==> aff_dim s <= &3) /\
            (!s. s IN c /\ ~(s = {}) ==> ?tet. tet IN c /\ aff_dim tet = &3 /\ s SUBSET tet) /\
            (!t. t IN c /\ aff_dim t = &2
                 ==> CARD {tet | tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet} = 2) /\
            (!e. e IN c /\ aff_dim e = &1
                 ==> ?n S. 3 <= n /\ (!i. S(i + n) = (S:num->real^N->bool) i) /\
                           (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
                           (!i. S i IN c /\ aff_dim(S i) = &3 /\ e SUBSET S i /\
                                aff_dim(S i INTER S(SUC i)) = &2) /\
                           (!tet. tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet
                                ==> ?i. i < n /\ tet = S i))`;;

(* C3. The base structure is a smooth atlas off the 1-skeleton (transition *)
(* maps are isometries of real^3), and star charts exist at every vertex.  *)

let MOI_SMO_BASE_STATEMENT = new_definition
 `MOI_SMO_BASE_STATEMENT (u:N->bool) <=>
    !c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 3 c
        ==> smooth_manifold_atlas
              (subtopology euclidean
                 (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}))
              (moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c) /\
            (!tet v. tet IN c /\ aff_dim tet = &3 /\ v extreme_point_of tet
                   ==> ?A. (relative_interior tet,A) IN moi_smo_star_atlas c v) /\
            (!t v. t IN c /\ aff_dim t = &2 /\ v extreme_point_of t
                   ==> ?w. (moi_smo_open_star c t,w) IN moi_smo_star_atlas c v)`;;

(* C4. Edge charts exist (conical at either end), are homeomorphisms onto   *)
(* open subsets of real^3, and are smoothly compatible with all charts of   *)
(* the three families.                                                      *)

let MOI_SMO_EDGE_STATEMENT = new_definition
 `MOI_SMO_EDGE_STATEMENT (u:N->bool) <=>
    !c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 3 c
        ==> (!e v. e IN c /\ aff_dim e = &1 /\ v extreme_point_of e
                   ==> ?kappa. (moi_smo_open_star c e,kappa) IN moi_smo_edge_atlas c /\
                               (moi_smo_open_star c e,kappa) IN moi_smo_star_atlas c v) /\
            (!U kappa. (U,kappa) IN moi_smo_edge_atlas c
                       ==> open_in (subtopology euclidean (UNIONS c)) U /\
                           open (IMAGE kappa U) /\
                           homeomorphic_map (subtopology euclidean U,
                                             subtopology euclidean (IMAGE kappa U))
                                            kappa) /\
            (!U kappa V phi.
                 (U,kappa) IN moi_smo_edge_atlas c /\
                 (V,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                            moi_smo_edge_atlas c
                 ==> (?g. smooth_map_on (IMAGE kappa (U INTER V)) g /\
                          !x. x IN U INTER V ==> g(kappa x) = phi x) /\
                     (?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
                          !x. x IN U INTER V ==> g(phi x) = kappa x))`;;

(* C5. The punctured atlas: the three families form a smooth atlas on the   *)
(* polyhedron minus its vertices.                                           *)

let MOI_SMO_PUNCTURED_STATEMENT = new_definition
 `MOI_SMO_PUNCTURED_STATEMENT (u:N->bool) <=>
    !c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 3 c
        ==> smooth_manifold_atlas
              (subtopology euclidean (UNIONS c DIFF {v | {v} IN c}))
              (moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
               moi_smo_edge_atlas c)`;;

(* C6. The link atlas at a vertex is a smooth atlas (charts into real^2) on *)
(* the link polyhedron.                                                     *)

let MOI_SMO_LINK_ATLAS_STATEMENT = new_definition
 `MOI_SMO_LINK_ATLAS_STATEMENT (u:N->bool) <=>
    !c (v:real^N).
        FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
        ==> smooth_manifold_atlas (subtopology euclidean (UNIONS(simplicial_link c v)))
                                  (moi_smo_link_atlas c v)`;;

(* C7. The link is conically piecewise smooth over S^2: h = radial         *)
(* projection of a PL homeomorphism onto the boundary of a tetrahedron      *)
(* about 0 (from the definition of combinatorial_manifold), L a subdivision *)
(* of the link on which it is affine (SIMPLICIAL_SUBDIVISION_PL_MAP).       *)

let MOI_SMO_LINK_PD_STATEMENT = new_definition
 `MOI_SMO_LINK_PD_STATEMENT (u:N->bool) <=>
    !c (v:real^N).
        FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
        ==> ?L h h'. simplicial_complex L /\ UNIONS L = UNIONS(simplicial_link c v) /\
                     homeomorphism (UNIONS L,sphere(vec 0:real^3,&1)) (h,h') /\
                     moi_smo_conical_pd L (moi_smo_link_atlas c v) h`;;

(* C8. The link smoothing theorem: the link atlas is diffeomorphic to the   *)
(* round S^2 (a homeomorphism onto S^2 that is a smooth immersion in every  *)
(* chart).  Follows from C6, C7 and the 2D theorem D7.                      *)

let MOI_SMO_LINK_SMOOTH_STATEMENT = new_definition
 `MOI_SMO_LINK_SMOOTH_STATEMENT (u:N->bool) <=>
    !c (v:real^N).
        FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
        ==> ?d d'. homeomorphism (UNIONS(simplicial_link c v),
                                  sphere(vec 0:real^3,&1)) (d,d') /\
                   smooth_immersion_into (moi_smo_link_atlas c v) d`;;

(* C9. Vertex charts: the cone over a link smoothing is a chart on the     *)
(* regular ball of radius 1/2, smoothly compatible with the three families. *)

let MOI_SMO_VERTEX_STATEMENT = new_definition
 `MOI_SMO_VERTEX_STATEMENT (u:N->bool) <=>
    !c (v:real^N) d d'.
        FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
        homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
        smooth_immersion_into (moi_smo_link_atlas c v) d
        ==> v IN moi_smo_vertex_dom c v /\
            open_in (subtopology euclidean (UNIONS c)) (moi_smo_vertex_dom c v) /\
            open (IMAGE (moi_smo_vertex_chart c v d) (moi_smo_vertex_dom c v)) /\
            homeomorphic_map
              (subtopology euclidean (moi_smo_vertex_dom c v),
               subtopology euclidean
                 (IMAGE (moi_smo_vertex_chart c v d) (moi_smo_vertex_dom c v)))
              (moi_smo_vertex_chart c v d) /\
            !U phi. (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                               moi_smo_edge_atlas c
                    ==> (?g. smooth_map_on
                               (IMAGE (moi_smo_vertex_chart c v d)
                                      (moi_smo_vertex_dom c v INTER U)) g /\
                             !x. x IN moi_smo_vertex_dom c v INTER U
                                 ==> g(moi_smo_vertex_chart c v d x) = phi x) /\
                        (?g. smooth_map_on (IMAGE phi (moi_smo_vertex_dom c v INTER U)) g /\
                             !x. x IN moi_smo_vertex_dom c v INTER U
                                 ==> g(phi x) = moi_smo_vertex_chart c v d x)`;;

(* ------------------------------------------------------------------------- *)
(* D. Statement constants of the 2D layer (smoothing a conically piecewise  *)
(* smooth homeomorphism onto S^2; Munkres-Whitehead style, local).          *)
(* ------------------------------------------------------------------------- *)

(* D1. Linearization at a vertex: on a closed convex cone S, replacing G by *)
(* L + beta(2|y|/r - 1)(G - L) (L = DG(0), beta = smooth_step) keeps the    *)
(* Jacobian invertible for small r; the formula depends only on the values  *)
(* of G, so adjacent sectors still agree on their common ray.               *)

let MOI_SMO_LIN_STATEMENT = new_definition
 `MOI_SMO_LIN_STATEMENT <=>
    !(G:real^2->real^2) u S R.
        open u /\ S SUBSET u /\ closed S /\ convex S /\ conic S /\ &0 < R /\
        smooth_map_on u G /\ G(vec 0) = vec 0 /\
        (!x. x IN S INTER cball(vec 0,R) ==> ~(det(jacobian G (at x)) = &0))
        ==> ?r0. &0 < r0 /\
                 !r x. &0 < r /\ r < r0 /\ x IN S INTER cball(vec 0,R)
                       ==> ~(det(jacobian
                               (\y. frechet_derivative G (at (vec 0)) y +
                                    smooth_step(&2 * norm y / r - &1) %
                                    (G y - frechet_derivative G (at (vec 0)) y))
                               (at x)) = &0)`;;

(* D2. Smoothing at a conical vertex: a positively homogeneous injective    *)
(* map, smooth with positive Jacobian on finitely many closed convex cones  *)
(* covering the plane, is replaced inside ball(0,R2) by a map smooth near   *)
(* cball(0,R1) and still piecewise smooth on the cones outside, with the    *)
(* crease jumps vanishing near radius R1 (radial interpolation in log r of  *)
(* the angular lift towards a linear map: Gamma_2 = 0).                     *)

let MOI_SMO_VERTEX2_STATEMENT = new_definition
 `MOI_SMO_VERTEX2_STATEMENT <=>
    !(P:real^2->real^2) (S:num->real^2->bool) n R2.
        &0 < R2 /\ P continuous_on (:real^2) /\
        (!t x. &0 <= t ==> P(t % x) = t % P x) /\
        (!x y. P x = P y ==> x = y) /\
        (!i. i < n ==> closed(S i) /\ convex(S i) /\ conic(S i)) /\
        UNIONS {S i | i < n} = (:real^2) /\
        (!i. i < n
             ==> ?u g. open u /\ S i DIFF {vec 0} SUBSET u /\ smooth_map_on u g /\
                       (!x. x IN S i ==> g x = P x) /\
                       (!x. x IN S i DIFF {vec 0} ==> &0 < det(jacobian g (at x))))
        ==> ?P' R1. &0 < R1 /\ R1 < R2 /\ P' continuous_on (:real^2) /\
                    (!x. R2 <= norm x ==> P' x = P x) /\
                    (?u. open u /\ cball(vec 0,R1) SUBSET u /\ smooth_map_on u P' /\
                         !x. x IN u ==> &0 < det(jacobian P' (at x))) /\
                    (!i. i < n
                         ==> ?u g. open u /\ {x | x IN S i /\ R1 / &2 <= norm x} SUBSET u /\
                                   smooth_map_on u g /\
                                   (!x. x IN S i /\ R1 / &2 <= norm x ==> g x = P' x) /\
                                   (!x. x IN u /\ norm x < R1 ==> g x = P' x) /\
                                   (!x. x IN S i /\ R1 / &2 <= norm x
                                        ==> &0 < det(jacobian g (at x))))`;;

(* D3. Crease smoothing along a straight segment (the x-axis from a to b):  *)
(* two orientation-consistent local diffeomorphisms agreeing on the crease *)
(* and equal near both ends give a smooth map with invertible Jacobian on   *)
(* the open strip, equal to the creased map outside a thinner strip and     *)
(* near the ends (normalize by Fm^-1, interpolate fibrewise).               *)

let MOI_SMO_CREASE_STATEMENT = new_definition
 `MOI_SMO_CREASE_STATEMENT <=>
    !(Fp:real^2->real^2) Fm u a b d e.
        open u /\ a < b /\ &0 < d /\ &0 < e /\ &2 * e < b - a /\
        {x:real^2 | a <= x$1 /\ x$1 <= b /\ abs(x$2) <= d} SUBSET u /\
        smooth_map_on u Fp /\ smooth_map_on u Fm /\
        (!t. a <= t /\ t <= b ==> Fp(vector[t; &0]) = Fm(vector[t; &0])) /\
        (!s t. a <= s /\ s <= b /\ a <= t /\ t <= b /\
               Fm(vector[s; &0]) = Fm(vector[t; &0]) ==> s = t) /\
        (!x:real^2. a <= x$1 /\ x$1 <= b /\ abs(x$2) <= d
                    ==> &0 < det(jacobian Fp (at x)) /\ &0 < det(jacobian Fm (at x))) /\
        (!x:real^2. a <= x$1 /\ x$1 <= b /\ abs(x$2) <= d /\
                    (x$1 <= a + e \/ b - e <= x$1) ==> Fp x = Fm x)
        ==> ?F' d'. &0 < d' /\ d' < d /\
                    smooth_map_on {x:real^2 | a < x$1 /\ x$1 < b /\ abs(x$2) < d} F' /\
                    (!x:real^2. a < x$1 /\ x$1 < b /\ abs(x$2) < d
                                ==> &0 < det(jacobian F' (at x))) /\
                    (!x:real^2. a < x$1 /\ x$1 < b /\ abs(x$2) < d /\
                                (d' <= abs(x$2) \/ x$1 <= a + e / &2 \/ b - e / &2 <= x$1)
                                ==> F' x = (if &0 <= x$2 then Fp x else Fm x))`;;

(* D4. Local topology of injective piecewise smooth maps: no folds along a  *)
(* crease (the two one-sided Jacobians have the same sign), and the conical *)
(* blow-up at a vertex has winding number +1 or -1 (via the Jordan curve    *)
(* theorem: a simple closed curve winds once around its inside).            *)

let MOI_SMO_CREASE_ORIENT_STATEMENT = new_definition
 `MOI_SMO_CREASE_ORIENT_STATEMENT <=>
    !(G:real^2->real^2) Gp Gm u.
        open u /\ vec 0 IN u /\ G continuous_on u /\
        (!x y. x IN u /\ y IN u /\ G x = G y ==> x = y) /\
        smooth_map_on u Gp /\ smooth_map_on u Gm /\
        (!x. x IN u /\ &0 <= x$2 ==> G x = Gp x) /\
        (!x. x IN u /\ x$2 <= &0 ==> G x = Gm x) /\
        ~(det(jacobian Gp (at (vec 0))) = &0) /\ ~(det(jacobian Gm (at (vec 0))) = &0)
        ==> &0 < det(jacobian Gp (at (vec 0))) * det(jacobian Gm (at (vec 0)))`;;

let MOI_SMO_VERTEX_DEGREE_STATEMENT = new_definition
 `MOI_SMO_VERTEX_DEGREE_STATEMENT <=>
    !(G:complex->complex) (P:complex->complex) u.
        open u /\ Cx(&0) IN u /\ G continuous_on u /\
        (!x y. x IN u /\ y IN u /\ G x = G y ==> x = y) /\ G(Cx(&0)) = Cx(&0) /\
        P continuous_on (:complex) /\ (!t x. &0 <= t ==> P(Cx t * x) = Cx t * P x) /\
        (!x. ~(x = Cx(&0)) ==> ~(P x = Cx(&0))) /\
        (!e. &0 < e ==> ?r. &0 < r /\ !x. norm x < r ==> norm(G x - P x) <= e * norm x)
        ==> winding_number((\t. P(cexp(ii * Cx(&2 * pi * drop t)))),Cx(&0)) = Cx(&1) \/
            winding_number((\t. P(cexp(ii * Cx(&2 * pi * drop t)))),Cx(&0)) = --Cx(&1)`;;

(* D5. A local homeomorphism of a compact connected locally path-connected *)
(* set onto S^2 is a homeomorphism (covering space argument;               *)
(* PROPER_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP, COVERING_SPACE_HOMEOMORPHISM, *)
(* SIMPLY_CONNECTED_SPHERE).  Generalizes SMT_SPHERE_COVERING_STATEMENT.    *)

let MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT = new_definition
 `MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT (u:N->bool) <=>
    !(X:real^N->bool) (f:real^N->real^3).
        compact X /\ connected X /\ locally path_connected X /\ ~(X = {}) /\
        IMAGE f X SUBSET sphere(vec 0,&1) /\
        (!x. x IN X
             ==> ?U V g. x IN U /\ open_in (subtopology euclidean X) U /\
                         open_in (subtopology euclidean (sphere(vec 0,&1))) V /\
                         homeomorphism (U,V) (f,g))
        ==> ?f'. homeomorphism (X,sphere(vec 0,&1)) (f,f')`;;

(* D6. The 2D theorem: a conically piecewise smooth homeomorphism onto S^2  *)
(* can be smoothed (linearize and smooth at vertices, then smooth creases;  *)
(* the result is a local diffeomorphism, hence a diffeomorphism by D5).     *)

let MOI_SMO_PD2_STATEMENT = new_definition
 `MOI_SMO_PD2_STATEMENT (u:N->bool) <=>
    !(L:(real^N->bool)->bool) (sigma:((real^N->bool)#(real^N->real^2))->bool)
     (h:real^N->real^3) h'.
        simplicial_complex L /\
        smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\
        homeomorphism (UNIONS L,sphere(vec 0,&1)) (h,h') /\
        moi_smo_conical_pd L sigma h
        ==> ?(d:real^N->real^3) d'.
                   homeomorphism (UNIONS L,sphere(vec 0,&1)) (d,d') /\
                   smooth_immersion_into sigma d`;;

(* ------------------------------------------------------------------------- *)
(* E. The glue implications as terms (type-checked here; the assembly files *)
(* prove the steps, e.g. MOI_SMO_TOP_FROM_PARTS and                         *)
(* MOI_SMO_LINK_SMOOTH_FROM_PARTS of pc_moi_smo_vertex).                    *)
(* ------------------------------------------------------------------------- *)

let MOI_SMO_TOP_TERM =
 `!u:N->bool. MOI_SMO_PUNCTURED_STATEMENT u /\ MOI_SMO_LINK_SMOOTH_STATEMENT u /\
              MOI_SMO_VERTEX_STATEMENT u
              ==> COMBINATORIAL_SMOOTHING_STATEMENT u`;;

let MOI_SMO_PUNCTURED_TERM =
 `!u:N->bool. MOI_SMO_CF_STATEMENT u /\ MOI_SMO_BASE_STATEMENT u /\
              MOI_SMO_EDGE_STATEMENT u
              ==> MOI_SMO_PUNCTURED_STATEMENT u`;;

let MOI_SMO_CF_TERM =
 `!u:N->bool. MOI_SMO_SURFACE_COMPLEX_STATEMENT u ==> MOI_SMO_CF_STATEMENT u`;;

let MOI_SMO_LINK_TERM =
 `!u:N->bool. MOI_SMO_LINK_ATLAS_STATEMENT u /\ MOI_SMO_LINK_PD_STATEMENT u /\
              MOI_SMO_PD2_STATEMENT u
              ==> MOI_SMO_LINK_SMOOTH_STATEMENT u`;;

let MOI_SMO_PD2_TERM =
 `!u:N->bool. MOI_SMO_LIN_STATEMENT /\ MOI_SMO_VERTEX2_STATEMENT /\
              MOI_SMO_CREASE_STATEMENT /\ MOI_SMO_CREASE_ORIENT_STATEMENT /\
              MOI_SMO_VERTEX_DEGREE_STATEMENT /\
              MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT u /\
              MOI_SMO_SURFACE_COMPLEX_STATEMENT u
              ==> MOI_SMO_PD2_STATEMENT u`;;

let MOI_SMO_HEADLINE_TERM =
 `!u:N->bool.
     MOI_SMO_SURFACE_COMPLEX_STATEMENT u /\ MOI_SMO_BASE_STATEMENT u /\
     MOI_SMO_EDGE_STATEMENT u /\ MOI_SMO_LINK_ATLAS_STATEMENT u /\
     MOI_SMO_LINK_PD_STATEMENT u /\ MOI_SMO_VERTEX_STATEMENT u /\
     MOI_SMO_LIN_STATEMENT /\ MOI_SMO_VERTEX2_STATEMENT /\ MOI_SMO_CREASE_STATEMENT /\
     MOI_SMO_CREASE_ORIENT_STATEMENT /\ MOI_SMO_VERTEX_DEGREE_STATEMENT /\
     MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT u
     ==> COMBINATORIAL_SMOOTHING_STATEMENT u`;;

(* ------------------------------------------------------------------------- *)
(* F. Alternative statements (type-checked only, not used in the proof).    *)
(* ------------------------------------------------------------------------- *)

(* F1. Smooth recognition of S^2 in the general (topological) form, DG      *)
(* Topology/Manifold/SphereDiffeomorph.lean:50.  It would replace C7, D1-D6 *)
(* in one stroke (MOI_SMO_S2_TERM), but its DG proof needs smooth           *)
(* Schoenflies in the plane (about 90K Lean lines beyond the topological    *)
(* Schoenflies theorem).                                                    *)

let MOI_SMO_S2_RECOGNITION_STATEMENT = new_definition
 `MOI_SMO_S2_RECOGNITION_STATEMENT (u:N->bool) <=>
    !(X:real^N->bool) (sigma:((real^N->bool)#(real^N->real^2))->bool).
        compact X /\ X homeomorphic (sphere(vec 0:real^3,&1)) /\
        smooth_manifold_atlas (subtopology euclidean X) sigma
        ==> ?(d:real^N->real^3) d'. homeomorphism (X,sphere(vec 0,&1)) (d,d') /\
                                    smooth_immersion_into sigma d`;;

let MOI_SMO_S2_TERM =
 `!u:N->bool. MOI_SMO_S2_RECOGNITION_STATEMENT u /\ MOI_SMO_LINK_ATLAS_STATEMENT u
              ==> MOI_SMO_LINK_SMOOTH_STATEMENT u`;;

(* F2. The DG route (handle filtration and smooth stages), for comparison.  *)
(* PL boundary of a 3-complex: the triangles lying in exactly one           *)
(* tetrahedron.  Handle models in real^3 (DG PL/CellAttachment.lean:53):    *)
(* 0 and 3: the standard 3-simplex attached along nothing, resp. its        *)
(* boundary; 1 and 2: the prism triangle x [0,1] attached along the two     *)
(* ends, resp. along (boundary of the triangle) x [0,1].                    *)

let moi_smo_pl_boundary = new_definition
 `moi_smo_pl_boundary (c:(real^N->bool)->bool) =
    UNIONS {t | t IN c /\ aff_dim t = &2 /\
                CARD {tet | tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet} = 1}`;;

let moi_smo_prism = new_definition
 `moi_smo_prism = {x:real^3 | &0 <= x$1 /\ &0 <= x$2 /\ x$1 + x$2 <= &1 /\
                              &0 <= x$3 /\ x$3 <= &1}`;;

let moi_smo_handle_model = new_definition
 `moi_smo_handle_model k =
    if k = 1 \/ k = 2 then moi_smo_prism
    else convex hull {vec 0:real^3, basis 1, basis 2, basis 3}`;;

let moi_smo_handle_attach = new_definition
 `moi_smo_handle_attach k =
    if k = 0 then {}
    else if k = 1 then {x | x IN moi_smo_prism /\ (x$3 = &0 \/ x$3 = &1)}
    else if k = 2 then {x | x IN moi_smo_prism /\
                            (x$1 = &0 \/ x$2 = &0 \/ x$1 + x$2 = &1)}
    else relative_frontier(convex hull {vec 0:real^3, basis 1, basis 2, basis 3})`;;

(* DG exists_pl_three_handle_filtration (PL/DerivedNeighborhoodHandle       *)
(* Filtration.lean:18), HOL form: second-derived neighbourhoods of the      *)
(* faces in order of dimension; each step attaches a k-handle along part    *)
(* of the PL boundary.                                                      *)

let MOI_SMO_HANDLE_FILTRATION_STATEMENT = new_definition
 `MOI_SMO_HANDLE_FILTRATION_STATEMENT (u:N->bool) <=>
    !c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 3 c
        ==> ?m (K:num->(real^N->bool)->bool) (k:num->num).
              (!i. i <= m
                   ==> FINITE(K i) /\ combinatorial_manifold_with_boundary 3 (K i)) /\
              UNIONS(K 0) = {} /\ UNIONS(K m) = UNIONS c /\
              !i. i < m
                  ==> k i <= 3 /\
                      ?H (f:real^3->real^N) g.
                          pl_homeomorphism (moi_smo_handle_model(k i),H) (f,g) /\
                          UNIONS(K(SUC i)) = UNIONS(K i) UNION H /\
                          H INTER UNIONS(K i) = IMAGE f (moi_smo_handle_attach(k i)) /\
                          IMAGE f (moi_smo_handle_attach(k i)) SUBSET
                          moi_smo_pl_boundary(K i)`;;

(* DG isSmoothHandleStage_step (PL/PLSmoothingCompact.lean:245) in stage    *)
(* form: a smooth atlas with boundary on the PL set itself whose atlas      *)
(* boundary is the PL boundary.                                             *)

let MOI_SMO_STAGE_STEP_STATEMENT = new_definition
 `MOI_SMO_STAGE_STEP_STATEMENT (u:N->bool) <=>
    !(K:(real^N->bool)->bool) K' k H (f:real^3->real^N) g.
        FINITE K /\ combinatorial_manifold_with_boundary 3 K /\
        FINITE K' /\ combinatorial_manifold_with_boundary 3 K' /\ k <= 3 /\
        pl_homeomorphism (moi_smo_handle_model k,H) (f,g) /\
        UNIONS K' = UNIONS K UNION H /\
        H INTER UNIONS K = IMAGE f (moi_smo_handle_attach k) /\
        IMAGE f (moi_smo_handle_attach k) SUBSET moi_smo_pl_boundary K /\
        (?atlas:((real^N->bool)#(real^N->real^3))->bool.
             smooth_boundary_atlas (subtopology euclidean (UNIONS K)) atlas /\
             atlas_boundary atlas = moi_smo_pl_boundary K)
        ==> ?atlas:((real^N->bool)#(real^N->real^3))->bool.
              smooth_boundary_atlas (subtopology euclidean (UNIONS K')) atlas /\
              atlas_boundary atlas = moi_smo_pl_boundary K'`;;

(* F3. The planar annulus theorem (the 2D topological tool the DG route     *)
(* needs for germ linearization and disc or annulus taming; from            *)
(* JORDAN_SCHOENFLIES and SPLIT_INSIDE_SIMPLE_CLOSED_CURVE).                *)

let MOI_SMO_PLANAR_ANNULUS_STATEMENT = new_definition
 `MOI_SMO_PLANAR_ANNULUS_STATEMENT <=>
    !g h:real^1->real^2.
        simple_path g /\ pathfinish g = pathstart g /\
        simple_path h /\ pathfinish h = pathstart h /\
        path_image g SUBSET inside(path_image h)
        ==> ((path_image h UNION inside(path_image h)) DIFF inside(path_image g))
            homeomorphic {x:real^2 | &1 <= norm x /\ norm x <= &2}`;;

let MOI_SMO_DG_TERM =
 `!u:N->bool. MOI_SMO_HANDLE_FILTRATION_STATEMENT u /\ MOI_SMO_STAGE_STEP_STATEMENT u
              ==> COMBINATORIAL_SMOOTHING_STATEMENT u`;;

(* ------------------------------------------------------------------------- *)
(* G. Sanity theorems (definitional checks; proved here).                   *)
(* ------------------------------------------------------------------------- *)
let MOI_SMO_ANG_ONE = prove
 (`!b y. moi_smo_ang (&1) b y = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_smo_ang; REAL_MUL_LID] THEN
  ABBREV_TAC `z = cexp(--(ii * Cx b)) * y` THEN
  SUBGOAL_THEN `norm(z:complex) = norm(y:complex)` (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP] THEN
    REWRITE_TAC[RE_NEG; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `y = cexp(ii * Cx b) * z` (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CEXP_ADD] THEN
    REWRITE_TAC[COMPLEX_ADD_RINV; CEXP_0; COMPLEX_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [last(CONJUNCTS(SPEC `z:complex` ARG))] THEN
  CONV_TAC COMPLEX_RING);;
let MOI_SMO_TWIST_ONE = prove
 (`!x:real^3. moi_smo_twist (&1) x = x`,
  GEN_TAC THEN REWRITE_TAC[moi_smo_twist; REAL_MUL_LID] THEN
  ABBREV_TAC `w = complex((x:real^3)$1,x$2)` THEN
  SUBGOAL_THEN `Re w = (x:real^3)$1 /\ Im w = x$2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[RE; IM]; ALL_TAC] THEN
  MP_TAC(last(CONJUNCTS(SPEC `w:complex` ARG))) THEN
  DISCH_THEN(fun th -> MP_TAC(AP_TERM `Re` th) THEN MP_TAC(AP_TERM `Im` th)) THEN
  REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II;
              RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  ASM_MESON_TAC[]);;

let MOI_SMO_TWIST_HOMOG = prove
 (`!k t x:real^3. &0 < t ==> moi_smo_twist k (t % x) = t % moi_smo_twist k x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_twist; VECTOR_MUL_COMPONENT] THEN
  SUBGOAL_THEN `complex(t * (x:real^3)$1,t * x$2) = Cx t * complex(x$1,x$2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_EQ; RE; IM; RE_MUL_CX; IM_MUL_CX]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARG_MUL_CX; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
               REAL_ARITH `&0 < t ==> abs t = t`] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_SMO_DIHEDRAL_COS = prove
 (`cos moi_smo_dihedral = &1 / &3 /\ &0 < moi_smo_dihedral /\
   moi_smo_dihedral < pi / &2`,
  REWRITE_TAC[moi_smo_dihedral] THEN
  SUBGOAL_THEN `cos(acs(&1 / &3)) = &1 / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_ACS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `&1 / &3` ACS_BOUNDS) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `cos(acs(&1 / &3)) = &1 / &3` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[COS_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`pi / &2`; `acs(&1 / &3)`] COS_MONO_LE) THEN
  ASM_REWRITE_TAC[COS_PI2] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
let MOI_SMO_REGMAP_EXAMPLE = prove
 (`moi_smo_regmap
     (convex hull {vector[&1;&0;&0],vector[&0;&1;&0],vector[&0;&0;&1],
                   vector[&1;&1;&1]}:real^3->bool)
     (\x:real^3. inv(sqrt(&2)) % x)`,
  SUBGOAL_THEN `abs(inv(sqrt(&2))) * sqrt(&2) = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_smo_regmap] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^3. inv(sqrt(&2)) % x`; `vec 0:real^3`] THEN
    REWRITE_TAC[LINEAR_SCALING; VECTOR_ADD_RID];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP EXTREME_POINT_OF_CONVEX_HULL (CONJUNCT1 th)) THEN
                       MP_TAC(MATCH_MP EXTREME_POINT_OF_CONVEX_HULL
                                       (CONJUNCT1(CONJUNCT2 th))) THEN
                       MP_TAC(CONJUNCT2(CONJUNCT2 th))) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[dist; GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
  DISCH_TAC THEN REPEAT(DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[vector_norm; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[]);;
let MOI_SMO_TWIST_NORM = prove
 (`!k x:real^3. norm(moi_smo_twist k x) = norm x /\
                norm(moi_smo_rotz k x) = norm x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_smo_twist; moi_smo_rotz] THEN
  REWRITE_TAC[NORM_EQ; DOT_3; VECTOR_3] THEN
  SUBGOAL_THEN `norm(complex((x:real^3)$1,x$2)) pow 2 = x$1 pow 2 + x$2 pow 2`
  MP_TAC THENL
   [REWRITE_TAC[COMPLEX_SQNORM; RE; IM]; ALL_TAC] THEN
  MP_TAC(SPEC `k * Arg(complex((x:real^3)$1,x$2))` SIN_CIRCLE) THEN
  MP_TAC(SPEC `k:real` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

