(* ========================================================================= *)
(* pc_moi_fnd_stmt: the statements of the foundations of the Moise PL core,  *)
(* in the sections T3 (regular neighbourhoods, tubes, collars, general       *)
(* position, splitting), T5 (surfaces), T7 (combinatorial 3-manifolds with   *)
(* boundary) and T8 (double covers), with D (definitions), F (Moise 26.6)    *)
(* and S (sanity theorems). The foundation terms MOI_FND_... are closed      *)
(* boolean terms; the theorems proving them are named in the headers of the  *)
(* pc_moi_fnd files. MOI_FD_... are sanity theorems, and two glue proofs     *)
(* derive DOUBLE_COVER_STATEMENT and MOISE_268_STATEMENT of                  *)
(* pc_moi_core_stmt.ml, which also defines MOISE_266_STATEMENT and           *)
(* pl_torus_model.                                                           *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* D. Definitions.                                                           *)
(* derived_nbhd_complex t l: the subcomplex of the second barycentric       *)
(* subdivision formed by the simplices meeting UNIONS l and their faces;    *)
(* its polyhedron is derived_nbhd t l (Moise p.155).  derived_frontier t l: *)
(* the frontier of the regular neighbourhood relative to UNIONS t (Bd N of *)
(* p.223 when the vertices of l are interior).  boundary_complex c: the     *)
(* simplices of c inside complex_boundary c (Moise p.165, the complex dK). *)
(* ------------------------------------------------------------------------- *)

let derived_nbhd_complex = new_definition
 `derived_nbhd_complex (t:(real^N->bool)->bool) (l:(real^N->bool)->bool) =
    {s | ?r. r IN barycentric_subdivision (barycentric_subdivision t) /\
             ~(r INTER UNIONS l = {}) /\ s face_of r}`;;

let derived_frontier = new_definition
 `derived_frontier (t:(real^N->bool)->bool) (l:(real^N->bool)->bool) =
    (subtopology euclidean (UNIONS t)) frontier_of (derived_nbhd t l)`;;

let boundary_complex = new_definition
 `boundary_complex (c:(real^N->bool)->bool) =
    {s | s IN c /\ s SUBSET complex_boundary c}`;;

(* Euler characteristic of a finite complex (Moise Sec 21, p.147): the      *)
(* alternating count of its nonempty simplices by dimension.  Real-valued   *)
(* (integer values) to use the sum library and REAL_ARITH; Library/isum.ml  *)
(* does not load under type_invention_error.                                 *)

let complex_euler = new_definition
 `complex_euler (c:(real^N->bool)->bool) =
    sum (0..dimindex(:N))
        (\k. --(&1) pow k * &(CARD {s | s IN c /\ aff_dim s = &k}))`;;

(* Standard PL models: the disk with k holes (Moise k-annulus; k = 0 a      *)
(* square, k = 1 an annulus) and the PL torus (product of two square        *)
(* circles).  pl_holed_disk k a: a is PL homeomorphic to the model.         *)

let holed_disk_model = new_definition
 `holed_disk_model k =
    interval[vec 0:real^2,vector[&4 * &k + &4; &4]] DIFF
    UNIONS {interval(vector[&4 * &i + &2; &1]:real^2,vector[&4 * &i + &4; &3]) |
            i | i < k}`;;

let pl_holed_disk = new_definition
 `pl_holed_disk k (a:real^N->bool) <=>
    ?(f:real^2->real^N) g. pl_homeomorphism (holed_disk_model k,a) (f,g)`;;

(* pl_torus_model: defined in pc_moi_core_stmt.ml. *)

(* Two-sidedness (Moise p.191; DG IsTwoSided, Topology/Connected/TwoSided   *)
(* .lean:10): every component k of s has a neighbourhood v in x such that  *)
(* every connected neighbourhood w of k inside v falls apart when k is      *)
(* removed.                                                                  *)

let two_sided_in = new_definition
 `two_sided_in (x:real^N->bool) (s:real^N->bool) <=>
    !k. k IN components s
        ==> ?v. open_in (subtopology euclidean x) v /\ k SUBSET v /\
                !w. w SUBSET v /\ connected w /\
                    k SUBSET (subtopology euclidean x) interior_of w
                    ==> ~connected (w DIFF k)`;;

(* Crossing of two curves j, k at x inside a surface m (the 2D analogue of  *)
(* pl_crossing_at; Moise p.202, true crossing points).                     *)

let pl_curve_crossing_at = new_definition
 `pl_curve_crossing_at (m:real^N->bool) (j:real^N->bool) (k:real^N->bool)
                       (x:real^N) <=>
    ?u (f:real^N->real^2) g.
        open_in (subtopology euclidean m) u /\ x IN u /\
        pl_homeomorphism (u,IMAGE f u) (f,g) /\ open (IMAGE f u) /\
        f x = vec 0 /\
        IMAGE f (j INTER u) = IMAGE f u INTER {y:real^2 | y$1 = &0} /\
        IMAGE f (k INTER u) = IMAGE f u INTER {y:real^2 | y$2 = &0}`;;

(* Affine general position of two simplices in real^3 (Moise p.194, the    *)
(* conditions (4)-(5) and their higher analogues): disjoint, or affine     *)
(* hulls meeting in the expected dimension.                                  *)

let affine_gp_3 = new_definition
 `affine_gp_3 (s:real^3->bool) (t:real^3->bool) <=>
    DISJOINT s t \/
    (&3 <= aff_dim s + aff_dim t /\
     aff_dim (affine hull s INTER affine hull t) = aff_dim s + aff_dim t - &3)`;;

(* Z/2 1-cochains of a complex as sets of edges: cocycles (every triangle   *)
(* has an even number of edges in z) and coboundaries (z is the set of     *)
(* edges with exactly one end in a vertex set w).  Moise 24.8 (p.178) and  *)
(* DG SimplicialBoolCocycle (PL/HomologyCocycle.lean).                      *)

let z2_cocycle = new_definition
 `z2_cocycle (c:(real^N->bool)->bool) (z:(real^N->bool)->bool) <=>
    (!e. e IN z ==> e IN c /\ aff_dim e = &1) /\
    (!s. s IN c /\ aff_dim s = &2 ==> EVEN (CARD {e | e IN z /\ e SUBSET s}))`;;

let z2_coboundary = new_definition
 `z2_coboundary (c:(real^N->bool)->bool) (z:(real^N->bool)->bool) <=>
    ?w:real^N->bool.
      !e. e IN c /\ aff_dim e = &1
          ==> (e IN z <=> ODD (CARD {v | v IN w /\ v IN e /\ {v} IN c}))`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [derived_nbhd_complex; derived_frontier; boundary_complex; complex_euler];;

(* ========================================================================= *)
(* T3. Regular (second-derived) neighbourhoods, tubes, collars, general     *)
(* position, splitting.                                                      *)
(* ========================================================================= *)

(* T3a. Basic facts (Moise p.155; DG RegularNeighborhood.lean:57,          *)
(* DerivedNeighborhood.lean:63).  Used everywhere below.                    *)

let MOI_FND_DERIVED_NBHD_BASIC =
 `!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> lf_simplicial_complex (derived_nbhd_complex t l) /\
         simplicial_subcomplex (derived_nbhd_complex t l)
           (barycentric_subdivision (barycentric_subdivision t)) /\
         UNIONS (derived_nbhd_complex t l) = derived_nbhd t l /\
         derived_nbhd t l SUBSET UNIONS t /\
         closed_in (subtopology euclidean (UNIONS t)) (derived_nbhd t l) /\
         UNIONS l SUBSET
           (subtopology euclidean (UNIONS t)) interior_of (derived_nbhd t l) /\
         (FINITE l ==> FINITE (derived_nbhd_complex t l) /\
                       compact (derived_nbhd t l))`;;

(* Barycentric subdivision of a subcomplex is a subcomplex of the            *)
(* barycentric subdivision, with the same polyhedron (needed by the          *)
(* iterations below).                                                        *)

let MOI_FND_BARYCENTRIC_SUBCOMPLEX =
 `!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> simplicial_subcomplex (barycentric_subdivision l)
                               (barycentric_subdivision t) /\
         UNIONS (barycentric_subdivision l) = UNIONS l`;;

(* Thin regular neighbourhoods (Moise p.223: by subdivision the dual cells  *)
(* get arbitrarily small; p.230 and p.239: N inside a given U).             *)

let MOI_FND_DERIVED_NBHD_SMALL =
 `!(t:(real^N->bool)->bool) l v.
     simplicial_complex t /\ simplicial_subcomplex l t /\
     open_in (subtopology euclidean (UNIONS t)) v /\ UNIONS l SUBSET v
     ==> ?n. derived_nbhd (ITER n barycentric_subdivision t)
                          (ITER n barycentric_subdivision l) SUBSET v`;;

(* T3b. Tubes of graphs (Moise p.223; DG DualCells.lean:392 graphDualCell, *)
(* DualCellDecomposition.lean:176, SplittingDiskRim.lean:20,                *)
(* TubeOfGraphDualCells.lean:101).  Users: MOI_PROD_322, MOI_PROD_323,      *)
(* MOI_PROD_331, MOI_PROD_34_EXT, MOI_PROD_351 and the glue of 34.1.        *)

let MOI_FND_GRAPH_IN_COMPLEX_BARYCENTRIC =
 `!(t:(real^N->bool)->bool) l.
     graph_in_complex t l
     ==> graph_in_complex (barycentric_subdivision t) (barycentric_subdivision l)`;;

let MOI_FND_GRAPH_TUBE =
 `!(t:(real^N->bool)->bool) l.
     graph_in_complex t l
     ==> derived_nbhd t l = UNIONS {derived_dual_cell t l v | v | {v} IN l} /\
         (!v. {v} IN l
              ==> derived_dual_cell t l v SUBSET UNIONS {s | s IN t /\ v IN s} /\
                  {w | {w} IN t /\ w IN derived_dual_cell t l v} = {v} /\
                  derived_dual_cell t l v INTER UNIONS l =
                  v INSERT UNIONS {segment[v,midpoint(v,w)] | w |
                                   ~(w = v) /\ segment[v,w] IN l} /\
                  pl_cell_with_boundary 3 (derived_dual_cell t l v)
                    ((derived_dual_cell t l v INTER derived_frontier t l) UNION
                     UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w |
                             w | ~(w = v) /\ segment[v,w] IN l})) /\
         (!u v. ~(u = v) /\ segment[u,v] IN l
                ==> pl_cell_with_boundary 2
                      (derived_dual_cell t l u INTER derived_dual_cell t l v)
                      (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                       derived_frontier t l) /\
                    derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                    UNIONS l = {midpoint(u,v)}) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
                ==> derived_dual_cell t l u INTER derived_dual_cell t l v = {})`;;

(* In real^3 the relative frontier is the frontier and N is a neighbourhood *)
(* of UNIONS l (the form used by MOISE_322_STATEMENT, MOISE_323_STATEMENT). *)

let MOI_FND_GRAPH_TUBE_FRONTIER_3 =
 `!(t:(real^3->bool)->bool) l.
     graph_in_complex t l /\ FINITE l
     ==> frontier (derived_nbhd t l) = derived_frontier t l /\
         interior (derived_nbhd t l) =
         (subtopology euclidean (UNIONS t)) interior_of (derived_nbhd t l) /\
         UNIONS l SUBSET interior (derived_nbhd t l)`;;

(* Moise 33.1 Lemma 10 (p.235, straightforwardly demonstrable): N minus    *)
(* the graph is a half-open product over Bd N.                              *)

let MOI_FND_GRAPH_TUBE_PRODUCT =
 `!(t:(real^N->bool)->bool) l.
     graph_in_complex t l
     ==> ?(f:real^(N,1)finite_sum->real^N) g.
           homeomorphism
             (derived_frontier t l PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1},
              derived_nbhd t l DIFF UNIONS l) (f,g) /\
           !y. y IN derived_frontier t l ==> f(pastecart y (vec 0)) = y`;;

(* The sets A_v = C_v INTER Bd N (Moise 33.1 Lemmas 12-13, p.236): a sphere *)
(* with deg(v) holes, i.e. a disk with deg(v) - 1 holes, bounded by the     *)
(* rims of the splitting disks at v.                                         *)

let MOI_FND_GRAPH_TUBE_HOLES =
 `!(t:(real^N->bool)->bool) l v d.
     graph_in_complex t l /\ {v} IN l /\
     CARD {e | e IN l /\ aff_dim e = &1 /\ v IN e} = d + 1
     ==> ?(f:real^2->real^N) g.
           pl_homeomorphism (holed_disk_model d,
                             derived_dual_cell t l v INTER derived_frontier t l) (f,g) /\
           IMAGE f (frontier (holed_disk_model d)) =
           UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w INTER
                   derived_frontier t l | w | ~(w = v) /\ segment[v,w] IN l}`;;

(* Euler characteristic of Bd N (DG HandleCount.lean:30 eulerChar_boundary_ *)
(* derivedNeighborhood_eq_two_mul): chi(Bd N) = 2 chi(l); with 22.5 the     *)
(* genus of Bd N (the direct computation of 33.1 Lemma 12).                  *)

let MOI_FND_GRAPH_NBHD_EULER =
 `!(t:(real^N->bool)->bool) l.
     graph_in_complex t l /\ FINITE l
     ==> combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t l) /\
         complex_boundary (derived_nbhd_complex t l) = derived_frontier t l /\
         complex_euler (boundary_complex (derived_nbhd_complex t l)) =
         &2 * complex_euler l`;;

(* Moise p.240: for a 2-simplex s whose edges are in the graph, the union   *)
(* N_s of the dual cells of its vertices is a solid torus with spine Bd s.  *)
(* In real^N (MOISE_34_EXT_STATEMENT is used at N = 7 for 35.2).            *)

let MOI_FND_SOLID_TORUS_TRIANGLE =
 `!(t:(real^N->bool)->bool) l s.
     graph_in_complex t l /\ s IN t /\ aff_dim s = &2 /\
     (!e. e face_of s /\ aff_dim e = &1 ==> e IN l)
     ==> pl_solid_torus (UNIONS {derived_dual_cell t l v | v | v IN s /\ {v} IN l}) /\
         spine (relative_frontier s)
               (UNIONS {derived_dual_cell t l v | v | v IN s /\ {v} IN l})`;;

(* Moise 24.11 (p.179) in real^3 (orientable): the regular neighbourhood of *)
(* a polygon is a PL solid torus with the polygon as spine.                  *)

let MOI_FND_POLYGON_SOLID_TORUS_3 =
 `!(t:(real^3->bool)->bool) l.
     graph_in_complex t l /\ pl_sphere 1 (UNIONS l)
     ==> pl_solid_torus (derived_nbhd t l) /\ spine (UNIONS l) (derived_nbhd t l)`;;

(* T3c. Regular neighbourhoods of subcomplexes.                              *)
(* Manifold property (DG DerivedNeighborhoodManifold.lean:104); boundary =  *)
(* relative frontier plus the trace on the boundary of t.  Users: the loop  *)
(* theorem tower (regular neighbourhoods of singular disks), SPLIT below.   *)

let MOI_FND_DERIVED_NBHD_MANIFOLD =
 `!(t:(real^N->bool)->bool) l.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t
     ==> combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t l) /\
         complex_boundary (derived_nbhd_complex t l) =
         derived_frontier t l UNION (derived_nbhd t l INTER complex_boundary t)`;;

(* UNIONS l is a strong deformation retract of N (DG DerivedNeighborhood-   *)
(* Retraction.lean, DerivedNeighborhoodLoop.lean:24); hence loops_carried, *)
(* the hypothesis of LOOP_NORMAL_SYSTEM_STATEMENT for regular neighbour-    *)
(* hoods of singular disks (Moise p.188).                                    *)

let MOI_FND_DERIVED_NBHD_RETRACT =
 `!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> loops_carried (UNIONS l) (derived_nbhd t l) /\
         ?r. retraction (derived_nbhd t l,UNIONS l) r /\
             homotopic_with (\h. !x. x IN UNIONS l ==> h x = x)
               (subtopology euclidean (derived_nbhd t l),
                subtopology euclidean (derived_nbhd t l))
               (\x. x) r`;;

(* Regular neighbourhoods of PL balls of dimension at most 3 and of trees    *)
(* are PL 3-balls bounded by Bd N (Moise p.169, 23.11-23.12, 23.18 step 2,  *)
(* 28.18 proof; DG DiskDerivedNeighborhood, SimplexDerivedNeighborhood).    *)

let MOI_FND_DERIVED_NBHD_BALL =
 `!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ FINITE l /\
     (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     ((?n. n <= 3 /\ pl_ball n (UNIONS l)) \/
      ((!s. s IN l ==> aff_dim s <= &1) /\ connected (UNIONS l) /\
       ~(UNIONS l = {}) /\
       CARD {v | {v} IN l} = CARD {e | e IN l /\ aff_dim e = &1} + 1))
     ==> pl_cell_with_boundary 3 (derived_nbhd t l) (derived_frontier t l)`;;

(* Regular neighbourhood of a closed surface: one or two sides, each        *)
(* accumulating on the surface; two exactly when two-sided (Moise 26.6      *)
(* proof p.195, 26.3 proof p.192).  Input of MOISE_266 and of the bicollar. *)

let MOI_FND_SURFACE_NBHD_SIDES =
 `!(t:(real^N->bool)->bool) (s:(real^N->bool)->bool).
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\ connected (UNIONS s) /\ ~(UNIONS s = {}) /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v)))
     ==> FINITE (components (derived_nbhd t s DIFF UNIONS s)) /\
         1 <= CARD (components (derived_nbhd t s DIFF UNIONS s)) /\
         CARD (components (derived_nbhd t s DIFF UNIONS s)) <= 2 /\
         (!k. k IN components (derived_nbhd t s DIFF UNIONS s)
              ==> UNIONS s SUBSET closure k) /\
         (CARD (components (derived_nbhd t s DIFF UNIONS s)) = 2 <=>
          two_sided_in (UNIONS t) (UNIONS s))`;;

(* T3d. Collars and bicollars (Moise 26.1-26.3, pp.191-192; DG              *)
(* CollarNeighborhood.lean:130, Bicollar.lean:103, TwoSidedNeighborhood).   *)

let MOI_FND_COLLAR =
 `!(c:(real^N->bool)->bool) v.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     open_in (subtopology euclidean (UNIONS c)) v /\ complex_boundary c SUBSET v
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism
             (complex_boundary c PCROSS interval[vec 0:real^1,vec 1],w) (p,q) /\
           w SUBSET v /\
           complex_boundary c SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN complex_boundary c ==> p(pastecart x (vec 0)) = x`;;

let MOI_FND_TWO_SIDED_BOUNDARY =
 `!(c:(real^N->bool)->bool) (m:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE m /\ combinatorial_manifold_with_boundary 3 m /\
     UNIONS m SUBSET UNIONS c /\ s SUBSET complex_boundary m /\
     (!k. k IN components (complex_boundary m) /\ ~(k INTER s = {}) ==> k SUBSET s) /\
     DISJOINT s (complex_boundary c)
     ==> two_sided_in (UNIONS c) s`;;

let MOI_FND_BICOLLAR =
 `!(c:(real^N->bool)->bool) (s:(real^N->bool)->bool) v.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE s /\ combinatorial_manifold 2 s /\
     UNIONS s SUBSET UNIONS c DIFF complex_boundary c /\
     two_sided_in (UNIONS c) (UNIONS s) /\
     open_in (subtopology euclidean (UNIONS c)) v /\ UNIONS s SUBSET v
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism
             (UNIONS s PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
           w SUBSET v /\
           UNIONS s SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN UNIONS s ==> p(pastecart x (vec 0)) = x`;;

(* Curves in orientable surfaces are two-sided: annular bicollars (Moise    *)
(* 26.3 for 1-manifolds in 2-manifolds, p.192; 28.7, 28.19).                 *)

let MOI_FND_BICOLLAR_CURVE_2 =
 `!(c:(real^N->bool)->bool) (l:(real^N->bool)->bool) v.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     orientable_surface_complex c /\
     FINITE l /\ combinatorial_manifold 1 l /\
     UNIONS l SUBSET UNIONS c DIFF surface_boundary c /\
     open_in (subtopology euclidean (UNIONS c)) v /\ UNIONS l SUBSET v
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism
             (UNIONS l PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
           w SUBSET v /\
           UNIONS l SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN UNIONS l ==> p(pastecart x (vec 0)) = x`;;

(* T3e. General position.                                                    *)
(* Closed polyhedral surfaces are moved by a small ambient PLH, supported   *)
(* in w, to cross a closed (in w) polyhedral surface t (Moise 31.1 and the  *)
(* canonical configurations p.221, 33.1 Lemma 2 p.231 with t a pseudo-cell  *)
(* minus its rim and centre, 34 Lemmas 3, 5 p.240; DG HasPLCrossingAt,      *)
(* PL/GeneralPosition.lean:2366).                                            *)

let MOI_FND_GP_SURFACES_3 =
 `!(s:(real^3->bool)->bool) (t:(real^3->bool)->bool) w e.
     FINITE s /\ combinatorial_manifold 2 s /\ combinatorial_manifold 2 t /\
     open w /\ UNIONS s SUBSET w /\ UNIONS t SUBSET w /\
     closed_in (subtopology euclidean w) (UNIONS t) /\ &0 < e
     ==> ?f g. pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
               (?k. compact k /\ k SUBSET w /\ !x. ~(x IN k) ==> f x = x) /\
               (!x. dist(f x,x) < e) /\
               !x. x IN IMAGE f (UNIONS s) INTER UNIONS t
                   ==> pl_crossing_at (IMAGE f (UNIONS s)) (UNIONS t) x`;;

(* Polygons in a surface moved to cross other polygons at finitely many     *)
(* true crossing points (Moise 28.2, p.202).                                 *)

let MOI_FND_GP_CURVES_2 =
 `!(c:(real^N->bool)->bool) (j:(real^N->bool)->bool) (k:(real^N->bool)->bool) v e.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     FINITE j /\ combinatorial_manifold 1 j /\
     FINITE k /\ combinatorial_manifold 1 k /\
     UNIONS j SUBSET UNIONS c DIFF surface_boundary c /\
     UNIONS k SUBSET UNIONS c DIFF surface_boundary c /\
     open_in (subtopology euclidean (UNIONS c)) v /\ UNIONS j SUBSET v /\ &0 < e
     ==> ?f g. pl_homeomorphism (UNIONS c,UNIONS c) (f,g) /\
               (!x. x IN UNIONS c DIFF v ==> f x = x) /\
               (!x. x IN UNIONS c ==> dist(f x,x) < e) /\
               FINITE (IMAGE f (UNIONS j) INTER UNIONS k) /\
               !x. x IN IMAGE f (UNIONS j) INTER UNIONS k
                   ==> pl_curve_crossing_at (UNIONS c) (IMAGE f (UNIONS j))
                                            (UNIONS k) x`;;

(* PL maps of polyhedra of dimension at most 2 into real^3, made simplex-   *)
(* wise affine, injective on simplices and in affine general position with  *)
(* a finite complex s, close to f and fixed on a subcomplex k0 already in   *)
(* general position (Moise 26.4 proof (a)-(b) p.193, 26.6 proof (2)-(5)     *)
(* p.194, 33.1 Lemma 10 p.235).                                              *)

let MOI_FND_GP_MAP_3 =
 `!(k:(real^M->bool)->bool) (k0:(real^M->bool)->bool) (s:(real^3->bool)->bool)
   (f:real^M->real^3) e.
     simplicial_complex k /\ simplicial_subcomplex k0 k /\
     (!r. r IN k ==> aff_dim r <= &2) /\
     simplicial_complex s /\ pl_map_on (UNIONS k) f /\
     (!r. r IN k0
          ==> (?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
              (!x y. x IN r /\ y IN r /\ f x = f y ==> x = y) /\
              (!q. q IN s ==> affine_gp_3 (IMAGE f r) q)) /\
     &0 < e
     ==> ?k' f'. simplicial_complex k' /\ subdivides k' k /\
                 (!x. x IN UNIONS k0 ==> f' x = f x) /\
                 (!x. x IN UNIONS k ==> dist(f' x,f x) < e) /\
                 (!r. r IN k'
                      ==> (?l y. linear l /\ !x. x IN r ==> f' x = l x + y) /\
                          (!x y. x IN r /\ y IN r /\ f' x = f' y ==> x = y)) /\
                 (!r q. r IN k' /\ q IN s ==> affine_gp_3 (IMAGE f' r) q)`;;

(* T3f. The splitting operations in real^3.  At a disk (Moise 28.19-28.20,  *)
(* p.209; used by 30.3 p.215, 33.1 Lemmas 3 and 7 pp.231-233, 34            *)
(* Operations 1-2 p.241): j has an annular neighbourhood a in M, and M is   *)
(* replaced by (M - a) plus two disks parallel to d; chi rises by 2; if M   *)
(* bounds a polyhedral 3-manifold x, the new surface bounds x minus or plus *)
(* a thin regular neighbourhood of d.  At an annulus (33.1 Lemma 4, p.232). *)

let MOI_FND_SPLIT_DISK_R3 =
 `!(m:(real^3->bool)->bool) d j v.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     open v /\ d SUBSET v
     ==> ?a j1 j2 d1 d2 (m':(real^3->bool)->bool).
           pl_annulus_with_ends a j1 j2 /\ a SUBSET UNIONS m INTER v /\
           j SUBSET a DIFF (j1 UNION j2) /\
           pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
           d1 SUBSET v /\ d2 SUBSET v /\ DISJOINT d1 d2 /\
           DISJOINT d (d1 UNION d2) /\
           d1 INTER UNIONS m = j1 /\ d2 INTER UNIONS m = j2 /\
           FINITE m' /\ combinatorial_manifold 2 m' /\
           UNIONS m' = (UNIONS m DIFF a) UNION d1 UNION d2 /\
           complex_euler m' = complex_euler m + &2 /\
           !x:(real^3->bool)->bool.
             FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
             frontier (UNIONS x) = UNIONS m
             ==> ?x':(real^3->bool)->bool.
                   FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
                   frontier (UNIONS x') = UNIONS m' /\
                   (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x)
                   SUBSET v /\
                   (d SUBSET UNIONS x
                    ==> UNIONS x' SUBSET UNIONS x /\ DISJOINT d (UNIONS x')) /\
                   (d INTER UNIONS x = j
                    ==> UNIONS x SUBSET UNIONS x' /\ d SUBSET interior (UNIONS x'))`;;

let MOI_FND_SPLIT_ANNULUS_R3 =
 `!(m:(real^3->bool)->bool) a j1 j2 v.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     open v /\ a SUBSET v
     ==> ?a1 a2 b1 b2 k11 k12 k21 k22 (m':(real^3->bool)->bool).
           pl_annulus_with_ends a1 k11 k12 /\ pl_annulus_with_ends a2 k21 k22 /\
           pl_annulus_with_ends b1 k11 k21 /\ pl_annulus_with_ends b2 k12 k22 /\
           a1 SUBSET UNIONS m INTER v /\ a2 SUBSET UNIONS m INTER v /\
           DISJOINT a1 a2 /\
           j1 SUBSET a1 DIFF (k11 UNION k12) /\ j2 SUBSET a2 DIFF (k21 UNION k22) /\
           b1 SUBSET v /\ b2 SUBSET v /\ DISJOINT b1 b2 /\
           DISJOINT a (b1 UNION b2) /\
           b1 INTER UNIONS m = k11 UNION k21 /\ b2 INTER UNIONS m = k12 UNION k22 /\
           FINITE m' /\ combinatorial_manifold 2 m' /\
           UNIONS m' = (UNIONS m DIFF (a1 UNION a2)) UNION b1 UNION b2 /\
           complex_euler m' = complex_euler m /\
           !x:(real^3->bool)->bool.
             FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
             frontier (UNIONS x) = UNIONS m
             ==> ?x':(real^3->bool)->bool.
                   FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
                   frontier (UNIONS x') = UNIONS m' /\
                   (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x)
                   SUBSET v /\
                   (a SUBSET UNIONS x
                    ==> UNIONS x' SUBSET UNIONS x /\ DISJOINT a (UNIONS x')) /\
                   (a INTER UNIONS x = j1 UNION j2
                    ==> UNIONS x SUBSET UNIONS x' /\ a SUBSET interior (UNIONS x'))`;;

map type_of
  [MOI_FND_DERIVED_NBHD_BASIC; MOI_FND_BARYCENTRIC_SUBCOMPLEX;
   MOI_FND_DERIVED_NBHD_SMALL; MOI_FND_GRAPH_IN_COMPLEX_BARYCENTRIC;
   MOI_FND_GRAPH_TUBE; MOI_FND_GRAPH_TUBE_FRONTIER_3; MOI_FND_GRAPH_TUBE_PRODUCT;
   MOI_FND_GRAPH_TUBE_HOLES; MOI_FND_GRAPH_NBHD_EULER;
   MOI_FND_SOLID_TORUS_TRIANGLE; MOI_FND_POLYGON_SOLID_TORUS_3;
   MOI_FND_DERIVED_NBHD_MANIFOLD; MOI_FND_DERIVED_NBHD_RETRACT;
   MOI_FND_DERIVED_NBHD_BALL; MOI_FND_SURFACE_NBHD_SIDES;
   MOI_FND_COLLAR; MOI_FND_TWO_SIDED_BOUNDARY; MOI_FND_BICOLLAR;
   MOI_FND_BICOLLAR_CURVE_2; MOI_FND_GP_SURFACES_3; MOI_FND_GP_CURVES_2;
   MOI_FND_GP_MAP_3; MOI_FND_SPLIT_DISK_R3; MOI_FND_SPLIT_ANNULUS_R3];;

(* ========================================================================= *)
(* T5. Surfaces: Euler characteristic, recognition, pi_1 and H_1 of the     *)
(* models.  Combinatorial surfaces: FINITE c /\ combinatorial_manifold 2 c *)
(* (closed) or combinatorial_manifold_with_boundary 2 c, boundary          *)
(* surface_boundary c (pc_moi_core_stmt.ml).                                *)
(* ========================================================================= *)

(* Additivity (Moise 21.8, p.150): inclusion-exclusion of simplex counts.   *)

let MOI_FND_EULER_UNION =
 `!(c:(real^N->bool)->bool) d.
     FINITE c /\ FINITE d
     ==> complex_euler (c UNION d) =
         complex_euler c + complex_euler d - complex_euler (c INTER d)`;;

(* PL invariance for complexes of dimension at most 2 (Moise 21.4-21.5,     *)
(* 21.9, pp.148-150, via common subdivisions; no Hauptvermutung needed).    *)

let MOI_FND_EULER_PL_INVARIANT =
 `!(c:(real^M->bool)->bool) (d:(real^N->bool)->bool) f g.
     simplicial_complex c /\ simplicial_complex d /\
     (!s. s IN c ==> aff_dim s <= &2) /\ (!s. s IN d ==> aff_dim s <= &2) /\
     pl_homeomorphism (UNIONS c,UNIONS d) (f,g)
     ==> complex_euler c = complex_euler d`;;

(* Values on the standard pieces (Moise 21.6, 21.7, p.149; 22.5).           *)

let MOI_FND_EULER_VALUES =
 `!c:(real^N->bool)->bool.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2)
     ==> (pl_sphere 1 (UNIONS c) ==> complex_euler c = &0) /\
         (pl_ball 1 (UNIONS c) ==> complex_euler c = &1) /\
         (pl_ball 2 (UNIONS c) ==> complex_euler c = &1) /\
         (pl_sphere 2 (UNIONS c) ==> complex_euler c = &2) /\
         (pl_annulus (UNIONS c) ==> complex_euler c = &0) /\
         ((?(f:real^(2,2)finite_sum->real^N) g.
              pl_homeomorphism (pl_torus_model,UNIONS c) (f,g))
          ==> complex_euler c = &0) /\
         (!k. pl_holed_disk k (UNIONS c) ==> complex_euler c = &1 - &k)`;;

(* Recognition (Moise 22.4-22.5, pp.159-161, with 22.1 p.155): a closed     *)
(* connected surface has chi at most 2, with equality exactly for PL        *)
(* 2-spheres.  Users: DOUBLE_COVER (via T8 COCYCLE), LOOP_SPHERE_CASE.       *)

let MOI_FND_SURFACE_SPHERE =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {})
     ==> complex_euler c <= &2 /\
         (complex_euler c = &2 <=> pl_sphere 2 (UNIONS c))`;;

(* Planar surfaces (genus 0; automatically orientable): chi + b <= 2 for a  *)
(* connected compact surface with b boundary components, with equality     *)
(* exactly for disks with b - 1 holes, the PLH carrying the model boundary  *)
(* onto surface_boundary c.  Users: 33.1 Lemmas 12-13 (p.236), 28.6 (p.204), *)
(* 25.1 (p.184, the k-annulus B').                                           *)

let MOI_FND_SURFACE_PLANAR =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     connected (UNIONS c) /\ ~(UNIONS c = {})
     ==> FINITE (components (surface_boundary c)) /\
         complex_euler c + &(CARD (components (surface_boundary c))) <= &2 /\
         !k. CARD (components (surface_boundary c)) = k + 1 /\
             complex_euler c = &1 - &k
             ==> ?(f:real^2->real^N) g.
                   pl_homeomorphism (holed_disk_model k,UNIONS c) (f,g) /\
                   IMAGE f (frontier (holed_disk_model k)) = surface_boundary c`;;

(* Tori (Moise 22.4-22.5 with m = 0, h = 1).  Users: 30.6-30.7 (the        *)
(* separating torus), 28.1.                                                  *)

let MOI_FND_SURFACE_TORUS =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {}) /\ orientable_surface_complex c /\ complex_euler c = &0
     ==> ?(f:real^(2,2)finite_sum->real^N) g.
           pl_homeomorphism (pl_torus_model,UNIONS c) (f,g)`;;

(* The two annulus notions agree (model change), with ends.                  *)

let MOI_FND_HOLED_DISK_ANNULUS =
 `!a:real^N->bool. pl_holed_disk 1 a <=> pl_annulus a`;;

(* 26.8 input (Moise p.195, in the form proved by sides instead of H_3 of  *)
(* S^3): a closed surface in real^3 that is the common frontier of the two *)
(* parts of its complement is orientable.  With 26.6 this gives            *)
(* MOISE_268_STATEMENT (glue MOI_FD_268_GLUE below).                         *)

let MOI_FND_SIDES_ORIENT_R3 =
 `!s:(real^3->bool)->bool.
     FINITE s /\ combinatorial_manifold 2 s /\
     (?i e. open i /\ open e /\ DISJOINT i e /\
            i UNION e = (:real^3) DIFF UNIONS s /\
            frontier i = UNIONS s /\ frontier e = UNIONS s)
     ==> orientable_surface_complex s`;;

(* pi_1 of the models in map form (no group structure): spines and annulus   *)
(* ends carry all loops; loops in the solid torus and torus models are       *)
(* classified by winding numbers of their circle coordinates (real^2 =       *)
(* complex). Users: 30.8, 31.4, 27.3, 28.4-28.10.                            *)

let MOI_FND_LOOPS_SPINE =
 `!(j:real^N->bool) s. spine j s ==> loops_carried j s`;;

let MOI_FND_LOOPS_ANNULUS =
 `!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1 ==> loops_carried j0 a /\ loops_carried j1 a`;;

let MOI_FND_LOOPS_SOLID_TORUS_MODEL =
 `!p:real^1->real^(2,2)finite_sum.
     path p /\ pathfinish p = pathstart p /\
     path_image p SUBSET cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> (homotopic_loops (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                          p (linepath(pathstart p,pathstart p)) <=>
          winding_number(sndcart o p,vec 0) = Cx(&0))`;;

let MOI_FND_LOOPS_TORUS_MODEL =
 `!p:real^1->real^(2,2)finite_sum.
     path p /\ pathfinish p = pathstart p /\
     path_image p SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> (homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                          p (linepath(pathstart p,pathstart p)) <=>
          winding_number(fstcart o p,vec 0) = Cx(&0) /\
          winding_number(sndcart o p,vec 0) = Cx(&0))`;;

(* Integral H_1 (homology.ml; used for 28.8, 28.10 and Sec 34). Solid tori:  *)
(* H_1 is infinite cyclic and the spine induces an iso (so carries_h1).      *)
(* Tori: Z x Z. Free loops carry homology (loops_carried implies             *)
(* carries_h1).                                                              *)

let MOI_FND_H1_SPINE =
 `!(j:real^N->bool) s.
     spine j s
     ==> homology_group(&1,subtopology euclidean s) isomorphic_group integer_group /\
         group_isomorphism (homology_group(&1,subtopology euclidean j),
                            homology_group(&1,subtopology euclidean s))
           (hom_induced (&1) (subtopology euclidean j,{})
                             (subtopology euclidean s,{}) (\x. x)) /\
         carries_h1 j s`;;

let MOI_FND_H1_TORUS =
 `!t:real^N->bool.
     torus_surface t
     ==> homology_group(&1,subtopology euclidean t) isomorphic_group
         prod_group integer_group integer_group`;;

let MOI_FND_LOOPS_CARRIED_H1 =
 `!(j:real^N->bool) s.
     j SUBSET s /\ path_connected s /\ loops_carried j s ==> carries_h1 j s`;;

let MOI_FND_H1_ANNULUS =
 `!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> homology_group(&1,subtopology euclidean a) isomorphic_group integer_group /\
         group_isomorphism (homology_group(&1,subtopology euclidean j0),
                            homology_group(&1,subtopology euclidean a))
           (hom_induced (&1) (subtopology euclidean j0,{})
                             (subtopology euclidean a,{}) (\x. x)) /\
         group_isomorphism (homology_group(&1,subtopology euclidean j1),
                            homology_group(&1,subtopology euclidean a))
           (hom_induced (&1) (subtopology euclidean j1,{})
                             (subtopology euclidean a,{}) (\x. x))`;;

(* Bridges for the PL solid torus model (pl_solid_torus, pc_moi_core_stmt): *)
(* it is a solid torus with a polygonal spine, and in real^3 its frontier is *)
(* a PL torus (invariance of domain).  Users: MOISE_286, MOISE_288,          *)
(* MOISE_2810 (frontier s), 30.8 and 31.4 (spines), 28.1-28.10.             *)

let MOI_FND_PL_SOLID_TORUS_BASIC =
 `(!s:real^N->bool.
      pl_solid_torus s ==> solid_torus s /\ ?j. spine j s /\ pl_sphere 1 j) /\
  (!s:real^3->bool.
      pl_solid_torus s
      ==> ?(f:real^(2,2)finite_sum->real^3) g.
            pl_homeomorphism (pl_torus_model,frontier s) (f,g))`;;

map type_of
  [MOI_FND_EULER_UNION; MOI_FND_EULER_PL_INVARIANT; MOI_FND_EULER_VALUES;
   MOI_FND_SURFACE_SPHERE; MOI_FND_SURFACE_PLANAR; MOI_FND_SURFACE_TORUS;
   MOI_FND_HOLED_DISK_ANNULUS; MOI_FND_SIDES_ORIENT_R3; MOI_FND_LOOPS_SPINE;
   MOI_FND_LOOPS_ANNULUS; MOI_FND_LOOPS_SOLID_TORUS_MODEL;
   MOI_FND_LOOPS_TORUS_MODEL; MOI_FND_H1_SPINE; MOI_FND_H1_TORUS;
   MOI_FND_LOOPS_CARRIED_H1; MOI_FND_H1_ANNULUS; MOI_FND_PL_SOLID_TORUS_BASIC];;

(* ========================================================================= *)
(* T7. Combinatorial 3-manifolds with boundary (Moise Sec 23, pp.165-173).  *)
(* ========================================================================= *)

(* Dimension bound (pure of dimension 3 when there is a vertex).            *)

let MOI_FND_CM_WB_DIM =
 `!c:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 c ==> !s. s IN c ==> aff_dim s <= &3`;;

(* Moise 23.7 and 23.8 (p.168) for complexes in real^3: the combinatorial   *)
(* boundary is the topological boundary; the frontier for finite c.  Users: *)
(* MOI_CORE_GLUE_LOOP3, MOI_PROD_264, 28.1, 30.x, 33.1, SPLIT above.         *)

let MOI_FND_COMPLEX_BOUNDARY_3 =
 `!c:(real^3->bool)->bool.
     combinatorial_manifold_with_boundary 3 c
     ==> complex_boundary c = UNIONS c DIFF interior (UNIONS c) /\
         (FINITE c ==> complex_boundary c = frontier (UNIONS c))`;;

(* Boundary vertices have PL 2-ball links, interior vertices PL 2-sphere    *)
(* links; the boundary complex and each boundary component are closed       *)
(* combinatorial surfaces (Moise 23.3, p.168; DG BoundaryOfBall.lean:156,   *)
(* ManifoldWithBoundary.lean:91).                                            *)

let MOI_FND_BOUNDARY_COMPLEX =
 `!c:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 c
     ==> (!v. {v} IN c
              ==> (v IN complex_boundary c <=>
                   pl_ball 2 (UNIONS (simplicial_link c v))) /\
                  (~(v IN complex_boundary c) <=>
                   pl_sphere 2 (UNIONS (simplicial_link c v)))) /\
         simplicial_subcomplex (boundary_complex c) c /\
         UNIONS (boundary_complex c) = complex_boundary c /\
         combinatorial_manifold 2 (boundary_complex c) /\
         (!b. b IN components (complex_boundary c)
              ==> combinatorial_manifold 2 {s | s IN c /\ s SUBSET b} /\
                  UNIONS {s | s IN c /\ s SUBSET b} = b)`;;

(* PL invariance of combinatorial 3-manifolds with boundary and of their    *)
(* boundary (Moise 23.6-23.7; Rourke-Sanderson 2.21); the boundary of a PL  *)
(* 3-ball is a PL 2-sphere (DG BoundaryOfBall.lean:143).  Users: the cell   *)
(* assembly inputs, MOI_FND_BALL_TRIANGULATION (pc_moi_core_stmt.ml), 33.1. *)

let MOI_FND_COMPLEX_BOUNDARY_PL_INVARIANT =
 `!(c:(real^M->bool)->bool) (d:(real^N->bool)->bool) f g.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE d /\ lf_simplicial_complex d /\
     pl_homeomorphism (UNIONS c,UNIONS d) (f,g)
     ==> combinatorial_manifold_with_boundary 3 d /\
         IMAGE f (complex_boundary c) = complex_boundary d`;;

let MOI_FND_PL_BALL_COMPLEX =
 `!(d:(real^N->bool)->bool) b.
     FINITE d /\ lf_simplicial_complex d /\ pl_cell_with_boundary 3 (UNIONS d) b
     ==> combinatorial_manifold_with_boundary 3 d /\ complex_boundary d = b /\
         pl_sphere 2 b`;;

(* Links of vertices of a retriangulation lying in the open star of an      *)
(* interior vertex are PL 2-spheres (local form of COMBINATORIAL_RETRIAN-   *)
(* GULATION, pc_moi_star).  Users: graph_in_complex for subdivisions        *)
(* (MOI_FND_GRAPH_IN_COMPLEX_BARYCENTRIC, MOI_PROD_34_EXT).                  *)

let MOI_FND_INTERIOR_LINK_RETRIANGULATION =
 `!(t:(real^N->bool)->bool) t' v w.
     lf_simplicial_complex t /\ lf_simplicial_complex t' /\ UNIONS t' = UNIONS t /\
     {v} IN t /\ pl_sphere 2 (UNIONS (simplicial_link t v)) /\
     {w} IN t' /\
     w IN UNIONS {s | s IN t /\ v IN s} DIFF UNIONS (simplicial_link t v)
     ==> pl_sphere 2 (UNIONS (simplicial_link t' w))`;;

(* Orientation (Moise p.170, 23.14-23.17): every complex in real^3 is       *)
(* orientable by the sign of a determinant; orientations restrict to        *)
(* subsets (in particular subcomplexes) and pass to barycentric             *)
(* subdivisions, which also preserve the manifold property and the boundary *)
(* (Moise 23.6 proof, p.168).                                                *)

let MOI_FND_ORIENTABLE_R3 =
 `!c:(real^3->bool)->bool. lf_simplicial_complex c ==> orientable_complex c`;;

let MOI_FND_ORIENTABLE_SUBSET =
 `!(c:(real^N->bool)->bool) k. orientable_complex c /\ k SUBSET c
                               ==> orientable_complex k`;;

let MOI_FND_BARYCENTRIC_CM_WB =
 `!c:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 c
     ==> combinatorial_manifold_with_boundary 3 (barycentric_subdivision c) /\
         complex_boundary (barycentric_subdivision c) = complex_boundary c /\
         (orientable_complex c ==> orientable_complex (barycentric_subdivision c))`;;

(* Transport along injective linear maps (MOI_CORE_GLUE_LOOP3: real^3 into  *)
(* real^7).                                                                  *)

let MOI_FND_LINEAR_IMAGE_COMPLEX =
 `!(f:real^M->real^N) (c:(real^M->bool)->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (lf_simplicial_complex (IMAGE (IMAGE f) c) <=> lf_simplicial_complex c) /\
         (FINITE (IMAGE (IMAGE f) c) <=> FINITE c) /\
         (!n. combinatorial_manifold n (IMAGE (IMAGE f) c) <=>
              combinatorial_manifold n c) /\
         (!n. combinatorial_manifold_with_boundary n (IMAGE (IMAGE f) c) <=>
              combinatorial_manifold_with_boundary n c) /\
         complex_boundary (IMAGE (IMAGE f) c) = IMAGE f (complex_boundary c) /\
         (orientable_complex (IMAGE (IMAGE f) c) <=> orientable_complex c)`;;

map type_of
  [MOI_FND_CM_WB_DIM; MOI_FND_COMPLEX_BOUNDARY_3; MOI_FND_BOUNDARY_COMPLEX;
   MOI_FND_COMPLEX_BOUNDARY_PL_INVARIANT; MOI_FND_PL_BALL_COMPLEX;
   MOI_FND_INTERIOR_LINK_RETRIANGULATION; MOI_FND_ORIENTABLE_R3;
   MOI_FND_ORIENTABLE_SUBSET; MOI_FND_BARYCENTRIC_CM_WB;
   MOI_FND_LINEAR_IMAGE_COMPLEX];;

(* ========================================================================= *)
(* T8. Double covers (Moise 24.6-24.8, pp.177-178; DG DoubleCoverComplex,   *)
(* DoubleCoverExistence.lean:50-98, CoveringTriangulation.lean:532,         *)
(* CoveringLift.lean, HandleCount.lean:46).                                  *)
(* ========================================================================= *)

(* The double cover of a Z/2 cocycle that is not a coboundary: an abstract  *)
(* complex on vertices x bool re-realized in real^N (pc_moi_real,           *)
(* 7 <= dimindex(:N)), simplicial projection, HOL covering_space,        *)
(* fibres of size 2, connected; manifold, boundary and orientation lift.    *)

let MOI_FND_DOUBLE_COVER_OF_COCYCLE =
 `!(c:(real^N->bool)->bool) z.
     7 <= dimindex(:N) /\ FINITE c /\ lf_simplicial_complex c /\
     (!s. s IN c ==> aff_dim s <= &3) /\ connected (UNIONS c) /\
     z2_cocycle c z /\ ~z2_coboundary c z
     ==> ?(c':(real^N->bool)->bool) (q:real^N->real^N).
           FINITE c' /\ lf_simplicial_complex c' /\ connected (UNIONS c') /\
           simplicial_map_on c' c q /\
           (!s. s IN c' ==> !x y. x IN s /\ y IN s /\ q x = q y ==> x = y) /\
           covering_space (UNIONS c',q) (UNIONS c) /\
           (!y. y IN UNIONS c ==> {x | x IN UNIONS c' /\ q x = y} HAS_SIZE 2) /\
           (combinatorial_manifold_with_boundary 3 c
            ==> combinatorial_manifold_with_boundary 3 c' /\
                complex_boundary c' = {x | x IN UNIONS c' /\ q x IN complex_boundary c}) /\
           (orientable_complex c ==> orientable_complex c')`;;

(* Moise 23.19 in Z/2 form (p.172): a non-spherical boundary component     *)
(* forces H^1(c;Z/2) <> 0.  Proof route (no orientation needed over Z/2):  *)
(* chi(boundary) = 2 chi(c) by link counting; Euler-Poincare for Z/2       *)
(* cochains; h^0 = 1, h^3 = 0, h^2 >= (number of boundary components) - 1   *)
(* by pairing with the boundary cycles; chi of each boundary component at  *)
(* most 2, below 2 for a non-sphere (MOI_FND_SURFACE_SPHERE).                *)

let MOI_FND_COCYCLE_NONSPHERE_BOUNDARY =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ connected (UNIONS c) /\
     (?b. b IN components (complex_boundary c) /\ ~pl_sphere 2 b)
     ==> ?z. z2_cocycle c z /\ ~z2_coboundary c z`;;

(* Lifts through simplicial coverings: of simplicial maps of simply         *)
(* connected polyhedra (singular disks in the tower, Moise p.189), and any  *)
(* continuous lift of a PL map is PL.                                        *)

let MOI_FND_COVER_LIFT_SIMPLICIAL =
 `!(c:(real^N->bool)->bool) (c':(real^N->bool)->bool) (q:real^N->real^N)
   (k:(real^M->bool)->bool) (f:real^M->real^N) x0 y0.
     FINITE c /\ lf_simplicial_complex c /\ FINITE c' /\ lf_simplicial_complex c' /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     simplicial_complex k /\ simply_connected (UNIONS k) /\
     locally path_connected (UNIONS k) /\
     simplicial_map_on k c f /\ x0 IN UNIONS k /\ y0 IN UNIONS c' /\ q y0 = f x0
     ==> ?f'. simplicial_map_on k c' f' /\ f' x0 = y0 /\
              !x. x IN UNIONS k ==> q(f' x) = f x`;;

let MOI_FND_COVER_LIFT_PL =
 `!(c:(real^N->bool)->bool) (c':(real^N->bool)->bool) (q:real^N->real^N)
   (u:real^M->bool) (f:real^M->real^N) g.
     FINITE c /\ lf_simplicial_complex c /\ FINITE c' /\ lf_simplicial_complex c' /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     pl_map_on u f /\ g continuous_on u /\ IMAGE g u SUBSET UNIONS c' /\
     (!x. x IN u ==> q(g x) = f x)
     ==> pl_map_on u g`;;

map type_of
  [MOI_FND_DOUBLE_COVER_OF_COCYCLE; MOI_FND_COCYCLE_NONSPHERE_BOUNDARY;
   MOI_FND_COVER_LIFT_SIMPLICIAL; MOI_FND_COVER_LIFT_PL];;

(* ========================================================================= *)
(* F. Moise 26.6 (p.194). MOISE_266_STATEMENT of pc_moi_core_stmt.ml assumes *)
(* UNIONS c nonempty, not just c: the complex containing only the empty      *)
(* simplex is finite, a combinatorial 2-manifold (MOI_FD_CM2_EMPTY_SIMPLEX   *)
(* below), nonempty, with empty (connected) polyhedron, but the complement   *)
(* of the empty set has only one component. The two-sidedness and bicollar   *)
(* facts in real^3 are stated from MOISE_266_STATEMENT.                      *)
(* ========================================================================= *)

(* Two-sidedness and bicollars of closed surfaces in real^3. *)

let MOI_FND_TWO_SIDED_R3 =
 `MOISE_266_STATEMENT
  ==> !s:(real^3->bool)->bool.
        FINITE s /\ combinatorial_manifold 2 s ==> two_sided_in (:real^3) (UNIONS s)`;;

let MOI_FND_BICOLLAR_R3 =
 `MOISE_266_STATEMENT
  ==> !(s:(real^3->bool)->bool) u.
        FINITE s /\ combinatorial_manifold 2 s /\ open u /\ UNIONS s SUBSET u
        ==> ?w (p:real^(3,1)finite_sum->real^3) q.
              pl_homeomorphism
                (UNIONS s PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
              w SUBSET u /\ UNIONS s SUBSET interior w /\
              !x. x IN UNIONS s ==> p(pastecart x (vec 0)) = x`;;

map type_of [MOI_FND_TWO_SIDED_R3; MOI_FND_BICOLLAR_R3];;

(* ========================================================================= *)
(* S. Sanity theorems on the definitions.                                    *)
(* ========================================================================= *)

let MOI_FD_CM2_EMPTY_SIMPLEX = prove
 (`combinatorial_manifold 2 {{}:real^3->bool}`,
  REWRITE_TAC[combinatorial_manifold; lf_simplicial_complex; IN_SING; UNIONS_1;
              NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `-- &1:int` THEN
    REWRITE_TAC[SIMPLEX_EMPTY];
    MESON_TAC[FACE_OF_EMPTY];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[INTER_EMPTY; FACE_OF_EMPTY];
    GEN_TAC THEN REWRITE_TAC[SET_RULE `~({v:real^3} = {})`]]);;

let MOI_FD_DERIVED_NBHD_COMPLEX_EMPTY = prove
 (`!t:(real^N->bool)->bool. derived_nbhd_complex t {} = {}`,
  REWRITE_TAC[derived_nbhd_complex; UNIONS_0; INTER_EMPTY; EMPTY_GSPEC]);;

let MOI_FD_COMPLEX_EULER_EMPTY = prove
 (`complex_euler ({}:(real^N->bool)->bool) = &0`,
  REWRITE_TAC[complex_euler; NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES] THEN
  REWRITE_TAC[REAL_MUL_RZERO; SUM_0]);;

let MOI_FD_Z2_COBOUNDARY_EMPTY = prove
 (`!c:(real^N->bool)->bool. z2_coboundary c {}`,
  GEN_TAC THEN REWRITE_TAC[z2_coboundary] THEN EXISTS_TAC `{}:real^N->bool` THEN
  REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; ODD]);;

let MOI_FD_TWO_SIDED_EMPTY = prove
 (`!x:real^N->bool. two_sided_in x {}`,
  REWRITE_TAC[two_sided_in; COMPONENTS_EMPTY; NOT_IN_EMPTY]);;

let MOI_FD_ORIENTABLE_SUBSET = prove
 (MOI_FND_ORIENTABLE_SUBSET,
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`] THEN
  REWRITE_TAC[orientable_complex; SUBSET] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `sg:real^N->real^N->real^N->real^N->real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a") (LABEL_TAC "b")) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] THEN
    STRIP_TAC THEN REMOVE_THEN "a" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                         `e':real^N`] THEN
    STRIP_TAC THEN REMOVE_THEN "b" MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

let MOI_FD_HOLED_DISK_MODEL_0 = prove
 (`holed_disk_model 0 = interval[vec 0:real^2,vector[&4; &4]]`,
  REWRITE_TAC[holed_disk_model; LT] THEN
  REWRITE_TAC[SET_RULE `{(f:num->real^2->bool) i | i | F} = {}`] THEN
  REWRITE_TAC[UNIONS_0; DIFF_EMPTY] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Glue: the two T8 statements and the dimension bound give                  *)
(* DOUBLE_COVER_STATEMENT (pc_moi_core_stmt.ml).                             *)

let MOI_FD_DOUBLE_COVER_GLUE = prove
 (mk_imp(list_mk_conj [MOI_FND_COCYCLE_NONSPHERE_BOUNDARY;
                       MOI_FND_DOUBLE_COVER_OF_COCYCLE; MOI_FND_CM_WB_DIM],
         `DOUBLE_COVER_STATEMENT (:N)`),
  REWRITE_TAC[DOUBLE_COVER_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "coc") (CONJUNCTS_THEN2
    (LABEL_TAC "cov") (LABEL_TAC "dim"))) THEN
  DISCH_TAC THEN X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REMOVE_THEN "coc" (MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "cov" (MP_TAC o SPECL [`c:(real^N->bool)->bool`;
                                     `z:(real^N->bool)->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold_with_boundary];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':(real^N->bool)->bool`
   (X_CHOOSE_THEN `q:real^N->real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c':(real^N->bool)->bool`; `q:real^N->real^N`] THEN
  ASM_MESON_TAC[]);;

(* Glue: the 26.8 input with MOISE_266_STATEMENT gives MOISE_268_STATEMENT   *)
(* (pc_moi_core_stmt.ml).                                                    *)

let MOI_FD_268_GLUE = prove
 (mk_imp(mk_conj(MOI_FND_SIDES_ORIENT_R3,`MOISE_266_STATEMENT`),
         `MOISE_268_STATEMENT`),
  REWRITE_TAC[MOISE_268_STATEMENT; MOISE_266_STATEMENT] THEN
  STRIP_TAC THEN X_GEN_TAC `c:(real^3->bool)->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `UNIONS c:real^3->bool = {}` THENL
   [REWRITE_TAC[orientable_surface_complex] THEN
    EXISTS_TAC `\(a:real^3) (b:real^3) (d:real^3). &1` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `!s:real^3->bool. s IN c ==> s = {}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [SUBGOAL_THEN `convex hull {a:real^3,b,d} = {}` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `aff_dim(convex hull {a:real^3,b,d}) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      SUBGOAL_THEN `convex hull {a:real^3,b,d} = {}` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `aff_dim(convex hull {a:real^3,b,d}) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^3->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed(UNIONS c:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [combinatorial_manifold]) THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1 o CONJUNCT1) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `open((:real^3) DIFF UNIONS c)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM closed]; ALL_TAC] THEN
  SUBGOAL_THEN `b IN components((:real^3) DIFF UNIONS c) /\
                outside(UNIONS c:real^3->bool) IN components((:real^3) DIFF UNIONS c)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`b:real^3->bool`; `outside(UNIONS c:real^3->bool)`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_COMPONENTS];
    ASM_MESON_TAC[OPEN_COMPONENTS];
    REWRITE_TAC[DISJOINT] THEN ASM_MESON_TAC[COMPONENTS_NONOVERLAP];
    MP_TAC(ISPEC `(:real^3) DIFF UNIONS c` UNIONS_COMPONENTS) THEN
    ASM_REWRITE_TAC[UNIONS_2] THEN MESON_TAC[]]);;

map (fun th -> length (hyp th), concl th)
  [MOI_FD_CM2_EMPTY_SIMPLEX; MOI_FD_DERIVED_NBHD_COMPLEX_EMPTY; MOI_FD_COMPLEX_EULER_EMPTY;
   MOI_FD_Z2_COBOUNDARY_EMPTY; MOI_FD_TWO_SIDED_EMPTY; MOI_FD_ORIENTABLE_SUBSET;
   MOI_FD_HOLED_DISK_MODEL_0; MOI_FD_DOUBLE_COVER_GLUE; MOI_FD_268_GLUE];;

