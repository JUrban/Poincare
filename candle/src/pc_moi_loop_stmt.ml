(* ========================================================================= *)
(* pc_moi_loop_stmt: the statements of the loop theorem (C25: the loop       *)
(* theorem, Moise Secs 24-25): definitions, the statement terms of the loop  *)
(* files and the glue theorems that derive the loop items of the PL core     *)
(* from them.                                                                *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;

(* ========================================================================= *)
(* The C25 loop theorem, file by file. Definitions moi_lt_..., statement     *)
(* terms MOI_LT_... (closed boolean terms, each proved by the loop file      *)
(* named in its comment), glue theorems MOI_LTD_... (the statement terms     *)
(* imply the loop items of pc_moi_core_stmt.ml) and sanity theorems          *)
(* MOI_LTD_SAN_...  Book: Moise GTM 47, Secs 24-25, printed pp.177-190       *)
(* (PDF = printed + 9).                                                      *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* D1. Cellwise simplicial singular disks (the tower, Moise pp.187-190).    *)
(* f is affine on each of finitely many polytopes covering std_triangle and *)
(* maps each of them onto a simplex of c.  Simplicial maps of a             *)
(* triangulation are cellwise; lifts through simplicial covers and          *)
(* restrictions to regular neighbourhoods stay cellwise (the cells are      *)
(* refined), so no source retriangulation is needed in the tower (the book  *)
(* uses restricted barycentric subdivisions instead, p.188).                *)
(* ------------------------------------------------------------------------- *)

let moi_lt_cellwise = new_definition
 `moi_lt_cellwise (f:real^2->real^N) (c:(real^N->bool)->bool) <=>
    ?p. FINITE p /\ UNIONS p = std_triangle /\
        !r. r IN p ==> polytope r /\ IMAGE f r IN c /\
                       ?l y. linear l /\ !x. x IN r ==> f x = l x + y`;;

(* D2. The tower complexity: the number of connected components of the     *)
(* identification set of f in std_triangle x std_triangle.  A lift f2 of f *)
(* through a 2-sheeted cover has a closed-and-open identification set      *)
(* inside that of f, proper when the cover is connected over the image of  *)
(* f (Moise p.189: otherwise the projection would be a homeomorphism on    *)
(* the image); so the complexity drops strictly.  Intrinsic: it does not   *)
(* depend on a triangulation (the book counts identified vertex pairs of a *)
(* fixed source triangulation K(A), p.188).                                 *)

let moi_lt_pairs = new_definition
 `moi_lt_pairs (f:real^2->real^N) =
    {pastecart x y | x IN std_triangle /\ y IN std_triangle /\ f x = f y}`;;

let moi_lt_tower_complexity = new_definition
 `moi_lt_tower_complexity (f:real^2->real^N) = CARD (components (moi_lt_pairs f))`;;

(* D3. Singular disks of Lemma 25.2 (p.184): PL, proper, locally injective, *)
(* at most two-to-one.  The clauses are those of LOOP_DESCENT_STATEMENT.    *)

let moi_lt_singular_disk = new_definition
 `moi_lt_singular_disk (c:(real^N->bool)->bool) (f:real^2->real^N) <=>
    pl_map_on std_triangle f /\ IMAGE f std_triangle SUBSET UNIONS c /\
    {x | x IN std_triangle /\ f x IN complex_boundary c} =
    relative_frontier std_triangle /\
    (!x. x IN std_triangle
         ==> ?n. open n /\ x IN n /\
                 !y z. y IN n INTER std_triangle /\ z IN n INTER std_triangle /\
                       f y = f z ==> y = z) /\
    (!y. FINITE {x | x IN std_triangle /\ f x = y} /\
         CARD {x | x IN std_triangle /\ f x = y} <= 2)`;;

(* D4. Double points (in the image) and the disk complexity m + n of the   *)
(* book (p.184): the number of components of the double image.              *)

let moi_lt_double_image = new_definition
 `moi_lt_double_image (f:real^2->real^N) =
    {y | ?x x'. x IN std_triangle /\ x' IN std_triangle /\ ~(x = x') /\
                f x = y /\ f x' = y}`;;

let moi_lt_disk_complexity = new_definition
 `moi_lt_disk_complexity (f:real^2->real^N) =
    CARD (components (moi_lt_double_image f))`;;

(* D5. Crossing singularities (p.184: the sheets cross like the xy- and    *)
(* xz-planes): a PL chart of the 3-manifold at the double point y, onto the *)
(* unit ball (interior point) or the half ball with the boundary on z3 = 0 *)
(* (boundary point), in which the preimage of the chart splits into two     *)
(* sheets mapped onto the planes z1 = 0 and z2 = 0, and the double image is *)
(* the z3-axis.  At a boundary point the double image is a ray: the         *)
(* endpoint of a double arc (a self-crossing of the boundary curve).        *)

let moi_lt_crossing_at = new_definition
 `moi_lt_crossing_at (c:(real^N->bool)->bool) (f:real^2->real^N) (y:real^N) <=>
    ?u (h:real^N->real^3) h' n1 n2.
       open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
       pl_homeomorphism (u,IMAGE h u) (h,h') /\ h y = vec 0 /\
       ((~(y IN complex_boundary c) /\ u INTER complex_boundary c = {} /\
         IMAGE h u = ball(vec 0,&1)) \/
        (y IN complex_boundary c /\
         IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
         IMAGE h (u INTER complex_boundary c) =
         IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
       {x | x IN std_triangle /\ f x IN u} = n1 UNION n2 /\ DISJOINT n1 n2 /\
       IMAGE (h o f) n1 = IMAGE h u INTER {z:real^3 | z$1 = &0} /\
       IMAGE (h o f) n2 = IMAGE h u INTER {z:real^3 | z$2 = &0} /\
       IMAGE h (moi_lt_double_image f INTER u) =
       IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}`;;

(* D6. Normal singular disks (p.184): singular disks with crossing         *)
(* singularities whose double image is a compact 1-manifold (a finite       *)
(* combinatorial 1-manifold with boundary s: polygons Gamma_i in the        *)
(* interior and broken lines Lambda_j) meeting the boundary of c exactly in *)
(* the endpoints of the arcs.                                               *)

let moi_lt_normal_disk = new_definition
 `moi_lt_normal_disk (c:(real^N->bool)->bool) (f:real^2->real^N) <=>
    moi_lt_singular_disk c f /\
    (?s:(real^N->bool)->bool.
        FINITE s /\ combinatorial_manifold_with_boundary 1 s /\
        UNIONS s = moi_lt_double_image f /\
        !v. {v} IN s
            ==> (pl_ball 0 (UNIONS (simplicial_link s v)) <=>
                 v IN complex_boundary c)) /\
    (!y. y IN moi_lt_double_image f ==> moi_lt_crossing_at c f y)`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_lt_cellwise; moi_lt_pairs; moi_lt_tower_complexity; moi_lt_singular_disk;
   moi_lt_double_image; moi_lt_disk_complexity; moi_lt_crossing_at;
   moi_lt_normal_disk];;

(* ------------------------------------------------------------------------- *)
(* T. The statement terms of the loop files. Each is a closed boolean term   *)
(* (type variables N, M, P only); the loop file named in the comment         *)
(* (lt_cover_a is pc_moi_lt_cova.ml, and so on) proves it, usually as a      *)
(* theorem of the same name without the MOI_LT_ prefix (LT_FILL for          *)
(* MOI_LT_FILL).                                                             *)
(* ------------------------------------------------------------------------- *)

(* lt_fill (Moise p.183 Theorem 2 derivation and p.187: the loop bounds a   *)
(* singular disk; made proper and simplicial into an iterated barycentric   *)
(* subdivision, with the boundary loop homotopic to p inside b).            *)

let MOI_LT_FILL =
 `!(c:(real^N->bool)->bool) b (p:real^1->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c) /\
     path p /\ path_image p SUBSET b /\ pathfinish p = pathstart p /\
     homotopic_loops (UNIONS c) p (linepath(pathstart p,pathstart p))
     ==> ?n (k:(real^2->bool)->bool) (f:real^2->real^N).
           simplicial_complex k /\ UNIONS k = std_triangle /\
           simplicial_map_on k (ITER n barycentric_subdivision c) f /\
           {x | x IN std_triangle /\ f x IN complex_boundary c} =
           relative_frontier std_triangle /\
           homotopic_loops b (f o std_triangle_loop) p`;;

(* lt_nsys (Moise p.187, the first normal system (1)-(4)): re-simplicial-   *)
(* ization along barycentric subdivisions keeping the open carriers, and    *)
(* the regular neighbourhood of the image (derived_nbhd_complex).           *)

let MOI_LT_RESIMPLICIAL =
 `!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f
     ==> ?f'. simplicial_map_on (barycentric_subdivision k)
                                (barycentric_subdivision c) f' /\
              IMAGE f' (UNIONS k) = IMAGE f (UNIONS k) /\
              !x. x IN UNIONS k
                  ==> ?s. s IN c /\ f x IN relative_interior s /\
                          f' x IN relative_interior s`;;

let MOI_LT_NSYS =
 `!(c0:(real^N->bool)->bool) (k:(real^2->bool)->bool) f.
     FINITE c0 /\ combinatorial_manifold_with_boundary 3 c0 /\
     simplicial_complex k /\ UNIONS k = std_triangle /\ simplicial_map_on k c0 f /\
     {x | x IN std_triangle /\ f x IN complex_boundary c0} =
     relative_frontier std_triangle
     ==> ?(c1:(real^N->bool)->bool) (k1:(real^2->bool)->bool) f1.
           FINITE c1 /\ combinatorial_manifold_with_boundary 3 c1 /\
           (orientable_complex c0 ==> orientable_complex c1) /\
           simplicial_complex k1 /\ UNIONS k1 = std_triangle /\
           simplicial_map_on k1 c1 f1 /\
           {x | x IN std_triangle /\ f1 x IN complex_boundary c1} =
           relative_frontier std_triangle /\
           loops_carried (IMAGE f1 std_triangle) (UNIONS c1) /\
           UNIONS c1 SUBSET UNIONS c0 /\
           UNIONS c1 INTER complex_boundary c0 SUBSET complex_boundary c1 /\
           !b. b IN components (complex_boundary c0) /\
               IMAGE f (relative_frontier std_triangle) SUBSET b
               ==> homotopic_loops b (f o std_triangle_loop)
                                     (f1 o std_triangle_loop) /\
                   UNIONS {s | s IN c1 /\ s SUBSET complex_boundary c1 /\
                               ~(s INTER IMAGE f1 (relative_frontier std_triangle) =
                                 {})} SUBSET b`;;

(* lt_sphere (Moise Lemma 25.1, p.183, map form): a boundary curve of the  *)
(* k-annulus neighbourhood of the loop in the sphere b that g does not      *)
(* kill bounds a PL disk in b; its interior is pushed into the interior of *)
(* |c| along a collar.                                                       *)

let MOI_LT_SPHERE_HOLE =
 `!(c:(real^N->bool)->bool) b (cb:(real^N->bool)->bool) (p:real^1->real^N)
    (g:real^N->real^M) (v:real^M->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c) /\ pl_sphere 2 b /\
     cb SUBSET c /\ UNIONS cb SUBSET b /\
     path p /\ pathfinish p = pathstart p /\
     path_image p SUBSET (subtopology euclidean b) interior_of (UNIONS cb) /\
     g continuous_on UNIONS cb /\ IMAGE g (UNIONS cb) SUBSET v /\
     ~homotopic_loops v (g o p) (linepath(g(pathstart p),g(pathstart p)))
     ==> ?(e0:real^2->real^N) e0'.
           pl_homeomorphism (std_triangle,IMAGE e0 std_triangle) (e0,e0') /\
           IMAGE e0 std_triangle SUBSET b /\
           IMAGE e0 (relative_frontier std_triangle) SUBSET UNIONS cb /\
           ~homotopic_loops v (g o e0 o std_triangle_loop)
                              (linepath(g(e0(vec 0)),g(e0(vec 0))))`;;

let MOI_LT_PUSH_IN_DISK =
 `!(c:(real^N->bool)->bool) (e0:real^2->real^N) e0'.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     pl_homeomorphism (std_triangle,IMAGE e0 std_triangle) (e0,e0') /\
     IMAGE e0 std_triangle SUBSET complex_boundary c
     ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
           pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
           d INTER complex_boundary c = IMAGE e (relative_frontier std_triangle) /\
           !x. x IN relative_frontier std_triangle ==> e x = e0 x`;;

(* lt_cover_a (Moise p.189, 24.1, 24.6): simplicial coverings.  Lifts of    *)
(* cellwise maps are cellwise (each cell lifts into one sheet, a simplex);  *)
(* the boundary is the preimage of the boundary; projections of embedded    *)
(* disks are PL, locally injective and at most two-to-one (Lemma 2 input).  *)

let MOI_LT_COVER_LIFT_CELLWISE =
 `!(c:(real^N->bool)->bool) (c':(real^N->bool)->bool) (q:real^N->real^N)
    (f:real^2->real^N).
     FINITE c /\ lf_simplicial_complex c /\ FINITE c' /\ lf_simplicial_complex c' /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     moi_lt_cellwise f c
     ==> ?f2. f2 continuous_on std_triangle /\
              IMAGE f2 std_triangle SUBSET UNIONS c' /\
              (!x. x IN std_triangle ==> q(f2 x) = f x) /\
              moi_lt_cellwise f2 c'`;;

let MOI_LT_COVER_BOUNDARY =
 `!(c:(real^N->bool)->bool) (c':(real^N->bool)->bool) (q:real^N->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE c' /\ combinatorial_manifold_with_boundary 3 c' /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c)
     ==> complex_boundary c' = {x | x IN UNIONS c' /\ q x IN complex_boundary c}`;;

let MOI_LT_DESCENT_INPUT =
 `!(c:(real^N->bool)->bool) (c':(real^N->bool)->bool) (q:real^N->real^N)
    (d2:real^N->bool) (e2:real^2->real^N) e2'.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE c' /\ combinatorial_manifold_with_boundary 3 c' /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     (!y. y IN UNIONS c ==> {x | x IN UNIONS c' /\ q x = y} HAS_SIZE 2) /\
     pl_homeomorphism (std_triangle,d2) (e2,e2') /\ d2 SUBSET UNIONS c'
     ==> pl_map_on std_triangle (q o e2) /\
         IMAGE (q o e2) std_triangle SUBSET UNIONS c /\
         (!x. x IN std_triangle
              ==> ?n. open n /\ x IN n /\
                      !y z. y IN n INTER std_triangle /\ z IN n INTER std_triangle /\
                            (q o e2) y = (q o e2) z ==> y = z) /\
         (!y. FINITE {x | x IN std_triangle /\ (q o e2) x = y} /\
              CARD {x | x IN std_triangle /\ (q o e2) x = y} <= 2)`;;

(* lt_cover_b (Moise pp.188-189): no section of a connected double cover   *)
(* over a set carrying all loops; the complexity drops under lifting; the   *)
(* identification sets of cellwise maps have finitely many components; the  *)
(* next system: the regular neighbourhood of the lifted image (Moise p.189, *)
(* with the second derived neighbourhood instead of the restricted one).    *)

let MOI_LT_NO_SECTION =
 `!(c:(real^N->bool)->bool) (c':(real^N->bool)->bool) (q:real^N->real^N) a.
     FINITE c /\ lf_simplicial_complex c /\ FINITE c' /\ lf_simplicial_complex c' /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     connected (UNIONS c') /\
     (!y. y IN UNIONS c ==> {x | x IN UNIONS c' /\ q x = y} HAS_SIZE 2) /\
     ~(a = {}) /\ a SUBSET UNIONS c /\ loops_carried a (UNIONS c)
     ==> ~(?h. h continuous_on a /\ IMAGE h a SUBSET UNIONS c' /\
               !y. y IN a ==> q(h y) = y)`;;

let MOI_LT_COMPLEXITY_LIFT =
 `!(c':real^N->bool) (q:real^N->real^N) s (f:real^2->real^N) f2.
     covering_space (c',q) s /\
     f continuous_on std_triangle /\ IMAGE f std_triangle SUBSET s /\
     f2 continuous_on std_triangle /\ IMAGE f2 std_triangle SUBSET c' /\
     (!x. x IN std_triangle ==> q(f2 x) = f x) /\
     FINITE (components (moi_lt_pairs f)) /\
     ~(?h. h continuous_on (IMAGE f std_triangle) /\
           IMAGE h (IMAGE f std_triangle) SUBSET c' /\
           !y. y IN IMAGE f std_triangle ==> q(h y) = y)
     ==> moi_lt_tower_complexity f2 < moi_lt_tower_complexity f`;;

let MOI_LT_CELLWISE_FINITE =
 `!(f:real^2->real^N) (c:(real^N->bool)->bool).
     moi_lt_cellwise f c ==> FINITE (components (moi_lt_pairs f))`;;

let MOI_LT_NEXT_SYSTEM =
 `!(c':(real^N->bool)->bool) (f2:real^2->real^N).
     FINITE c' /\ combinatorial_manifold_with_boundary 3 c' /\
     moi_lt_cellwise f2 c'
     ==> ?c2:(real^N->bool)->bool.
           FINITE c2 /\ combinatorial_manifold_with_boundary 3 c2 /\
           (orientable_complex c' ==> orientable_complex c2) /\
           moi_lt_cellwise f2 c2 /\
           UNIONS c2 SUBSET UNIONS c' /\
           IMAGE f2 std_triangle SUBSET UNIONS c2 /\
           loops_carried (IMAGE f2 std_triangle) (UNIONS c2) /\
           ?fr. closed fr /\ fr INTER IMAGE f2 std_triangle = {} /\
                complex_boundary c2 = fr UNION (UNIONS c2 INTER complex_boundary c')`;;

(* lt_tower (Moise pp.187-190): a simplicial normal system is a cellwise   *)
(* buffered one; the sphere case of a buffered system (Lemma 25.1 after a   *)
(* fine subdivision, so that a subcomplex neighbourhood fits inside b1).    *)

let MOI_LT_FROZEN_TO_CELL =
 `!(c:(real^N->bool)->bool) (k:(real^2->bool)->bool) (f:real^2->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     simplicial_complex k /\ UNIONS k = std_triangle /\ simplicial_map_on k c f /\
     {x | x IN std_triangle /\ f x IN complex_boundary c} =
     relative_frontier std_triangle
     ==> moi_lt_cellwise f c /\
         closed (UNIONS {s | s IN c /\ s SUBSET complex_boundary c /\
                             ~(s INTER IMAGE f (relative_frontier std_triangle) = {})}) /\
         IMAGE f (relative_frontier std_triangle) SUBSET
         (subtopology euclidean (complex_boundary c)) interior_of
         (UNIONS {s | s IN c /\ s SUBSET complex_boundary c /\
                      ~(s INTER IMAGE f (relative_frontier std_triangle) = {})})`;;

let MOI_LT_SPHERE_STEP =
 `!(u:N->bool) (w:M->bool).
     LOOP_SPHERE_CASE_STATEMENT u w
     ==> !(c:(real^N->bool)->bool) (f:real^2->real^N) b1 (g:real^N->real^M) v b.
           FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
           moi_lt_cellwise f c /\
           {x | x IN std_triangle /\ f x IN complex_boundary c} =
           relative_frontier std_triangle /\
           b1 SUBSET complex_boundary c /\ closed b1 /\
           IMAGE f (relative_frontier std_triangle) SUBSET
           (subtopology euclidean (complex_boundary c)) interior_of b1 /\
           g continuous_on b1 /\ IMAGE g b1 SUBSET v /\
           ~homotopic_loops v (g o f o std_triangle_loop)
                              (linepath(g(f(vec 0)),g(f(vec 0)))) /\
           b IN components (complex_boundary c) /\
           IMAGE f (relative_frontier std_triangle) SUBSET b /\ pl_sphere 2 b
           ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
                 pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
                 d INTER complex_boundary c =
                 IMAGE e (relative_frontier std_triangle) /\
                 IMAGE e (relative_frontier std_triangle) SUBSET b1 /\
                 ~homotopic_loops v (g o e o std_triangle_loop)
                                    (linepath(g(e(vec 0)),g(e(vec 0))))`;;

(* lt_gp_a, lt_gp_b, lt_gp_c (Moise p.184, general position of D):        *)
(* simplicial after subdivision (singular disks are then injective on each  *)
(* simplex); PL charts of finite combinatorial 3-manifolds with boundary;   *)
(* the perturbation to crossing singularities; crossings everywhere give a *)
(* normal disk (the double image is a compact PL 1-manifold).               *)

let MOI_LT_GP_SIMPLICIAL =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N).
     FINITE c /\ lf_simplicial_complex c /\ moi_lt_singular_disk c f
     ==> ?(t:(real^N->bool)->bool) (k:(real^2->bool)->bool).
           FINITE t /\ lf_simplicial_complex t /\ subdivides t c /\
           simplicial_complex k /\ UNIONS k = std_triangle /\
           simplicial_map_on k t f`;;

let MOI_LT_MANIFOLD_CHARTS =
 `!(c:(real^N->bool)->bool) y e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ y IN UNIONS c /\ &0 < e
     ==> ?u (h:real^N->real^3) h'.
           open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
           u SUBSET ball(y,e) /\
           pl_homeomorphism (u,IMAGE h u) (h,h') /\ h y = vec 0 /\
           ((~(y IN complex_boundary c) /\ u INTER complex_boundary c = {} /\
             IMAGE h u = ball(vec 0,&1)) \/
            (y IN complex_boundary c /\
             IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
             IMAGE h (u INTER complex_boundary c) =
             IMAGE h u INTER {z:real^3 | z$3 = &0}))`;;

let MOI_LT_GP_CROSSINGS =
 `!(c:(real^N->bool)->bool) (t:(real^N->bool)->bool) (k:(real^2->bool)->bool)
    (f:real^2->real^N) w.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE t /\ lf_simplicial_complex t /\ subdivides t c /\
     simplicial_complex k /\ UNIONS k = std_triangle /\ simplicial_map_on k t f /\
     moi_lt_singular_disk c f /\
     open_in (subtopology euclidean (complex_boundary c)) w /\
     IMAGE f (relative_frontier std_triangle) SUBSET w
     ==> ?f'. moi_lt_singular_disk c f' /\
              (!y. y IN moi_lt_double_image f' ==> moi_lt_crossing_at c f' y) /\
              IMAGE f' (relative_frontier std_triangle) SUBSET w /\
              homotopic_loops w (f o std_triangle_loop) (f' o std_triangle_loop)`;;

let MOI_LT_CROSSINGS_NORMAL =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_singular_disk c f /\
     (!y. y IN moi_lt_double_image f ==> moi_lt_crossing_at c f y)
     ==> moi_lt_normal_disk c f`;;

(* The combined statement of lt_gp_a-c (glue MOI_LTD_GP below).          *)

let MOI_LT_GENERAL_POSITION =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N) w.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_singular_disk c f /\
     open_in (subtopology euclidean (complex_boundary c)) w /\
     IMAGE f (relative_frontier std_triangle) SUBSET w
     ==> ?f'. moi_lt_normal_disk c f' /\
              IMAGE f' (relative_frontier std_triangle) SUBSET w /\
              homotopic_loops w (f o std_triangle_loop) (f' o std_triangle_loop)`;;

(* lt_cut_a (Moise p.185, Cases 1-2): a closed double curve is removed     *)
(* without changing the boundary map (Case 1 cannot occur when c is        *)
(* orientable: the monodromy of the crossing along Gamma would be a         *)
(* reflection, a solid Klein bottle; Case 2: the disk inside an innermost   *)
(* double polygon replaces the disk inside its partner, pushed off).        *)

let MOI_LT_CUT_CLOSED =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ orientable_complex c /\
     moi_lt_normal_disk c f /\
     (?k. k IN components (moi_lt_double_image f) /\
          k INTER complex_boundary c = {})
     ==> ?f'. moi_lt_normal_disk c f' /\
              moi_lt_disk_complexity f' < moi_lt_disk_complexity f /\
              !x. x IN relative_frontier std_triangle ==> f' x = f x`;;

(* lt_cut_b (Moise pp.185-187, Cases 3-4): cutting |D| apart at a double   *)
(* arc gives the two normal disks D_1, D_2; their boundary loops are words  *)
(* in the four arcs s1 = sigma, s2 = tau, s3 = nu, s4 = phi of L (the four  *)
(* paths with domains s, t, u, v of Figures 25.3 and 25.5).  Case 3:        *)
(* L_1 = sigma nu^-1, L_2 = sigma phi nu tau; Case 4: L_1 = sigma nu,       *)
(* L_2 = sigma tau^-1 nu phi^-1 (book's notation; p.186 prints v for nu).   *)

let MOI_LT_CUT_ARC_SPLIT =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ orientable_complex c /\
     moi_lt_normal_disk c f /\
     (?k. k IN components (moi_lt_double_image f) /\
          ~(k INTER complex_boundary c = {}))
     ==> ?f1 f2 (s1:real^1->real^N) s2 s3 s4.
           moi_lt_normal_disk c f1 /\ moi_lt_normal_disk c f2 /\
           moi_lt_disk_complexity f1 < moi_lt_disk_complexity f /\
           moi_lt_disk_complexity f2 < moi_lt_disk_complexity f /\
           path s1 /\ path s2 /\ path s3 /\ path s4 /\
           path_image s1 SUBSET IMAGE f (relative_frontier std_triangle) /\
           path_image s2 SUBSET IMAGE f (relative_frontier std_triangle) /\
           path_image s3 SUBSET IMAGE f (relative_frontier std_triangle) /\
           path_image s4 SUBSET IMAGE f (relative_frontier std_triangle) /\
           pathfinish s1 = pathstart s2 /\ pathfinish s2 = pathstart s3 /\
           pathfinish s3 = pathstart s4 /\ pathfinish s4 = pathstart s1 /\
           homotopic_loops (IMAGE f (relative_frontier std_triangle))
             (f o std_triangle_loop) (s1 ++ s2 ++ s3 ++ s4) /\
           ((pathstart s3 = pathstart s1 /\ pathfinish s3 = pathfinish s1 /\
             homotopic_loops (IMAGE f (relative_frontier std_triangle))
               (f1 o std_triangle_loop) (s1 ++ reversepath s3) /\
             homotopic_loops (IMAGE f (relative_frontier std_triangle))
               (f2 o std_triangle_loop) (s1 ++ s4 ++ s3 ++ s2)) \/
            (pathfinish s2 = pathstart s2 /\ pathfinish s4 = pathstart s4 /\
             homotopic_loops (IMAGE f (relative_frontier std_triangle))
               (f1 o std_triangle_loop) (s1 ++ s3) /\
             homotopic_loops (IMAGE f (relative_frontier std_triangle))
               (f2 o std_triangle_loop)
               (s1 ++ reversepath s2 ++ s3 ++ reversepath s4)))`;;

(* lt_cut_c (Moise p.186, the two cancellation identities, in map form):   *)
(* if both cut loops are null-homotopic then so is L.                       *)

let MOI_LT_WORD_3 =
 `!(s:real^M->bool) (s1:real^1->real^M) s2 s3 s4.
     path s1 /\ path s2 /\ path s3 /\ path s4 /\
     path_image s1 SUBSET s /\ path_image s2 SUBSET s /\
     path_image s3 SUBSET s /\ path_image s4 SUBSET s /\
     pathfinish s1 = pathstart s2 /\ pathfinish s2 = pathstart s3 /\
     pathfinish s3 = pathstart s4 /\ pathfinish s4 = pathstart s1 /\
     pathstart s3 = pathstart s1 /\ pathfinish s3 = pathfinish s1 /\
     homotopic_loops s (s1 ++ reversepath s3)
                       (linepath(pathstart s1,pathstart s1)) /\
     homotopic_loops s (s1 ++ s4 ++ s3 ++ s2)
                       (linepath(pathstart s1,pathstart s1))
     ==> homotopic_loops s (s1 ++ s2 ++ s3 ++ s4)
                           (linepath(pathstart s1,pathstart s1))`;;

let MOI_LT_WORD_4 =
 `!(s:real^M->bool) (s1:real^1->real^M) s2 s3 s4.
     path s1 /\ path s2 /\ path s3 /\ path s4 /\
     path_image s1 SUBSET s /\ path_image s2 SUBSET s /\
     path_image s3 SUBSET s /\ path_image s4 SUBSET s /\
     pathfinish s1 = pathstart s2 /\ pathfinish s2 = pathstart s3 /\
     pathfinish s3 = pathstart s4 /\ pathfinish s4 = pathstart s1 /\
     pathfinish s2 = pathstart s2 /\ pathfinish s4 = pathstart s4 /\
     homotopic_loops s (s1 ++ s3) (linepath(pathstart s1,pathstart s1)) /\
     homotopic_loops s (s1 ++ reversepath s2 ++ s3 ++ reversepath s4)
                       (linepath(pathstart s1,pathstart s1))
     ==> homotopic_loops s (s1 ++ s2 ++ s3 ++ s4)
                           (linepath(pathstart s1,pathstart s1))`;;

(* The source double set of a normal disk is a properly embedded compact   *)
(* PL 1-manifold in std_triangle (polygons and chords; shared by lt_cut_a   *)
(* and lt_cut_b for the innermost-polygon and chord arguments).            *)

let MOI_LT_SOURCE_STRUCTURE =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ moi_lt_normal_disk c f
     ==> ?s:(real^2->bool)->bool.
           FINITE s /\ combinatorial_manifold_with_boundary 1 s /\
           UNIONS s = {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
           !v. {v} IN s
               ==> (pl_ball 0 (UNIONS (simplicial_link s v)) <=>
                    v IN relative_frontier std_triangle)`;;

(* The combined statement of lt_cut_b and lt_cut_c (glue MOI_LTD_CUT_ARC). *)

let MOI_LT_CUT_ARC =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ orientable_complex c /\
     moi_lt_normal_disk c f /\
     (?k. k IN components (moi_lt_double_image f) /\
          ~(k INTER complex_boundary c = {}))
     ==> ?f1 f2. moi_lt_normal_disk c f1 /\ moi_lt_normal_disk c f2 /\
                 moi_lt_disk_complexity f1 < moi_lt_disk_complexity f /\
                 moi_lt_disk_complexity f2 < moi_lt_disk_complexity f /\
                 IMAGE f1 (relative_frontier std_triangle) SUBSET
                 IMAGE f (relative_frontier std_triangle) /\
                 IMAGE f2 (relative_frontier std_triangle) SUBSET
                 IMAGE f (relative_frontier std_triangle) /\
                 !(g:real^N->real^M) v.
                    g continuous_on IMAGE f (relative_frontier std_triangle) /\
                    IMAGE g (IMAGE f (relative_frontier std_triangle)) SUBSET v /\
                    homotopic_loops v (g o f1 o std_triangle_loop)
                                      (linepath(g(f1(vec 0)),g(f1(vec 0)))) /\
                    homotopic_loops v (g o f2 o std_triangle_loop)
                                      (linepath(g(f2(vec 0)),g(f2(vec 0))))
                    ==> homotopic_loops v (g o f o std_triangle_loop)
                                          (linepath(g(f(vec 0)),g(f(vec 0))))`;;

map type_of
  [MOI_LT_FILL; MOI_LT_RESIMPLICIAL; MOI_LT_NSYS; MOI_LT_SPHERE_HOLE;
   MOI_LT_PUSH_IN_DISK; MOI_LT_COVER_LIFT_CELLWISE; MOI_LT_COVER_BOUNDARY;
   MOI_LT_DESCENT_INPUT; MOI_LT_NO_SECTION; MOI_LT_COMPLEXITY_LIFT;
   MOI_LT_CELLWISE_FINITE; MOI_LT_NEXT_SYSTEM; MOI_LT_FROZEN_TO_CELL;
   MOI_LT_SPHERE_STEP; MOI_LT_GP_SIMPLICIAL; MOI_LT_MANIFOLD_CHARTS;
   MOI_LT_GP_CROSSINGS; MOI_LT_CROSSINGS_NORMAL; MOI_LT_GENERAL_POSITION;
   MOI_LT_CUT_CLOSED; MOI_LT_CUT_ARC_SPLIT; MOI_LT_WORD_3; MOI_LT_WORD_4;
   MOI_LT_SOURCE_STRUCTURE; MOI_LT_CUT_ARC];;

(* ------------------------------------------------------------------------- *)
(* Second-level split of lt_cut_a (Moise p.185, Case 2; Case 1 excluded by  *)
(* orientability): lt_cut_a1 finds an innermost double polygon j1 whose     *)
(* partner j2 is disjoint from the disk bounded by j1; lt_cut_a2 swaps the  *)
(* disk bounded by j2 for a pushed-off copy of the disk bounded by j1.      *)
(* ------------------------------------------------------------------------- *)

let MOI_LT_CUT_INNERMOST =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ orientable_complex c /\
     moi_lt_normal_disk c f /\
     (?k. k IN components (moi_lt_double_image f) /\
          k INTER complex_boundary c = {})
     ==> ?k (j1:real^2->bool) j2.
           k IN components (moi_lt_double_image f) /\
           k INTER complex_boundary c = {} /\
           pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ DISJOINT j1 j2 /\
           {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\
           j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle /\
           j2 UNION inside j2 SUBSET std_triangle DIFF relative_frontier std_triangle /\
           {x | x IN inside j1 /\ f x IN moi_lt_double_image f} = {} /\
           DISJOINT j2 (inside j1)`;;

let MOI_LT_CUT_SWAP =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N) k (j1:real^2->bool) j2.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_normal_disk c f /\
     k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {} /\
     pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ DISJOINT j1 j2 /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\
     j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     j2 UNION inside j2 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     {x | x IN inside j1 /\ f x IN moi_lt_double_image f} = {} /\
     DISJOINT j2 (inside j1)
     ==> ?f'. moi_lt_normal_disk c f' /\
              moi_lt_disk_complexity f' < moi_lt_disk_complexity f /\
              !x. x IN relative_frontier std_triangle ==> f' x = f x`;;

map type_of [MOI_LT_CUT_INNERMOST; MOI_LT_CUT_SWAP];;


(* ------------------------------------------------------------------------- *)
(* H. Helper lemmas for the glue (the standard triangle, its boundary loop, *)
(* constant loops).                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_STD_TRIANGLE_NONCOLLINEAR = prove
 (`~collinear {vec 0:real^2, basis 1, basis 2}`,
  REWRITE_TAC[COLLINEAR_3_2D; VEC_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let MOI_LTD_STD_TRIANGLE_SIMPLEX = prove
 (`&2 simplex std_triangle`,
  REWRITE_TAC[std_triangle] THEN MATCH_MP_TAC SIMPLEX_CONVEX_HULL THEN
  MP_TAC MOI_LTD_STD_TRIANGLE_NONCOLLINEAR THEN
  REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `CARD {vec 0:real^2, basis 1, basis 2} = 3` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    INT_ARITH_TAC]);;

let MOI_LTD_STD_TRIANGLE_BASIC = prove
 (`compact std_triangle /\ convex std_triangle /\ polytope std_triangle /\
   ~(std_triangle = {}) /\ vec 0 IN std_triangle /\
   simply_connected std_triangle /\ locally path_connected std_triangle /\
   connected std_triangle /\ closed std_triangle /\
   locally_polyhedral std_triangle /\ pl_polyhedron std_triangle`,
  SUBGOAL_THEN `polytope std_triangle /\ convex std_triangle /\
                vec 0 IN std_triangle` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[std_triangle; CONVEX_CONVEX_HULL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CLOSED;
               CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_IMP_LOCALLY_PATH_CONNECTED;
               CONVEX_CONNECTED; LOCALLY_POLYHEDRAL_POLYTOPE] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{std_triangle}` THEN
  ASM_REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN ASM_MESON_TAC[]);;

let MOI_LTD_STD_TRIANGLE_FRONTIER = prove
 (`relative_frontier std_triangle =
   segment[vec 0:real^2,basis 1] UNION segment[basis 1,basis 2] UNION
   segment[basis 2,vec 0]`,
  REWRITE_TAC[std_triangle] THEN MATCH_MP_TAC RELATIVE_FRONTIER_OF_TRIANGLE THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_NONCOLLINEAR]);;

let MOI_LTD_STD_TRIANGLE_LOOP = prove
 (`path std_triangle_loop /\
   pathstart std_triangle_loop = vec 0 /\ pathfinish std_triangle_loop = vec 0 /\
   path_image std_triangle_loop = relative_frontier std_triangle`,
  REWRITE_TAC[std_triangle_loop; MOI_LTD_STD_TRIANGLE_FRONTIER] THEN
  SIMP_TAC[PATH_JOIN; PATH_LINEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_JOIN;
           PATH_IMAGE_LINEPATH]);;

let MOI_LTD_FRONTIER_SUBSET_TRIANGLE = prove
 (`relative_frontier std_triangle SUBSET std_triangle /\
   ~(relative_frontier std_triangle = {}) /\
   vec 0 IN relative_frontier std_triangle /\
   compact (relative_frontier std_triangle) /\
   path_connected (relative_frontier std_triangle)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    MESON_TAC[MOI_LTD_STD_TRIANGLE_BASIC; CLOSURE_CLOSED; SUBSET_DIFF];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^2` THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER; IN_UNION; ENDS_IN_SEGMENT];
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER; IN_UNION; ENDS_IN_SEGMENT];
    MESON_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED; COMPACT_IMP_BOUNDED;
              MOI_LTD_STD_TRIANGLE_BASIC];
    MESON_TAC[PATH_CONNECTED_PATH_IMAGE; MOI_LTD_STD_TRIANGLE_LOOP]]);;

(* Composites of the boundary loop with maps defined on the triangle.       *)

let MOI_LTD_LOOP_COMPOSE = prove
 (`!(f:real^2->real^N).
     f continuous_on std_triangle
     ==> path (f o std_triangle_loop) /\
         pathstart (f o std_triangle_loop) = f(vec 0) /\
         pathfinish (f o std_triangle_loop) = f(vec 0) /\
         path_image (f o std_triangle_loop) =
         IMAGE f (relative_frontier std_triangle)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE;
              MOI_LTD_STD_TRIANGLE_LOOP] THEN
  MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_LOOP] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; MOI_LTD_FRONTIER_SUBSET_TRIANGLE]);;

(* A loop null-homotopic to some constant is null-homotopic to the constant *)
(* at its own start.                                                         *)

let MOI_LTD_LOOP_NULL_BASE = prove
 (`!s (p:real^1->real^N) a.
     homotopic_loops s p (linepath(a,a))
     ==> homotopic_loops s p (linepath(pathstart p,pathstart p))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL) THEN
  DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ASM_MESON_TAC[HOMOTOPIC_LOOPS_IMP_LOOP]);;

let MOI_LTD_LOOP_NULL_ANY = prove
 (`!s (p:real^1->real^N) a b.
     homotopic_loops s p (linepath(a,a)) /\ b = pathstart p
     ==> homotopic_loops s p (linepath(b,b))`,
  MESON_TAC[MOI_LTD_LOOP_NULL_BASE]);;

(* Maps that agree on the boundary of the triangle have the same boundary  *)
(* loops (on [0,1]).                                                          *)

let MOI_LTD_LOOP_EQ = prove
 (`!(f:real^2->real^N) g s.
     f continuous_on std_triangle /\
     IMAGE f (relative_frontier std_triangle) SUBSET s /\
     (!x. x IN relative_frontier std_triangle ==> f x = g x)
     ==> homotopic_loops s (f o std_triangle_loop) (g o std_triangle_loop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LTD_LOOP_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[GSYM MOI_LTD_STD_TRIANGLE_LOOP; path_image] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More helpers: boundary loops of maps continuous on the boundary only.    *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_LOOP_COMPOSE_RF = prove
 (`!(f:real^2->real^N).
     f continuous_on relative_frontier std_triangle
     ==> path (f o std_triangle_loop) /\
         pathstart (f o std_triangle_loop) = f(vec 0) /\
         pathfinish (f o std_triangle_loop) = f(vec 0) /\
         path_image (f o std_triangle_loop) =
         IMAGE f (relative_frontier std_triangle)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE;
              MOI_LTD_STD_TRIANGLE_LOOP] THEN
  MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_LOOP]);;

let MOI_LTD_LOOP_EQ_RF = prove
 (`!(f:real^2->real^N) g s.
     f continuous_on relative_frontier std_triangle /\
     IMAGE f (relative_frontier std_triangle) SUBSET s /\
     (!x. x IN relative_frontier std_triangle ==> f x = g x)
     ==> homotopic_loops s (f o std_triangle_loop) (g o std_triangle_loop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LTD_LOOP_COMPOSE_RF) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[GSYM MOI_LTD_STD_TRIANGLE_LOOP; path_image] THEN
  ASM SET_TAC[]);;

(* Pointwise agreement on the boundary gives equal images of the boundary.  *)

let MOI_LTD_IMAGE_EQ_RF = prove
 (`!(f:real^2->real^N) g.
     (!x. x IN relative_frontier std_triangle ==> f x = g x)
     ==> IMAGE f (relative_frontier std_triangle) =
         IMAGE g (relative_frontier std_triangle)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* G1. Lemma 25.1 (LOOP_SPHERE_CASE_STATEMENT) from the two lt_sphere        *)
(* statements.                                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_SPHERE = prove
 (mk_imp(mk_conj(MOI_LT_SPHERE_HOLE,MOI_LT_PUSH_IN_DISK),
         `!(u:N->bool) (w:M->bool). LOOP_SPHERE_CASE_STATEMENT u w`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "HOLE") (LABEL_TAC "PUSH")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOP_SPHERE_CASE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `b:real^N->bool`; `cb:(real^N->bool)->bool`;
    `p:real^1->real^N`; `g:real^N->real^M`; `v:real^M->bool`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "HOLE" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `b:real^N->bool`; `cb:(real^N->bool)->bool`;
    `p:real^1->real^N`; `g:real^N->real^M`; `v:real^M->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^2->real^N`
   (X_CHOOSE_THEN `e0':real^N->real^2` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "PUSH" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `e0:real^2->real^N`; `e0':real^N->real^2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  MAP_EVERY (fun t -> MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t)
   [`d:real^N->bool`; `e:real^2->real^N`; `e':real^N->real^2`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LTD_IMAGE_EQ_RF) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^2->real^N) (vec 0) = (e0:real^2->real^N) (vec 0)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops v ((g:real^N->real^M) o (e0:real^2->real^N) o std_triangle_loop)
                      (g o (e:real^2->real^N) o std_triangle_loop)`
  MP_TAC THENL
   [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC MOI_LTD_LOOP_EQ_RF THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `std_triangle` THEN
        REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE] THEN
        ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
      REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
      ASM_SIMP_TAC[o_THM]];
    ALL_TAC] THEN
  ASM_MESON_TAC[HOMOTOPIC_LOOPS_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* G2. The combined general position statement of lt_gp_a, lt_gp_b and    *)
(* lt_gp_c.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_GP = prove
 (mk_imp(list_mk_conj[MOI_LT_GP_SIMPLICIAL; MOI_LT_GP_CROSSINGS;
                      MOI_LT_CROSSINGS_NORMAL],
         MOI_LT_GENERAL_POSITION),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SIMP")
   (CONJUNCTS_THEN2 (LABEL_TAC "CROSS") (LABEL_TAC "NORM"))) THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "SIMP" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool`
   (X_CHOOSE_THEN `k:(real^2->bool)->bool` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "CROSS" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
    `k:(real^2->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':real^2->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "NORM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transfer of null-homotopy along a homotopy of loops pushed forward by g. *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_NULL_TRANSFER = prove
 (`!(l:real^N->bool) (g:real^N->real^M) v p q a.
     homotopic_loops l p q /\ g continuous_on l /\ IMAGE g l SUBSET v /\
     homotopic_loops v (g o p) (linepath(a,a))
     ==> homotopic_loops v (g o q) (linepath(pathstart (g o q),pathstart (g o q)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LTD_LOOP_NULL_BASE THEN
  EXISTS_TAC `a:real^M` THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(g:real^N->real^M) o (p:real^1->real^N)` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
  EXISTS_TAC `l:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_LTD_PATH_IMAGE_IN = prove
 (`!(g:real^N->real^M) l v (s:real^1->real^N).
     path s /\ path_image s SUBSET l /\ g continuous_on l /\ IMAGE g l SUBSET v
     ==> path (g o s) /\ path_image (g o s) SUBSET v`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* G3. The cut at a double arc in map form, from lt_cut_b (the cut and the  *)
(* boundary words) and lt_cut_c (the two cancellation identities).          *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_CUT_ARC = prove
 (mk_imp(list_mk_conj[MOI_LT_CUT_ARC_SPLIT; MOI_LT_WORD_3; MOI_LT_WORD_4],
         MOI_LT_CUT_ARC),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SPLIT")
   (CONJUNCTS_THEN2 (LABEL_TAC "W3") (LABEL_TAC "W4"))) THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
  DISCH_TAC THEN
  REMOVE_THEN "SPLIT" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun t -> DISCH_THEN(X_CHOOSE_THEN t MP_TAC))
   [`f1:real^2->real^N`; `f2:real^2->real^N`; `s1:real^1->real^N`;
    `s2:real^1->real^N`; `s3:real^1->real^N`; `s4:real^1->real^N`] THEN
  ABBREV_TAC `l = IMAGE (f:real^2->real^N) (relative_frontier std_triangle)` THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN MAP_EVERY EXISTS_TAC [`f1:real^2->real^N`; `f2:real^2->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the boundary images of the cut disks lie in l *)
  SUBGOAL_THEN
   `!h:real^2->real^N q. homotopic_loops l (h o std_triangle_loop) q
                         ==> IMAGE h (relative_frontier std_triangle) SUBSET l`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
    REWRITE_TAC[PATH_IMAGE_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->real^M`; `v:real^M->bool`] THEN
  STRIP_TAC THEN
  (* paths pushed forward by g *)
  SUBGOAL_THEN
   `path ((g:real^N->real^M) o (s1:real^1->real^N)) /\ path (g o s2) /\
    path (g o s3) /\ path (g o s4) /\
    path_image (g o s1) SUBSET v /\ path_image (g o s2) SUBSET v /\
    path_image (g o s3) SUBSET v /\ path_image (g o s4) SUBSET v`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LTD_PATH_IMAGE_IN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pathfinish ((g:real^N->real^M) o (s1:real^1->real^N)) = pathstart (g o s2) /\
    pathfinish (g o s2) = pathstart (g o s3) /\
    pathfinish (g o s3) = pathstart (g o s4) /\
    pathfinish (g o s4) = pathstart (g o s1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE]; ALL_TAC] THEN
  (* it suffices to kill the four-arc word *)
  SUBGOAL_THEN
   `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++
                       (g o s2) ++ (g o s3) ++ (g o s4))
                      (linepath(pathstart (g o s1),pathstart (g o s1)))`
  ASSUME_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL
     [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
      `(s1:real^1->real^N) ++ s2 ++ s3 ++ s4`;
      `(f:real^2->real^N) o std_triangle_loop`;
      `pathstart ((g:real^N->real^M) o (s1:real^1->real^N))`]
     MOI_LTD_NULL_TRANSFER) THEN
    ASM_REWRITE_TAC[PATH_COMPOSE_JOIN] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[HOMOTOPIC_LOOPS_SYM]; ALL_TAC] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP]] THEN
  (* the two cases of the cut *)
  FIRST_X_ASSUM DISJ_CASES_TAC THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++
                         reversepath (g o s3))
                        (linepath(pathstart (g o s1),pathstart (g o s1)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
        `(f1:real^2->real^N) o std_triangle_loop`;
        `(s1:real^1->real^N) ++ reversepath s3`;
        `(g:real^N->real^M) ((f1:real^2->real^N) (vec 0))`]
       MOI_LTD_NULL_TRANSFER) THEN
      ASM_REWRITE_TAC[PATH_COMPOSE_JOIN; PATH_COMPOSE_REVERSEPATH;
                      PATHSTART_JOIN];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++
                         (g o s4) ++ (g o s3) ++ (g o s2))
                        (linepath(pathstart (g o s1),pathstart (g o s1)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
        `(f2:real^2->real^N) o std_triangle_loop`;
        `(s1:real^1->real^N) ++ s4 ++ s3 ++ s2`;
        `(g:real^N->real^M) ((f2:real^2->real^N) (vec 0))`]
       MOI_LTD_NULL_TRANSFER) THEN
      ASM_REWRITE_TAC[PATH_COMPOSE_JOIN; PATHSTART_JOIN];
      ALL_TAC] THEN
    USE_THEN "W3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN
     `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++ (g o s3))
                        (linepath(pathstart (g o s1),pathstart (g o s1)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
        `(f1:real^2->real^N) o std_triangle_loop`;
        `(s1:real^1->real^N) ++ s3`;
        `(g:real^N->real^M) ((f1:real^2->real^N) (vec 0))`]
       MOI_LTD_NULL_TRANSFER) THEN
      ASM_REWRITE_TAC[PATH_COMPOSE_JOIN; PATHSTART_JOIN];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++
                         reversepath (g o s2) ++ (g o s3) ++ reversepath (g o s4))
                        (linepath(pathstart (g o s1),pathstart (g o s1)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
        `(f2:real^2->real^N) o std_triangle_loop`;
        `(s1:real^1->real^N) ++ reversepath s2 ++ s3 ++ reversepath s4`;
        `(g:real^N->real^M) ((f2:real^2->real^N) (vec 0))`]
       MOI_LTD_NULL_TRANSFER) THEN
      ASM_REWRITE_TAC[PATH_COMPOSE_JOIN; PATH_COMPOSE_REVERSEPATH;
                      PATHSTART_JOIN];
      ALL_TAC] THEN
    USE_THEN "W4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Finitely many components for finite unions of connected sets; normal     *)
(* disks have a finite disk complexity.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_FINITE_COMPONENTS_UNIONS = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ (!t. t IN c ==> connected t)
     ==> FINITE (components (UNIONS c))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\t:real^N->bool. connected_component (UNIONS c) (CHOICE t))
                    {t | t IN c /\ ~(t = {})}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT] THEN
  REWRITE_TAC[SUBSET; components; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `k:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^N->bool` THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET connected_component (UNIONS c) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  ASM_MESON_TAC[CHOICE_DEF]);;

let MOI_LTD_NORMAL_FINITE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_normal_disk c f ==> FINITE (components (moi_lt_double_image f))`,
  REWRITE_TAC[moi_lt_normal_disk] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_LTD_FINITE_COMPONENTS_UNIONS THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [combinatorial_manifold_with_boundary]) THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^N->bool` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED]);;

(* A singular disk without double points is an embedded PL disk.            *)

let MOI_LTD_EMBEDDED_DISK = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_singular_disk c f /\ moi_lt_double_image f = {}
     ==> ?f'. pl_homeomorphism (std_triangle,IMAGE f std_triangle) (f,f') /\
              IMAGE f std_triangle SUBSET UNIONS c /\
              IMAGE f std_triangle INTER complex_boundary c =
              IMAGE f (relative_frontier std_triangle)`,
  REWRITE_TAC[moi_lt_singular_disk; moi_lt_double_image] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN std_triangle /\ y IN std_triangle /\
                      (f:real^2->real^N) x = f y ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`std_triangle`; `f:real^2->real^N`;
                 `IMAGE (f:real^2->real^N) std_triangle`] HOMEOMORPHISM_COMPACT) THEN
  ASM_SIMP_TAC[MOI_LTD_STD_TRIANGLE_BASIC; PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':real^N->real^2` THEN
  DISCH_TAC THEN ASM_SIMP_TAC[HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM] THEN
  MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* G4. Lemma 25.2 (LOOP_DESCENT_STATEMENT) from general position and the    *)
(* two cuts, by induction on the disk complexity (the book takes a normal   *)
(* disk of minimal complexity, p.184).                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_DESCENT_INDUCT = prove
 (mk_imp(mk_conj(MOI_LT_CUT_CLOSED,MOI_LT_CUT_ARC),
 `!(c:(real^N->bool)->bool) (b1:real^N->bool) (g:real^N->real^M) v w0.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     orientable_complex c /\ w0 SUBSET b1 /\
     g continuous_on w0 /\ IMAGE g w0 SUBSET v
     ==> !n (h:real^2->real^N).
           moi_lt_normal_disk c h /\ moi_lt_disk_complexity h = n /\
           IMAGE h (relative_frontier std_triangle) SUBSET w0 /\
           ~homotopic_loops v (g o h o std_triangle_loop)
                              (linepath(g(h(vec 0)),g(h(vec 0))))
           ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
                 pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
                 d INTER complex_boundary c =
                 IMAGE e (relative_frontier std_triangle) /\
                 IMAGE e (relative_frontier std_triangle) SUBSET b1 /\
                 ~homotopic_loops v (g o e o std_triangle_loop)
                                    (linepath(g(e(vec 0)),g(e(vec 0))))`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CLOSED") (LABEL_TAC "ARC")) THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `b1:real^N->bool`; `g:real^N->real^M`;
    `v:real^M->bool`; `w0:real^N->bool`] THEN
  STRIP_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "IH") THEN X_GEN_TAC `h:real^2->real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^2->real^N) continuous_on std_triangle /\
                moi_lt_singular_disk c h` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lt_normal_disk]) THEN
    SIMP_TAC[] THEN REWRITE_TAC[moi_lt_singular_disk] THEN
    MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_CASES_TAC `moi_lt_double_image (h:real^2->real^N) = {}` THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^2->real^N`]
      MOI_LTD_EMBEDDED_DISK) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (h:real^2->real^N) std_triangle`; `h:real^2->real^N`;
      `h':real^N->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `w0:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k:real^N->bool. k IN components (moi_lt_double_image h)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_REWRITE_TAC[COMPONENTS_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h1:real^2->real^N.
       moi_lt_normal_disk c h1 /\
       moi_lt_disk_complexity h1 < moi_lt_disk_complexity (h:real^2->real^N) /\
       IMAGE h1 (relative_frontier std_triangle) SUBSET w0 /\
       ~homotopic_loops v ((g:real^N->real^M) o h1 o std_triangle_loop)
                          (linepath(g(h1(vec 0)),g(h1(vec 0))))
       ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
             pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
             d INTER complex_boundary c =
             IMAGE e (relative_frontier std_triangle) /\
             IMAGE e (relative_frontier std_triangle) SUBSET b1 /\
             ~homotopic_loops v (g o e o std_triangle_loop)
                                (linepath(g(e(vec 0)),g(e(vec 0))))`
  (LABEL_TAC "IH1") THENL
   [X_GEN_TAC `h1:real^2->real^N` THEN STRIP_TAC THEN
    REMOVE_THEN "IH" (MP_TAC o SPEC `moi_lt_disk_complexity (h1:real^2->real^N)`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `h1:real^2->real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(k:real^N->bool) INTER complex_boundary c = {}` THENL
   [(* a closed double curve: Cases 1-2 *)
    USE_THEN "CLOSED" (MP_TAC o SPECL
     [`c:(real^N->bool)->bool`; `h:real^2->real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "IH1" MATCH_MP_TAC THEN EXISTS_TAC `h1:real^2->real^N` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (h1:real^2->real^N) (relative_frontier std_triangle) =
                  IMAGE (h:real^2->real^N) (relative_frontier std_triangle)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LTD_IMAGE_EQ_RF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(h1:real^2->real^N) (vec 0) = (h:real^2->real^N) (vec 0)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC
     `~homotopic_loops v ((g:real^N->real^M) o (h:real^2->real^N) o std_triangle_loop)
                         (linepath(g(h(vec 0)),g(h(vec 0))))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(g:real^N->real^M) o (h1:real^2->real^N) o std_triangle_loop` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC MOI_LTD_LOOP_EQ_RF THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w0:real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^N->real^M) w0` THEN ASM_SIMP_TAC[IMAGE_SUBSET];
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]];
    (* a double arc: Cases 3-4 *)
    USE_THEN "ARC" (MP_TAC o SPECL
     [`c:(real^N->bool)->bool`; `h:real^2->real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^N`
     (X_CHOOSE_THEN `h2:real^2->real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`g:real^N->real^M`; `v:real^M->bool`]) THEN
    REWRITE_TAC[IMP_CONJ] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w0:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^N->real^M) w0` THEN ASM_SIMP_TAC[IMAGE_SUBSET];
      ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC
     `homotopic_loops v ((g:real^N->real^M) o (h1:real^2->real^N) o
                          std_triangle_loop)
                         (linepath(g(h1(vec 0)),g(h1(vec 0))))` THENL
     [ASM_CASES_TAC
       `homotopic_loops v ((g:real^N->real^M) o (h2:real^2->real^N) o
                            std_triangle_loop)
                           (linepath(g(h2(vec 0)),g(h2(vec 0))))` THENL
       [ASM_MESON_TAC[];
        USE_THEN "IH1" MATCH_MP_TAC THEN EXISTS_TAC `h2:real^2->real^N` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      USE_THEN "IH1" MATCH_MP_TAC THEN EXISTS_TAC `h1:real^2->real^N` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]);;

let MOI_LTD_DESCENT = prove
 (mk_imp(list_mk_conj[MOI_LT_GENERAL_POSITION; MOI_LT_CUT_CLOSED; MOI_LT_CUT_ARC],
         `!(u:N->bool) (w:M->bool). LOOP_DESCENT_STATEMENT u w`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GP") (LABEL_TAC "CUTS")) THEN
  USE_THEN "CUTS" (LABEL_TAC "IND" o MATCH_MP MOI_LTD_DESCENT_INDUCT) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOP_DESCENT_STATEMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `b1:real^N->bool`;
    `g:real^N->real^M`; `v:real^M->bool`] THEN
  ABBREV_TAC `w0 = (subtopology euclidean (complex_boundary c)) interior_of
                   (b1:real^N->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(w0:real^N->bool) SUBSET b1 /\
                open_in (subtopology euclidean (complex_boundary c)) w0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN REWRITE_TAC[INTERIOR_OF_SUBSET; OPEN_IN_INTERIOR_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^M) continuous_on w0 /\ IMAGE g w0 SUBSET v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `b1:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "GP" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w0:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[moi_lt_singular_disk]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^2->real^N` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "IND" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `b1:real^N->bool`; `g:real^N->real^M`;
    `v:real^M->bool`; `w0:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`moi_lt_disk_complexity (f':real^2->real^N)`; `f':real^2->real^N`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `~homotopic_loops v ((g:real^N->real^M) o f o std_triangle_loop)
                       (linepath(g(f(vec 0)),g(f(vec 0))))` THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`w0:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
    `(f':real^2->real^N) o std_triangle_loop`;
    `(f:real^2->real^N) o std_triangle_loop`;
    `(g:real^N->real^M) ((f':real^2->real^N) (vec 0))`]
   MOI_LTD_NULL_TRANSFER) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[HOMOTOPIC_LOOPS_SYM]);;

let MOI_LTD_CUT_CLOSED = prove
 (mk_imp(mk_conj(MOI_LT_CUT_INNERMOST,MOI_LT_CUT_SWAP), MOI_LT_CUT_CLOSED),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IN") (LABEL_TAC "SW")) THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "IN" (MP_TAC o SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k':real^N->bool` (X_CHOOSE_THEN `j1:real^2->bool`
    (X_CHOOSE_THEN `j2:real^2->bool` STRIP_ASSUME_TAC))) THEN
  REMOVE_THEN "SW" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k':real^N->bool`;
    `j1:real^2->bool`; `j2:real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* G5. MOI_CORE_GLUE_LOOPN (Moise p.183, Theorem 2 from Theorem 1, and      *)
(* p.187, the first normal system) from lt_fill and lt_nsys.                *)
(* ------------------------------------------------------------------------- *)

(* Iterated barycentric subdivisions of finite combinatorial 3-manifolds    *)
(* with boundary (from the foundation term MOI_FND_BARYCENTRIC_CM_WB).       *)

let MOI_LTD_ITER_SD = prove
 (mk_imp(MOI_FND_BARYCENTRIC_CM_WB,
  `!n (c:(real^N->bool)->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> FINITE (ITER n barycentric_subdivision c) /\
         combinatorial_manifold_with_boundary 3 (ITER n barycentric_subdivision c) /\
         complex_boundary (ITER n barycentric_subdivision c) = complex_boundary c /\
         UNIONS (ITER n barycentric_subdivision c) = UNIONS c /\
         (orientable_complex c
          ==> orientable_complex (ITER n barycentric_subdivision c))`),
  DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ITER n barycentric_subdivision
                                    (c:(real^N->bool)->bool)`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE] THEN
  ASM_MESON_TAC[UNIONS_BARYCENTRIC_SUBDIVISION;
                combinatorial_manifold_with_boundary]);;

(* A disk parametrized by std_triangle is parametrized by a 2-simplex of    *)
(* real^N (the form of the conclusion of LOOP_THEOREM_N_STATEMENT).          *)

let MOI_LTD_PARAM_SIMPLEX = prove
 (`!(d:real^N->bool) (e:real^2->real^N) e'.
     2 <= dimindex(:N) /\ pl_homeomorphism (std_triangle,d) (e,e')
     ==> ?(k:real^N->bool) f g.
           &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\
           IMAGE f (relative_frontier k) = IMAGE e (relative_frontier std_triangle)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:2`,`:M`] ISOMETRY_UNIV_UNIV) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^2->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x y. (j:real^2->real^N) x = j y ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(j:real^2->real^N)(x - y) = vec 0` MP_TAC THENL
     [ASM_SIMP_TAC[LINEAR_SUB; VECTOR_SUB_REFL];
      DISCH_THEN(MP_TAC o AP_TERM `norm:real^N->real`) THEN
      ASM_REWRITE_TAC[NORM_0; NORM_EQ_0; VECTOR_SUB_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `j:real^2->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j':real^N->real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM]))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (std_triangle,IMAGE (j:real^2->real^N) std_triangle) (j,j')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `\x:real^2. (j:real^2->real^N) x + vec 0` THEN
      CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
      ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (j:real^2->real^N) std_triangle`;
    `(e:real^2->real^N) o (j':real^N->real^2)`;
    `(j:real^2->real^N) o (e':real^N->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`j:real^2->real^N`; `std_triangle`; `&2:int`]
      SIMPLEX_LINEAR_IMAGE_EQ) THEN
    ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX];
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `std_triangle` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`j:real^2->real^N`; `std_triangle`]
      RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* A null-homotopic inclusion of the image of the boundary loop kills the   *)
(* loop.                                                                     *)

let MOI_LTD_INCLUSION_NULL = prove
 (`!(e:real^2->real^N) b a.
     e continuous_on relative_frontier std_triangle /\
     IMAGE e (relative_frontier std_triangle) SUBSET b /\
     homotopic_with (\h. T)
       (subtopology euclidean (IMAGE e (relative_frontier std_triangle)),
        subtopology euclidean b) (\x. x) (\x. a)
     ==> homotopic_loops b (e o std_triangle_loop) (linepath(a,a))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LTD_LOOP_COMPOSE_RF) THEN
  REWRITE_TAC[homotopic_loops; LINEPATH_REFL] THEN
  SUBGOAL_THEN
   `homotopic_with (\r. pathfinish r = pathstart r)
      (subtopology euclidean (interval[vec 0,vec 1]),subtopology euclidean b)
      ((\x:real^N. x) o ((e:real^2->real^N) o std_triangle_loop))
      ((\x:real^N. a) o (e o std_triangle_loop))`
  MP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `IMAGE (e:real^2->real^N) (relative_frontier std_triangle)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
      EXISTS_TAC `\h:real^N->real^N. T` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `h:real^N->real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
                  MOI_LTD_STD_TRIANGLE_LOOP];
      ASM_MESON_TAC[path];
      ASM_MESON_TAC[path_image; SUBSET_REFL]];
    REWRITE_TAC[o_DEF; ETA_AX]]);;

let MOI_LTD_ID_O = prove
 (`!h:real^1->real^N. (\x:real^N. x) o h = h`,
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let MOI_LTD_LOOPN = prove
 (mk_imp(list_mk_conj[MOI_LT_FILL; MOI_LT_NSYS; MOI_FND_BARYCENTRIC_CM_WB],
         MOI_CORE_GLUE_LOOPN),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FILL")
   (CONJUNCTS_THEN2 (LABEL_TAC "NSYS") (LABEL_TAC "BARY"))) THEN
  USE_THEN "BARY" (LABEL_TAC "ITER" o MATCH_MP MOI_LTD_ITER_SD) THEN
  X_GEN_TAC `u:N->bool` THEN DISCH_THEN(LABEL_TAC "LNS") THEN
  REWRITE_TAC[LOOP_THEOREM_N_STATEMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `b:real^N->bool`; `p:real^1->real^N`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "FILL" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `b:real^N->bool`; `p:real^1->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `k:(real^2->bool)->bool`
   (X_CHOOSE_THEN `f:real^2->real^N` STRIP_ASSUME_TAC))) THEN
  REMOVE_THEN "ITER" (MP_TAC o SPECL [`n:num`; `c:(real^N->bool)->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = ITER n barycentric_subdivision (c:(real^N->bool)->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `orientable_complex (c0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET b`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
    REWRITE_TAC[PATH_IMAGE_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP];
    ALL_TAC] THEN
  REMOVE_THEN "NSYS" (MP_TAC o SPECL
   [`c0:(real^N->bool)->bool`; `k:(real^2->bool)->bool`; `f:real^2->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(real^N->bool)->bool`
   (X_CHOOSE_THEN `k1:(real^2->bool)->bool`
    (X_CHOOSE_THEN `f1:real^2->real^N` MP_TAC))) THEN
  ABBREV_TAC `b1 = UNIONS {s | s IN c1 /\ s SUBSET complex_boundary c1 /\
                              ~(s INTER IMAGE (f1:real^2->real^N)
                                      (relative_frontier std_triangle) = {})}` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "LNS" (MP_TAC o REWRITE_RULE[LOOP_NORMAL_SYSTEM_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c1:(real^N->bool)->bool`; `k1:(real^2->bool)->bool`; `f1:real^2->real^N`;
    `b1:real^N->bool`; `\x:real^N. x`; `b:real^N->bool`]) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID] THEN
  REWRITE_TAC[MOI_LTD_ID_O] THEN
  ANTS_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC
     `~homotopic_loops b (p:real^1->real^N) (linepath(pathstart p,pathstart p))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LTD_LOOP_NULL_BASE THEN
    EXISTS_TAC `(f1:real^2->real^N) (vec 0)` THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(f:real^2->real^N) o std_triangle_loop` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HOMOTOPIC_LOOPS_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(f1:real^2->real^N) o std_triangle_loop` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool`
   (X_CHOOSE_THEN `e:real^2->real^N`
    (X_CHOOSE_THEN `e':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`d:real^N->bool`; `e:real^2->real^N`; `e':real^N->real^2`]
    MOI_LTD_PARAM_SIMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^N->bool`
   (X_CHOOSE_THEN `ff:real^N->real^N`
    (X_CHOOSE_THEN `gg:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`kk:real^N->bool`; `d:real^N->bool`; `ff:real^N->real^N`;
    `gg:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(b1:real^N->bool) SUBSET complex_boundary c` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^2->real^N) (relative_frontier std_triangle) SUBSET d`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]];
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    UNDISCH_TAC
     `~homotopic_loops b ((e:real^2->real^N) o std_triangle_loop)
                         (linepath(e(vec 0),e(vec 0)))` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(e:real^2->real^N) continuous_on relative_frontier std_triangle`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE] THEN
      ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`e:real^2->real^N`; `b:real^N->bool`; `a:real^N`]
      MOI_LTD_INCLUSION_NULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_LTD_LOOP_NULL_BASE) THEN
    ASM_SIMP_TAC[MOI_LTD_LOOP_COMPOSE_RF]]);;

(* ------------------------------------------------------------------------- *)
(* G6. The tower (MOI_PROD_LOOP_NS): helpers.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_CELLWISE_BASIC = prove
 (`!(f:real^2->real^N) (c:(real^N->bool)->bool).
     moi_lt_cellwise f c
     ==> f continuous_on std_triangle /\ pl_map_on std_triangle f /\
         IMAGE f std_triangle SUBSET UNIONS c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_cellwise] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `p:(real^2->bool)->bool`]
    MOI_REAL_PIECEWISE_AFFINE_UNIONS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS] THEN
  X_GEN_TAC `x:real^2` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (f:real^2->real^N) r` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let MOI_LTD_LOOPS_CARRIED_PCONN = prove
 (`!(j:real^N->bool) s.
     loops_carried j s /\ path_connected j /\ j SUBSET s ==> path_connected s`,
  REWRITE_TAC[loops_carried] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> ?y. y IN j /\ path_component s x y`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `linepath(x:real^N,x)`) THEN
    REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(q:real^1->real^N) (vec 0)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
      MP_TAC(ISPECL [`s:real^N->bool`; `linepath(x:real^N,x)`;
                     `q:real^1->real^N`; `vec 0:real^1`]
        HOMOTOPIC_LOOPS_IMP_PATH_COMPONENT_VALUE) THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; LINEPATH_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC PATH_COMPONENT_TRANS THEN EXISTS_TAC `x':real^N` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_COMPONENT_TRANS THEN
  EXISTS_TAC `y':real^N` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[PATH_COMPONENT_SYM]] THEN
  MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THEN EXISTS_TAC `j:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
  ASM_SIMP_TAC[]);;

let MOI_LTD_CLOSED_BUFFER = prove
 (`!x k u:real^N->bool.
     closed x /\ compact k /\ open_in (subtopology euclidean x) u /\ k SUBSET u
     ==> ?f. closed f /\ f SUBSET u /\
             k SUBSET (subtopology euclidean x) interior_of f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `x DIFF u:real^N->bool`] SEPARATION_NORMAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN EXISTS_TAC `x:real^N->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^N->bool` (X_CHOOSE_THEN `o2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `x INTER closure o1:real^N->bool` THEN
  ASM_SIMP_TAC[CLOSED_INTER; CLOSED_CLOSURE] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `o2 INTER closure o1:real^N->bool = {}` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; INTER_COMM];
      ASM SET_TAC[]];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `x INTER o1:real^N->bool` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
      MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `o1:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[];
        MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]]]]);;

let MOI_LTD_FINITE_COMPLEX_CLOSED = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c
     ==> compact (UNIONS c) /\ closed (UNIONS c) /\
         compact (complex_boundary c) /\ closed (complex_boundary c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> compact s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
      [lf_simplicial_complex]) THEN
    MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ (r ==> s) /\ p /\ r ==> p /\ q /\ r /\ s`) THEN
  REWRITE_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[complex_boundary] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM]]);;

let MOI_LTD_COMPLEX_BOUNDARY_SUBSET = prove
 (`!c:(real^N->bool)->bool. complex_boundary c SUBSET UNIONS c`,
  REWRITE_TAC[complex_boundary; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_LTD_TOWER_STEP_GOAL =
 mk_imp(list_mk_conj[MOI_LT_COVER_LIFT_CELLWISE; MOI_LT_COVER_BOUNDARY;
                     MOI_LT_NO_SECTION; MOI_LT_COMPLEXITY_LIFT;
                     MOI_LT_CELLWISE_FINITE; MOI_LT_NEXT_SYSTEM],
 `!(u:N->bool).
     DOUBLE_COVER_STATEMENT u /\ 7 <= dimindex(:N)
     ==> !(c:(real^N->bool)->bool) (f:real^2->real^N) b1 b.
           FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
           orientable_complex c /\ moi_lt_cellwise f c /\
           {x | x IN std_triangle /\ f x IN complex_boundary c} =
           relative_frontier std_triangle /\
           loops_carried (IMAGE f std_triangle) (UNIONS c) /\
           b1 SUBSET complex_boundary c /\ closed b1 /\
           IMAGE f (relative_frontier std_triangle) SUBSET
           (subtopology euclidean (complex_boundary c)) interior_of b1 /\
           b IN components (complex_boundary c) /\
           IMAGE f (relative_frontier std_triangle) SUBSET b /\ ~pl_sphere 2 b
           ==> ?(c':(real^N->bool)->bool) (q:real^N->real^N) c2 f2 b12.
                 FINITE c' /\ combinatorial_manifold_with_boundary 3 c' /\
                 simplicial_map_on c' c q /\
                 covering_space (UNIONS c',q) (UNIONS c) /\
                 (!y. y IN UNIONS c ==> {x | x IN UNIONS c' /\ q x = y} HAS_SIZE 2) /\
                 complex_boundary c' =
                 {x | x IN UNIONS c' /\ q x IN complex_boundary c} /\
                 FINITE c2 /\ combinatorial_manifold_with_boundary 3 c2 /\
                 orientable_complex c2 /\ UNIONS c2 SUBSET UNIONS c' /\
                 UNIONS c2 INTER complex_boundary c' SUBSET complex_boundary c2 /\
                 moi_lt_cellwise f2 c2 /\
                 {x | x IN std_triangle /\ f2 x IN complex_boundary c2} =
                 relative_frontier std_triangle /\
                 loops_carried (IMAGE f2 std_triangle) (UNIONS c2) /\
                 b12 SUBSET complex_boundary c2 /\ closed b12 /\
                 IMAGE f2 (relative_frontier std_triangle) SUBSET
                 (subtopology euclidean (complex_boundary c2)) interior_of b12 /\
                 b12 SUBSET UNIONS c2 INTER complex_boundary c' /\
                 IMAGE q b12 SUBSET
                 (subtopology euclidean (complex_boundary c)) interior_of b1 /\
                 (!x. x IN std_triangle ==> q(f2 x) = f x) /\
                 moi_lt_tower_complexity f2 < moi_lt_tower_complexity f`);;

let MOI_LTD_TOWER_STEP = prove
 (MOI_LTD_TOWER_STEP_GOAL,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LIFT") (CONJUNCTS_THEN2 (LABEL_TAC "BDY")
   (CONJUNCTS_THEN2 (LABEL_TAC "NOSEC") (CONJUNCTS_THEN2 (LABEL_TAC "CPLX")
   (CONJUNCTS_THEN2 (LABEL_TAC "CFIN") (LABEL_TAC "NEXT")))))) THEN
  X_GEN_TAC `u:N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "DC") ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `b1:real^N->bool`;
    `b:real^N->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LTD_CELLWISE_BASIC) THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `connected (UNIONS (c:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
    MATCH_MP_TAC MOI_LTD_LOOPS_CARRIED_PCONN THEN
    EXISTS_TAC `IMAGE (f:real^2->real^N) std_triangle` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; MOI_LTD_STD_TRIANGLE_BASIC];
    ALL_TAC] THEN
  REMOVE_THEN "DC" (MP_TAC o REWRITE_RULE[DOUBLE_COVER_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':(real^N->bool)->bool`
   (X_CHOOSE_THEN `q:real^N->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (c':(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  REMOVE_THEN "LIFT" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `c':(real^N->bool)->bool`; `q:real^N->real^N`;
    `f:real^2->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^N` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "BDY" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `c':(real^N->bool)->bool`; `q:real^N->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
  REMOVE_THEN "NOSEC" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `c':(real^N->bool)->bool`; `q:real^N->real^N`;
    `IMAGE (f:real^2->real^N) std_triangle`]) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; MOI_LTD_STD_TRIANGLE_BASIC] THEN DISCH_TAC THEN
  REMOVE_THEN "CPLX" (MP_TAC o SPECL
   [`UNIONS (c':(real^N->bool)->bool)`; `q:real^N->real^N`;
    `UNIONS (c:(real^N->bool)->bool)`; `f:real^2->real^N`; `f2:real^2->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [USE_THEN "CFIN" MATCH_MP_TAC THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  REMOVE_THEN "NEXT" (MP_TAC o SPECL
   [`c':(real^N->bool)->bool`; `f2:real^2->real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(real^N->bool)->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) ORELSE DISCH_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `fr:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BDF" o GSYM)))) THEN
  SUBGOAL_THEN `orientable_complex (c2:(real^N->bool)->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN UNIONS c' ==> (y IN complex_boundary c' <=>
                                   (q:real^N->real^N) y IN complex_boundary c)`
  (LABEL_TAC "BREL") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN std_triangle /\ (f2:real^2->real^N) x IN complex_boundary c2} =
    relative_frontier std_triangle`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c}` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN std_triangle` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f2:real^2->real^N) x IN UNIONS c2 /\
                  ~((f2:real^2->real^N) x IN fr) /\ f2 x IN UNIONS c'`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "BDF" (fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_INTER] THEN
    USE_THEN "BREL" (MP_TAC o SPEC `(f2:real^2->real^N) x`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`complex_boundary c:real^N->bool`;
                 `IMAGE (f:real^2->real^N) (relative_frontier std_triangle)`;
                 `(subtopology euclidean (complex_boundary c)) interior_of
                  (b1:real^N->bool)`] MOI_LTD_CLOSED_BUFFER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_LTD_FINITE_COMPLEX_CLOSED; OPEN_IN_INTERIOR_OF] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1':real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `b12 = {y | y IN UNIONS c2 /\ y IN complex_boundary c' /\
                         (q:real^N->real^N) y IN b1'}` THEN
  SUBGOAL_THEN `(q:real^N->real^N) continuous_on UNIONS c'` ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS]; ALL_TAC] THEN
  SUBGOAL_THEN `(b12:real^N->bool) SUBSET UNIONS c2 INTER complex_boundary c' /\
                b12 SUBSET complex_boundary c2 /\
                IMAGE (q:real^N->real^N) b12 SUBSET
                (subtopology euclidean (complex_boundary c)) interior_of b1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b12" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (b12:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `b12 = (UNIONS c2 INTER complex_boundary c') INTER
            {y | y IN UNIONS c' /\ (q:real^N->real^N) y IN b1'}`
    SUBST1_TAC THENL [EXPAND_TAC "b12" THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_INTER THEN
      ASM_MESON_TAC[MOI_LTD_FINITE_COMPLEX_CLOSED;
                    combinatorial_manifold_with_boundary];
      MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
      EXISTS_TAC `UNIONS c':real^N->bool` THEN
      ASM_SIMP_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE; MOI_LTD_FINITE_COMPLEX_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(subtopology euclidean (complex_boundary c)) interior_of
                  (b1':real^N->bool)`;
                 `complex_boundary c:real^N->bool`] OPEN_IN_OPEN) THEN
  REWRITE_TAC[OPEN_IN_INTERIOR_OF] THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN relative_frontier std_triangle
        ==> (f2:real^2->real^N) x IN complex_boundary c2 /\
            (q:real^N->real^N) (f2 x) IN o1 /\ ~(f2 x IN fr)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
      MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
      UNDISCH_TAC `(x:real^2) IN std_triangle` THEN
      UNDISCH_TAC `{x | x IN std_triangle /\ (f2:real^2->real^N) x IN complex_boundary c2} =
                   relative_frontier std_triangle` THEN SET_TAC[];
      SUBGOAL_THEN `(q:real^N->real^N) ((f2:real^2->real^N) x) = f x` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET
                   (subtopology euclidean (complex_boundary c)) interior_of b1'` THEN
      UNDISCH_TAC `(subtopology euclidean (complex_boundary c)) interior_of b1' =
                   complex_boundary c INTER (o1:real^N->bool)` THEN SET_TAC[];
      UNDISCH_TAC `(x:real^2) IN std_triangle` THEN
      UNDISCH_TAC `fr INTER IMAGE (f2:real^2->real^N) std_triangle = {}` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f2:real^2->real^N) (relative_frontier std_triangle) SUBSET
    (subtopology euclidean (complex_boundary c2)) interior_of b12`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{y | y IN complex_boundary c2 /\ (q:real^N->real^N) y IN o1} INTER
                ((:real^N) DIFF fr)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; IN_DIFF;
                  IN_UNIV] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN EXPAND_TAC "b12" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      SUBGOAL_THEN `(y:real^N) IN UNIONS c2 /\ y IN complex_boundary c'`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^N) IN complex_boundary c2` THEN
        UNDISCH_TAC `~((y:real^N) IN fr)` THEN
        USE_THEN "BDF" (MP_TAC o GSYM) THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(q:real^N->real^N) y IN complex_boundary c` ASSUME_TAC THENL
       [USE_THEN "BREL" (MP_TAC o SPEC `y:real^N`) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `(y:real^N) IN UNIONS c2` THEN
          UNDISCH_TAC `UNIONS c2 SUBSET UNIONS (c':(real^N->bool)->bool)` THEN
          SET_TAC[];
          DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `(q:real^N->real^N) y IN complex_boundary c` THEN
      UNDISCH_TAC `(q:real^N->real^N) y IN o1` THEN
      UNDISCH_TAC `(subtopology euclidean (complex_boundary c)) interior_of b1' =
                   complex_boundary c INTER (o1:real^N->bool)` THEN
      MP_TAC(ISPECL [`subtopology euclidean (complex_boundary c:real^N->bool)`;
                     `b1':real^N->bool`] INTERIOR_OF_SUBSET) THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN
      REWRITE_TAC[GSYM closed] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS c':real^N->bool` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS c2:real^N->bool` THEN
      REWRITE_TAC[MOI_LTD_COMPLEX_BOUNDARY_SUBSET] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`c':(real^N->bool)->bool`; `q:real^N->real^N`; `c2:(real^N->bool)->bool`;
    `f2:real^2->real^N`; `b12:real^N->bool`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [FIRST_ASSUM(ACCEPT_TAC o GSYM);
    USE_THEN "BDF" (fun th -> REWRITE_TAC[GSYM th]) THEN SET_TAC[]]);;


(* The cellwise buffered normal system, by strong induction on the tower   *)
(* complexity (Moise Lemma 3, p.188: the induction on k).                   *)

let MOI_LTD_NS_CELL = prove
 (mk_imp(list_mk_conj[MOI_LT_COVER_LIFT_CELLWISE; MOI_LT_COVER_BOUNDARY;
                      MOI_LT_NO_SECTION; MOI_LT_COMPLEXITY_LIFT;
                      MOI_LT_CELLWISE_FINITE; MOI_LT_NEXT_SYSTEM;
                      MOI_LT_SPHERE_STEP; MOI_LT_DESCENT_INPUT],
 `!(u:N->bool) (w:M->bool).
     LOOP_SPHERE_CASE_STATEMENT u w /\ DOUBLE_COVER_STATEMENT u /\
     LOOP_DESCENT_STATEMENT u w /\ 7 <= dimindex(:N)
     ==> !n (c:(real^N->bool)->bool) (f:real^2->real^N) b1 (g:real^N->real^M) v.
           FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
           orientable_complex c /\ moi_lt_cellwise f c /\
           {x | x IN std_triangle /\ f x IN complex_boundary c} =
           relative_frontier std_triangle /\
           loops_carried (IMAGE f std_triangle) (UNIONS c) /\
           b1 SUBSET complex_boundary c /\ closed b1 /\
           IMAGE f (relative_frontier std_triangle) SUBSET
           (subtopology euclidean (complex_boundary c)) interior_of b1 /\
           g continuous_on b1 /\ IMAGE g b1 SUBSET v /\
           ~homotopic_loops v (g o f o std_triangle_loop)
                              (linepath(g(f(vec 0)),g(f(vec 0)))) /\
           moi_lt_tower_complexity f = n
           ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
                 pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
                 d INTER complex_boundary c =
                 IMAGE e (relative_frontier std_triangle) /\
                 IMAGE e (relative_frontier std_triangle) SUBSET b1 /\
                 ~homotopic_loops v (g o e o std_triangle_loop)
                                    (linepath(g(e(vec 0)),g(e(vec 0))))`),
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    LABEL_TAC "TS" (MATCH_MP MOI_LTD_TOWER_STEP (end_itlist CONJ (fst(chop_list 6 ths)))) THEN
    LABEL_TAC "SS" (el 6 ths) THEN LABEL_TAC "DI" (el 7 ths)) THEN
  MAP_EVERY X_GEN_TAC [`u:N->bool`; `w:M->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LSC") (CONJUNCTS_THEN2 (LABEL_TAC "DC")
    (CONJUNCTS_THEN2 (LABEL_TAC "LD") ASSUME_TAC))) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `b1:real^N->bool`;
    `g:real^N->real^M`; `v:real^M->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LTD_CELLWISE_BASIC) THEN
  SUBGOAL_THEN
   `?b:real^N->bool. b IN components (complex_boundary c) /\
                     IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET b`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXISTS_COMPONENT_SUPERSET THEN
    SUBGOAL_THEN `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET
                  complex_boundary c` ASSUME_TAC THENL
     [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN
                        complex_boundary c} = relative_frontier std_triangle` THEN
      MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET
                   complex_boundary c` THEN
      MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN SET_TAC[];
      MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
      MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE]];
    ALL_TAC] THEN
  ASM_CASES_TAC `pl_sphere 2 (b:real^N->bool)` THENL
   [USE_THEN "SS" (MP_TAC o SPECL [`u:N->bool`; `w:M->bool`]) THEN
    USE_THEN "LSC" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `b1:real^N->bool`;
      `g:real^N->real^M`; `v:real^M->bool`; `b:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "TS" (MP_TAC o SPEC `u:N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `b1:real^N->bool`;
    `b:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':(real^N->bool)->bool`
   (X_CHOOSE_THEN `q:real^N->real^N` (X_CHOOSE_THEN `c2:(real^N->bool)->bool`
   (X_CHOOSE_THEN `f2:real^2->real^N` (X_CHOOSE_THEN `b12:real^N->bool`
    STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LTD_CELLWISE_BASIC o
    check (fun th -> concl th = `moi_lt_cellwise (f2:real^2->real^N) c2`)) THEN
  SUBGOAL_THEN `(q:real^N->real^N) continuous_on UNIONS c'` ASSUME_TAC THENL
   [MATCH_MP_TAC COVERING_SPACE_IMP_CONTINUOUS THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(subtopology euclidean (complex_boundary c)) interior_of
                (b1:real^N->bool) SUBSET b1` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_OF_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(b12:real^N->bool) SUBSET UNIONS c' /\
                IMAGE (q:real^N->real^N) b12 SUBSET b1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(b12:real^N->bool) SUBSET UNIONS c2 INTER complex_boundary c'` THEN
      UNDISCH_TAC `UNIONS c2 SUBSET UNIONS (c':(real^N->bool)->bool)` THEN
      SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(subtopology euclidean (complex_boundary c)) interior_of
                  (b1:real^N->bool)` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^N->real^M) o (q:real^N->real^N)) continuous_on b12 /\
                IMAGE (g o q) b12 SUBSET v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `UNIONS c':real^N->bool` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `b1:real^N->bool` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^N->real^M) b1` THEN
      CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET; ALL_TAC] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC `moi_lt_tower_complexity (f2:real^2->real^N)`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c2:(real^N->bool)->bool`; `f2:real^2->real^N`; `b12:real^N->bool`;
    `(g:real^N->real^M) o (q:real^N->real^N)`; `v:real^M->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~homotopic_loops v ((g:real^N->real^M) o f o std_triangle_loop)
                                    (linepath(g(f(vec 0)),g(f(vec 0))))` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `((g:real^N->real^M) o (q:real^N->real^N)) ((f2:real^2->real^N) (vec 0)) =
                  g((f:real^2->real^N) (vec 0))` ASSUME_TAC THENL
     [REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `((g:real^N->real^M) o (q:real^N->real^N)) o
                (f2:real^2->real^N) o std_triangle_loop` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC MOI_LTD_LOOP_EQ_RF THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `b12:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `(subtopology euclidean (complex_boundary c2)) interior_of
                    (b12:real^N->bool)` THEN
        ASM_REWRITE_TAC[INTERIOR_OF_SUBSET]];
      ONCE_REWRITE_TAC[IMAGE_o] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((g:real^N->real^M) o (q:real^N->real^N)) b12` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(subtopology euclidean (complex_boundary c2)) interior_of
                  (b12:real^N->bool)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[INTERIOR_OF_SUBSET]];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
      MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^N->bool` (X_CHOOSE_THEN `e2:real^2->real^N`
   (X_CHOOSE_THEN `e2':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  USE_THEN "DI" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `c':(real^N->bool)->bool`; `q:real^N->real^N`;
    `d2:real^N->bool`; `e2:real^2->real^N`; `e2':real^N->real^2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS c2:real^N->bool` THEN CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(!x. x IN std_triangle ==> (e2':real^N->real^2) (e2 x) = x) /\
                IMAGE (e2:real^2->real^N) std_triangle = d2`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
      check (fun th -> concl th =
        `pl_homeomorphism (std_triangle,d2) ((e2:real^2->real^N),e2')`)) THEN
    REWRITE_TAC[homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "LD" (MP_TAC o REWRITE_RULE[LOOP_DESCENT_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `(q:real^N->real^N) o (e2:real^2->real^N)`;
    `b1:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM] THEN X_GEN_TAC `x:real^2` THEN
      EQ_TAC THENL
       [(STRIP_TAC THEN
  SUBGOAL_THEN `(e2:real^2->real^N) x IN UNIONS c2 /\ e2 x IN complex_boundary c'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (e2:real^2->real^N) std_triangle = d2` THEN
      UNDISCH_TAC `(d2:real^N->bool) SUBSET UNIONS c2` THEN
      UNDISCH_TAC `(x:real^2) IN std_triangle` THEN SET_TAC[];
      UNDISCH_TAC `complex_boundary c' =
                   {x | x IN UNIONS c' /\ (q:real^N->real^N) x IN complex_boundary c}` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e2:real^2->real^N) std_triangle = d2` THEN
      UNDISCH_TAC `(d2:real^N->bool) SUBSET UNIONS c2` THEN
      UNDISCH_TAC `UNIONS c2 SUBSET UNIONS (c':(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(x:real^2) IN std_triangle` THEN SET_TAC[]];
    ALL_TAC]) THEN
        (SUBGOAL_THEN `(e2:real^2->real^N) x IN IMAGE e2 (relative_frontier std_triangle)`
  MP_TAC THENL
   [UNDISCH_TAC `d2 INTER complex_boundary c2 =
                 IMAGE (e2:real^2->real^N) (relative_frontier std_triangle)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (e2:real^2->real^N) std_triangle = d2` THEN
      UNDISCH_TAC `(x:real^2) IN std_triangle` THEN SET_TAC[];
      UNDISCH_TAC `UNIONS c2 INTER complex_boundary c' SUBSET
                   complex_boundary (c2:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(e2:real^2->real^N) x IN UNIONS c2` THEN
      UNDISCH_TAC `(e2:real^2->real^N) x IN complex_boundary c'` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x':real^2) IN std_triangle` ASSUME_TAC THENL
   [UNDISCH_TAC `(x':real^2) IN relative_frontier std_triangle` THEN
    MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `x':real^2 = x` (fun th -> ASM_REWRITE_TAC[SYM th]) THEN
  UNDISCH_TAC `!x. x IN std_triangle ==> (e2':real^N->real^2) (e2 x) = x` THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `x':real^2` th) THEN MP_TAC(SPEC `x:real^2` th)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);
        DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
    MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(e2:real^2->real^N) x IN complex_boundary c'` MP_TAC THENL
   [UNDISCH_TAC `(b12:real^N->bool) SUBSET UNIONS c2 INTER complex_boundary c'` THEN
    UNDISCH_TAC `IMAGE (e2:real^2->real^N) (relative_frontier std_triangle) SUBSET b12` THEN
    UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `complex_boundary c' =
               {x | x IN UNIONS c' /\ (q:real^N->real^N) x IN complex_boundary c}` THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[IN_ELIM_THM]];
      CONJ_TAC THENL
       [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (q:real^N->real^N) b12` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET; ALL_TAC] THEN
    FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `~homotopic_loops v (((g:real^N->real^M) o (q:real^N->real^N)) o
                                   (e2:real^2->real^N) o std_triangle_loop)
                                  (linepath(((g:real^N->real^M) o q) (e2 (vec 0)),
                                            (g o q) (e2 (vec 0))))` THEN
  REWRITE_TAC[o_ASSOC; o_THM]]];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* G6. MOI_PROD_LOOP_NS from the tower statements.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_PROD_LOOP_NS = prove
 (mk_imp(list_mk_conj[MOI_LT_COVER_LIFT_CELLWISE; MOI_LT_COVER_BOUNDARY;
                      MOI_LT_NO_SECTION; MOI_LT_COMPLEXITY_LIFT;
                      MOI_LT_CELLWISE_FINITE; MOI_LT_NEXT_SYSTEM;
                      MOI_LT_SPHERE_STEP; MOI_LT_DESCENT_INPUT;
                      MOI_LT_FROZEN_TO_CELL],
         MOI_PROD_LOOP_NS),
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    LABEL_TAC "NS" (MATCH_MP MOI_LTD_NS_CELL (end_itlist CONJ (fst(chop_list 8 ths)))) THEN
    LABEL_TAC "FTC" (el 8 ths)) THEN
  MAP_EVERY X_GEN_TAC [`u:N->bool`; `w:M->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LSC") (CONJUNCTS_THEN2 (LABEL_TAC "DC")
    (LABEL_TAC "LD"))) THEN
  REWRITE_TAC[LOOP_NORMAL_SYSTEM_STATEMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `k:(real^2->bool)->bool`; `f:real^2->real^N`;
    `b1:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "FTC" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `k:(real^2->bool)->bool`; `f:real^2->real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
     fst(dest_var(lhs(concl th))) = "b1")) THEN
  STRIP_TAC THEN
  REMOVE_THEN "NS" (MP_TAC o SPECL [`u:N->bool`; `w:M->bool`]) THEN
  USE_THEN "LSC" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "DC" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "LD" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`moi_lt_tower_complexity (f:real^2->real^N)`; `c:(real^N->bool)->bool`;
    `f:real^2->real^N`;
    `UNIONS {s | s IN c /\ s SUBSET complex_boundary c /\
                 ~(s INTER IMAGE (f:real^2->real^N) (relative_frontier std_triangle) =
                   {})}`;
    `g:real^N->real^M`; `v:real^M->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* G7. Closure of the C25 decomposition: the statement terms of the loop     *)
(* files (at :7), four foundation terms and the real^3 glue                  *)
(* MOI_CORE_GLUE_LOOP3 (pc_moi_cglue.ml, MOI_CGL_LOOP3) give                 *)
(* LOOP_THEOREM_3_STATEMENT (pc_moi_stmt.ml).                                *)
(* ------------------------------------------------------------------------- *)

let MOI_LT_UNIT_TARGETS =
  [MOI_LT_FILL; MOI_LT_NSYS; MOI_LT_SPHERE_HOLE; MOI_LT_PUSH_IN_DISK;
   MOI_LT_COVER_LIFT_CELLWISE; MOI_LT_COVER_BOUNDARY; MOI_LT_NO_SECTION;
   MOI_LT_COMPLEXITY_LIFT; MOI_LT_CELLWISE_FINITE; MOI_LT_NEXT_SYSTEM;
   MOI_LT_SPHERE_STEP; MOI_LT_DESCENT_INPUT; MOI_LT_FROZEN_TO_CELL;
   MOI_LT_GP_SIMPLICIAL; MOI_LT_GP_CROSSINGS; MOI_LT_CROSSINGS_NORMAL;
   MOI_LT_CUT_INNERMOST; MOI_LT_CUT_SWAP; MOI_LT_CUT_ARC_SPLIT;
   MOI_LT_WORD_3; MOI_LT_WORD_4];;

let MOI_LT_FND_TERMS =
  [MOI_FND_BARYCENTRIC_CM_WB; MOI_FND_COCYCLE_NONSPHERE_BOUNDARY;
   MOI_FND_DOUBLE_COVER_OF_COCYCLE; MOI_FND_CM_WB_DIM];;

let MOI_LTD_C25_CLOSURE =
  let ity = [`:7`,`:N`; `:7`,`:M`] in
  let hs = map (inst ity) (MOI_LT_UNIT_TARGETS @ MOI_LT_FND_TERMS) @
           [MOI_CORE_GLUE_LOOP3] in
  let hconj = list_mk_conj hs in
  let asm = CONJUNCTS (ASSUME hconj) in
  let _ = if length asm = length hs then () else failwith "conjunct count" in
  let get t = el (index (inst ity t) (map (inst ity)
                 (MOI_LT_UNIT_TARGETS @ MOI_LT_FND_TERMS))) asm in
  let conjs ts = end_itlist CONJ (map get ts) in
  let it th = INST_TYPE ity th in
  let gp = MP (it MOI_LTD_GP)
              (conjs [MOI_LT_GP_SIMPLICIAL; MOI_LT_GP_CROSSINGS;
                      MOI_LT_CROSSINGS_NORMAL]) in
  let ca = MP (it MOI_LTD_CUT_ARC)
              (conjs [MOI_LT_CUT_ARC_SPLIT; MOI_LT_WORD_3; MOI_LT_WORD_4]) in
  let cc = MP (it MOI_LTD_CUT_CLOSED)
              (conjs [MOI_LT_CUT_INNERMOST; MOI_LT_CUT_SWAP]) in
  let ld = MP (it MOI_LTD_DESCENT) (CONJ gp (CONJ cc ca)) in
  let lsc = MP (it MOI_LTD_SPHERE)
               (conjs [MOI_LT_SPHERE_HOLE; MOI_LT_PUSH_IN_DISK]) in
  let dc = MP (INST_TYPE [`:7`,`:N`] MOI_FD_DOUBLE_COVER_GLUE)
              (conjs [MOI_FND_COCYCLE_NONSPHERE_BOUNDARY;
                      MOI_FND_DOUBLE_COVER_OF_COCYCLE; MOI_FND_CM_WB_DIM]) in
  let prod = MP (it MOI_LTD_PROD_LOOP_NS)
                (conjs [MOI_LT_COVER_LIFT_CELLWISE; MOI_LT_COVER_BOUNDARY;
                        MOI_LT_NO_SECTION; MOI_LT_COMPLEXITY_LIFT;
                        MOI_LT_CELLWISE_FINITE; MOI_LT_NEXT_SYSTEM;
                        MOI_LT_SPHERE_STEP; MOI_LT_DESCENT_INPUT;
                        MOI_LT_FROZEN_TO_CELL]) in
  let u7 = `(:7)` in
  let lns = MP (SPECL [u7; u7] prod)
               (CONJ (SPECL [u7; u7] lsc) (CONJ dc (SPECL [u7; u7] ld))) in
  let loopn = MP (it MOI_LTD_LOOPN)
                 (conjs [MOI_LT_FILL; MOI_LT_NSYS; MOI_FND_BARYCENTRIC_CM_WB]) in
  let ltn = MP (SPEC u7 loopn) lns in
  let lt3 = MP (last asm) ltn in
  DISCH hconj lt3;;

(* The statement of the closure, for the record. *)
let MOI_LTD_C25_CLOSURE_HYPS = length (hyp MOI_LTD_C25_CLOSURE);;
concl MOI_LTD_C25_CLOSURE = mk_imp(list_mk_conj(map (inst [`:7`,`:N`; `:7`,`:M`])
  (MOI_LT_UNIT_TARGETS @ MOI_LT_FND_TERMS) @ [MOI_CORE_GLUE_LOOP3]),
  `LOOP_THEOREM_3_STATEMENT`);;

(* ------------------------------------------------------------------------- *)
(* S. Sanity theorems for the notions of this file (degenerate cases).      *)
(* ------------------------------------------------------------------------- *)

(* Simplicial singular disks (as in the normal systems) are cellwise.       *)

let MOI_LTD_SAN_SIMPLICIAL_CELLWISE = prove
 (`!(k:(real^2->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ UNIONS k = std_triangle /\ simplicial_map_on k c f
     ==> moi_lt_cellwise f c`,
  REWRITE_TAC[simplicial_complex; simplicial_map_on; moi_lt_cellwise] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `k:(real^2->bool)->bool` THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

(* Constant maps onto a vertex are cellwise (the notion is not vacuous).    *)

let MOI_LTD_SAN_CELLWISE_CONST = prove
 (`!(c:(real^N->bool)->bool) y. {y} IN c ==> moi_lt_cellwise (\x:real^2. y) c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lt_cellwise] THEN
  EXISTS_TAC `{std_triangle}` THEN
  REWRITE_TAC[FINITE_SING; UNIONS_1; IN_SING] THEN
  X_GEN_TAC `r:real^2->bool` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (\x:real^2. (y:real^N)) std_triangle = {y}`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC MOI_LTD_STD_TRIANGLE_BASIC THEN SET_TAC[];
    MAP_EVERY EXISTS_TAC [`(\x:real^2. vec 0):real^2->real^N`; `y:real^N`] THEN
    REWRITE_TAC[LINEAR_ZERO; VECTOR_ADD_LID]]);;

(* The tower complexity of an injective map, and of a constant map, is 1:  *)
(* the identification set is connected in both cases, so the complexity is *)
(* only a well-founded measure (the tower stops at the sphere case, not at  *)
(* complexity 0; compare the book's vertex-pair count k, p.188).            *)

let MOI_LTD_SAN_COMPLEXITY_INJECTIVE = prove
 (`!(f:real^2->real^N).
     (!x y. x IN std_triangle /\ y IN std_triangle /\ f x = f y ==> x = y)
     ==> moi_lt_tower_complexity f = 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lt_tower_complexity] THEN
  SUBGOAL_THEN `moi_lt_pairs (f:real^2->real^N) =
                IMAGE (\x. pastecart x x) std_triangle` SUBST1_TAC THENL
   [REWRITE_TAC[moi_lt_pairs; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `components (IMAGE (\x:real^2. pastecart x x) std_triangle) =
                {IMAGE (\x. pastecart x x) std_triangle}` SUBST1_TAC THENL
   [REWRITE_TAC[COMPONENTS_EQ_SING; IMAGE_EQ_EMPTY;
                MOI_LTD_STD_TRIANGLE_BASIC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_ID];
    REWRITE_TAC[CARD_SING]]);;

let MOI_LTD_SAN_COMPLEXITY_CONST = prove
 (`!y:real^N. moi_lt_tower_complexity (\x:real^2. y) = 1`,
  GEN_TAC THEN REWRITE_TAC[moi_lt_tower_complexity] THEN
  SUBGOAL_THEN `moi_lt_pairs (\x:real^2. (y:real^N)) =
                std_triangle PCROSS std_triangle` SUBST1_TAC THENL
   [REWRITE_TAC[moi_lt_pairs; PCROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN `components (std_triangle PCROSS std_triangle) =
                {std_triangle PCROSS std_triangle}` SUBST1_TAC THENL
   [REWRITE_TAC[COMPONENTS_EQ_SING; PCROSS_EQ_EMPTY;
                MOI_LTD_STD_TRIANGLE_BASIC; CONNECTED_PCROSS_EQ];
    REWRITE_TAC[CARD_SING]]);;

(* Double points: none exactly for injective maps.                          *)

let MOI_LTD_SAN_DOUBLE_IMAGE_EMPTY = prove
 (`!(f:real^2->real^N).
     moi_lt_double_image f = {} <=>
     (!x y. x IN std_triangle /\ y IN std_triangle /\ f x = f y ==> x = y)`,
  REWRITE_TAC[moi_lt_double_image; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* An embedded proper PL disk is a normal disk of disk complexity 0 (with  *)
(* the empty 1-manifold s): the base case of the descent is not vacuous.    *)

let MOI_LTD_SAN_NORMAL_EMBEDDED = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_singular_disk c f /\
     (!x y. x IN std_triangle /\ y IN std_triangle /\ f x = f y ==> x = y)
     ==> moi_lt_normal_disk c f /\ moi_lt_disk_complexity f = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM MOI_LTD_SAN_DOUBLE_IMAGE_EMPTY] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_lt_normal_disk; moi_lt_disk_complexity; NOT_IN_EMPTY;
                  COMPONENTS_EMPTY; CARD_CLAUSES] THEN
  EXISTS_TAC `{}:(real^N->bool)->bool` THEN
  REWRITE_TAC[FINITE_EMPTY; UNIONS_0; NOT_IN_EMPTY] THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex;
              NOT_IN_EMPTY; UNIONS_0]);;

(* Singular disks need a nonempty boundary of c (properness).               *)

let MOI_LTD_SAN_SINGULAR_BOUNDARY = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_singular_disk c f ==> ~(complex_boundary c = {})`,
  REWRITE_TAC[moi_lt_singular_disk] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN
                    complex_boundary c} = relative_frontier std_triangle` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC] THEN
  MESON_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE]);;

(* The singular disks of LOOP_DESCENT_STATEMENT are exactly moi_lt_       *)
(* singular_disk (used by the descent glue).                                *)

let MOI_LTD_SAN_DESCENT_INPUT_FORM = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_singular_disk c f <=>
     pl_map_on std_triangle f /\ IMAGE f std_triangle SUBSET UNIONS c /\
     {x | x IN std_triangle /\ f x IN complex_boundary c} =
     relative_frontier std_triangle /\
     (!x. x IN std_triangle
          ==> ?n. open n /\ x IN n /\
                  !y z. y IN n INTER std_triangle /\ z IN n INTER std_triangle /\
                        f y = f z ==> y = z) /\
     (!y. FINITE {x | x IN std_triangle /\ f x = y} /\
          CARD {x | x IN std_triangle /\ f x = y} <= 2)`,
  REWRITE_TAC[moi_lt_singular_disk]);;
(* ------------------------------------------------------------------------- *)
(* Summary check (printed on load).                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_LTD_ALL =
  [MOI_LTD_SPHERE; MOI_LTD_GP; MOI_LTD_CUT_ARC; MOI_LTD_CUT_CLOSED;
   MOI_LTD_DESCENT_INDUCT; MOI_LTD_DESCENT; MOI_LTD_LOOPN; MOI_LTD_TOWER_STEP;
   MOI_LTD_NS_CELL; MOI_LTD_PROD_LOOP_NS; MOI_LTD_C25_CLOSURE;
   MOI_LTD_SAN_SIMPLICIAL_CELLWISE; MOI_LTD_SAN_CELLWISE_CONST;
   MOI_LTD_SAN_COMPLEXITY_INJECTIVE; MOI_LTD_SAN_COMPLEXITY_CONST;
   MOI_LTD_SAN_DOUBLE_IMAGE_EMPTY; MOI_LTD_SAN_NORMAL_EMBEDDED;
   MOI_LTD_SAN_SINGULAR_BOUNDARY; MOI_LTD_SAN_DESCENT_INPUT_FORM;
   MOI_LTD_NORMAL_FINITE];;

print_string ("MOI_LTD_SUMMARY theorems=" ^
   string_of_int ((length MOI_LTD_ALL)) ^
   " hyps=" ^
   string_of_int ((itlist (fun th n -> length(hyp th) + n) MOI_LTD_ALL 0)) ^
   " axioms=" ^
   string_of_int ((length(axioms()))) ^
   "\n");;

(* The glue conclusions are exactly the loop items of the PL core.          *)

print_string ("MOI_LTD_GLUE_CHECK " ^
   string_of_bool ((rand(concl MOI_LTD_SPHERE) =
   `!(u:N->bool) (w:M->bool). LOOP_SPHERE_CASE_STATEMENT u w`)) ^
   " " ^
   string_of_bool ((rand(concl MOI_LTD_DESCENT) =
   `!(u:N->bool) (w:M->bool). LOOP_DESCENT_STATEMENT u w`)) ^
   " " ^
   string_of_bool ((rand(concl MOI_LTD_LOOPN) = MOI_CORE_GLUE_LOOPN)) ^
   " " ^
   string_of_bool ((rand(concl MOI_LTD_PROD_LOOP_NS) = MOI_PROD_LOOP_NS)) ^
   " " ^
   string_of_bool ((rand(concl MOI_LTD_C25_CLOSURE) = `LOOP_THEOREM_3_STATEMENT`)) ^
   " " ^
   string_of_bool ((concl MOI_LTD_C25_CLOSURE =
   mk_imp(list_mk_conj(map (inst [`:7`,`:N`; `:7`,`:M`])
     (MOI_LT_UNIT_TARGETS @ MOI_LT_FND_TERMS) @ [MOI_CORE_GLUE_LOOP3]),
   `LOOP_THEOREM_3_STATEMENT`))) ^
   "\n");;

print_string ("MOI_LTD_TARGETS unit=" ^
   string_of_int ((length MOI_LT_UNIT_TARGETS)) ^
   " fnd=" ^
   string_of_int ((length MOI_LT_FND_TERMS)) ^
   " all_terms=" ^
   string_of_int ((length (filter (fun t -> type_of t = bool_ty)
    [MOI_LT_FILL; MOI_LT_RESIMPLICIAL; MOI_LT_NSYS; MOI_LT_SPHERE_HOLE;
     MOI_LT_PUSH_IN_DISK; MOI_LT_COVER_LIFT_CELLWISE; MOI_LT_COVER_BOUNDARY;
     MOI_LT_DESCENT_INPUT; MOI_LT_NO_SECTION; MOI_LT_COMPLEXITY_LIFT;
     MOI_LT_CELLWISE_FINITE; MOI_LT_NEXT_SYSTEM; MOI_LT_FROZEN_TO_CELL;
     MOI_LT_SPHERE_STEP; MOI_LT_GP_SIMPLICIAL; MOI_LT_MANIFOLD_CHARTS;
     MOI_LT_GP_CROSSINGS; MOI_LT_CROSSINGS_NORMAL; MOI_LT_GENERAL_POSITION;
     MOI_LT_CUT_CLOSED; MOI_LT_CUT_INNERMOST; MOI_LT_CUT_SWAP;
     MOI_LT_CUT_ARC_SPLIT; MOI_LT_WORD_3; MOI_LT_WORD_4;
     MOI_LT_SOURCE_STRUCTURE; MOI_LT_CUT_ARC]))) ^
   "\n");;

