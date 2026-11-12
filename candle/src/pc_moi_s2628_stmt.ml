(* ========================================================================= *)
(* pc_moi_s2628_stmt: the statements for the Sec 26-28 items of the Moise PL *)
(* core (26.4 open form, 26.6, 26.7, 26.8, 28.6, 28.8, 28.10), with the glue *)
(* theorems MOI_SDD_... and the sanity theorems MOI_SDD_SAN_...              *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;

(* ========================================================================= *)
(* The Sec 26-28 items of the Moise PL core (Moise GTM 47, Secs 26-28,       *)
(* printed pp.191-210; PDF page = printed page + 9), split into statements:  *)
(* definitions moi_s26_... and moi_s28_..., statement terms MOI_S26_... and  *)
(* MOI_S28_... (closed boolean OCaml term values), glue theorems MOI_SDD_... *)
(* (the statements and the input terms imply the seven items MOISE_266,      *)
(* MOISE_267, MOISE_268, MOISE_286, MOISE_288, MOISE_2810 and the producer   *)
(* MOI_PROD_264) and sanity theorems MOI_SDD_SAN_....                        *)
(* The producer for 26.4 is MOI_SDD_PROD_264 (used in                        *)
(* pc_moi_core_status.ml).  The other six items are proved there directly    *)
(* from their own files (26.6 from pc_moi_s26_sep.ml, 26.7 from              *)
(* pc_moi_s26_three.ml, 26.8 by MOI_FD_268_GLUE, 28.6, 28.8 and 28.10 in     *)
(* pc_moi_s286.ml, pc_moi_s288_cov.ml and pc_moi_s2810.ml), so the           *)
(* statements MOI_S28_NONSEP, MOI_S28_SEP_DISK, MOI_S28_ESSENTIAL_ANNULUS,   *)
(* MOI_S28_286, MOI_S28_288 and MOI_S28_2810, used only by the glue of this  *)
(* file, are not needed.                                                     *)
(* Convention (as pc_moi_s34_stmt.ml): a statement with inputs from other    *)
(* files is a term X_BODY; the statement is X = inputs ==> X_BODY.           *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1. Vocabulary.                                                       *)
(* ------------------------------------------------------------------------- *)

(* A PL bicollar of m (Moise 26.3, p.192): a PL homeomorphism of m x [-1,1] *)
(* onto w which is the identity on m x 0 (the form of MOI_FND_BICOLLAR,      *)
(* MOI_FND_BICOLLAR_R3 and MOI_FND_BICOLLAR_CURVE_2 of pc_moi_fnd_stmt.ml).  *)

let moi_s26_bicollar = new_definition
 `moi_s26_bicollar (m:real^N->bool) (w:real^N->bool)
                   (p:real^(N,1)finite_sum->real^N) q <=>
    pl_homeomorphism (m PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
    !x. x IN m ==> p(pastecart x (vec 0)) = x`;;

(* The level t of a bicollar and the open strip between levels a and b.     *)

let moi_s26_level = new_definition
 `moi_s26_level (m:real^N->bool) (p:real^(N,1)finite_sum->real^N) (t:real) =
    IMAGE p (m PCROSS {lift t})`;;

let moi_s26_strip = new_definition
 `moi_s26_strip (m:real^N->bool) (p:real^(N,1)finite_sum->real^N) (a:real) (b:real) =
    IMAGE p (m PCROSS {x:real^1 | a < drop x /\ drop x < b})`;;

(* j bounds a PL 2-cell inside t (the clause of MOISE_286, MOISE_288 and   *)
(* MOISE_2810; Moise writes "J bounds a 2-cell in T").                      *)

let moi_s28_bounds_disk = new_definition
 `moi_s28_bounds_disk (t:real^N->bool) (j:real^N->bool) <=>
    ?d. d SUBSET t /\ pl_cell_with_boundary 2 d j`;;

(* Local charts of a topological surface x at y: an open neighbourhood       *)
(* homeomorphic to the plane, or to the closed upper half plane with y going *)
(* to the origin (Moise p.191, the definition of a 2-manifold with boundary).*)

let moi_s28_locally_r2 = new_definition
 `moi_s28_locally_r2 (x:real^N->bool) (y:real^N) <=>
    ?u. open_in (subtopology euclidean x) u /\ y IN u /\ u homeomorphic (:real^2)`;;

let moi_s28_locally_half = new_definition
 `moi_s28_locally_half (x:real^N->bool) (y:real^N) <=>
    ?u (h:real^N->real^2) k.
        open_in (subtopology euclidean x) u /\ y IN u /\
        homeomorphism (u,{z:real^2 | &0 <= z$2}) (h,k) /\ h y = vec 0`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s26_level; moi_s26_strip];;
map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s26_bicollar; moi_s28_bounds_disk; moi_s28_locally_r2; moi_s28_locally_half];;
(* ========================================================================= *)
(* Part 2. The statements for Sec 26 (Moise Sec 26, pp.191-195).            *)
(* ========================================================================= *)

(* Type instances: an input used at a fixed type is stated at that type    *)
(* (an assumed polymorphic hypothesis cannot be instantiated in a proof).   *)

(* The rule table: every composite statement is built by sdd_rule, which     *)
(* records its input list and conclusion for the glue of part 4.             *)

let sdd_rules = ref ([]:(term list * term * term) list);;

let sdd_rule ins body =
  let imp = mk_imp(list_mk_conj ins,body) in
  sdd_rules := (ins,body,imp) :: !sdd_rules; imp;;

let sdd_i3 t = inst [`:3`,`:N`] t;;
let sdd_i33 t = inst [`:3`,`:M`; `:3`,`:N`] t;;
let sdd_iNN t = inst [`:N`,`:M`] t;;
let sdd_iM t = inst [`:M`,`:N`] t;;

(* s26_cross (Moise 26.6 proof, p.194, steps (1)-(5), via a cone from a     *)
(* generic apex instead of an arbitrary singular disk): a closed polygon in *)
(* affine general position with a finite 2-complex all of whose edges lie  *)
(* in an even number of triangles crosses it an even number of times.       *)

let MOI_S26_EVEN_CROSSING =
 `!(c:(real^3->bool)->bool) (p:num->real^3) n.
     FINITE c /\ simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     (!e. e IN c /\ aff_dim e = &1
          ==> EVEN (CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t})) /\
     p n = p 0 /\
     (!i. i < n ==> ~(p i = p (SUC i)) /\ ~(p i IN UNIONS c)) /\
     (!i s. i < n /\ s IN c ==> affine_gp_3 (segment[p i,p (SUC i)]) s)
     ==> FINITE {(i,x) | i < n /\ x IN segment[p i,p (SUC i)] /\ x IN UNIONS c} /\
         EVEN (CARD {(i,x) | i < n /\ x IN segment[p i,p (SUC i)] /\
                              x IN UNIONS c})`;;

(* s26_local: near a relative interior point of a triangle, or of an edge  *)
(* lying in exactly two triangles, a 2-complex in real^3 is a plane, or two *)
(* half planes, and the small balls minus the complex have exactly two      *)
(* connected parts, each accumulating on the whole local sheet.             *)

let MOI_S26_LOCAL_TRI =
 `!(c:(real^3->bool)->bool) q y.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     q IN c /\ aff_dim q = &2 /\ y IN relative_interior q
     ==> ?r0. &0 < r0 /\
              !r. &0 < r /\ r <= r0
                  ==> ball(y,r) INTER UNIONS c = ball(y,r) INTER affine hull q /\
                      ?u v. open u /\ open v /\ connected u /\ connected v /\
                            DISJOINT u v /\
                            u UNION v = ball(y,r) DIFF affine hull q /\
                            ball(y,r) INTER affine hull q SUBSET
                            closure u INTER closure v`;;

let MOI_S26_LOCAL_EDGE =
 `!(c:(real^3->bool)->bool) e q q' y.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     e IN c /\ aff_dim e = &1 /\
     {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = {q,q'} /\ ~(q = q') /\
     y IN relative_interior e
     ==> ?r0. &0 < r0 /\
              !r. &0 < r /\ r <= r0
                  ==> ball(y,r) INTER UNIONS c = ball(y,r) INTER (q UNION q') /\
                      ?u v. open u /\ open v /\ connected u /\ connected v /\
                            DISJOINT u v /\
                            u UNION v = ball(y,r) DIFF (q UNION q') /\
                            ball(y,r) INTER (q UNION q') SUBSET
                            closure u INTER closure v`;;

(* s26_sep: Moise 26.6 (p.194).  At least two components by the crossing  *)
(* parity; every component has frontier |c| (local sheets, dual            *)
(* connectivity of c through its edges); at most two (two local sides).   *)

let MOI_S26_SEP =
  sdd_rule [MOI_S26_EVEN_CROSSING; MOI_S26_LOCAL_TRI; MOI_S26_LOCAL_EDGE]
    `MOISE_266_STATEMENT`;;

(* s28_tria and s28_trib (2-dimensional infrastructure, used for Secs 26     *)
(* and 28; Moise Secs 21-22 conventions): combinatorial surfaces are         *)
(* topological surfaces with the combinatorial boundary as topological     *)
(* boundary, and conversely every triangulation of a topological surface   *)
(* is combinatorial.  Stated here because s26_surf and s26_ext use them.  *)

let MOI_S28_SURF_CHARTS =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> (!y. y IN UNIONS c DIFF surface_boundary c
              ==> moi_s28_locally_r2 (UNIONS c) y) /\
         (!y. y IN surface_boundary c
              ==> moi_s28_locally_half (UNIONS c) y /\
                  ~moi_s28_locally_r2 (UNIONS c) y) /\
         (combinatorial_manifold 2 c ==> surface_boundary c = {})`;;

let MOI_S28_SURF_LOCAL =
 `!d:(real^N->bool)->bool.
     FINITE d /\ simplicial_complex d /\
     (!y. y IN UNIONS d
          ==> moi_s28_locally_r2 (UNIONS d) y \/ moi_s28_locally_half (UNIONS d) y)
     ==> combinatorial_manifold_with_boundary 2 d /\
         surface_boundary d = {y | y IN UNIONS d /\ ~moi_s28_locally_r2 (UNIONS d) y} /\
         (surface_boundary d = {} ==> combinatorial_manifold 2 d)`;;

let MOI_S28_SURF_INVARIANT_BODY =
 `!(c:(real^M->bool)->bool) (d:(real^N->bool)->bool) f g.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     FINITE d /\ simplicial_complex d /\
     homeomorphism (UNIONS c,UNIONS d) (f,g)
     ==> combinatorial_manifold_with_boundary 2 d /\
         IMAGE f (surface_boundary c) = surface_boundary d /\
         (combinatorial_manifold 2 c ==> combinatorial_manifold 2 d)`;;

let MOI_S28_SURF_INVARIANT =
  sdd_rule [sdd_iM MOI_S28_SURF_CHARTS; MOI_S28_SURF_LOCAL]
    MOI_S28_SURF_INVARIANT_BODY;;

(* s26_surf: two surfaces glued along common boundary components (Moise   *)
(* 26.7 proof, p.195, and the annulus unions of 28.6); the interior of a   *)
(* connected surface with boundary is connected.                           *)

let MOI_S26_SURF_GLUE_BODY =
 `!(c:(real^N->bool)->bool) d k.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     FINITE d /\ combinatorial_manifold_with_boundary 2 d /\
     k SUBSET surface_boundary c /\ k SUBSET surface_boundary d /\
     (!b. b IN components (surface_boundary c) /\ ~(b INTER k = {}) ==> b SUBSET k) /\
     (!b. b IN components (surface_boundary d) /\ ~(b INTER k = {}) ==> b SUBSET k) /\
     UNIONS c INTER UNIONS d = k
     ==> ?e. FINITE e /\ combinatorial_manifold_with_boundary 2 e /\
             UNIONS e = UNIONS c UNION UNIONS d /\
             surface_boundary e =
             (surface_boundary c DIFF k) UNION (surface_boundary d DIFF k) /\
             complex_euler e = complex_euler c + complex_euler d /\
             (surface_boundary c = k /\ surface_boundary d = k
              ==> combinatorial_manifold 2 e)`;;

let MOI_S26_SURF_GLUE =
  sdd_rule [sdd_iNN MOI_S28_SURF_INVARIANT_BODY]
    MOI_S26_SURF_GLUE_BODY;;

let MOI_S26_INT_CONNECTED =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ connected (UNIONS c)
     ==> connected (UNIONS c DIFF surface_boundary c)`;;

(* s26_three: Moise 26.7 (p.195) from 26.6 for the three closed surfaces    *)
(* M_i UNION M_j, the local sides at an interior point of a triangle on    *)
(* the frontier of the unbounded component, and connected interiors (no    *)
(* three-fin analysis at the common boundary is needed).                   *)

let MOI_S26_THREE =
  sdd_rule [`MOISE_266_STATEMENT`; sdd_i3 MOI_S26_SURF_GLUE_BODY;
                       sdd_i3 MOI_S26_INT_CONNECTED; MOI_S26_LOCAL_TRI]
    `MOISE_267_STATEMENT`;;

(* s26_nbhd (26.4 proof, compact reduction): a compact set in an open set  *)
(* of real^3 has a compact combinatorial 3-manifold neighbourhood in it,   *)
(* triangulated so that a given complex inside the compact set appears     *)
(* subdivided as a subcomplex.                                             *)

let MOI_S26_COMPACT_NBHD_BODY =
 `!(u:real^3->bool) k (c:(real^3->bool)->bool).
     open u /\ compact k /\ k SUBSET u /\ FINITE c /\ simplicial_complex c /\
     UNIONS c SUBSET k
     ==> ?w s. FINITE w /\ combinatorial_manifold_with_boundary 3 w /\
               k SUBSET interior (UNIONS w) /\ UNIONS w SUBSET u /\
               simplicial_subcomplex s w /\ UNIONS s = UNIONS c /\
               (!t. t IN s ==> ?t'. t' IN c /\ t SUBSET t')`;;

let MOI_S26_COMPACT_NBHD =
  sdd_rule [sdd_i3 MOI_FND_DERIVED_NBHD_MANIFOLD]
    MOI_S26_COMPACT_NBHD_BODY;;

(* s26_cut (26.4 proof): a compact combinatorial 3-manifold is cut by a    *)
(* closed connected surface subcomplex in its interior into the parts      *)
(* inside and outside the surface (26.6), both combinatorial 3-manifolds   *)
(* with boundary, the surface a union of boundary components of each.     *)
(* Input: MOI_S26_SPHERE_SPLIT below is the text of the term               *)
(* MOI_SCH3_SPHERE_SPLIT of pc_moi_sch3_stmt.ml (a polygon splits a PL     *)
(* 2-sphere in real^3 into two PL disks), copied because that file is not  *)
(* in the load closure of pc_moi_fnd_stmt.ml.                               *)

let MOI_S26_SPHERE_SPLIT =
 `!s j:real^3->bool.
     pl_sphere 2 s /\ pl_sphere 1 j /\ j SUBSET s
     ==> ?d1 d2. pl_cell_with_boundary 2 d1 j /\ pl_cell_with_boundary 2 d2 j /\
                 d1 UNION d2 = s /\ d1 INTER d2 = j`;;

let MOI_S26_CUT_BODY =
 `!(w:(real^3->bool)->bool) s.
     FINITE w /\ combinatorial_manifold_with_boundary 3 w /\
     simplicial_subcomplex s w /\ combinatorial_manifold 2 s /\
     connected (UNIONS s) /\ ~(UNIONS s = {}) /\
     DISJOINT (UNIONS s) (complex_boundary w)
     ==> ?w1 w2. simplicial_subcomplex w1 w /\ simplicial_subcomplex w2 w /\
                 combinatorial_manifold_with_boundary 3 w1 /\
                 combinatorial_manifold_with_boundary 3 w2 /\
                 UNIONS w1 = UNIONS w DIFF outside (UNIONS s) /\
                 UNIONS w2 = UNIONS w DIFF inside (UNIONS s) /\
                 complex_boundary w1 =
                 (complex_boundary w DIFF outside (UNIONS s)) UNION UNIONS s /\
                 complex_boundary w2 =
                 (complex_boundary w DIFF inside (UNIONS s)) UNION UNIONS s`;;

let MOI_S26_CUT =
  sdd_rule [`MOISE_266_STATEMENT`; MOI_S26_SPHERE_SPLIT]
    MOI_S26_CUT_BODY;;

(* s26_fill (26.4 proof, the singular disk D of p.193): a loop in a       *)
(* polyhedron, null-homotopic in an open set containing it, bounds a PL   *)
(* singular disk in the open set whose boundary loop lies in the          *)
(* polyhedron and is homotopic there to the given loop.                    *)

let MOI_S26_PL_FILL =
 `!(c:(real^3->bool)->bool) u (p:real^1->real^3).
     FINITE c /\ simplicial_complex c /\ open u /\ UNIONS c SUBSET u /\
     path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p /\
     homotopic_loops u p (linepath(pathstart p,pathstart p))
     ==> ?f:real^2->real^3.
           pl_map_on std_triangle f /\ IMAGE f std_triangle SUBSET u /\
           IMAGE f (relative_frontier std_triangle) SUBSET UNIONS c /\
           homotopic_loops (UNIONS c) (f o std_triangle_loop) p`;;

(* s26_level (26.4 proof (a)-(b), p.193, in the level form of DG          *)
(* exists_finite_isPLSphere_levels_of_bicollar): for a PL singular disk   *)
(* with boundary in a closed surface with a bicollar, the preimage of two  *)
(* generic levels is a finite disjoint union of PL circles inside the     *)
(* open triangle.                                                          *)

let MOI_S26_LEVEL_CIRCLES =
 `!(c:(real^3->bool)->bool) w (rho:real^(3,1)finite_sum->real^3) rho'
   (f:real^2->real^3).
     FINITE c /\ combinatorial_manifold 2 c /\
     moi_s26_bicollar (UNIONS c) w rho rho' /\
     pl_map_on std_triangle f /\
     IMAGE f (relative_frontier std_triangle) SUBSET UNIONS c
     ==> ?e cc. &0 < e /\ e < &1 /\ FINITE cc /\ pairwise DISJOINT cc /\
                (!j. j IN cc ==> pl_sphere 1 j /\ j SUBSET relative_interior std_triangle) /\
                {x | x IN std_triangle /\
                     f x IN moi_s26_level (UNIONS c) rho e UNION
                            moi_s26_level (UNIONS c) rho (--e)} = UNIONS cc`;;

(* s26_ext: Moise 26.4 (p.192) in open subsets of real^3 (the             *)
(* producer MOI_PROD_264 = LOOP_THEOREM_3_STATEMENT ==> MOISE_264_OPEN):    *)
(* compact reduction, cut along the surface, bicollar levels, an          *)
(* innermost-essential level circle (a minimality argument on the nesting  *)
(* of the circles, no modification of the singular disk), and the loop     *)
(* theorem in the inside or outside part.                                  *)

let MOI_S26_EXT =
  sdd_rule [`LOOP_THEOREM_3_STATEMENT`; `MOISE_266_STATEMENT`;
                       MOI_FND_BICOLLAR_R3; MOI_S26_COMPACT_NBHD_BODY;
                       MOI_S26_CUT_BODY; MOI_S26_PL_FILL; MOI_S26_LEVEL_CIRCLES;
                       sdd_i33 MOI_S28_SURF_INVARIANT_BODY]
    `MOISE_264_OPEN_STATEMENT`;;

map type_of [MOI_S26_EVEN_CROSSING; MOI_S26_LOCAL_TRI; MOI_S26_LOCAL_EDGE; MOI_S26_SEP;
             MOI_S28_SURF_CHARTS; MOI_S28_SURF_LOCAL; MOI_S28_SURF_INVARIANT;
             MOI_S26_SURF_GLUE; MOI_S26_INT_CONNECTED; MOI_S26_THREE;
             MOI_S26_COMPACT_NBHD; MOI_S26_SPHERE_SPLIT; MOI_S26_CUT;
             MOI_S26_PL_FILL; MOI_S26_LEVEL_CIRCLES; MOI_S26_EXT];;
(* ========================================================================= *)
(* Part 3. The statements for Sec 28 (Moise Sec 28, pp.201-210), with the    *)
(* 2-dimensional cut-and-paste infrastructure it needs.  Route: Euler        *)
(* characteristic and orientability in place of the standard-position        *)
(* combinatorics of 28.2-28.5.                                               *)
(* ========================================================================= *)

(* s28_tria: a PL 1-sphere is triangulated by a connected combinatorial    *)
(* 1-manifold (the form in which MOI_FND_BICOLLAR_CURVE_2 takes curves).   *)

let MOI_S28_POLYGON_COMPLEX =
 `!j:real^N->bool.
     pl_sphere 1 j
     ==> ?l. FINITE l /\ combinatorial_manifold 1 l /\ UNIONS l = j /\
             connected (UNIONS l)`;;

(* s28_cut: cutting surfaces along bicollared curves.                      *)
(* STRIP_REMOVE: removing an open strip between two levels of a bicollar   *)
(* of a family of polygons in the interior of a surface leaves a surface   *)
(* whose boundary gains the two levels, with the same Euler characteristic. *)

let MOI_S28_STRIP_REMOVE_BODY =
 `!(c:(real^N->bool)->bool) (l:(real^N->bool)->bool) w
   (p:real^(N,1)finite_sum->real^N) q a b.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     FINITE l /\ combinatorial_manifold 1 l /\
     moi_s26_bicollar (UNIONS l) w p q /\ w SUBSET UNIONS c DIFF surface_boundary c /\
     UNIONS l SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
     --(&1) < a /\ a < b /\ b < &1
     ==> ?e. FINITE e /\ combinatorial_manifold_with_boundary 2 e /\
             UNIONS e = UNIONS c DIFF moi_s26_strip (UNIONS l) p a b /\
             surface_boundary e =
             surface_boundary c UNION moi_s26_level (UNIONS l) p a UNION
             moi_s26_level (UNIONS l) p b /\
             complex_euler e = complex_euler c`;;

let MOI_S28_STRIP_REMOVE =
  sdd_rule [sdd_iNN MOI_S28_SURF_INVARIANT_BODY]
    MOI_S28_STRIP_REMOVE_BODY;;

(* CUT_SEPARATING: a bicollared polygon separating a closed connected      *)
(* surface cuts it into two connected surfaces bounded by the polygon, with *)
(* Euler characteristics adding up (Moise 21.10 form, p.150).               *)

let MOI_S28_CUT_SEPARATING_BODY =
 `!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) w
   (p:real^(N,1)finite_sum->real^N) q.
     FINITE t /\ combinatorial_manifold 2 t /\ connected (UNIONS t) /\
     FINITE l /\ combinatorial_manifold 1 l /\ connected (UNIONS l) /\
     ~(UNIONS l = {}) /\
     moi_s26_bicollar (UNIONS l) w p q /\ w SUBSET UNIONS t /\
     UNIONS l SUBSET (subtopology euclidean (UNIONS t)) interior_of w /\
     ~connected (UNIONS t DIFF UNIONS l)
     ==> ?k1 k2 c1 c2.
           components (UNIONS t DIFF UNIONS l) = {k1,k2} /\ ~(k1 = k2) /\
           FINITE c1 /\ combinatorial_manifold_with_boundary 2 c1 /\
           UNIONS c1 = closure k1 /\ surface_boundary c1 = UNIONS l /\
           FINITE c2 /\ combinatorial_manifold_with_boundary 2 c2 /\
           UNIONS c2 = closure k2 /\ surface_boundary c2 = UNIONS l /\
           complex_euler c1 + complex_euler c2 = complex_euler t`;;

let MOI_S28_CUT_SEPARATING =
  sdd_rule [sdd_iNN MOI_S28_SURF_INVARIANT_BODY]
    MOI_S28_CUT_SEPARATING_BODY;;

(* COMPONENT_COMPLEX: the components of a combinatorial surface are        *)
(* subcomplexes, combinatorial surfaces again, and chi is additive.        *)

let MOI_S28_COMPONENT_COMPLEX =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> FINITE (components (UNIONS c)) /\
         complex_euler c =
         sum (components (UNIONS c)) (\k. complex_euler {s | s IN c /\ s SUBSET k}) /\
         !k. k IN components (UNIONS c)
             ==> FINITE {s | s IN c /\ s SUBSET k} /\
                 combinatorial_manifold_with_boundary 2 {s | s IN c /\ s SUBSET k} /\
                 UNIONS {s | s IN c /\ s SUBSET k} = k /\
                 surface_boundary {s | s IN c /\ s SUBSET k} =
                 surface_boundary c INTER k`;;

(* s28_nonsep (the parity step that 28.6 needs; DG proves it by the        *)
(* orientable Euler parity, OrientableSurfaceEulerParity.lean): a          *)
(* connected compact surface that is not planar (chi + b < 2) contains a   *)
(* polygon in its interior that does not separate it (dual cycle of a      *)
(* tree-cotree decomposition, MOI_FSA_TREE and MOI_FSA_COTREE).             *)

let MOI_S28_NONSEP =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     connected (UNIONS c) /\ ~(UNIONS c = {}) /\
     complex_euler c + &(CARD (components (surface_boundary c))) < &2
     ==> ?l:(real^N->bool)->bool.
           FINITE l /\ combinatorial_manifold 1 l /\ connected (UNIONS l) /\
           ~(UNIONS l = {}) /\
           UNIONS l SUBSET UNIONS c DIFF surface_boundary c /\
           connected (UNIONS c DIFF UNIONS l)`;;

(* s28_plane: planar facts transported along PL homeomorphisms.            *)
(* A polygon in the interior of a PL annulus either cuts off a component   *)
(* of its complement whose closure is a PL 2-cell bounded by it, or every  *)
(* component of its complement reaches an end of the annulus (Moise 27.3   *)
(* in component form, p.198).                                               *)

let MOI_S28_ANNULUS_COMPONENTS =
 `!(a:real^N->bool) j0 j1 j.
     pl_annulus_with_ends a j0 j1 /\ pl_sphere 1 j /\ j SUBSET a DIFF (j0 UNION j1)
     ==> (?k. k IN components (a DIFF j) /\ DISJOINT k (j0 UNION j1) /\
              pl_cell_with_boundary 2 (closure k) j) \/
         (!k. k IN components (a DIFF j) ==> ~(k INTER (j0 UNION j1) = {}))`;;

(* A polygon in a PL 2-cell bounds a PL 2-cell inside it (PL Schoenflies). *)

let MOI_S28_DISK_POLYGON =
 `!(d:real^N->bool) b j.
     pl_cell_with_boundary 2 d b /\ pl_sphere 1 j /\ j SUBSET d
     ==> moi_s28_bounds_disk d j`;;

(* The outputs of MOI_FND_SURFACE_PLANAR for k = 1 and k = 0 in the forms  *)
(* pl_annulus_with_ends (either end may be the inner one) and              *)
(* pl_cell_with_boundary.                                                   *)

let MOI_S28_ANNULUS_FROM_HOLED =
 `!(a:real^N->bool) (f:real^2->real^N) g j0 j1.
     pl_homeomorphism (holed_disk_model 1,a) (f,g) /\
     IMAGE f (frontier (holed_disk_model 1)) = j0 UNION j1 /\
     connected j0 /\ connected j1 /\ ~(j0 = {}) /\ ~(j1 = {}) /\ DISJOINT j0 j1
     ==> pl_annulus_with_ends a j0 j1`;;

let MOI_S28_SQUARE_CELL =
 `!(a:real^N->bool) (f:real^2->real^N) g.
     pl_homeomorphism (holed_disk_model 0,a) (f,g)
     ==> pl_cell_with_boundary 2 a (IMAGE f (frontier (holed_disk_model 0)))`;;

(* A product piece of a bicollar of a polygon is a PL annulus with the two *)
(* levels as ends, and a PL annulus is triangulated by a combinatorial     *)
(* surface with chi 0 whose boundary is the union of the ends.             *)

let MOI_S28_PRODUCT_ANNULUS =
 `!(j:real^N->bool) w (p:real^(N,1)finite_sum->real^N) q a b.
     pl_sphere 1 j /\ moi_s26_bicollar j w p q /\ --(&1) <= a /\ a < b /\ b <= &1
     ==> pl_annulus_with_ends (IMAGE p (j PCROSS {x:real^1 | a <= drop x /\ drop x <= b}))
                              (moi_s26_level j p a) (moi_s26_level j p b)`;;

let MOI_S28_ANNULUS_COMPLEX =
 `!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> ?d. FINITE d /\ combinatorial_manifold_with_boundary 2 d /\ UNIONS d = a /\
             connected a /\ surface_boundary d = j0 UNION j1 /\ complex_euler d = &0`;;

(* s28_torus (Moise 28.1 for the frontier; the CST of p.200 is our          *)
(* pl_solid_torus): the frontier of a PL solid torus in real^3 is a closed *)
(* connected orientable combinatorial surface with chi 0.                  *)

let MOI_S28_TORUS_SETUP_BODY =
 `!s:real^3->bool.
     pl_solid_torus s
     ==> ?t. FINITE t /\ combinatorial_manifold 2 t /\ UNIONS t = frontier s /\
             connected (frontier s) /\ orientable_surface_complex t /\
             complex_euler t = &0`;;

let MOI_S28_TORUS_SETUP =
  sdd_rule [sdd_i3 MOI_FND_PL_SOLID_TORUS_BASIC; MOI_FND_SIDES_ORIENT_R3;
                       sdd_i3 MOI_S28_SURF_LOCAL]
    MOI_S28_TORUS_SETUP_BODY;;

(* s28_sep: on a closed connected orientable surface with chi 0 (a torus), *)
(* a separating polygon cuts off a PL disk (Moise 28.9 for separating      *)
(* curves; DG IsPLTorus.exists_isPLHomeomorphOn_disk_of_not_isPreconnected *)
(* _sdiff), and a polygon bounding no disk has an annulus as complement of *)
(* a thin strip (Moise 28.7, p.204).                                       *)

let MOI_S28_SEP_DISK_BODY =
 `!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool).
     FINITE t /\ combinatorial_manifold 2 t /\ connected (UNIONS t) /\
     orientable_surface_complex t /\ complex_euler t = &0 /\
     FINITE l /\ combinatorial_manifold 1 l /\ connected (UNIONS l) /\
     ~(UNIONS l = {}) /\ UNIONS l SUBSET UNIONS t /\
     ~connected (UNIONS t DIFF UNIONS l)
     ==> ?k. k IN components (UNIONS t DIFF UNIONS l) /\
             pl_cell_with_boundary 2 (closure k) (UNIONS l)`;;

let MOI_S28_SEP_DISK =
  sdd_rule [MOI_FND_SURFACE_PLANAR; MOI_FND_BICOLLAR_CURVE_2;
                       MOI_S28_CUT_SEPARATING_BODY; MOI_S28_NONSEP;
                       MOI_S28_STRIP_REMOVE_BODY; MOI_S28_ANNULUS_FROM_HOLED;
                       MOI_S28_ANNULUS_COMPONENTS; MOI_S28_SQUARE_CELL]
    MOI_S28_SEP_DISK_BODY;;

let MOI_S28_ESSENTIAL_ANNULUS_BODY =
 `!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) w
   (p:real^(N,1)finite_sum->real^N) q.
     FINITE t /\ combinatorial_manifold 2 t /\ connected (UNIONS t) /\
     orientable_surface_complex t /\ complex_euler t = &0 /\
     FINITE l /\ combinatorial_manifold 1 l /\ connected (UNIONS l) /\
     ~(UNIONS l = {}) /\
     moi_s26_bicollar (UNIONS l) w p q /\ w SUBSET UNIONS t /\
     UNIONS l SUBSET (subtopology euclidean (UNIONS t)) interior_of w /\
     ~moi_s28_bounds_disk (UNIONS t) (UNIONS l)
     ==> pl_annulus_with_ends
           (UNIONS t DIFF moi_s26_strip (UNIONS l) p (--(&1 / &2)) (&1 / &2))
           (moi_s26_level (UNIONS l) p (--(&1 / &2)))
           (moi_s26_level (UNIONS l) p (&1 / &2))`;;

let MOI_S28_ESSENTIAL_ANNULUS =
  sdd_rule [MOI_S28_SEP_DISK_BODY; MOI_FND_SURFACE_PLANAR;
                       MOI_S28_STRIP_REMOVE_BODY; MOI_S28_ANNULUS_FROM_HOLED]
    MOI_S28_ESSENTIAL_ANNULUS_BODY;;

(* s28_annuli: Moise 28.6 (p.204), with n >= 2 (hypothesis 2 <= CARD gg):    *)
(* all strips removed at once, every piece has chi 0 and two boundary      *)
(* circles (chi count, SURFACE_PLANAR, SEP_DISK), hence an annulus.        *)

let MOI_S28_286 =
  sdd_rule (MOI_S28_TORUS_SETUP_BODY ::
                       map sdd_i3
                       [MOI_S28_POLYGON_COMPLEX; MOI_FND_BICOLLAR_CURVE_2;
                        MOI_S28_STRIP_REMOVE_BODY; MOI_S28_COMPONENT_COMPLEX;
                        MOI_FND_SURFACE_PLANAR; MOI_S28_SEP_DISK_BODY;
                        MOI_S28_DISK_POLYGON; MOI_S26_SURF_GLUE_BODY;
                        MOI_S28_ANNULUS_FROM_HOLED; MOI_S28_ANNULUS_COMPLEX;
                        MOI_S28_PRODUCT_ANNULUS; MOI_S28_SQUARE_CELL])
    `MOISE_286_STATEMENT`;;

(* s28_h1: Moise 28.8 in the form used on p.244, and 28.10 (p.204; cited   *)
(* as 28.9 on p.222), with integral H_1 (fnd_h1 and pc_top_hurewicz).      *)

let MOI_S28_288 =
  sdd_rule [`MOISE_286_STATEMENT`; sdd_i3 MOI_FND_PL_SOLID_TORUS_BASIC]
    `MOISE_288_STATEMENT`;;

let MOI_S28_2810 =
  sdd_rule (MOI_S28_TORUS_SETUP_BODY ::
                       map sdd_i3
                       [MOI_S28_POLYGON_COMPLEX; MOI_FND_BICOLLAR_CURVE_2;
                        MOI_S28_ESSENTIAL_ANNULUS_BODY; MOI_S28_PRODUCT_ANNULUS])
    `MOISE_2810_STATEMENT`;;

map type_of [MOI_S28_POLYGON_COMPLEX; MOI_S28_STRIP_REMOVE; MOI_S28_CUT_SEPARATING;
             MOI_S28_COMPONENT_COMPLEX; MOI_S28_NONSEP; MOI_S28_ANNULUS_COMPONENTS;
             MOI_S28_DISK_POLYGON; MOI_S28_ANNULUS_FROM_HOLED; MOI_S28_SQUARE_CELL;
             MOI_S28_PRODUCT_ANNULUS; MOI_S28_ANNULUS_COMPLEX; MOI_S28_TORUS_SETUP;
             MOI_S28_SEP_DISK; MOI_S28_ESSENTIAL_ANNULUS; MOI_S28_286; MOI_S28_288;
             MOI_S28_2810];;
(* ========================================================================= *)
(* Part 4. Glue: the statements and the input terms imply the seven items.   *)
(* sdd_derive proves a term from assumed leaves (instances of the            *)
(* statements, of the foundation and Schoenflies input terms, and            *)
(* LOOP_THEOREM_3_STATEMENT for the producer) by Modus Ponens along the      *)
(* rules recorded by sdd_rule, matching up to type instantiation;            *)
(* MOI_FD_268_GLUE of pc_moi_fnd_stmt.ml is the rule for 26.8.  Each glue    *)
(* theorem has as hypotheses exactly the leaf instances it uses; a           *)
(* polymorphic theorem gives every instance by INST_TYPE.                    *)
(* ========================================================================= *)

let MOI_S26_UNIT_TARGETS =
  [MOI_S26_EVEN_CROSSING; MOI_S26_LOCAL_TRI; MOI_S26_LOCAL_EDGE; MOI_S26_SEP;
   MOI_S26_SURF_GLUE; MOI_S26_INT_CONNECTED; MOI_S26_THREE;
   MOI_S26_COMPACT_NBHD; MOI_S26_CUT; MOI_S26_PL_FILL; MOI_S26_LEVEL_CIRCLES;
   MOI_S26_EXT];;

let MOI_S28_UNIT_TARGETS =
  [MOI_S28_SURF_CHARTS; MOI_S28_POLYGON_COMPLEX; MOI_S28_SURF_LOCAL;
   MOI_S28_SURF_INVARIANT; MOI_S28_STRIP_REMOVE; MOI_S28_CUT_SEPARATING;
   MOI_S28_COMPONENT_COMPLEX; MOI_S28_NONSEP; MOI_S28_ANNULUS_COMPONENTS;
   MOI_S28_DISK_POLYGON; MOI_S28_ANNULUS_FROM_HOLED; MOI_S28_SQUARE_CELL;
   MOI_S28_PRODUCT_ANNULUS; MOI_S28_ANNULUS_COMPLEX; MOI_S28_TORUS_SETUP;
   MOI_S28_SEP_DISK; MOI_S28_ESSENTIAL_ANNULUS; MOI_S28_286; MOI_S28_288;
   MOI_S28_2810];;

let MOI_SDD_UNIT_TARGETS = MOI_S26_UNIT_TARGETS @ MOI_S28_UNIT_TARGETS;;

(* Inputs from other parts: foundation terms of pc_moi_fnd_stmt.ml and the   *)
(* term MOI_SCH3_SPHERE_SPLIT (copied text MOI_S26_SPHERE_SPLIT).            *)

let MOI_SDD_INPUTS =
  [MOI_FND_SIDES_ORIENT_R3; MOI_FND_BICOLLAR_R3; MOI_FND_BICOLLAR_CURVE_2;
   MOI_FND_SURFACE_PLANAR; MOI_FND_PL_SOLID_TORUS_BASIC;
   MOI_FND_DERIVED_NBHD_MANIFOLD; MOI_S26_SPHERE_SPLIT];;

let MOI_SDD_ALL_LEAVES =
  MOI_SDD_UNIT_TARGETS @ MOI_SDD_INPUTS @ [`LOOP_THEOREM_3_STATEMENT`];;

(* Type instance test: t is pat with its type variables instantiated.       *)

let sdd_tyinst pat t =
  try let (_,tms,tys) = term_match [] pat t in
      if tms = [] && inst tys pat = t then Some tys else None
  with Failure _ -> None;;

let sdd_is_leaf t =
  exists (fun l -> sdd_tyinst l t <> None) MOI_SDD_ALL_LEAVES;;

let rec sdd_derive t =
  if sdd_is_leaf t then ASSUME t
  else if t = `MOISE_268_STATEMENT` then
    MP MOI_FD_268_GLUE
       (CONJ (sdd_derive MOI_FND_SIDES_ORIENT_R3) (sdd_derive `MOISE_266_STATEMENT`))
  else
    let (ins,body,imp),tys =
      tryfind (fun ((_,b,_) as r) ->
                 match sdd_tyinst b t with Some tys -> r,tys | None -> failwith "")
              !sdd_rules in
    MP (sdd_derive (inst tys imp)) (end_itlist CONJ (map (sdd_derive o inst tys) ins));;

(* Leaf instances in master order (by generic leaf, then by print form).    *)

let sdd_index t =
  let rec go i l = match l with
      [] -> failwith "sdd_index"
    | h::r -> if sdd_tyinst h t <> None then i else go (i + 1) r in
  go 0 MOI_SDD_ALL_LEAVES;;

let sdd_order ts =
  let key t = (sdd_index t, string_of_term t) in
  (* Candle: < is on int only; this is OCaml's order on (int * string) pairs *)
  let lt (i1,s1) (i2,s2) = i1 < i2 || (i1 = i2 && String.compare s1 s2 < 0) in
  sort (fun a b -> lt (key a) (key b)) (setify Term.(<) ts);;

let rec sdd_split n th =
  if n <= 1 then [th] else CONJUNCT1 th :: sdd_split (n - 1) (CONJUNCT2 th);;

let sdd_close th =
  let used = sdd_order (hyp th) in
  let cj = list_mk_conj used in
  DISCH cj (itlist PROVE_HYP (sdd_split (length used) (ASSUME cj)) th);;

let sdd_th266 = sdd_derive `MOISE_266_STATEMENT`;;
let sdd_th267 = sdd_derive `MOISE_267_STATEMENT`;;
let sdd_th268 = sdd_derive `MOISE_268_STATEMENT`;;
let sdd_th286 = sdd_derive `MOISE_286_STATEMENT`;;
let sdd_th288 = sdd_derive `MOISE_288_STATEMENT`;;
let sdd_th2810 = sdd_derive `MOISE_2810_STATEMENT`;;
let sdd_thp264 = DISCH `LOOP_THEOREM_3_STATEMENT`
                       (sdd_derive `MOISE_264_OPEN_STATEMENT`);;

(* One glue theorem per item; the producer discharges                        *)
(* LOOP_THEOREM_3_STATEMENT into the implication MOI_PROD_264.               *)

let MOI_SDD_266 = sdd_close sdd_th266;;
let MOI_SDD_267 = sdd_close sdd_th267;;
let MOI_SDD_268 = sdd_close sdd_th268;;
let MOI_SDD_286 = sdd_close sdd_th286;;
let MOI_SDD_288 = sdd_close sdd_th288;;
let MOI_SDD_2810 = sdd_close sdd_th2810;;
let MOI_SDD_PROD_264 = sdd_close sdd_thp264;;

(* The closure: the leaf instances used by any item imply all seven.       *)

let MOI_SDD_ITEMS =
  [`MOISE_266_STATEMENT`; `MOISE_267_STATEMENT`; `MOISE_268_STATEMENT`;
   `MOISE_286_STATEMENT`; `MOISE_288_STATEMENT`; `MOISE_2810_STATEMENT`;
   MOI_PROD_264];;

let MOI_SDD_CLOSURE =
  sdd_close (end_itlist CONJ [sdd_th266; sdd_th267; sdd_th268; sdd_th286;
                              sdd_th288; sdd_th2810; sdd_thp264]);;

(* The leaf instances of the closure (its antecedent, split in order).      *)

let MOI_SDD_CLOSURE_LEAVES =
  sdd_order (itlist (union o hyp) [sdd_th266; sdd_th267; sdd_th268; sdd_th286;
                                   sdd_th288; sdd_th2810; sdd_thp264] []);;

(* Shape checks: no hypotheses; the closure concludes the seven items, the   *)
(* producer is MOI_PROD_264 (= MOI_CORE_GLUE_264); every leaf instance is a  *)
(* type instance of a declared statement or input; every declared statement  *)
(* and input is used; all declared terms are closed boolean terms.           *)

let MOI_SDD_SHAPE =
  forall (fun th -> hyp th = [])
    [MOI_SDD_266; MOI_SDD_267; MOI_SDD_268; MOI_SDD_286; MOI_SDD_288; MOI_SDD_2810;
     MOI_SDD_PROD_264; MOI_SDD_CLOSURE] &&
  rand(concl MOI_SDD_CLOSURE) = list_mk_conj MOI_SDD_ITEMS &&
  lhand(concl MOI_SDD_CLOSURE) = list_mk_conj MOI_SDD_CLOSURE_LEAVES &&
  rand(concl MOI_SDD_PROD_264) = MOI_PROD_264 &&
  MOI_PROD_264 = MOI_CORE_GLUE_264 &&
  forall sdd_is_leaf MOI_SDD_CLOSURE_LEAVES &&
  forall (fun l -> exists (fun t -> sdd_tyinst l t <> None) MOI_SDD_CLOSURE_LEAVES)
         (MOI_SDD_UNIT_TARGETS @ MOI_SDD_INPUTS) &&
  forall (fun t -> type_of t = bool_ty && frees t = [])
         (MOI_SDD_UNIT_TARGETS @ MOI_SDD_INPUTS);;

(MOI_SDD_SHAPE, length MOI_SDD_CLOSURE_LEAVES, length MOI_SDD_UNIT_TARGETS,
 length MOI_SDD_INPUTS, length !sdd_rules);;
(* ========================================================================= *)
(* Part 5. Sanity theorems (HYP 0): degenerate cases of the vocabulary and   *)
(* statements, non-vacuity of the chart definitions, and a                   *)
(* teeth test (a boundary point of the half plane has no planar chart, so  *)
(* the boundary characterizations of SURF_CHARTS and SURF_LOCAL are not    *)
(* vacuous).                                                                *)
(* ========================================================================= *)

let MOI_SDD_SAN_LEVEL_EMPTY = prove
 (`!(p:real^(N,1)finite_sum->real^N) t a b.
      moi_s26_level {} p t = {} /\ moi_s26_strip {} p a b = {}`,
  REWRITE_TAC[moi_s26_level; moi_s26_strip; PCROSS_EMPTY; IMAGE_CLAUSES]);;

let MOI_SDD_SAN_STRIP_EMPTY = prove
 (`!(m:real^N->bool) (p:real^(N,1)finite_sum->real^N) a b.
      b <= a ==> moi_s26_strip m p a b = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s26_strip] THEN
  SUBGOAL_THEN `{x:real^1 | a < drop x /\ drop x < b} = {}`
    (fun th -> REWRITE_TAC[th; PCROSS_EMPTY; IMAGE_CLAUSES]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  GEN_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let MOI_SDD_SAN_LEVEL_IN_STRIP = prove
 (`!(m:real^N->bool) (p:real^(N,1)finite_sum->real^N) a b t.
      a < t /\ t < b ==> moi_s26_level m p t SUBSET moi_s26_strip m p a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s26_level; moi_s26_strip] THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC PCROSS_MONO THEN
  REWRITE_TAC[SUBSET_REFL; SUBSET; IN_SING; IN_ELIM_THM] THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]);;

let MOI_SDD_SAN_BOUNDS_DISK_MONO = prove
 (`!(t:real^N->bool) t' j.
      t SUBSET t' /\ moi_s28_bounds_disk t j ==> moi_s28_bounds_disk t' j`,
  REWRITE_TAC[moi_s28_bounds_disk] THEN MESON_TAC[SUBSET_TRANS]);;

let MOI_SDD_SAN_LOCALLY_R2_PLANE = prove
 (`!y:real^2. moi_s28_locally_r2 (:real^2) y`,
  GEN_TAC THEN REWRITE_TAC[moi_s28_locally_r2] THEN
  EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[OPEN_IN_REFL; IN_UNIV; HOMEOMORPHIC_REFL] THEN
  REWRITE_TAC[GSYM OPEN_IN; OPEN_UNIV; SUBTOPOLOGY_UNIV]);;

let MOI_SDD_SAN_LOCALLY_HALF = prove
 (`moi_s28_locally_half {z:real^2 | &0 <= z$2} (vec 0)`,
  REWRITE_TAC[moi_s28_locally_half] THEN
  MAP_EVERY EXISTS_TAC [`{z:real^2 | &0 <= z$2}`; `\x:real^2. x`; `\x:real^2. x`] THEN
  REWRITE_TAC[OPEN_IN_REFL; HOMEOMORPHISM_ID; IN_ELIM_THM; VEC_COMPONENT;
              REAL_LE_REFL]);;

(* Teeth: the origin of the closed half plane has no planar chart          *)
(* (invariance of domain).                                                  *)

let MOI_SDD_SAN_HALF_NOT_R2 = prove
 (`~moi_s28_locally_r2 {z:real^2 | &0 <= z$2} (vec 0)`,
  REWRITE_TAC[moi_s28_locally_r2; NOT_EXISTS_THM] THEN
  X_GEN_TAC `u:real^2->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[HOMEOMORPHIC_SYM]) THEN
  REWRITE_TAC[homeomorphic; homeomorphism; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^2->real^2`; `h:real^2->real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(u:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^2->real^2`; `(:real^2)`] INVARIANCE_OF_DOMAIN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC
      [GSYM (SPEC `x:real^2` (REWRITE_RULE[IN_UNIV] th))]) THEN
    ASM_MESON_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2->bool) SUBSET {z:real^2 | &0 <= z$2}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
                check (fun th -> concl th = `open (u:real^2->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(--(e / &2) % basis 2:real^2) IN ball(vec 0,e)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(--(e / &2) % basis 2:real^2) IN {z:real^2 | &0 <= z$2}` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[IN_ELIM_THM; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  ASM_REAL_ARITH_TAC);;

(* EVEN_CROSSING: the closed polygon with no edges has no crossings.       *)

let MOI_SDD_SAN_CROSSING_0 = prove
 (`!(c:(real^3->bool)->bool) (p:num->real^3).
      FINITE {(i,x) | i < 0 /\ x IN segment[p i,p (SUC i)] /\ x IN UNIONS c} /\
      EVEN (CARD {(i,x) | i < 0 /\ x IN segment[p i,p (SUC i)] /\ x IN UNIONS c})`,
  REWRITE_TAC[LT] THEN
  SUBGOAL_THEN `{(i:num,x:real^3) | F} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; FORALL_PAIR_THM; PAIR_EQ] THEN
    MESON_TAC[];
    REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; EVEN]]);;

(* NONSEP: every hypothesis but the nonemptiness of the polyhedron holds   *)
(* for the empty complex, and its conclusion fails there, so that          *)
(* hypothesis is needed (degenerate-case check).                            *)

let MOI_SDD_SAN_NONSEP_EMPTY = prove
 (`FINITE ({}:(real^N->bool)->bool) /\
   combinatorial_manifold_with_boundary 2 ({}:(real^N->bool)->bool) /\
   connected (UNIONS ({}:(real^N->bool)->bool)) /\
   complex_euler ({}:(real^N->bool)->bool) +
   &(CARD (components (surface_boundary ({}:(real^N->bool)->bool)))) < &2 /\
   ~(?l:(real^N->bool)->bool.
        ~(UNIONS l = {}) /\
        UNIONS l SUBSET UNIONS {} DIFF surface_boundary ({}:(real^N->bool)->bool))`,
  REWRITE_TAC[FINITE_EMPTY; UNIONS_0; CONNECTED_EMPTY; EMPTY_DIFF;
              SUBSET_EMPTY; MOI_FD_COMPLEX_EULER_EMPTY] THEN
  REWRITE_TAC[surface_boundary; NOT_IN_EMPTY; EMPTY_GSPEC; UNIONS_0;
              COMPONENTS_EMPTY; CARD_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex;
                NOT_IN_EMPTY; UNIONS_0];
    REAL_ARITH_TAC;
    MESON_TAC[]]);;

(* COMPONENT_COMPLEX at the empty complex: no components, chi 0.           *)

let MOI_SDD_SAN_COMPONENT_EMPTY = prove
 (`FINITE (components (UNIONS ({}:(real^N->bool)->bool))) /\
   complex_euler ({}:(real^N->bool)->bool) =
   sum (components (UNIONS ({}:(real^N->bool)->bool)))
       (\k. complex_euler {s | s IN ({}:(real^N->bool)->bool) /\ s SUBSET k})`,
  REWRITE_TAC[UNIONS_0; COMPONENTS_EMPTY; FINITE_EMPTY; SUM_CLAUSES;
              MOI_FD_COMPLEX_EULER_EMPTY]);;

(* SURF_GLUE at three empty sets: the empty complex is the glued surface.  *)

let MOI_SDD_SAN_GLUE_EMPTY = prove
 (`?e:(real^N->bool)->bool.
      FINITE e /\ combinatorial_manifold_with_boundary 2 e /\
      UNIONS e = UNIONS {} UNION UNIONS {} /\
      surface_boundary e =
      (surface_boundary ({}:(real^N->bool)->bool) DIFF {}) UNION
      (surface_boundary ({}:(real^N->bool)->bool) DIFF {}) /\
      complex_euler e = complex_euler ({}:(real^N->bool)->bool) +
                        complex_euler ({}:(real^N->bool)->bool) /\
      combinatorial_manifold 2 e`,
  EXISTS_TAC `{}:(real^N->bool)->bool` THEN
  REWRITE_TAC[FINITE_EMPTY; UNIONS_0; UNION_EMPTY; EMPTY_DIFF; DIFF_EMPTY;
              UNION_IDEMPOT; MOI_FD_COMPLEX_EULER_EMPTY; REAL_ADD_LID] THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary; combinatorial_manifold;
              lf_simplicial_complex; NOT_IN_EMPTY; UNIONS_0]);;

(* STRIP_REMOVE with no curves: nothing is removed and no boundary added.  *)

let MOI_SDD_SAN_STRIP_NO_CURVES = prove
 (`!(c:(real^N->bool)->bool) (p:real^(N,1)finite_sum->real^N) a b.
      UNIONS c DIFF moi_s26_strip (UNIONS {}) p a b = UNIONS c /\
      surface_boundary c UNION moi_s26_level (UNIONS {}) p a UNION
      moi_s26_level (UNIONS {}) p b = surface_boundary c`,
  REWRITE_TAC[UNIONS_0; MOI_SDD_SAN_LEVEL_EMPTY; DIFF_EMPTY; UNION_EMPTY]);;

let MOI_SDD_SANITY =
  [MOI_SDD_SAN_LEVEL_EMPTY; MOI_SDD_SAN_STRIP_EMPTY; MOI_SDD_SAN_LEVEL_IN_STRIP;
   MOI_SDD_SAN_BOUNDS_DISK_MONO; MOI_SDD_SAN_LOCALLY_R2_PLANE;
   MOI_SDD_SAN_LOCALLY_HALF; MOI_SDD_SAN_HALF_NOT_R2; MOI_SDD_SAN_CROSSING_0;
   MOI_SDD_SAN_NONSEP_EMPTY; MOI_SDD_SAN_COMPONENT_EMPTY; MOI_SDD_SAN_GLUE_EMPTY;
   MOI_SDD_SAN_STRIP_NO_CURVES];;

map (fun th -> length (hyp th)) MOI_SDD_SANITY;;
(* ========================================================================= *)
(* Final checks (printed): every glue and sanity theorem has no            *)
(* hypotheses, the glue shape holds, and no axiom was added (3 axioms).    *)
(* ========================================================================= *)

let MOI_SDD_THEOREMS =
  [MOI_SDD_266; MOI_SDD_267; MOI_SDD_268; MOI_SDD_286; MOI_SDD_288; MOI_SDD_2810;
   MOI_SDD_PROD_264; MOI_SDD_CLOSURE] @ MOI_SDD_SANITY;;

let MOI_SDD_CHECK =
  MOI_SDD_SHAPE &&
  forall (fun th -> hyp th = []) MOI_SDD_THEOREMS &&
  length (axioms()) = 3;;

(length MOI_SDD_UNIT_TARGETS, length MOI_SDD_INPUTS, length MOI_SDD_THEOREMS,
 length MOI_SDD_CLOSURE_LEAVES, MOI_SDD_CHECK);;

