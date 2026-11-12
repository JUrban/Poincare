(* ========================================================================= *)
(* pc_moi_s33_stmt: the statements of Moise 33.1 in tube form                *)
(* (MOISE_331_STATEMENT, producer MOI_PROD_331 of pc_moi_core_stmt.ml; Moise *)
(* GTM 47, Sec 33, printed pp.230-238, PDF +9): definitions moi_s33_...,     *)
(* statement terms MOI_S33_... (each proved in one of the pc_moi_s33 files), *)
(* glue theorems MOI_S3D_... with the statement terms as hypotheses (the     *)
(* closure MOI_S3D_PROD_331: the statements and a few foundation terms imply *)
(* MOI_PROD_331) and sanity theorems MOI_S3D_SAN_....  Loads after           *)
(* pc_moi_fnd_stmt.ml.                                                       *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;



prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: vocabulary.  Notation: (t,l) the canonical tube in real^3, N =   *)
(* derived_nbhd t l, C_v = derived_dual_cell t l v, Bd N = derived_frontier *)
(* t l (= frontier N in real^3); h the embedding of the union of t.  Target *)
(* side: N' = IMAGE h N, K' = IMAGE h (UNIONS l), W = interior N' minus K'  *)
(* (moi_s33_ww), pseudo-cells e s and pieces c v from 32.3 (moi_s33_hd),    *)
(* the polyhedral 3-manifold X = UNIONS x with Bd X = frontier (UNIONS x).  *)
(* ========================================================================= *)

(* The hypotheses of MOISE_331_STATEMENT: a finite connected graph with an  *)
(* edge and no vertex of degree 1 in a finite complex t, h an embedding.    *)

let moi_s33_tube = new_definition
 `moi_s33_tube (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)
               (h:real^3->real^3) <=>
    FINITE t /\ graph_in_complex t l /\ connected (UNIONS l) /\
    (?s. s IN l /\ aff_dim s = &1) /\
    (!v. {v} IN l ==> ~(CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s} = 1)) /\
    h continuous_on UNIONS t /\
    (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y)`;;

(* W = Int N' - K' (p.234), the open set of Lemmas 9-10 and of 26.4.        *)

let moi_s33_ww = new_definition
 `moi_s33_ww (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)
             (h:real^3->real^3) =
    interior (IMAGE h (derived_nbhd t l)) DIFF IMAGE h (UNIONS l)`;;

(* The rim h(Bd D) of the splitting disk D = C_u INTER C_v (as written in   *)
(* MOISE_323_STATEMENT).                                                     *)

let moi_s33_rim = new_definition
 `moi_s33_rim (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)
              (h:real^3->real^3) (u:real^3) (v:real^3) =
    IMAGE h (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
             frontier (derived_nbhd t l))`;;

(* The handle decomposition given by 32.3 (p.228; DG IsHandleDecomposition- *)
(* OfTube PL/PseudoCell.lean:251): the conclusions of MOISE_323_STATEMENT   *)
(* without the smallness clause c v SUBSET nb v.                             *)

let moi_s33_hd = new_definition
 `moi_s33_hd (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)
             (h:real^3->real^3) (e:(real^3->bool)->real^3->bool)
             (c:real^3->real^3->bool) <=>
    moi_s33_tube t l h /\
    (!u v. ~(u = v) /\ segment[u,v] IN l
           ==> pseudo_cell (e(segment[u,v])) (moi_s33_rim t l h u v)
                           (h(midpoint(u,v))) /\
               e(segment[u,v]) INTER IMAGE h (UNIONS l) = {h(midpoint(u,v))} /\
               e(segment[u,v]) INTER frontier (IMAGE h (derived_nbhd t l)) =
               moi_s33_rim t l h u v) /\
    (!s s'. s IN l /\ s' IN l /\ aff_dim s = &1 /\ aff_dim s' = &1 /\ ~(s = s')
            ==> DISJOINT (e s) (e s')) /\
    (!v. {v} IN l
         ==> c v = closure (connected_component
                     (IMAGE h (derived_nbhd t l) DIFF
                      UNIONS {e s | s IN l /\ aff_dim s = &1}) (h v)) /\
             c v INTER IMAGE h {w | {w} IN l} = {h v}) /\
    IMAGE h (derived_nbhd t l) = UNIONS {c v | {v} IN l} /\
    (!v w. {v} IN l /\ {w} IN l /\ ~(v = w)
           ==> c v INTER c w = (if segment[v,w] IN l then e(segment[v,w]) else {}))`;;

(* Lemma 2 (p.231; DG IsPolyhedralTubeNeighborhood, PolyhedralTube-         *)
(* Neighborhood.lean:18): X a compact combinatorial 3-manifold with         *)
(* boundary, a neighbourhood of K' inside Int N', whose frontier crosses     *)
(* every pseudo-cell interior (E minus its rim) in the PL sense.            *)

let moi_s33_x2 = new_definition
 `moi_s33_x2 (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)
             (h:real^3->real^3) (e:(real^3->bool)->real^3->bool)
             (x:(real^3->bool)->bool) <=>
    FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
    IMAGE h (UNIONS l) SUBSET interior (UNIONS x) /\
    UNIONS x SUBSET interior (IMAGE h (derived_nbhd t l)) /\
    (!u v y. ~(u = v) /\ segment[u,v] IN l /\
             y IN e(segment[u,v]) INTER frontier (UNIONS x)
             ==> pl_crossing_at (e(segment[u,v]) DIFF moi_s33_rim t l h u v)
                                (frontier (UNIONS x)) y)`;;

(* Lemmas 3-4 (pp.231-232; DG HasSinglePolygonTraces): each trace E INTER  *)
(* Bd X is one PL polygon bounding the disk E INTER X (which contains the   *)
(* centre, an interior point of X).                                          *)

let moi_s33_traces = new_definition
 `moi_s33_traces (l:(real^3->bool)->bool) (e:(real^3->bool)->real^3->bool)
                 (x:(real^3->bool)->bool) <=>
    !u v. ~(u = v) /\ segment[u,v] IN l
          ==> pl_sphere 1 (e(segment[u,v]) INTER frontier (UNIONS x)) /\
              disk_with_boundary (e(segment[u,v]) INTER UNIONS x)
                                 (e(segment[u,v]) INTER frontier (UNIONS x))`;;

(* Lemmas 2-5 together: the X-invariants (Lemma 5: X and Bd X connected).   *)

let moi_s33_inv = new_definition
 `moi_s33_inv (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)
              (h:real^3->real^3) (e:(real^3->bool)->real^3->bool)
              (x:(real^3->bool)->bool) <=>
    moi_s33_x2 t l h e x /\ moi_s33_traces l e x /\
    connected (UNIONS x) /\ connected (frontier (UNIONS x))`;;

(* Lemma 6 (p.232; DG HasConnectedHandlePieces): a triangulation bx of Bd X *)
(* in which every piece A_v' = c v INTER Bd X is a connected subcomplex,    *)
(* a surface whose boundary is the union of the traces at v.                *)

let moi_s33_pieces = new_definition
 `moi_s33_pieces (l:(real^3->bool)->bool) (e:(real^3->bool)->real^3->bool)
                 (c:real^3->real^3->bool) (x:(real^3->bool)->bool)
                 (bx:(real^3->bool)->bool) <=>
    FINITE bx /\ combinatorial_manifold 2 bx /\ UNIONS bx = frontier (UNIONS x) /\
    (!v. {v} IN l
         ==> combinatorial_manifold_with_boundary 2 {s | s IN bx /\ s SUBSET c v} /\
             UNIONS {s | s IN bx /\ s SUBSET c v} = c v INTER frontier (UNIONS x) /\
             connected (c v INTER frontier (UNIONS x)) /\
             surface_boundary {s | s IN bx /\ s SUBSET c v} =
             UNIONS {e(segment[v,w]) INTER frontier (UNIONS x) | w |
                     ~(w = v) /\ segment[v,w] IN l})`;;

(* Loop theorem disks (p.232; DG IsLoopTheoremDisk, LoopTheoremDisk-        *)
(* Vocabulary.lean:12), in exactly the shape of the conclusion of           *)
(* MOISE_264_OPEN_STATEMENT with u = W and the surface Bd X.                *)

let moi_s33_ltd = new_definition
 `moi_s33_ltd (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)
              (h:real^3->real^3) (x:(real^3->bool)->bool) (d:real^3->bool) <=>
    ?(k:real^3->bool) (f:real^3->real^3) g.
      &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\ d SUBSET moi_s33_ww t l h /\
      d INTER frontier (UNIONS x) = IMAGE f (relative_frontier k) /\
      ~(?a. homotopic_with (\q. T)
              (subtopology euclidean (IMAGE f (relative_frontier k)),
               subtopology euclidean (frontier (UNIONS x)))
              (\y. y) (\y. a))`;;

(* Lemma 7 (p.232): no piece c v contains a loop theorem disk.              *)

let moi_s33_noltd = new_definition
 `moi_s33_noltd (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)
                (h:real^3->real^3) (c:real^3->real^3->bool)
                (x:(real^3->bool)->bool) <=>
    !v d. {v} IN l /\ moi_s33_ltd t l h x d ==> ~(d SUBSET c v)`;;

(* Lemma 12 (p.236): every piece A_v' is a PL disk with deg(v) - 1 holes,  *)
(* its boundary circles being the traces at v (the same shape as           *)
(* MOI_FND_GRAPH_TUBE_HOLES for the source pieces A_v).                     *)

let moi_s33_holed = new_definition
 `moi_s33_holed (l:(real^3->bool)->bool) (e:(real^3->bool)->real^3->bool)
                (c:real^3->real^3->bool) (x:(real^3->bool)->bool) <=>
    !v. {v} IN l
        ==> ?(f:real^2->real^3) g d.
              CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s} = d + 1 /\
              pl_homeomorphism (holed_disk_model d, c v INTER frontier (UNIONS x)) (f,g) /\
              IMAGE f (frontier (holed_disk_model d)) =
              UNIONS {e(segment[v,w]) INTER frontier (UNIONS x) | w |
                      ~(w = v) /\ segment[v,w] IN l}`;;

(* Lemma 13 (p.236): a PLH Bd N -> Bd X carrying A_v onto A_v' and each    *)
(* rim onto the corresponding trace.                                         *)

let moi_s33_match = new_definition
 `moi_s33_match (t:(real^3->bool)->bool) (l:(real^3->bool)->bool)
                (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
                (x:(real^3->bool)->bool) (g:real^3->real^3) <=>
    (?g'. pl_homeomorphism (derived_frontier t l, frontier (UNIONS x)) (g,g')) /\
    (!v. {v} IN l
         ==> IMAGE g (derived_dual_cell t l v INTER derived_frontier t l) =
             c v INTER frontier (UNIONS x)) /\
    (!u v. ~(u = v) /\ segment[u,v] IN l
           ==> IMAGE g (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                        derived_frontier t l) =
               e(segment[u,v]) INTER frontier (UNIONS x))`;;

(* ========================================================================= *)
(* Part 1b: Z/2 loop characters (replacing the book's pi_1 -> H_1 step,     *)
(* Lemma 11 p.236).  A character of s is a Z/2-valued function on the loops *)
(* in s (here: a predicate, false off the loops of s), invariant under free *)
(* homotopy in s and additive under concatenation of loops at one base     *)
(* point (Hom(pi_1(s), Z/2) without group structure).  For a connected      *)
(* closed surface there are 2^(2 - chi) of them; for one with boundary      *)
(* 2^(1 - chi).  moi_s33_pi1 s w: loops of s null-homotopic in w are        *)
(* null-homotopic in s (Lemma 9 with 26.4), and at some base point a of s   *)
(* every loop of w is homotopic rel a to a loop of s (Lemma 10).            *)
(* Simplicial Z/2 cohomology: classes of z2_cocycle modulo z2_coboundary    *)
(* (both defined in pc_moi_fnd_stmt.ml).                                    *)
(* ========================================================================= *)

let moi_s33_char = new_definition
 `moi_s33_char (s:real^N->bool) (phi:(real^1->real^N)->bool) <=>
    (!p. phi p ==> path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p) /\
    (!p q. homotopic_loops s p q ==> (phi p <=> phi q)) /\
    (!p q. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
           path q /\ path_image q SUBSET s /\ pathstart q = pathstart p /\
           pathfinish q = pathstart p
           ==> (phi (p ++ q) <=> ~(phi p <=> phi q)))`;;

let moi_s33_pi1 = new_definition
 `moi_s33_pi1 (s:real^N->bool) (w:real^N->bool) <=>
    s SUBSET w /\
    (!p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
         homotopic_loops w p (linepath(pathstart p,pathstart p))
         ==> homotopic_loops s p (linepath(pathstart p,pathstart p))) /\
    (?a. a IN s /\
         !p. path p /\ path_image p SUBSET w /\ pathstart p = a /\ pathfinish p = a
             ==> ?q. path q /\ path_image q SUBSET s /\ pathstart q = a /\
                     pathfinish q = a /\ homotopic_paths w p q)`;;

let moi_s33_z2class = new_definition
 `moi_s33_z2class (c:(real^N->bool)->bool) (z:(real^N->bool)->bool) =
    {z' | z2_cocycle c z' /\ z2_coboundary c ((z DIFF z') UNION (z' DIFF z))}`;;

let moi_s33_h1z2 = new_definition
 `moi_s33_h1z2 (c:(real^N->bool)->bool) =
    {moi_s33_z2class c z | z | z2_cocycle c z}`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s33_ww; moi_s33_rim; moi_s33_z2class; moi_s33_h1z2];;

(* ========================================================================= *)
(* Part 2: the statement terms (closed boolean terms).  Each is introduced   *)
(* by the short name s33_x of the file pc_moi_s33_x that proves it.  Book    *)
(* statement constants that a proof needs (inputs of MOI_PROD_331) and the   *)
(* statements proved in other files of this section appear as antecedents;   *)
(* foundation terms MOI_FND_... are used inside the proofs, which prove the  *)
(* implication from them and then discharge them by MP.                      *)
(* ========================================================================= *)

(* s33_frame (p.223, p.234): facts about the canonical tube and its image. *)
(* N' = h(N) has interior h(N - Bd N) and frontier h(Bd N) (invariance of   *)
(* domain); K' lies in Int N'; Bd N is path connected; the complement of N'  *)
(* is connected (handlebody; local one-sidedness at the frontier); W is     *)
(* homeomorphic to Bd N x (0,1) (MOI_FND_GRAPH_TUBE_PRODUCT through h).     *)

let MOI_S33_TUBE_FACTS =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3).
     moi_s33_tube t l h
     ==> FINITE l /\
         frontier (derived_nbhd t l) = derived_frontier t l /\
         compact (derived_nbhd t l) /\ derived_nbhd t l SUBSET UNIONS t /\
         (!v. compact (derived_dual_cell t l v)) /\
         compact (IMAGE h (UNIONS l)) /\
         interior (IMAGE h (derived_nbhd t l)) =
         IMAGE h (derived_nbhd t l DIFF derived_frontier t l) /\
         frontier (IMAGE h (derived_nbhd t l)) = IMAGE h (derived_frontier t l) /\
         IMAGE h (UNIONS l) SUBSET interior (IMAGE h (derived_nbhd t l)) /\
         path_connected (derived_frontier t l) /\ ~(derived_frontier t l = {}) /\
         connected ((:real^3) DIFF IMAGE h (derived_nbhd t l)) /\
         ?(f:real^(3,1)finite_sum->real^3) g.
           homeomorphism
             (derived_frontier t l PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},
              moi_s33_ww t l h) (f,g)`;;

(* s33_x2 (Lemma 2, p.231): a polyhedral tube neighbourhood in general      *)
(* position (a fine triangulated neighbourhood of K' in Int N', its derived *)
(* neighbourhood, MOI_FND_GP_SURFACES_3 against the pseudo-cell interiors). *)

let MOI_S33_X2 =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool).
     moi_s33_hd t l h e c ==> ?x. moi_s33_x2 t l h e x`;;

(* s33_char (2D recognition; DG PolyhedralDiskRecognition.lean:89): a       *)
(* compact polyhedron homeomorphic to a disk (to the model disk with k     *)
(* holes) is a PL disk (PL holed disk) with the same boundary.  Route: the  *)
(* charts of triangulated surfaces (POLY_DISK of pc_moi_s30_tame,           *)
(* SURF_LOCAL) for the local structure, the character count for chi,        *)
(* MOI_FND_SURFACE_PLANAR.                                                  *)

let MOI_S33_DISK_RECOG_BODY =
 `!d j:real^N->bool.
     pl_polyhedron d /\ disk_with_boundary d j /\ pl_sphere 1 j
     ==> pl_cell_with_boundary 2 d j`;;

let MOI_S33_HOLED_RECOG_BODY =
 `!k (a:real^N->bool) (f:real^2->real^N) g.
     pl_polyhedron a /\ homeomorphism (holed_disk_model k,a) (f,g) /\
     pl_polyhedron (IMAGE f (frontier (holed_disk_model k)))
     ==> ?f' g'. pl_homeomorphism (holed_disk_model k,a) (f',g') /\
                 IMAGE f' (frontier (holed_disk_model k)) =
                 IMAGE f (frontier (holed_disk_model k))`;;

(* s33_char (characters): transfer along a pi_1 isomorphism in map form,    *)
(* invariance under homeomorphisms, the product with an open interval, and *)
(* path connectedness of connected finite unions of closed convex sets.     *)

let MOI_S33_CHAR_TRANSFER =
 `!s w:real^N->bool.
     path_connected s /\ path_connected w /\ moi_s33_pi1 s w
     ==> !n. {phi | moi_s33_char s phi} HAS_SIZE n <=>
             {phi | moi_s33_char w phi} HAS_SIZE n`;;

let MOI_S33_CHAR_HOMEO =
 `!(s:real^M->bool) (s':real^N->bool) f g.
     homeomorphism (s,s') (f,g)
     ==> !n. {phi | moi_s33_char s phi} HAS_SIZE n <=>
             {phi | moi_s33_char s' phi} HAS_SIZE n`;;

let MOI_S33_CHAR_PRODUCT =
 `!s:real^N->bool.
     !n. {phi | moi_s33_char (s PCROSS {x:real^1 | &0 < drop x /\ drop x < &1}) phi}
         HAS_SIZE n <=>
         {phi | moi_s33_char s phi} HAS_SIZE n`;;

let MOI_S33_POLY_PC =
 `!c:(real^N->bool)->bool.
     FINITE c /\ (!s. s IN c ==> convex s /\ closed s) /\ connected (UNIONS c)
     ==> path_connected (UNIONS c)`;;

(* s33_z2a (GF(2) Euler-Poincare for surfaces): simplicial H^1(c;Z/2) of a *)
(* connected closed surface has 2^(2 - chi) classes, of a connected surface *)
(* with nonempty boundary 2^(1 - chi) (h^0 = 1; h^2 = 1 resp. 0).           *)

let MOI_S33_Z2_COUNT =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {})
     ==> ?n. &n = &2 - complex_euler c /\ moi_s33_h1z2 c HAS_SIZE (2 EXP n)`;;

let MOI_S33_Z2_COUNT_BD =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     connected (UNIONS c) /\ ~(surface_boundary c = {})
     ==> ?n. &n = &1 - complex_euler c /\ moi_s33_h1z2 c HAS_SIZE (2 EXP n)`;;

(* s33_z2b (H^1(c;Z/2) = Hom(pi_1,Z/2) for finite connected complexes):    *)
(* cocycle parity of edge loops, simplicial approximation of loops and of  *)
(* free homotopies of loops (grid argument), injectivity and surjectivity  *)
(* of classes -> characters.                                                 *)

let MOI_S33_Z2_CHAR =
 `!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c /\ connected (UNIONS c) /\
     ~(UNIONS c = {})
     ==> !n. moi_s33_h1z2 c HAS_SIZE n <=>
             {phi | moi_s33_char (UNIONS c) phi} HAS_SIZE n`;;

(* Derived (glue MOI_S3D_CHAR_COUNT, _BD): the character counts.            *)

let MOI_S33_CHAR_COUNT =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {})
     ==> ?n. &n = &2 - complex_euler c /\
             {phi | moi_s33_char (UNIONS c) phi} HAS_SIZE (2 EXP n)`;;

let MOI_S33_CHAR_COUNT_BD =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     connected (UNIONS c) /\ ~(surface_boundary c = {})
     ==> ?n. &n = &1 - complex_euler c /\
             {phi | moi_s33_char (UNIONS c) phi} HAS_SIZE (2 EXP n)`;;

(* Antecedents at the types the recognition proofs need: the count for     *)
(* surfaces with boundary in real^N (the polyhedron) and in real^2 (a        *)
(* triangulated model), and the homeomorphism invariance from real^2 to      *)
(* real^N (characters of a topological disk are trivial directly: it is     *)
(* contractible).                                                            *)

let MOI_S33_DISK_RECOG = mk_imp(MOI_S33_CHAR_COUNT_BD, MOI_S33_DISK_RECOG_BODY);;

let MOI_S33_HOLED_RECOG =
  mk_imp(list_mk_conj [MOI_S33_CHAR_COUNT_BD; inst [`:2`,`:N`] MOI_S33_CHAR_COUNT_BD;
                       inst [`:2`,`:M`] MOI_S33_CHAR_HOMEO],
         MOI_S33_HOLED_RECOG_BODY);;

(* s33_traces (Lemmas 3-4, pp.231-232): single polygon traces.  Book route: *)
(* split at inmost disks D_J in Int E - P' and at annuli in E - X           *)
(* (MOI_FND_SPLIT_DISK_R3, MOI_FND_SPLIT_ANNULUS_R3; the disks and annuli   *)
(* are PL by the recognition statements, given JORDAN_SCHOENFLIES in the    *)
(* open 2-cell Int E); DG route: per edge, the outer trace and thin slabs   *)
(* (PolyhedralTubeSinglePolygonTraces.lean:58).                             *)

let MOI_S33_TRACES_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x
     ==> ?x'. moi_s33_x2 t l h e x' /\ moi_s33_traces l e x'`;;

let MOI_S33_TRACES =
  mk_imp(mk_conj(inst [`:3`,`:N`] MOI_S33_DISK_RECOG_BODY,
                 inst [`:3`,`:N`] MOI_S33_HOLED_RECOG_BODY),
         MOI_S33_TRACES_BODY);;

(* s33_conn (Lemmas 5-6, p.232).  L5: delete the components of X missing   *)
(* K', fill the bounded complementary components (they lie in Int N' since *)
(* the complement of N' is connected), then 30.2 and 26.6 make Bd X         *)
(* connected.  L6: each piece is connected (30.2 for the frontier of the   *)
(* component of X INTER C_v'' containing v'), triangulated compatibly.      *)

let MOI_S33_L5_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x.
     moi_s33_hd t l h e c /\ moi_s33_x2 t l h e x /\ moi_s33_traces l e x
     ==> ?x'. moi_s33_inv t l h e x'`;;

let MOI_S33_L5 =
  mk_imp(list_mk_conj [`MOISE_302_STATEMENT`; `MOISE_266_STATEMENT`; MOI_S33_TUBE_FACTS],
         MOI_S33_L5_BODY);;

let MOI_S33_L6_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x
     ==> ?bx. moi_s33_pieces l e c x bx`;;

let MOI_S33_L6 =
  mk_imp(mk_conj(`MOISE_302_STATEMENT`, MOI_S33_TUBE_FACTS), MOI_S33_L6_BODY);;

(* s33_ltd7 (Lemma 7, p.232-233): one splitting step.  An LTD inside a      *)
(* piece is pushed off the pseudo-cells, Bd X is split at it               *)
(* (MOI_FND_SPLIT_DISK_R3), the component separating K' from Bd N' (30.2)  *)
(* bounds the new X (26.6); chi of Bd X rises by at least 1 (by 2 if the   *)
(* split surface is connected; otherwise the cut-off part is not a sphere  *)
(* because Bd LTD is not contractible in Bd X).  The termination is the    *)
(* glue MOI_S3D_NOLTD (induction on 2 - chi, bound chi <= 2).              *)

let MOI_S33_LTD_STEP_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x v d.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ {v} IN l /\
     moi_s33_ltd t l h x d /\ d SUBSET c v
     ==> ?x'. moi_s33_inv t l h e x' /\
              complex_euler (boundary_complex x) + &1 <=
              complex_euler (boundary_complex x')`;;

let MOI_S33_LTD_STEP =
  mk_imp(list_mk_conj [`MOISE_302_STATEMENT`; `MOISE_266_STATEMENT`; MOI_S33_TUBE_FACTS],
         MOI_S33_LTD_STEP_BODY);;

(* s33_l8 (Lemma 8, p.233; DG section33_disk_meets_graph, DiskMeetsGraph   *)
(* .lean:780): a polyhedral disk in c v, inside Int N', whose boundary is   *)
(* its trace on a pseudo-cell E at v bounding there a disk around the       *)
(* centre, and missing the other pseudo-cells, meets K'.  Uses that no      *)
(* vertex has degree 1 (in moi_s33_tube), 32.4 and Jordan-Brouwer.  The     *)
(* book's condition (3) is read as missing the other pseudo-cells (defect). *)

let MOI_S33_L8_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) v w d
   (k:real^3->bool) (f:real^3->real^3) g.
     moi_s33_hd t l h e c /\ ~(v = w) /\ segment[v,w] IN l /\
     &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\
     d SUBSET c v INTER interior (IMAGE h (derived_nbhd t l)) /\
     d INTER e(segment[v,w]) = IMAGE f (relative_frontier k) /\
     (?dj. dj SUBSET e(segment[v,w]) /\
           disk_with_boundary dj (IMAGE f (relative_frontier k)) /\
           h(midpoint(v,w)) IN dj DIFF IMAGE f (relative_frontier k)) /\
     (!s. s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w]) ==> DISJOINT d (e s))
     ==> ~(d INTER IMAGE h (UNIONS l) = {})`;;

let MOI_S33_L8 = mk_imp(`MOISE_324_STATEMENT`, MOI_S33_L8_BODY);;

(* s33_l9 (Lemma 9, p.234; DG section33_not_isLoopTheoremDisk,             *)
(* NotLoopTheoremDisk.lean:73): no LTD in Int N' (general position of the   *)
(* LTD against the pseudo-cells by pc_moi_s33_gp, removal of circles via    *)
(* Lemma 8 and of arcs by moves, ending in one piece: Lemma 7).             *)

let MOI_S33_L9_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_noltd t l h c x
     ==> !d. ~moi_s33_ltd t l h x d`;;

let MOI_S33_L9 =
  mk_imp(mk_conj(MOI_S33_L8_BODY, mk_conj(inst [`:3`,`:N`] MOI_S33_DISK_RECOG_BODY,
                                          MOI_S33_TUBE_FACTS)),
         MOI_S33_L9_BODY);;

(* s33_l10 (Lemma 10, pp.234-236; DG Section33FundamentalGroupBijective    *)
(* .lean:19, SurfaceLoopDecomposition.lean:13, SquareHomotopyToSurface.lean *)
(* :69): every loop of W at a base point of Bd X is homotopic rel the base  *)
(* point in W to a loop in Bd X (the product structure of W, the square     *)
(* argument; 30.2 in the square is MOI_S30_302_GEN of pc_moi_s30sep).       *)

let MOI_S33_SURJ_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x
     ==> ?a. a IN frontier (UNIONS x) /\
             !p. path p /\ path_image p SUBSET moi_s33_ww t l h /\
                 pathstart p = a /\ pathfinish p = a
                 ==> ?q. path q /\ path_image q SUBSET frontier (UNIONS x) /\
                         pathstart q = a /\ pathfinish q = a /\
                         homotopic_paths (moi_s33_ww t l h) p q`;;

let MOI_S33_SURJ = mk_imp(MOI_S33_TUBE_FACTS, MOI_S33_SURJ_BODY);;

(* s33_l12 (Lemma 12, p.236; DG section33_faceEulerChar_handlePiece,       *)
(* HandlePieceEulerChar.lean:925): from chi(Bd X) = chi(Bd N) = 2 chi(l),  *)
(* Euler additivity over the pieces (traces have chi 0) and the planar      *)
(* bound chi + b <= 2 (MOI_FND_SURFACE_PLANAR), every piece is a disk with  *)
(* deg(v) - 1 holes.                                                         *)

let MOI_S33_EULER =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x bx.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx /\
     complex_euler (boundary_complex x) = &2 * complex_euler l
     ==> moi_s33_holed l e c x`;;

(* s33_hext (DG HoledSphereExtension.lean:140): a PLH between one boundary *)
(* circle of a PL holed disk and the corresponding circle of another (same *)
(* number of holes, circles matched by an index) extends to a PLH of the   *)
(* holed disks carrying every boundary circle onto its partner.            *)

let MOI_S33_HOLED_EXT =
 `!k (a:real^N->bool) (a':real^M->bool) (f:real^2->real^N) g
   (f':real^2->real^M) g' (jj:num->real^N->bool) (jj':num->real^M->bool) i0
   (phi:real^N->real^M) phi'.
     pl_homeomorphism (holed_disk_model k,a) (f,g) /\
     pl_homeomorphism (holed_disk_model k,a') (f',g') /\
     IMAGE f (frontier (holed_disk_model k)) = UNIONS {jj i | i <= k} /\
     IMAGE f' (frontier (holed_disk_model k)) = UNIONS {jj' i | i <= k} /\
     (!i. i <= k ==> pl_sphere 1 (jj i) /\ pl_sphere 1 (jj' i)) /\
     (!i i'. i <= k /\ i' <= k /\ ~(i = i')
             ==> DISJOINT (jj i) (jj i') /\ DISJOINT (jj' i) (jj' i')) /\
     i0 <= k /\ pl_homeomorphism (jj i0,jj' i0) (phi,phi')
     ==> ?G G'. pl_homeomorphism (a,a') (G,G') /\
                (!y. y IN jj i0 ==> G y = phi y) /\
                (!i. i <= k ==> IMAGE G (jj i) = jj' i)`;;

(* s33_match (Lemma 13, pp.236-238; DG exists_section33BoundaryMatch,      *)
(* Section33BoundaryMatch.lean:437): the vertex-by-vertex construction of  *)
(* g along a connected order, with the strip argument; orientability of Bd *)
(* X (26.8) excludes the Moebius band.  Distinct splitting disks of the     *)
(* source are disjoint by MOI_S33_TUBE_TRIPLE.                              *)

let MOI_S33_TUBE_TRIPLE =
 `!(t:(real^N->bool)->bool) l u v w.
     graph_in_complex t l /\ {u} IN l /\ {v} IN l /\ {w} IN l /\
     ~(u = v) /\ ~(u = w) /\ ~(v = w)
     ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
         derived_dual_cell t l w = {}`;;

let MOI_S33_MATCH_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x bx.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
     moi_s33_pieces l e c x bx /\ moi_s33_holed l e c x
     ==> ?g. moi_s33_match t l e c x g`;;

let MOI_S33_MATCH =
  mk_imp(list_mk_conj [`MOISE_268_STATEMENT`;
                       inst [`:3`,`:N`; `:3`,`:M`] MOI_S33_HOLED_EXT;
                       inst [`:3`,`:N`] MOI_S33_TUBE_TRIPLE; MOI_S33_TUBE_FACTS],
         MOI_S33_MATCH_BODY);;

(* s33_ext (end of the proof, p.238; DG exists_section33Extension_image_   *)
(* dualCell_subset, Section33TubeApproximation.lean:39): 32.4 replaces the *)
(* disk E INTER X near the centre by a polyhedral disk E' (PL by           *)
(* recognition) inside the d-ball; g extends over the splitting disks onto *)
(* the E' (2D cone extension), then over each dual cell onto the PL ball   *)
(* bounded by the image sphere (PL Schoenflies, MOI_SCD_COR_EXTEND: the     *)
(* book's "Theorem 18.2"); the pieces paste to f.                            *)

let MOI_S33_EXT_BODY =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x
   (g:real^3->real^3) d.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
     moi_s33_match t l e c x g /\ &0 < d
     ==> ?f:real^3->real^3.
           pl_map_on (derived_nbhd t l) f /\
           (!x y. x IN derived_nbhd t l /\ y IN derived_nbhd t l /\ f x = f y
                  ==> x = y) /\
           IMAGE h (UNIONS l) SUBSET interior (IMAGE f (derived_nbhd t l)) /\
           (!v. {v} IN l
                ==> IMAGE f (derived_dual_cell t l v) SUBSET
                    c v UNION UNIONS {ball(h(midpoint(v,w)),d) | w |
                                      ~(w = v) /\ segment[v,w] IN l})`;;

let MOI_S33_EXT =
  mk_imp(list_mk_conj [`MOISE_324_STATEMENT`; `PL_SCHOENFLIES_3_STATEMENT`;
                       inst [`:3`,`:N`] MOI_S33_DISK_RECOG_BODY;
                       inst [`:3`,`:N`] MOI_S33_TUBE_TRIPLE; MOI_S33_TUBE_FACTS],
         MOI_S33_EXT_BODY);;

(* All the statement terms, in order. *)

let MOI_S33_UNIT_TARGETS =
  [MOI_S33_TUBE_FACTS; MOI_S33_X2; MOI_S33_DISK_RECOG; MOI_S33_HOLED_RECOG;
   MOI_S33_CHAR_TRANSFER; MOI_S33_CHAR_HOMEO; MOI_S33_CHAR_PRODUCT; MOI_S33_POLY_PC;
   MOI_S33_Z2_COUNT; MOI_S33_Z2_COUNT_BD; MOI_S33_Z2_CHAR;
   MOI_S33_TRACES; MOI_S33_L5; MOI_S33_L6; MOI_S33_LTD_STEP; MOI_S33_L8;
   MOI_S33_L9; MOI_S33_SURJ; MOI_S33_EULER; MOI_S33_HOLED_EXT; MOI_S33_MATCH;
   MOI_S33_EXT];;

(* Foundation-level terms that are not statements of the main chain but     *)
(* shared: MOI_S33_TUBE_TRIPLE is identical (up to the name) to             *)
(* MOI_S35_TUBE_TRIPLE of pc_moi_s35_stmt.ml; one proof serves both.        *)

map (fun t -> type_of t = bool_ty && frees t = []) MOI_S33_UNIT_TARGETS;;
map (fun t -> type_of t = bool_ty && frees t = [])
  [MOI_S33_TUBE_TRIPLE; MOI_S33_CHAR_COUNT; MOI_S33_CHAR_COUNT_BD];;

(* ========================================================================= *)
(* Part 3a: glue for the characters.  The counts of characters of closed   *)
(* surfaces and of surfaces with boundary from the GF(2) counts and the     *)
(* comparison H^1(c;Z/2) = characters.                                      *)
(* ========================================================================= *)

let MOI_S3D_SURFACE_BOUNDARY_SUBSET = prove
 (`!c:(real^N->bool)->bool. surface_boundary c SUBSET UNIONS c`,
  GEN_TAC THEN REWRITE_TAC[surface_boundary] THEN
  MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[]);;

let MOI_S3D_CHAR_COUNT = prove
 (mk_imp(mk_conj(MOI_S33_Z2_COUNT,MOI_S33_Z2_CHAR),MOI_S33_CHAR_COUNT),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cnt") (LABEL_TAC "chr")) THEN
  X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REMOVE_THEN "cnt" (MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "chr" (MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]);;

let MOI_S3D_CHAR_COUNT_BD = prove
 (mk_imp(mk_conj(MOI_S33_Z2_COUNT_BD,MOI_S33_Z2_CHAR),MOI_S33_CHAR_COUNT_BD),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cnt") (LABEL_TAC "chr")) THEN
  X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REMOVE_THEN "cnt" (MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "chr" (MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold_with_boundary];
      MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3D_SURFACE_BOUNDARY_SUBSET) THEN
      UNDISCH_TAC `~(surface_boundary (c:(real^N->bool)->bool) = {})` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]);;

(* The recognition statements and the main-chain statements that take the   *)
(* character counts as antecedents receive them from these two theorems.    *)

map (fun th -> length (hyp th)) [MOI_S3D_SURFACE_BOUNDARY_SUBSET; MOI_S3D_CHAR_COUNT;
                                 MOI_S3D_CHAR_COUNT_BD];;

(* ========================================================================= *)
(* Part 3b: Lemma 7 termination (Moise p.233 "in a finite number of steps"): *)
(* repeated splitting steps raise chi(Bd X) by at least 1 and chi <= 2 for  *)
(* the closed connected surface Bd X, so some X has no LTD in any piece.    *)
(* ========================================================================= *)

let MOI_S3D_FND_SPHERE3 = inst [`:3`,`:N`] MOI_FND_SURFACE_SPHERE;;
let MOI_S3D_FND_BC3 = inst [`:3`,`:N`] MOI_FND_BOUNDARY_COMPLEX;;

(* Bd X is a closed connected nonempty surface, triangulated by the         *)
(* boundary complex of x.                                                    *)

let MOI_S3D_INV_BC = prove
 (mk_imp(mk_conj(MOI_S3D_FND_BC3,MOI_FND_COMPLEX_BOUNDARY_3),
   `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
     (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x.
       moi_s33_hd t l h e c /\ moi_s33_inv t l h e x
       ==> FINITE (boundary_complex x) /\
           combinatorial_manifold 2 (boundary_complex x) /\
           UNIONS (boundary_complex x) = frontier (UNIONS x) /\
           connected (UNIONS (boundary_complex x)) /\
           ~(UNIONS (boundary_complex x) = {})`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bc") (LABEL_TAC "cb3")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_inv; moi_s33_x2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (boundary_complex x) = frontier (UNIONS x:real^3->bool)`
  ASSUME_TAC THENL
   [REMOVE_THEN "bc" (MP_TAC o SPEC `x:(real^3->bool)->bool`) THEN
    REMOVE_THEN "cb3" (MP_TAC o SPEC `x:(real^3->bool)->bool`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `x:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[boundary_complex] THEN SET_TAC[];
    REMOVE_THEN "bc" (MP_TAC o SPEC `x:(real^3->bool)->bool`) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[FRONTIER_EQ_EMPTY; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `?s:real^3->bool. s IN l /\ aff_dim s = &1` MP_TAC THENL
       [ASM_MESON_TAC[moi_s33_hd; moi_s33_tube]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(s:real^3->bool = {})` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^3->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPEC `UNIONS x:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x)` THEN
      UNDISCH_TAC `(s:real^3->bool) IN l` THEN UNDISCH_TAC `~(s:real^3->bool = {})` THEN
      SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `bounded (UNIONS x:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC BOUNDED_UNIONS THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
        UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)` THEN
        REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1 o CONJUNCT1) THEN
        ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
        ASM_REWRITE_TAC[NOT_BOUNDED_UNIV]]]]);;

let MOI_S3D_NOLTD_CONCL =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x
     ==> ?x'. moi_s33_inv t l h e x' /\ moi_s33_noltd t l h c x'`;;

let MOI_S3D_NOLTD = prove
 (mk_imp(list_mk_conj [MOI_S33_LTD_STEP_BODY; MOI_S3D_FND_SPHERE3; MOI_S3D_FND_BC3;
                       MOI_FND_COMPLEX_BOUNDARY_3],
         MOI_S3D_NOLTD_CONCL),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "step") (CONJUNCTS_THEN2 (LABEL_TAC "sph")
    (CONJUNCTS_THEN2 (LABEL_TAC "bc") (LABEL_TAC "cb3")))) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`] THEN
  SUBGOAL_THEN
   `!x:(real^3->bool)->bool.
       moi_s33_hd t l h e c /\ moi_s33_inv t l h e x
       ==> complex_euler (boundary_complex x) <= &2`
  (LABEL_TAC "bound") THENL
   [X_GEN_TAC `x:(real^3->bool)->bool` THEN DISCH_TAC THEN
    MP_TAC(MP MOI_S3D_INV_BC (CONJ (ASSUME MOI_S3D_FND_BC3)
                                   (ASSUME MOI_FND_COMPLEX_BOUNDARY_3))) THEN
    DISCH_THEN(MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
      `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
      `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REMOVE_THEN "sph" (MP_TAC o SPEC `boundary_complex (x:(real^3->bool)->bool)`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:(real^3->bool)->bool.
       moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
       ~moi_s33_noltd t l h c x
       ==> ?x'. moi_s33_inv t l h e x' /\
                complex_euler (boundary_complex x) + &1 <=
                complex_euler (boundary_complex x')`
  (LABEL_TAC "one") THENL
   [X_GEN_TAC `x:(real^3->bool)->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `~moi_s33_noltd (t:(real^3->bool)->bool) l h c x` THEN
    REWRITE_TAC[moi_s33_noltd; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` (X_CHOOSE_THEN `d:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "step" (MP_TAC o SPECL [`t:(real^3->bool)->bool`;
      `l:(real^3->bool)->bool`; `h:real^3->real^3`;
      `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
      `x:(real^3->bool)->bool`; `v:real^3`; `d:real^3->bool`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n x:(real^3->bool)->bool.
       moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
       &2 - complex_euler (boundary_complex x) <= &n
       ==> ?x'. moi_s33_inv t l h e x' /\ moi_s33_noltd t l h c x'`
  (LABEL_TAC "ind") THENL
   [INDUCT_TAC THENL
     [X_GEN_TAC `x:(real^3->bool)->bool` THEN STRIP_TAC THEN
      ASM_CASES_TAC `moi_s33_noltd (t:(real^3->bool)->bool) l h c x` THENL
       [EXISTS_TAC `x:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "one" (MP_TAC o SPEC `x:(real^3->bool)->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
      REMOVE_THEN "bound" (MP_TAC o SPEC `x':(real^3->bool)->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&2 - complex_euler (boundary_complex (x:(real^3->bool)->bool)) <= &0` THEN
      UNDISCH_TAC `complex_euler (boundary_complex (x:(real^3->bool)->bool)) + &1 <=
                   complex_euler (boundary_complex (x':(real^3->bool)->bool))` THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM(LABEL_TAC "ih") THEN
      X_GEN_TAC `x:(real^3->bool)->bool` THEN STRIP_TAC THEN
      ASM_CASES_TAC `moi_s33_noltd (t:(real^3->bool)->bool) l h c x` THENL
       [EXISTS_TAC `x:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "one" (MP_TAC o SPEC `x:(real^3->bool)->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
      REMOVE_THEN "ih" (MP_TAC o SPEC `x':(real^3->bool)->bool`) THEN
      ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&2 - complex_euler (boundary_complex (x:(real^3->bool)->bool)) <=
                   &(SUC n)` THEN
      UNDISCH_TAC `complex_euler (boundary_complex (x:(real^3->bool)->bool)) + &1 <=
                   complex_euler (boundary_complex (x':(real^3->bool)->bool))` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:(real^3->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(SPEC `&2 - complex_euler (boundary_complex (x:(real^3->bool)->bool))`
              REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  REMOVE_THEN "ind" (MP_TAC o SPECL [`n:num`; `x:(real^3->bool)->bool`]) THEN
  ASM_REWRITE_TAC[]);;

map (fun th -> length (hyp th)) [MOI_S3D_INV_BC; MOI_S3D_NOLTD];;

(* ========================================================================= *)
(* Part 3c: injectivity (p.234): with no LTD in W, the extended loop        *)
(* theorem 26.4 in the open set W (MOISE_264_OPEN_STATEMENT, applied to the *)
(* boundary complex of x) makes every loop of Bd X that is null-homotopic   *)
(* in W null-homotopic in Bd X.                                             *)
(* ========================================================================= *)

let MOI_S3D_X_COMPACT = prove
 (`!x:(real^3->bool)->bool.
     FINITE x /\ combinatorial_manifold_with_boundary 3 x ==> compact (UNIONS x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
  UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)` THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1 o CONJUNCT1) THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]);;

let MOI_S3D_BDX_SUBSET_W = prove
 (`!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
    (e:(real^3->bool)->real^3->bool) x.
     moi_s33_x2 t l h e x
     ==> frontier (UNIONS x) SUBSET moi_s33_ww t l h /\
         frontier (UNIONS x) SUBSET UNIONS x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_x2; moi_s33_ww] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (UNIONS x:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3D_X_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier (UNIONS x:real^3->bool) SUBSET UNIONS x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `UNIONS x:real^3->bool` frontier) THEN
  UNDISCH_TAC `UNIONS x SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
  UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x)` THEN
  UNDISCH_TAC `frontier (UNIONS x:real^3->bool) SUBSET UNIONS x` THEN
  SET_TAC[]);;

let MOI_S3D_INJ_CONCL =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
     (!d. ~moi_s33_ltd t l h x d)
     ==> !p. path p /\ path_image p SUBSET frontier (UNIONS x) /\
             pathfinish p = pathstart p /\
             homotopic_loops (moi_s33_ww t l h) p (linepath(pathstart p,pathstart p))
             ==> homotopic_loops (frontier (UNIONS x)) p
                                 (linepath(pathstart p,pathstart p))`;;

let MOI_S3D_INJ = prove
 (mk_imp(list_mk_conj [`MOISE_264_OPEN_STATEMENT`; MOI_S33_TUBE_FACTS;
                       MOI_S3D_FND_BC3; MOI_FND_COMPLEX_BOUNDARY_3],
         MOI_S3D_INJ_CONCL),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "264") (CONJUNCTS_THEN2 (LABEL_TAC "tf")
    (CONJUNCTS_THEN2 (LABEL_TAC "bc") (LABEL_TAC "cb3")))) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN X_GEN_TAC `p:real^1->real^3` THEN STRIP_TAC THEN
  MP_TAC(MP MOI_S3D_INV_BC (CONJ (ASSUME MOI_S3D_FND_BC3)
                                 (ASSUME MOI_FND_COMPLEX_BOUNDARY_3))) THEN
  DISCH_THEN(MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
    `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s33_hd]; ALL_TAC] THEN
  SUBGOAL_THEN `open (moi_s33_ww t l (h:real^3->real^3))` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s33_ww] THEN MATCH_MP_TAC OPEN_DIFF THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    REMOVE_THEN "tf" (MP_TAC o SPECL [`t:(real^3->bool)->bool`;
      `l:(real^3->bool)->bool`; `h:real^3->real^3`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (UNIONS x) SUBSET moi_s33_ww t l (h:real^3->real^3)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3D_BDX_SUBSET_W; moi_s33_inv]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  REMOVE_THEN "264" (MP_TAC o GEN_REWRITE_RULE I [MOISE_264_OPEN_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`moi_s33_ww t l (h:real^3->real^3)`;
    `boundary_complex (x:(real^3->bool)->bool)`; `p:real^1->real^3`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `d:real^3->bool`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  UNDISCH_TAC `!d:real^3->bool. ~moi_s33_ltd t l h x d` THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `d:real^3->bool` THEN
  REWRITE_TAC[moi_s33_ltd] THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_MESON_TAC[]);;

map (fun th -> length (hyp th)) [MOI_S3D_X_COMPACT; MOI_S3D_BDX_SUBSET_W; MOI_S3D_INJ];;

(* ========================================================================= *)
(* Part 3d: the replacement of Lemma 11 (p.236).  With the pi_1 iso in map  *)
(* form (injectivity from 3c, surjectivity from Lemma 10), Bd X and W have  *)
(* equally many Z/2 characters; W is homeomorphic to Bd N x (0,1), which    *)
(* has as many as Bd N; the counts for the closed connected surfaces Bd X   *)
(* and Bd N then give chi(Bd X) = chi(Bd N) = 2 chi(l)                      *)
(* (MOI_FND_GRAPH_NBHD_EULER).  No orientability and no H_1 are needed.     *)
(* ========================================================================= *)

let MOI_S3D_OPEN_UNIT_INTERVAL = prove
 (`{x:real^1 | &0 < drop x /\ drop x < &1} = interval(vec 0,vec 1)`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC]);;

let MOI_S3D_COMPLEX_CONVEX_CLOSED = prove
 (`!c:(real^N->bool)->bool.
     lf_simplicial_complex c ==> !s. s IN c ==> convex s /\ closed s`,
  GEN_TAC THEN REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(LABEL_TAC "simp" o CONJUNCT1) THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  REMOVE_THEN "simp" (MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]);;

let MOI_S3D_HAS_SIZE_EXP2 = prove
 (`!s:A->bool m n. s HAS_SIZE (2 EXP m) /\ s HAS_SIZE (2 EXP n) ==> m = n`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP m = 2 EXP n` MP_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[EQ_EXP] THEN ARITH_TAC]);;

let MOI_S3D_CHI_HYPS =
  [inst [`:3`,`:N`] MOI_S33_CHAR_TRANSFER;
   inst [`:(3,1)finite_sum`,`:M`; `:3`,`:N`] MOI_S33_CHAR_HOMEO;
   inst [`:3`,`:N`] MOI_S33_CHAR_PRODUCT;
   inst [`:3`,`:N`] MOI_S33_CHAR_COUNT;
   inst [`:3`,`:N`] MOI_S33_POLY_PC;
   MOI_S33_TUBE_FACTS;
   inst [`:3`,`:N`] MOI_FND_GRAPH_NBHD_EULER;
   MOI_S3D_FND_BC3; MOI_FND_COMPLEX_BOUNDARY_3;
   inst [`:3`,`:N`] MOI_FND_DERIVED_NBHD_BASIC];;

let MOI_S3D_CHI_CONCL =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool) x.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
     moi_s33_pi1 (frontier (UNIONS x)) (moi_s33_ww t l h)
     ==> complex_euler (boundary_complex x) = &2 * complex_euler l`;;

let MOI_S3D_CHI = prove
 (mk_imp(list_mk_conj MOI_S3D_CHI_HYPS, MOI_S3D_CHI_CONCL),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tr") (CONJUNCTS_THEN2 (LABEL_TAC "ho")
   (CONJUNCTS_THEN2 (LABEL_TAC "pr") (CONJUNCTS_THEN2 (LABEL_TAC "cnt")
   (CONJUNCTS_THEN2 (LABEL_TAC "pc") (CONJUNCTS_THEN2 (LABEL_TAC "tf")
   (CONJUNCTS_THEN2 (LABEL_TAC "eul") (CONJUNCTS_THEN2 (LABEL_TAC "bc")
   (CONJUNCTS_THEN2 (LABEL_TAC "cb3") (LABEL_TAC "dnb")))))))))) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s33_hd]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s33_tube]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  REMOVE_THEN "tf" (fun th -> MP_TAC(MATCH_MP (SPECL [`t:(real^3->bool)->bool`;
    `l:(real^3->bool)->bool`; `h:real^3->real^3`] th)
    (ASSUME `moi_s33_tube t l (h:real^3->real^3)`))) THEN
  STRIP_TAC THEN
  (* the target surface Bd X *)
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
    `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`]
    (MP MOI_S3D_INV_BC (CONJ (ASSUME MOI_S3D_FND_BC3)
                             (ASSUME MOI_FND_COMPLEX_BOUNDARY_3)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "cnt" (MP_TAC o SPEC `boundary_complex (x:(real^3->bool)->bool)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) &&
      lhs (concl th) = `UNIONS (boundary_complex (x:(real^3->bool)->bool))`
      then REWRITE_TAC[th] else NO_TAC) THEN
  DISCH_TAC THEN
  (* path connectedness of Bd X and of W *)
  SUBGOAL_THEN `path_connected (frontier (UNIONS x:real^3->bool))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq (concl th) &&
      lhs (concl th) = `UNIONS (boundary_complex (x:(real^3->bool)->bool))`
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    USE_THEN "pc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3D_COMPLEX_CONVEX_CLOSED THEN
    ASM_MESON_TAC[combinatorial_manifold];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_connected (moi_s33_ww t l (h:real^3->real^3))` ASSUME_TAC THENL
   [MP_TAC(ASSUME `homeomorphism
      (derived_frontier t l PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},
       moi_s33_ww t l (h:real^3->real^3))
      (f:real^(3,1)finite_sum->real^3,g:real^3->real^(3,1)finite_sum)`) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rhs (concl th) = `moi_s33_ww t l (h:real^3->real^3)`)) THEN
    MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PATH_CONNECTED_PCROSS THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOI_S3D_OPEN_UNIT_INTERVAL] THEN
    MATCH_MP_TAC CONVEX_IMP_PATH_CONNECTED THEN REWRITE_TAC[CONVEX_INTERVAL];
    ALL_TAC] THEN
  (* characters of W, of Bd N x (0,1) and of Bd N *)
  SUBGOAL_THEN
   `{phi | moi_s33_char (derived_frontier (t:(real^3->bool)->bool) l) phi}
    HAS_SIZE (2 EXP n1)`
  ASSUME_TAC THENL
   [USE_THEN "pr" (fun th ->
      REWRITE_TAC[GSYM (SPEC `derived_frontier t (l:(real^3->bool)->bool)` th)]) THEN
    USE_THEN "ho" (MP_TAC o SPECL
     [`derived_frontier (t:(real^3->bool)->bool) l PCROSS
       {x:real^1 | &0 < drop x /\ drop x < &1}`;
      `moi_s33_ww t l (h:real^3->real^3)`;
      `f:real^(3,1)finite_sum->real^3`; `g:real^3->real^(3,1)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    USE_THEN "tr" (MP_TAC o SPECL [`frontier (UNIONS x:real^3->bool)`;
      `moi_s33_ww t l (h:real^3->real^3)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the source surface Bd N *)
  USE_THEN "eul" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "dnb" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `FINITE (derived_nbhd_complex t (l:(real^3->bool)->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "bc" (MP_TAC o SPEC `derived_nbhd_complex t (l:(real^3->bool)->bool)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `UNIONS (boundary_complex (derived_nbhd_complex t (l:(real^3->bool)->bool))) =
                derived_frontier t l` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "cnt" (MP_TAC o SPEC
    `boundary_complex (derived_nbhd_complex t (l:(real^3->bool)->bool))`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `derived_nbhd_complex t (l:(real^3->bool)->bool)` THEN
      ASM_REWRITE_TAC[boundary_complex] THEN SET_TAC[];
      ASM_SIMP_TAC[PATH_CONNECTED_IMP_CONNECTED]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `n1:num = n2` ASSUME_TAC THENL
   [MP_TAC(ISPECL
      [`{phi | moi_s33_char (derived_frontier t (l:(real^3->bool)->bool)) phi}`;
       `n1:num`; `n2:num`] MOI_S3D_HAS_SIZE_EXP2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `&n1 = &2 - complex_euler (boundary_complex (x:(real^3->bool)->bool))` THEN
  UNDISCH_TAC `&n2 = &2 - complex_euler (boundary_complex
                 (derived_nbhd_complex t (l:(real^3->bool)->bool)))` THEN
  UNDISCH_TAC `complex_euler (boundary_complex
                 (derived_nbhd_complex t (l:(real^3->bool)->bool))) =
               &2 * complex_euler l` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

map (fun th -> length (hyp th))
  [MOI_S3D_OPEN_UNIT_INTERVAL; MOI_S3D_COMPLEX_CONVEX_CLOSED; MOI_S3D_HAS_SIZE_EXP2;
   MOI_S3D_CHI];;

(* ========================================================================= *)
(* Part 3e: the main assembly (Moise pp.230-231 and the tube form).  Given *)
(* open w v containing h(C_v), radii r v with the 2 r v neighbourhood of    *)
(* h(C_v) inside w v, nb v the r v neighbourhood, d below all r v; 32.3     *)
(* with nb gives the handle decomposition; the stages give f with f(C_v)    *)
(* inside c v plus the d-balls around the centres of the edges at v, which *)
(* lie in the 2 r v neighbourhood (the centres lie in c v, inside nb v).    *)
(* As DG Moise331OnTube (Section33TubeApproximation.lean:302).              *)
(* ========================================================================= *)

let MOI_S3D_FINITE_POS_MIN = prove
 (`!s:A->bool r. FINITE s /\ (!x. x IN s ==> &0 < r x)
                 ==> ?d. &0 < d /\ !x. x IN s ==> d <= r x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (r:A->real) s` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
  STRIP_TAC THEN EXISTS_TAC `inf (IMAGE (r:A->real) s)` THEN ASM_MESON_TAC[]);;

let MOI_S3D_THICK = prove
 (`!k u:real^N->bool.
     compact k /\ open u /\ k SUBSET u
     ==> ?r. &0 < r /\ !z y. z IN k /\ dist(z,y) < &2 * r ==> y IN u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^N) DIFF u`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MAP_EVERY X_GEN_TAC [`z:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  UNDISCH_TAC `dist(z:real^N,y) < d` THEN REAL_ARITH_TAC);;

let MOI_S3D_NB_OPEN = prove
 (`!(k:real^N->bool) r. open {y | ?z. z IN k /\ dist(z,y) < r}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y:real^N | ?z. z IN k /\ dist(z,y) < r} =
                UNIONS (IMAGE (\z. ball(z,r)) k)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE; IN_BALL] THEN
    MESON_TAC[];
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL]]);;

let MOI_S3D_EDGE_VERTEX = prove
 (`!(l:(real^N->bool)->bool) t a b.
     simplicial_subcomplex l t /\ segment[a,b] IN l ==> {a} IN l /\ {b} IN l`,
  REWRITE_TAC[simplicial_subcomplex] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `segment[a:real^N,b]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_S3D_MAIN_HYPS =
  [`MOISE_323_STATEMENT`; MOI_S33_TUBE_FACTS; MOI_S33_X2; MOI_S33_TRACES_BODY;
   MOI_S33_L5_BODY; MOI_S33_L6_BODY; MOI_S3D_NOLTD_CONCL; MOI_S33_L9_BODY;
   MOI_S3D_INJ_CONCL; MOI_S33_SURJ_BODY; MOI_S3D_CHI_CONCL; MOI_S33_EULER;
   MOI_S33_MATCH_BODY; MOI_S33_EXT_BODY];;

let MOI_S3D_MAIN = prove
 (mk_imp(list_mk_conj MOI_S3D_MAIN_HYPS, `MOISE_331_STATEMENT`),
  DISCH_THEN(fun th ->
    EVERY (map2 (fun lab th -> LABEL_TAC lab th)
      ["323"; "tf"; "x2"; "tr"; "l5"; "l6"; "nol"; "l9"; "inj"; "surj"; "chi";
       "eul"; "mat"; "ext"] (CONJUNCTS th))) THEN
  REWRITE_TAC[MOISE_331_STATEMENT; graph_approximable] THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`] THEN
  DISCH_THEN(LABEL_TAC "hyp") THEN
  X_GEN_TAC `w:real^3->real^3->bool` THEN DISCH_THEN(LABEL_TAC "w") THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s33_tube] THEN USE_THEN "hyp" ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s33_tube]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  REMOVE_THEN "tf" (fun th -> MP_TAC(MATCH_MP (SPECL [`t:(real^3->bool)->bool`;
    `l:(real^3->bool)->bool`; `h:real^3->real^3`] th)
    (ASSUME `moi_s33_tube t l (h:real^3->real^3)`))) THEN
  STRIP_TAC THEN
  (* radii *)
  SUBGOAL_THEN
   `?r:real^3->real.
      !v. {v} IN l
          ==> &0 < r v /\
              !z y. z IN IMAGE (h:real^3->real^3)
                                 (derived_dual_cell (t:(real^3->bool)->bool) l v) /\
                    dist(z,y) < &2 * r v
                    ==> y IN (w:real^3->real^3->bool) v`
  (X_CHOOSE_THEN `r:real^3->real` (LABEL_TAC "r")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `v:real^3` THEN
    ASM_CASES_TAC `{v:real^3} IN l` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3D_THICK THEN
    USE_THEN "w" (fun th -> MP_TAC(MATCH_MP (SPEC `v:real^3` th)
                                            (ASSUME `{v:real^3} IN l`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET) o check (fun th -> is_comb (concl th) &&
        fst (strip_comb (concl th)) = `(continuous_on):(real^3->real^3)->(real^3->bool)->bool`)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `derived_nbhd t (l:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[derived_dual_cell; INTER_SUBSET];
    ALL_TAC] THEN
  (* a common lower bound d *)
  SUBGOAL_THEN `FINITE {v:real^3 | {v} IN l}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\v:real^3. {v}`; `l:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{v:real^3 | {v} IN l}`; `r:real^3->real`] MOI_S3D_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "r" (fun th -> MP_TAC(MATCH_MP (SPEC `v:real^3` th)
                                            (ASSUME `{v:real^3} IN l`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd"))) THEN
  (* 32.3 with the r-neighbourhoods *)
  USE_THEN "323" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`;
    `\v:real^3. {y:real^3 | ?z. z IN IMAGE (h:real^3->real^3)
                                     (derived_dual_cell (t:(real^3->bool)->bool) l v) /\
                                dist(z,y) < (r:real^3->real) v}`] o
    GEN_REWRITE_RULE I [MOISE_323_STATEMENT]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S3D_NB_OPEN] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[DIST_REFL] THEN
    USE_THEN "r" (fun th -> MP_TAC(MATCH_MP (SPEC `v:real^3` th)
                                            (ASSUME `{v:real^3} IN l`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->real^3->bool`
   (X_CHOOSE_THEN `c:real^3->real^3->bool`
    (CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2")
     (CONJUNCTS_THEN2 (LABEL_TAC "c3") (CONJUNCTS_THEN2 (LABEL_TAC "c4")
      (LABEL_TAC "c5"))))))) THEN
  SUBGOAL_THEN `moi_s33_hd t l (h:real^3->real^3) e c` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s33_hd; moi_s33_rim] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "c1" ACCEPT_TAC;
      USE_THEN "c2" ACCEPT_TAC;
      USE_THEN "c3" MP_TAC THEN MESON_TAC[];
      USE_THEN "c4" ACCEPT_TAC;
      USE_THEN "c5" ACCEPT_TAC];
    ALL_TAC] THEN
  (* the chain of stages *)
  USE_THEN "x2" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `x0:(real^3->bool)->bool`) THEN
  USE_THEN "tr" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x0:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "l5" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x1:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `x2:(real^3->bool)->bool`) THEN
  USE_THEN "nol" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x2:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "l9" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "inj" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "surj" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `moi_s33_pi1 (frontier (UNIONS x)) (moi_s33_ww t l (h:real^3->real^3))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s33_pi1] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_S3D_BDX_SUBSET_W; moi_s33_inv];
    ALL_TAC] THEN
  USE_THEN "chi" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "l6" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `bx:(real^3->bool)->bool`) THEN
  USE_THEN "eul" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "mat" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `bx:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^3`) THEN
  USE_THEN "ext" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
    `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
    `x:(real^3->bool)->bool`; `g:real^3->real^3`; `dd:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fn:real^3->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `fn:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
  (* the tube-form estimate *)
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(c:real^3->real^3->bool) v UNION
              UNIONS {ball((h:real^3->real^3)(midpoint(v,w')),dd) | w' |
                      ~(w' = v) /\ segment[v,w'] IN l}` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  USE_THEN "r" (fun th -> MP_TAC(MATCH_MP (SPEC `v:real^3` th)
                                          (ASSUME `{v:real^3} IN l`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rv")) THEN
  USE_THEN "dd" (fun th -> ASSUME_TAC(MATCH_MP (SPEC `v:real^3` th)
                                              (ASSUME `{v:real^3} IN l`))) THEN
  SUBGOAL_THEN
   `(c:real^3->real^3->bool) v SUBSET
    {y:real^3 | ?z. z IN IMAGE (h:real^3->real^3) (derived_dual_cell t l v) /\
                    dist(z,y) < r v}`
  ASSUME_TAC THENL
   [USE_THEN "c3" (fun th -> MP_TAC(MATCH_MP (SPEC `v:real^3` th)
                                             (ASSUME `{v:real^3} IN l`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?z:real^3. z IN IMAGE (h:real^3->real^3) (derived_dual_cell t l v) /\
                             dist(z,y) < (r:real^3->real) v`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "rv" MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < r(v:real^3)` THEN
    UNDISCH_TAC `dist(z:real^3,y) < r(v:real^3)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `w':real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `{w':real^3} IN l` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3D_EDGE_VERTEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3)(midpoint(v,w')) IN c v` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(v:real^3 = w')` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "c5" (fun th -> MP_TAC(MATCH_MP (SPECL [`v:real^3`; `w':real^3`] th)
      (CONJ (ASSUME `{v:real^3} IN l`) (CONJ (ASSUME `{w':real^3} IN l`)
            (ASSUME `~(v:real^3 = w')`))))) THEN
    USE_THEN "c1" (fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP
      (SPECL [`v:real^3`; `w':real^3`] th)
      (CONJ (ASSUME `~(v:real^3 = w')`) (ASSUME `segment[v:real^3,w'] IN l`)))))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?z:real^3. z IN IMAGE (h:real^3->real^3) (derived_dual_cell t l v) /\
               dist(z,(h:real^3->real^3)(midpoint(v,w'))) < (r:real^3->real) v`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  USE_THEN "rv" MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`z:real^3`; `(h:real^3->real^3)(midpoint(v,w'))`; `y:real^3`]
                DIST_TRIANGLE) THEN
  UNDISCH_TAC `dd <= r(v:real^3)` THEN
  UNDISCH_TAC `dist(z:real^3,(h:real^3->real^3)(midpoint(v,w'))) < r(v:real^3)` THEN
  UNDISCH_TAC `dist((h:real^3->real^3)(midpoint(v,w')),y) < dd` THEN
  REAL_ARITH_TAC);;

map (fun th -> length (hyp th))
  [MOI_S3D_FINITE_POS_MIN; MOI_S3D_THICK; MOI_S3D_NB_OPEN; MOI_S3D_EDGE_VERTEX;
   MOI_S3D_MAIN];;

(* ========================================================================= *)
(* Part 3f: the closure.  The statement terms (at the type instances the    *)
(* glue uses; the files prove them polymorphically) and six foundation      *)
(* terms imply the producer MOI_PROD_331 of pc_moi_core_stmt.ml.  The cell  *)
(* assembly input of MOI_PROD_331 is not used (the final map is pasted from *)
(* the PLH extensions over the dual cells, as in the book).                 *)
(* ========================================================================= *)

let MOI_S3D_UNIT_INSTANCES =
  [MOI_S33_TUBE_FACTS; MOI_S33_X2;
   inst [`:3`,`:N`] MOI_S33_DISK_RECOG; inst [`:3`,`:N`] MOI_S33_HOLED_RECOG;
   inst [`:3`,`:N`] MOI_S33_CHAR_TRANSFER;
   inst [`:(3,1)finite_sum`,`:M`; `:3`,`:N`] MOI_S33_CHAR_HOMEO;
   inst [`:2`,`:M`; `:3`,`:N`] MOI_S33_CHAR_HOMEO;
   inst [`:3`,`:N`] MOI_S33_CHAR_PRODUCT; inst [`:3`,`:N`] MOI_S33_POLY_PC;
   inst [`:3`,`:N`] MOI_S33_Z2_COUNT;
   inst [`:3`,`:N`] MOI_S33_Z2_COUNT_BD; inst [`:2`,`:N`] MOI_S33_Z2_COUNT_BD;
   inst [`:3`,`:N`] MOI_S33_Z2_CHAR; inst [`:2`,`:N`] MOI_S33_Z2_CHAR;
   MOI_S33_TRACES; MOI_S33_L5; MOI_S33_L6; MOI_S33_LTD_STEP; MOI_S33_L8;
   MOI_S33_L9; MOI_S33_SURJ; MOI_S33_EULER;
   inst [`:3`,`:N`; `:3`,`:M`] MOI_S33_HOLED_EXT; MOI_S33_MATCH; MOI_S33_EXT];;

let MOI_S3D_FND_TERMS =
  [inst [`:3`,`:N`] MOI_S33_TUBE_TRIPLE; MOI_S3D_FND_SPHERE3; MOI_S3D_FND_BC3;
   MOI_FND_COMPLEX_BOUNDARY_3; inst [`:3`,`:N`] MOI_FND_GRAPH_NBHD_EULER;
   inst [`:3`,`:N`] MOI_FND_DERIVED_NBHD_BASIC];;

let MOI_S3D_CLOSURE_HYPS = MOI_S3D_UNIT_INSTANCES @ MOI_S3D_FND_TERMS;;

let MOI_S3D_PROD_331 = prove
 (mk_imp(list_mk_conj MOI_S3D_CLOSURE_HYPS, MOI_PROD_331),
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    let get t = find (fun th -> concl th = t) ths in
    let tf = get MOI_S33_TUBE_FACTS in
    let z2c3 = get (inst [`:3`,`:N`] MOI_S33_Z2_COUNT) in
    let z2b3 = get (inst [`:3`,`:N`] MOI_S33_Z2_COUNT_BD) in
    let z2b2 = get (inst [`:2`,`:N`] MOI_S33_Z2_COUNT_BD) in
    let z2h3 = get (inst [`:3`,`:N`] MOI_S33_Z2_CHAR) in
    let z2h2 = get (inst [`:2`,`:N`] MOI_S33_Z2_CHAR) in
    let cc3 = MP (INST_TYPE [`:3`,`:N`] MOI_S3D_CHAR_COUNT) (CONJ z2c3 z2h3) in
    let ccb3 = MP (INST_TYPE [`:3`,`:N`] MOI_S3D_CHAR_COUNT_BD) (CONJ z2b3 z2h3) in
    let ccb2 = MP (INST_TYPE [`:2`,`:N`] MOI_S3D_CHAR_COUNT_BD) (CONJ z2b2 z2h2) in
    let diskb = MP (get (inst [`:3`,`:N`] MOI_S33_DISK_RECOG)) ccb3 in
    let holedb = MP (get (inst [`:3`,`:N`] MOI_S33_HOLED_RECOG))
      (end_itlist CONJ [ccb3; ccb2;
         get (inst [`:2`,`:M`; `:3`,`:N`] MOI_S33_CHAR_HOMEO)]) in
    let tracesb = MP (get MOI_S33_TRACES) (CONJ diskb holedb) in
    let triple3 = get (inst [`:3`,`:N`] MOI_S33_TUBE_TRIPLE) in
    let bc3 = get MOI_S3D_FND_BC3 and cb3 = get MOI_FND_COMPLEX_BOUNDARY_3 in
    MAP_EVERY ASSUME_TAC
      [tf; get MOI_S33_X2; tracesb; get MOI_S33_L5; get MOI_S33_L6;
       get MOI_S33_LTD_STEP; get MOI_S33_L8; get MOI_S33_L9; get MOI_S33_SURJ;
       get MOI_S33_EULER; get MOI_S33_MATCH; get MOI_S33_EXT; diskb; triple3;
       get (inst [`:3`,`:N`; `:3`,`:M`] MOI_S33_HOLED_EXT);
       MP MOI_S3D_CHI (end_itlist CONJ
         [get (inst [`:3`,`:N`] MOI_S33_CHAR_TRANSFER);
          get (inst [`:(3,1)finite_sum`,`:M`; `:3`,`:N`] MOI_S33_CHAR_HOMEO);
          get (inst [`:3`,`:N`] MOI_S33_CHAR_PRODUCT); cc3;
          get (inst [`:3`,`:N`] MOI_S33_POLY_PC); tf;
          get (inst [`:3`,`:N`] MOI_FND_GRAPH_NBHD_EULER); bc3; cb3;
          get (inst [`:3`,`:N`] MOI_FND_DERIVED_NBHD_BASIC)]);
       get MOI_S3D_FND_SPHERE3; bc3; cb3]) THEN
  STRIP_TAC THEN
  (* the stage bodies *)
  SUBGOAL_THEN MOI_S33_L5_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S33_L5)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S33_L6_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S33_L6)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S33_LTD_STEP_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S33_LTD_STEP)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S33_L8_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S33_L8)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S33_L9_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S33_L9)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S33_SURJ_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S33_SURJ)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S33_MATCH_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S33_MATCH)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S33_EXT_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S33_EXT)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S3D_NOLTD_CONCL ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3D_NOLTD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S3D_INJ_CONCL ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3D_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3D_MAIN THEN ASM_REWRITE_TAC[]);;

(* Final shape checks: the closure has exactly the listed hypotheses and    *)
(* the producer as conclusion; every instance used is an instance of a      *)
(* statement term.                                                          *)

let MOI_S3D_CLOSURE_SHAPE =
  hyp MOI_S3D_PROD_331 = [] &&
  aconv (concl MOI_S3D_PROD_331) (mk_imp(list_mk_conj MOI_S3D_CLOSURE_HYPS, MOI_PROD_331)) &&
  forall (fun t -> exists (fun u -> can (term_match [] u) t) MOI_S33_UNIT_TARGETS)
         MOI_S3D_UNIT_INSTANCES;;

MOI_S3D_CLOSURE_SHAPE;;

(* ========================================================================= *)
(* Part 4: sanity theorems.  The tube predicate is exactly                 *)
(* the hypothesis of MOISE_331_STATEMENT; the zero character exists; the   *)
(* constant loop has value F and characters agree on a loop and its reverse *)
(* (teeth: additivity and homotopy invariance interact as for Hom(pi_1,Z/2));*)
(* convex sets have only the zero character (the count 2^(1 - chi) = 1 for *)
(* a disk); the circle has a nonzero character (odd winding number), so    *)
(* characters are not degenerate; simplicial Z/2 classes of the empty      *)
(* complex: one; LTDs are nonempty; moi_s33_pi1 s s holds for nonempty s.   *)
(* ========================================================================= *)

let MOI_S3D_SAN_TUBE_EQ = prove
 (mk_forall(`t:(real^3->bool)->bool`, mk_forall(`l:(real^3->bool)->bool`,
   mk_forall(`h:real^3->real^3`,
    mk_eq(`moi_s33_tube t l (h:real^3->real^3)`,
          fst(dest_imp(snd(strip_forall(rand(concl MOISE_331_STATEMENT))))))))),
  REWRITE_TAC[moi_s33_tube]);;

let MOI_S3D_SAN_HD_TUBE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c ==> moi_s33_tube t l h`,
  SIMP_TAC[moi_s33_hd]);;

let MOI_S3D_SAN_CHAR_ZERO = prove
 (`!s:real^N->bool. moi_s33_char s (\p. F)`,
  REWRITE_TAC[moi_s33_char]);;

let MOI_S3D_SAN_CHAR_CONST = prove
 (`!(s:real^N->bool) phi a.
     moi_s33_char s phi /\ a IN s ==> ~phi (linepath(a,a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_char] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path (linepath(a:real^N,a)) /\
                path_image (linepath(a,a)) SUBSET s /\
                pathfinish (linepath(a,a)) = pathstart (linepath(a,a))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL;
                PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`linepath(a:real^N,a)`; `linepath(a:real^N,a)`]) THEN
  ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  SUBGOAL_THEN `homotopic_loops s (linepath(a:real^N,a) ++ linepath(a,a))
                                  (linepath(a,a))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                PATHFINISH_LINEPATH] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `linepath(a:real^N,a)`] HOMOTOPIC_PATHS_LID) THEN
    ASM_REWRITE_TAC[PATHSTART_LINEPATH];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`linepath(a:real^N,a) ++ linepath(a,a)`;
                                `linepath(a:real^N,a)`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S3D_SAN_CHAR_REVERSE = prove
 (`!(s:real^N->bool) phi p.
     moi_s33_char s phi /\ path p /\ path_image p SUBSET s /\
     pathfinish p = pathstart p
     ==> (phi (reversepath p) <=> phi p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pathstart p IN (s:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `p:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`;
                 `pathstart(p:real^1->real^N)`] MOI_S3D_SAN_CHAR_CONST) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s33_char (s:real^N->bool) phi` THEN
  REWRITE_TAC[moi_s33_char] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^1->real^N`; `reversepath(p:real^1->real^N)`]) THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                  PATHFINISH_REVERSEPATH] THEN
  SUBGOAL_THEN `homotopic_loops s (p ++ reversepath p)
                  (linepath(pathstart p:real^N,pathstart p))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    ASM_SIMP_TAC[HOMOTOPIC_PATHS_RINV; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                 PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p ++ reversepath(p:real^1->real^N)`;
    `linepath(pathstart p:real^N,pathstart p)`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S3D_SAN_CHAR_CONVEX = prove
 (`!s:real^N->bool. convex s ==> {phi | moi_s33_char s phi} = {\p. F}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `phi:(real^1->real^N)->bool` THEN EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:real^1->real^N` THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `path p /\ path_image p SUBSET (s:real^N->bool) /\
                  pathfinish p = pathstart p` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s33_char (s:real^N->bool) phi` THEN
      REWRITE_TAC[moi_s33_char] THEN
      DISCH_THEN(MP_TAC o SPEC `p:real^1->real^N` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `pathstart p IN (s:real^N->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `p:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `homotopic_loops s p (linepath(pathstart p:real^N,pathstart p))`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `s:real^N->bool` CONVEX_IMP_SIMPLY_CONNECTED) THEN
      ASM_REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
      DISCH_THEN(MP_TAC o SPECL [`p:real^1->real^N`; `pathstart(p:real^1->real^N)`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`;
                   `pathstart(p:real^1->real^N)`] MOI_S3D_SAN_CHAR_CONST) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s33_char (s:real^N->bool) phi` THEN
    REWRITE_TAC[moi_s33_char] THEN
    DISCH_THEN(MP_TAC o SPECL [`p:real^1->real^N`;
      `linepath(pathstart p:real^N,pathstart p)`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_S3D_SAN_CHAR_ZERO]]);;

let MOI_S3D_SAN_H1Z2_EMPTY = prove
 (`moi_s33_h1z2 ({}:(real^N->bool)->bool) HAS_SIZE 1`,
  SUBGOAL_THEN `!z:(real^N->bool)->bool. z2_cocycle {} z <=> z = {}` ASSUME_TAC THENL
   [REWRITE_TAC[z2_cocycle; NOT_IN_EMPTY] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s33_h1z2 ({}:(real^N->bool)->bool) = {{{}}}` SUBST1_TAC THENL
   [REWRITE_TAC[moi_s33_h1z2; moi_s33_z2class] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[z2_coboundary; NOT_IN_EMPTY] THEN REWRITE_TAC[SING_GSPEC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    MESON_TAC[];
    REWRITE_TAC[HAS_SIZE; FINITE_SING; CARD_SING]]);;

let MOI_S3D_SAN_Z2CLASS_REFL = prove
 (`!(c:(real^N->bool)->bool) z. z2_cocycle c z ==> z IN moi_s33_z2class c z`,
  REWRITE_TAC[moi_s33_z2class; IN_ELIM_THM; DIFF_EQ_EMPTY; UNION_EMPTY] THEN
  SIMP_TAC[MOI_FD_Z2_COBOUNDARY_EMPTY]);;

let MOI_S3D_SAN_LTD_NONEMPTY = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) x d.
     moi_s33_ltd t l h x d ==> ~(d = {})`,
  REWRITE_TAC[moi_s33_ltd; pl_homeomorphism; homeomorphism] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k:real^3->bool = {}` MP_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[SIMPLEX_EMPTY; INT_ARITH `~(&2:int = -- &1)`]]);;

let MOI_S3D_SAN_PI1_REFL = prove
 (`!s:real^N->bool. ~(s = {}) ==> moi_s33_pi1 s s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s33_pi1; SUBSET_REFL] THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `p:real^1->real^N` THEN ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL]);;

(* Teeth: the circle carries a nonzero character, the parity of the winding *)
(* number about 0.                                                           *)

let MOI_S3D_INTEGER_HALF_CASES = prove
 (`!a. integer a ==> integer(a / &2) \/ integer((a - &1) / &2)`,
  GEN_TAC THEN REWRITE_TAC[integer] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [EVEN_EXISTS; ODD_EXISTS]) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
    `abs a = b ==> a = b \/ a = --b`)) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC] THENL
   [DISJ1_TAC THEN EXISTS_TAC `k:num` THEN REAL_ARITH_TAC;
    DISJ1_TAC THEN EXISTS_TAC `k:num` THEN REAL_ARITH_TAC;
    DISJ2_TAC THEN EXISTS_TAC `k:num` THEN REAL_ARITH_TAC;
    DISJ2_TAC THEN EXISTS_TAC `k + 1` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

let MOI_S3D_NOT_INTEGER_HALF = prove
 (`~integer(&1 / &2)`,
  REWRITE_TAC[integer] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `&0 < &n /\ &n < &1` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC]);;

let MOI_S3D_INTEGER_HALF_ADD = prove
 (`!a b. integer a /\ integer b
         ==> (integer((a + b) / &2) <=> (integer(a / &2) <=> integer(b / &2)))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `integer(a / &2)` THEN ASM_CASES_TAC `integer(b / &2)` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[REAL_ARITH `(a + b) / &2 = a / &2 + b / &2`] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED];
    DISCH_TAC THEN UNDISCH_TAC `~integer(b / &2)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `b / &2 = (a + b) / &2 - a / &2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[INTEGER_CLOSED]];
    DISCH_TAC THEN UNDISCH_TAC `~integer(a / &2)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `a / &2 = (a + b) / &2 - b / &2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[INTEGER_CLOSED]];
    MP_TAC(SPEC `a:real` MOI_S3D_INTEGER_HALF_CASES) THEN
    MP_TAC(SPEC `b:real` MOI_S3D_INTEGER_HALF_CASES) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(a + b) / &2 = (a - &1) / &2 + (b - &1) / &2 + &1` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[INTEGER_CLOSED]]]);;

let MOI_S3D_SAN_CHAR_CIRCLE = prove
 (`?phi. moi_s33_char (sphere(Cx(&0),&1)) phi /\ ~(phi = (\p. F))`,
  EXISTS_TAC
   `\p:real^1->complex. path p /\ path_image p SUBSET sphere(Cx(&0),&1) /\
                        pathfinish p = pathstart p /\
                        ~integer(Re(winding_number(p,Cx(&0))) / &2)` THEN
  SUBGOAL_THEN `~(Cx(&0) IN sphere(Cx(&0),&1))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE; DIST_REFL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s33_char] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `winding_number(p,Cx(&0)) = winding_number(q,Cx(&0))`
      (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
    EXISTS_TAC `sphere(Cx(&0),&1)` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    SUBGOAL_THEN `path(p ++ q:real^1->complex) /\
                  path_image(p ++ q) SUBSET sphere(Cx(&0),&1)`
      (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(Cx(&0) IN path_image p) /\ ~(Cx(&0) IN path_image q)`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[WINDING_NUMBER_JOIN; RE_ADD] THEN
    MP_TAC(ISPECL [`p:real^1->complex`; `Cx(&0)`] INTEGER_WINDING_NUMBER) THEN
    MP_TAC(ISPECL [`q:real^1->complex`; `Cx(&0)`] INTEGER_WINDING_NUMBER) THEN
    ASM_REWRITE_TAC[complex_integer] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_S3D_INTEGER_HALF_ADD] THEN CONV_TAC TAUT;
    REWRITE_TAC[FUN_EQ_THM; NOT_FORALL_THM] THEN
    EXISTS_TAC `circlepath(Cx(&0),&1)` THEN
    SIMP_TAC[PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_POS; SUBSET_REFL;
             PATHSTART_CIRCLEPATH; PATHFINISH_CIRCLEPATH] THEN
    SIMP_TAC[WINDING_NUMBER_CIRCLEPATH; COMPLEX_SUB_REFL; COMPLEX_NORM_0;
             REAL_LT_01; RE_CX; MOI_S3D_NOT_INTEGER_HALF]]);;

let MOI_S3D_SANITY =
  [MOI_S3D_SAN_TUBE_EQ; MOI_S3D_SAN_HD_TUBE; MOI_S3D_SAN_CHAR_ZERO;
   MOI_S3D_SAN_CHAR_CONST; MOI_S3D_SAN_CHAR_REVERSE; MOI_S3D_SAN_CHAR_CONVEX;
   MOI_S3D_SAN_H1Z2_EMPTY; MOI_S3D_SAN_Z2CLASS_REFL; MOI_S3D_SAN_LTD_NONEMPTY;
   MOI_S3D_SAN_PI1_REFL; MOI_S3D_INTEGER_HALF_CASES; MOI_S3D_NOT_INTEGER_HALF;
   MOI_S3D_INTEGER_HALF_ADD; MOI_S3D_SAN_CHAR_CIRCLE];;

map (fun th -> length (hyp th)) MOI_S3D_SANITY;;

(* ========================================================================= *)
(* Part 5: final checks (printed): every glue and sanity theorem has no     *)
(* hypotheses, the closure has the listed antecedent and the producer as    *)
(* conclusion, every statement term is a closed boolean term, and no axiom  *)
(* was added.                                                               *)
(* ========================================================================= *)

let MOI_S3D_THEOREMS =
  [MOI_S3D_SURFACE_BOUNDARY_SUBSET; MOI_S3D_CHAR_COUNT; MOI_S3D_CHAR_COUNT_BD;
   MOI_S3D_INV_BC; MOI_S3D_NOLTD; MOI_S3D_X_COMPACT; MOI_S3D_BDX_SUBSET_W;
   MOI_S3D_INJ; MOI_S3D_OPEN_UNIT_INTERVAL; MOI_S3D_COMPLEX_CONVEX_CLOSED;
   MOI_S3D_HAS_SIZE_EXP2; MOI_S3D_CHI; MOI_S3D_FINITE_POS_MIN; MOI_S3D_THICK;
   MOI_S3D_NB_OPEN; MOI_S3D_EDGE_VERTEX; MOI_S3D_MAIN; MOI_S3D_PROD_331] @
  MOI_S3D_SANITY;;

let MOI_S3D_CHECK =
  forall (fun th -> hyp th = []) MOI_S3D_THEOREMS &&
  MOI_S3D_CLOSURE_SHAPE &&
  forall (fun t -> type_of t = bool_ty && frees t = [])
         (MOI_S33_UNIT_TARGETS @ [MOI_S33_TUBE_TRIPLE; MOI_S33_CHAR_COUNT;
                                  MOI_S33_CHAR_COUNT_BD]) &&
  length (axioms()) = 3;;

(length MOI_S33_UNIT_TARGETS, length MOI_S3D_THEOREMS, MOI_S3D_CHECK);;


