(* ========================================================================= *)
(* pc_moi_s3032_stmt: the statements for the Sec 30-32 items of the Moise PL *)
(* core (Moise GTM 47, Secs 30-32, printed pp.214-229): the leaves MOISE_303 *)
(* and MOISE_324 and the producers MOI_PROD_304, 306, 307, 311, 314,         *)
(* 322_CELLS and 323 of pc_moi_core_stmt.ml.  Definitions moi_s30_...,       *)
(* moi_s31_..., moi_s32_..., statement terms MOI_S30_..., MOI_S31_...,       *)
(* MOI_S32_... (OCaml term values, closed booleans) and glue theorems        *)
(* MOI_STD_....                                                              *)
(* ========================================================================= *)

(* ========================================================================= *)
(* The statements are proved in the files pc_moi_s30_..., pc_moi_s31_... and *)
(* pc_moi_s32_... (the units named below).  The statements of                *)
(* pc_moi_s35_stmt.ml (model double cube, orientation and disk extension,    *)
(* tube charts), pc_moi_sch3_stmt.ml (2D sphere and disk statements),        *)
(* pc_moi_s33_stmt.ml (Z/2 loop characters and their counts) and             *)
(* pc_moi_s2628_stmt.ml (compact neighbourhoods, cutting along a surface,    *)
(* surface charts) enter as hypotheses.                                      *)
(* Some statements are restated in later files, and the main theorem uses    *)
(* the restated forms: DISK_CHART and NULL_POLYGON with the foundation term  *)
(* BALL_2 (pc_moi_s3032_stmt2.ml), LEVEL and ITERATE with a members clause   *)
(* (pc_moi_s3032_stmt3.ml), HANDLES with a vertex condition                  *)
(* (pc_moi_s3032_stmt4.ml; HANDLES as stated here is false), and the Step 1  *)
(* state with a member invariant (pc_moi_s3032_stmt6.ml; CLASSIFY as stated  *)
(* here is false).  pc_moi_s3032_stmt5.ml and pc_moi_s3032_stmt6.ml redo the *)
(* affected glue; the glue theorems MOI_STD_304, 306, 307 and 311 of this    *)
(* file are used unchanged.                                                  *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_s35_stmt.ml";;
needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_s2628_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* Instances at real^3 of polymorphic foundation terms used as antecedents. *)

let moi_n3 t = inst [`:3`,`:N`] t;;

(* The consequent of a statement T = (A ==> C) (T itself if T has no         *)
(* antecedents).  A statement used by another statement enters it in this    *)
(* form; the full glue theorems take the statements themselves.              *)

let moi_std_csq t = if is_imp t then snd(dest_imp t) else t;;

(* ------------------------------------------------------------------------- *)
(* 1. Definitions.                                                           *)
(* moi_s30_inner: the inner square of the middle square of the model cube   *)
(* moi_s35_cube (the disk a of 30.3 in the chart).                          *)
(* ------------------------------------------------------------------------- *)

let moi_s30_inner = new_definition
 `moi_s30_inner =
    {x:real^3 | x IN moi_s35_mid /\ abs(x$1) <= &1 / &2 /\ abs(x$2) <= &1 / &2}`;;

(* The torus model as a target of maps (for the toroidal shell coordinate). *)

let moi_s30_tt = new_definition
 `moi_s30_tt = sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s30_inner; moi_s30_tt];;

(* ========================================================================= *)
(* 2. Sec 30 statements.                                                     *)
(* ========================================================================= *)

(* 2.1 Moise 30.3 (leaf MOISE_303_STATEMENT, p.215).  Units s30_cut_a and   *)
(* s30_cut_b.  ANNULUS_2D: a PL disk inside the interior of a PL disk       *)
(* leaves a PL annulus (2D PL annulus theorem, from planar ambient PL       *)
(* Schoenflies).  DISK_CHART: a PL disk d in real^3 near a smaller disk a in *)
(* its interior has a bicollar chart: a PL embedding of the model cube into *)
(* any given neighbourhood of a, meeting d exactly in the middle square,    *)
(* with the inner square onto a (regular neighbourhood of a disk, 3D PL     *)
(* Schoenflies for the two halves).  CUTCAP: 30.3 from the chart (the cut   *)
(* and cap in the model, the side of the second sheet, and the rerouting of *)
(* paths through the lateral annulus of the capping box, p.215).            *)

let MOI_S30_ANNULUS_2D = mk_imp(`PL_SCHOENFLIES_2_AMBIENT_STATEMENT`,
 `!d jd a ja:real^3->bool.
     pl_cell_with_boundary 2 d jd /\ pl_cell_with_boundary 2 a ja /\
     a SUBSET d /\ DISJOINT a jd
     ==> pl_annulus_with_ends ((d DIFF a) UNION ja) ja jd`);;

let MOI_S30_DISK_CHART =
  mk_imp(list_mk_conj [`PL_SCHOENFLIES_3_STATEMENT`; moi_n3 MOI_FND_DERIVED_NBHD_BALL;
                       moi_std_csq MOI_S30_ANNULUS_2D],
 `!d jd a ja v:real^3->bool.
     pl_cell_with_boundary 2 d jd /\ pl_cell_with_boundary 2 a ja /\
     a SUBSET d /\ DISJOINT a jd /\ open v /\ a SUBSET v
     ==> ?(psi:real^3->real^3) phi.
           pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
           IMAGE psi moi_s35_cube SUBSET v /\
           IMAGE psi moi_s35_cube INTER d = IMAGE psi moi_s35_mid /\
           IMAGE psi moi_s30_inner = a`);;

let MOI_S30_CUTCAP =
  mk_imp(list_mk_conj [`PL_SCHOENFLIES_3_STATEMENT`; moi_std_csq MOI_S30_ANNULUS_2D;
                       moi_std_csq MOI_S30_DISK_CHART],
         `MOISE_303_STATEMENT`);;

(* 2.2 Euler characteristic bookkeeping (unit s30_bound).  EULER_NAT: chi   *)
(* of a closed connected surface is 2 - n (integer values, 22.5 bound).     *)
(* BOUNDS: a closed connected polyhedral surface in real^3 bounds a compact *)
(* combinatorial 3-manifold, the closure of its inside, its boundary        *)
(* complex having the Euler characteristic of m (26.6; a compact            *)
(* combinatorial neighbourhood and the cut along the surface of the         *)
(* pc_moi_s2628_stmt.ml, MOI_S26_COMPACT_NBHD and MOI_S26_CUT, and PL       *)
(* invariance of chi).  EULER_EVEN: chi(Bd c) = 2 chi c for compact         *)
(* combinatorial 3-manifolds (link counting).                               *)

let MOI_S30_EULER_NAT = mk_imp(moi_n3 MOI_FND_SURFACE_SPHERE,
 `!c:(real^3->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {})
     ==> ?n. complex_euler c = &2 - &n`);;

let MOI_S30_BOUNDS =
  mk_imp(list_mk_conj [`MOISE_266_STATEMENT`; moi_std_csq MOI_S26_COMPACT_NBHD;
                       moi_std_csq MOI_S26_CUT;
                       inst [`:3`,`:M`; `:3`,`:N`] MOI_FND_EULER_PL_INVARIANT],
 `!m:(real^3->bool)->bool.
     FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
     ~(UNIONS m = {})
     ==> ?x:(real^3->bool)->bool.
           FINITE (x:(real^3->bool)->bool) /\ combinatorial_manifold_with_boundary 3 x /\
           UNIONS x = UNIONS m UNION inside (UNIONS m) /\
           frontier (UNIONS x) = UNIONS m /\ complex_boundary x = UNIONS m /\
           complex_euler (boundary_complex x) = complex_euler m`);;

let MOI_S30_EULER_EVEN =
 `!x:(real^N->bool)->bool.
     FINITE x /\ combinatorial_manifold_with_boundary 3 x
     ==> complex_euler (boundary_complex x) = &2 * complex_euler x`;;

(* 2.3 Initial separating surface and compression (units s30_init,         *)
(* s30_comp; p.216 first paragraphs of 30.4 and 30.6).  INIT_SURFACE: a     *)
(* small polyhedral 3-manifold neighbourhood N of a, one component of Bd N  *)
(* separating (30.2).  SPLIT_ESSENTIAL: the surface m' of MOI_FND_SPLIT_     *)
(* DISK_R3 along an essential curve j is connected or has two non-spherical *)
(* components (27.3 in the annulus a, sphere minus disk is a disk).         *)
(* COMPRESS: the compression step of 30.4 and 30.6 for a separating closed  *)
(* surface and the 26.4 disk: a separating component with larger chi (the   *)
(* separation through the bounding 3-manifold of BOUNDS and the x-clause of *)
(* MOI_FND_SPLIT_DISK_R3, instead of 30.3).                                 *)

let MOI_S30_INIT_SURFACE =
  mk_imp(list_mk_conj [`MOISE_302_STATEMENT`; moi_n3 MOI_FND_DERIVED_NBHD_MANIFOLD],
 `!(a:real^3->bool) b v.
     compact a /\ connected a /\ ~(a = {}) /\ closed b /\ connected b /\
     ~(b = {}) /\ open v /\ a SUBSET v /\ DISJOINT v b
     ==> ?m:(real^3->bool)->bool.
           FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
           ~(UNIONS m = {}) /\ UNIONS m SUBSET v DIFF a /\
           euclidean_separates (UNIONS m) a b`);;

let MOI_S30_SPLIT_ESSENTIAL =
  mk_imp(list_mk_conj [`MOISE_273_STATEMENT (:3)`; MOI_SCH3_DISK_COMPLEMENT],
 `!(m:(real^3->bool)->bool) a j j1 j2 d1 d2 (m':(real^3->bool)->bool).
     FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
     pl_annulus_with_ends a j1 j2 /\ a SUBSET UNIONS m /\
     pl_sphere 1 j /\ j SUBSET a DIFF (j1 UNION j2) /\
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     DISJOINT d1 d2 /\ d1 INTER UNIONS m = j1 /\ d2 INTER UNIONS m = j2 /\
     FINITE m' /\ combinatorial_manifold 2 m' /\
     UNIONS m' = (UNIONS m DIFF a) UNION d1 UNION d2 /\
     ~(?z. homotopic_with (\f. T)
             (subtopology euclidean j,subtopology euclidean (UNIONS m))
             (\x. x) (\x. z))
     ==> connected (UNIONS m') \/
         ?m1 m2. m' = m1 UNION m2 /\ DISJOINT (UNIONS m1) (UNIONS m2) /\
                 FINITE m1 /\ combinatorial_manifold 2 m1 /\
                 connected (UNIONS m1) /\ ~(UNIONS m1 = {}) /\
                 ~pl_sphere 2 (UNIONS m1) /\
                 FINITE m2 /\ combinatorial_manifold 2 m2 /\
                 connected (UNIONS m2) /\ ~(UNIONS m2 = {}) /\
                 ~pl_sphere 2 (UNIONS m2)`);;

let MOI_S30_COMPRESS =
  mk_imp(list_mk_conj [MOI_FND_SPLIT_DISK_R3; `MOISE_302_STATEMENT`;
                       `MOISE_266_STATEMENT`; moi_n3 MOI_FND_SURFACE_SPHERE;
                       moi_std_csq MOI_S30_BOUNDS; moi_std_csq MOI_S30_SPLIT_ESSENTIAL],
 `!(m:(real^3->bool)->bool) hs ks u (s:real^3->bool) d (f:real^3->real^3) g.
     FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
     ~(UNIONS m = {}) /\ open u /\ UNIONS m SUBSET u /\
     closed hs /\ closed ks /\ connected hs /\ connected ks /\
     ~(hs = {}) /\ ~(ks = {}) /\ DISJOINT u (hs UNION ks) /\
     euclidean_separates (UNIONS m) hs ks /\
     &2 simplex s /\ pl_homeomorphism (s,d) (f,g) /\ d SUBSET u /\
     d INTER UNIONS m = IMAGE f (relative_frontier s) /\
     ~(?z. homotopic_with (\h. T)
             (subtopology euclidean (IMAGE f (relative_frontier s)),
              subtopology euclidean (UNIONS m))
             (\x. x) (\x. z))
     ==> ?m':(real^3->bool)->bool.
           FINITE m' /\ combinatorial_manifold 2 m' /\ connected (UNIONS m') /\
           ~(UNIONS m' = {}) /\ UNIONS m' SUBSET u /\
           euclidean_separates (UNIONS m') hs ks /\
           complex_euler m < complex_euler m'`);;

(* 2.4 Z/2 counts for surfaces (unit s30_z2c; replaces the classification of *)
(* surfaces used on pp.216-217).  The character counts of pc_moi_s33_stmt.ml *)
(* (MOI_S33_CHAR_COUNT, _BD: a connected closed surface has 2^(2 - chi) Z/2  *)
(* loop characters, one with boundary 2^(1 - chi); units s33_z2a, s33_z2b    *)
(* and the glue MOI_S3D_CHAR_COUNT) are the antecedents.                     *)
(* SC_CLOSED, SC_BOUNDARY: simply connected compact surfaces have chi 2     *)
(* (closed) or 1 (with boundary): the only character is trivial.            *)
(* TORUS_BOUND: a closed surface mapped to the torus so that loops with     *)
(* null-homotopic image are null-homotopic has chi >= 0 (a character is     *)
(* determined by its values on two loops whose winding pairs generate the   *)
(* image of the winding pair in Z^2, so there are at most 4).               *)

let MOI_S30_Z2_SC_CLOSED = mk_imp(MOI_S33_CHAR_COUNT,
 `!m:(real^N->bool)->bool.
     FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
     ~(UNIONS m = {}) /\
     (!p. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET UNIONS m
          ==> homotopic_loops (UNIONS m) p (linepath(pathstart p,pathstart p)))
     ==> complex_euler m = &2`);;

let MOI_S30_Z2_SC_BOUNDARY = mk_imp(MOI_S33_CHAR_COUNT_BD,
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     connected (UNIONS c) /\ ~(surface_boundary c = {}) /\
     (!p. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET UNIONS c
          ==> homotopic_loops (UNIONS c) p (linepath(pathstart p,pathstart p)))
     ==> complex_euler c = &1`);;

let MOI_S30_Z2_TORUS_BOUND = mk_imp(MOI_S33_CHAR_COUNT,
 `!(m:(real^N->bool)->bool) (g:real^N->real^(2,2)finite_sum).
     FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
     ~(UNIONS m = {}) /\ g continuous_on UNIONS m /\
     IMAGE g (UNIONS m) SUBSET moi_s30_tt /\
     (!p. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET UNIONS m /\
          homotopic_loops moi_s30_tt (g o p) (linepath(g(pathstart p),g(pathstart p)))
          ==> homotopic_loops (UNIONS m) p (linepath(pathstart p,pathstart p)))
     ==> &0 <= complex_euler m`);;

(* 2.5 Triangulated topological surfaces (unit s30_tame).  SURFACE_TRIANG:  *)
(* a locally finite triangulation of a topological 2-manifold (with         *)
(* boundary, in the chart predicates of pc_moi_s2628_stmt.ml) is            *)
(* combinatorial, its combinatorial boundary is the manifold boundary: the  *)
(* locally finite form of MOI_S28_SURF_LOCAL (the links are local; needed   *)
(* for the open pieces triangulated in RECROSS and CAP_SETUP).  POLY_DISK: *)
(* a locally polyhedral topological 2-cell is a PL 2-cell with the same     *)
(* boundary.  PL_TORUS_COMPLEX: a PL torus is a closed connected            *)
(* combinatorial surface, with chi 0 by MOI_FND_EULER_VALUES.               *)

let MOI_S30_SURFACE_TRIANG = mk_imp(MOI_S28_SURF_LOCAL,
 `!c:(real^N->bool)->bool.
     lf_simplicial_complex c /\
     (!y. y IN UNIONS c
          ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y)
     ==> combinatorial_manifold_with_boundary 2 c /\
         surface_boundary c = {y | y IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) y} /\
         (surface_boundary c = {} ==> combinatorial_manifold 2 c)`);;

let MOI_S30_POLY_DISK =
  mk_imp(list_mk_conj [moi_std_csq MOI_S30_SURFACE_TRIANG;
                       moi_std_csq MOI_S30_Z2_SC_BOUNDARY;
                       MOI_FND_SURFACE_PLANAR],
 `!(d:real^N->bool) (f:real^2->real^N) g.
     locally_polyhedral d /\ homeomorphism (cball(vec 0,&1),d) (f,g)
     ==> pl_cell_with_boundary 2 d (IMAGE f (sphere(vec 0,&1)))`);;

let MOI_S30_PL_TORUS_COMPLEX =
  mk_imp(list_mk_conj [moi_std_csq MOI_S30_SURFACE_TRIANG; MOI_FND_EULER_VALUES],
 `!(t:real^N->bool) (f:real^(2,2)finite_sum->real^N) g.
     pl_homeomorphism (pl_torus_model,t) (f,g)
     ==> ?m:(real^N->bool)->bool.
           FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = t /\
           connected t /\ ~(t = {}) /\ complex_euler m = &0`);;

(* 2.6 Shells (unit s30_shell).  Basic facts of spherical and toroidal      *)
(* shells (invariance of domain); the toroidal shell coordinate detects     *)
(* null-homotopy of loops in the interior; NO_SPHERE: a PL 2-sphere in the  *)
(* interior of a toroidal shell does not separate its ends (case (1) of     *)
(* 30.6, p.217, by a lifting argument instead of van Kampen: the circle     *)
(* coordinate has a logarithm on the sphere, extend it over one side and   *)
(* compare winding numbers on the two ends); CORE_ESSENTIAL: the spine of   *)
(* the inner solid torus is essential in the outer one (p.218, S_1 is a    *)
(* retract of S_2; from the shell collapse of pc_moi_s308).                *)

let MOI_S30_SPHERICAL_SHELL_FACTS =
 `!x b0 b1:real^3->bool.
     spherical_shell x b0 b1
     ==> compact x /\ connected x /\ compact b0 /\ connected b0 /\ ~(b0 = {}) /\
         compact b1 /\ connected b1 /\ ~(b1 = {}) /\ DISJOINT b0 b1 /\
         b0 UNION b1 SUBSET x /\ interior x = x DIFF (b0 UNION b1) /\
         simply_connected (interior x)`;;

let MOI_S30_TOROIDAL_SHELL_FACTS =
 `!y t0 t1:real^3->bool.
     toroidal_shell y t0 t1
     ==> compact y /\ connected y /\ compact t0 /\ connected t0 /\ ~(t0 = {}) /\
         compact t1 /\ connected t1 /\ ~(t1 = {}) /\ DISJOINT t0 t1 /\
         t0 UNION t1 SUBSET y /\ interior y = y DIFF (t0 UNION t1) /\
         ?g:real^3->real^(2,2)finite_sum.
           g continuous_on y /\ IMAGE g y SUBSET moi_s30_tt /\
           !p. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET interior y
               ==> (homotopic_loops (interior y) p (linepath(pathstart p,pathstart p)) <=>
                    homotopic_loops moi_s30_tt (g o p)
                      (linepath(g(pathstart p),g(pathstart p))))`;;

let MOI_S30_SHELL_NO_SPHERE =
 `!y t0 t1 s:real^3->bool.
     toroidal_shell y t0 t1 /\ pl_sphere 2 s /\ s SUBSET interior y
     ==> ~euclidean_separates s t0 t1`;;

let MOI_S30_SHELL_CORE_ESSENTIAL =
 `!s1 s2 j:real^3->bool.
     solid_torus s1 /\ solid_torus s2 /\ s1 SUBSET interior s2 /\
     toroidal_shell (closure(s2 DIFF s1)) (frontier s1) (frontier s2) /\
     spine j s1
     ==> ~(?z. homotopic_with (\f. T)
                 (subtopology euclidean j,subtopology euclidean s2) (\x. x) (\x. z))`;;

(* 2.7 30.7 (units s30_tor_a, s30_tor_b, s30_cst).  TORUS_REGION: the torus *)
(* of 30.6 bounds a region between the two solid tori (Borsuk separation:  *)
(* the complement of the outer interior is connected).  TORUS_LOOP: a PL    *)
(* torus in the interior of a solid torus carries a loop essential in it    *)
(* and null-homotopic in the solid torus (p.217, the inclusion has a       *)
(* kernel; winding numbers).  OUTSIDE: case 1 of p.217 is impossible (the  *)
(* compressed torus is a sphere bounding a ball containing S_1).  INSIDE:  *)
(* case 2 (p.218) gives a PL solid torus.  HANDLE_SOLID_TORUS: two PL     *)
(* 3-balls meeting in two disjoint boundary disks form a PL solid torus    *)
(* (orientability of the handle in real^3 via local determinant signs;    *)
(* gap of p.218: exactly as in 28.1).                                     *)

let MOI_S30_TORUS_REGION = mk_imp(`MOISE_266_STATEMENT`,
 `!s1 s2 (m:(real^3->bool)->bool).
     solid_torus s1 /\ solid_torus s2 /\ s1 SUBSET interior s2 /\
     toroidal_shell (closure(s2 DIFF s1)) (frontier s1) (frontier s2) /\
     FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
     ~(UNIONS m = {}) /\ UNIONS m SUBSET interior (closure(s2 DIFF s1)) /\
     euclidean_separates (UNIONS m) (frontier s1) (frontier s2)
     ==> s1 SUBSET inside (UNIONS m) /\
         UNIONS m UNION inside (UNIONS m) SUBSET interior s2`);;

let MOI_S30_TORUS_LOOP =
 `!(t:real^3->bool) s2 (f:real^(2,2)finite_sum->real^3) g.
     pl_homeomorphism (pl_torus_model,t) (f,g) /\ solid_torus s2 /\
     t SUBSET interior s2
     ==> ?p. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET t /\
             ~homotopic_loops t p (linepath(pathstart p,pathstart p)) /\
             homotopic_loops (interior s2) p (linepath(pathstart p,pathstart p))`;;

let MOI_S30_HANDLE_SOLID_TORUS =
  mk_imp(list_mk_conj [MOI_S35_LOCAL_SIGN; MOI_S35_ONE_DISK_EXT; MOI_S35_TWO_DISK_EXT],
 `!b hb d1 j1 d2 j2:real^3->bool.
     pl_ball 3 b /\ pl_ball 3 hb /\
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     DISJOINT d1 d2 /\ d1 UNION d2 SUBSET frontier b /\
     d1 UNION d2 SUBSET frontier hb /\ b INTER hb = d1 UNION d2
     ==> pl_solid_torus (b UNION hb)`);;

(* The common data of the two cases of 30.7: the shell, the PL torus |m| of *)
(* chi 0 with its bounding 3-manifold x between s1 and s2, and the 26.4     *)
(* disk d (PL image of the 2-simplex s under f) with essential rim.         *)

let moi_s30_case_hyps =
 `solid_torus (s1:real^3->bool) /\ solid_torus (s2:real^3->bool) /\
  s1 SUBSET interior s2 /\
  toroidal_shell (closure(s2 DIFF s1)) (frontier s1) (frontier s2) /\
  FINITE (m:(real^3->bool)->bool) /\ combinatorial_manifold 2 m /\
  connected (UNIONS m) /\
  ~(UNIONS m = {}) /\ complex_euler m = &0 /\
  FINITE (x:(real^3->bool)->bool) /\ combinatorial_manifold_with_boundary 3 x /\
  UNIONS x = UNIONS m UNION inside (UNIONS m) /\
  frontier (UNIONS x) = UNIONS m /\
  s1 SUBSET interior (UNIONS x) /\ UNIONS x SUBSET interior s2 /\
  &2 simplex (s:real^3->bool) /\
  pl_homeomorphism (s,d:real^3->bool) (f:real^3->real^3,g:real^3->real^3) /\
  d SUBSET interior s2 /\
  d INTER UNIONS m = IMAGE f (relative_frontier s) /\
  ~(?z. homotopic_with (\h. T)
          (subtopology euclidean (IMAGE f (relative_frontier s)),
           subtopology euclidean (UNIONS m))
          (\y:real^3. y) (\y. z:real^3))`;;

let moi_s30_case_vars =
  [`s1:real^3->bool`; `s2:real^3->bool`; `m:(real^3->bool)->bool`;
   `x:(real^3->bool)->bool`; `s:real^3->bool`; `d:real^3->bool`;
   `f:real^3->real^3`; `g:real^3->real^3`];;

let MOI_S30_307_OUTSIDE =
  mk_imp(list_mk_conj [MOI_FND_SPLIT_DISK_R3; `MOISE_266_STATEMENT`;
                       `PL_SCHOENFLIES_3_STATEMENT`; moi_n3 MOI_FND_SURFACE_SPHERE;
                       moi_std_csq MOI_S30_SPLIT_ESSENTIAL; moi_std_csq MOI_S30_BOUNDS;
                       moi_n3 MOI_S30_EULER_EVEN; MOI_S30_SHELL_CORE_ESSENTIAL],
         list_mk_forall(moi_s30_case_vars,
           mk_imp(mk_conj(moi_s30_case_hyps,
                          `d INTER UNIONS x = IMAGE (f:real^3->real^3)
                                                (relative_frontier s)`),
                  `F`)));;

let MOI_S30_307_INSIDE =
  mk_imp(list_mk_conj [MOI_FND_SPLIT_DISK_R3; `MOISE_266_STATEMENT`;
                       `PL_SCHOENFLIES_3_STATEMENT`; moi_n3 MOI_FND_SURFACE_SPHERE;
                       moi_std_csq MOI_S30_SPLIT_ESSENTIAL; moi_std_csq MOI_S30_BOUNDS;
                       moi_n3 MOI_S30_EULER_EVEN; moi_std_csq MOI_S30_HANDLE_SOLID_TORUS;
                       MOI_SCH3_DISK_UNION],
         list_mk_forall(moi_s30_case_vars,
           mk_imp(mk_conj(moi_s30_case_hyps,
                          `(d:real^3->bool) SUBSET UNIONS x`),
                  `pl_solid_torus (UNIONS (x:(real^3->bool)->bool))`)));;

map type_of
  [MOI_S30_ANNULUS_2D; MOI_S30_DISK_CHART; MOI_S30_CUTCAP; MOI_S30_EULER_NAT;
   MOI_S30_BOUNDS; MOI_S30_EULER_EVEN; MOI_S30_INIT_SURFACE;
   MOI_S30_SPLIT_ESSENTIAL; MOI_S30_COMPRESS; MOI_S30_Z2_SC_CLOSED;
   MOI_S30_Z2_SC_BOUNDARY; MOI_S30_Z2_TORUS_BOUND; MOI_S30_SURFACE_TRIANG;
   MOI_S30_POLY_DISK; MOI_S30_PL_TORUS_COMPLEX; MOI_S30_SPHERICAL_SHELL_FACTS;
   MOI_S30_TOROIDAL_SHELL_FACTS; MOI_S30_SHELL_NO_SPHERE;
   MOI_S30_SHELL_CORE_ESSENTIAL; MOI_S30_TORUS_REGION; MOI_S30_TORUS_LOOP;
   MOI_S30_HANDLE_SOLID_TORUS; MOI_S30_307_OUTSIDE; MOI_S30_307_INSIDE];;

(* ========================================================================= *)
(* 3. Sec 31 statements (canonical configurations, pp.220-222).             *)
(* ========================================================================= *)

(* 3.1 Revolution solid tori (unit s31_rev).  For a planar topological disk  *)
(* dd in the open half plane x3 = 0, x1 > 0 and an embedding h of its       *)
(* revolution about the x2 axis: h(rev dd) is a solid torus; a compact      *)
(* subset k of the relative interior lies in the interior of an inner solid *)
(* torus with a toroidal shell to h(rev dd) (radial shrinking in the disk   *)
(* chart; the input of 30.7 in 31.1); the circle of a point q is a spine of *)
(* an arbitrarily small such inner solid torus (the input of 30.8 in 31.4, *)
(* 32.1 Lemma 2).                                                            *)

let MOI_S31_REV_SHELL =
 `!(dd:real^3->bool) (h:real^3->real^3).
     disk_with_boundary dd (dd DIFF relative_interior dd) /\
     dd SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
     h continuous_on revolution dd /\
     (!x y. x IN revolution dd /\ y IN revolution dd /\ h x = h y ==> x = y)
     ==> solid_torus (IMAGE h (revolution dd)) /\
         (!k. compact k /\ k SUBSET relative_interior dd
              ==> ?s1. solid_torus s1 /\ IMAGE h (revolution k) SUBSET interior s1 /\
                       s1 SUBSET interior (IMAGE h (revolution dd)) /\
                       toroidal_shell (closure (IMAGE h (revolution dd) DIFF s1))
                                      (frontier s1)
                                      (frontier (IMAGE h (revolution dd)))) /\
         (!q w. q IN relative_interior dd /\ open w /\
                IMAGE h (revolution {q}) SUBSET w
                ==> ?s1. solid_torus s1 /\ spine (IMAGE h (revolution {q})) s1 /\
                         s1 SUBSET w INTER interior (IMAGE h (revolution dd)) /\
                         toroidal_shell (closure (IMAGE h (revolution dd) DIFF s1))
                                        (frontier s1)
                                        (frontier (IMAGE h (revolution dd))))`;;

(* 3.2 General position of solid torus boundaries (unit s31_cross; the     *)
(* crossing condition of p.221, missing from the proof of 31.1).  A PL      *)
(* solid torus is moved inside a given open set, keeping a compact subset   *)
(* of its interior inside, so that its boundary crosses each torus of a     *)
(* finite family of disjoint boundaries of PL solid tori (from MOI_FND_GP_   *)
(* SURFACES_3 applied to the torus complexes, on the open complement of the *)
(* compact set).  Both orders of pl_crossing_at are given.                  *)

let MOI_S31_RECROSS =
  mk_imp(list_mk_conj [MOI_FND_GP_SURFACES_3; moi_n3 MOI_FND_PL_SOLID_TORUS_BASIC;
                       moi_std_csq (moi_n3 MOI_S30_PL_TORUS_COMPLEX);
                       moi_std_csq (moi_n3 MOI_S30_SURFACE_TRIANG)],
 `!(s:real^3->bool) a w ff.
     pl_solid_torus s /\ compact a /\ a SUBSET interior s /\ open w /\ s SUBSET w /\
     FINITE ff /\ (!t. t IN ff ==> ?s'. pl_solid_torus s' /\ t = frontier s') /\
     pairwise DISJOINT ff
     ==> ?s'. pl_solid_torus s' /\ a SUBSET interior s' /\ s' SUBSET w /\
              (!t x. t IN ff /\ x IN frontier s' INTER t
                     ==> pl_crossing_at (frontier s') t x /\
                         pl_crossing_at t (frontier s') x)`);;

(* 3.3 Mayer-Vietoris for compact polyhedra (unit s31_mv), exactness at     *)
(* H_1(a) x H_1(b): the elementary homology of Moise 28.11 (p.205) and the  *)
(* chain cutting in the proof of 31.4 (p.221), from ATOP_MAYER_VIETORIS     *)
(* (pc_top_mv) by regular neighbourhood retractions.                       *)

let MOI_S31_MV_POLY =
 `!a b:real^N->bool.
     pl_polyhedron a /\ pl_polyhedron b
     ==> !x y. x IN group_carrier(homology_group(&1,subtopology euclidean a)) /\
               y IN group_carrier(homology_group(&1,subtopology euclidean b)) /\
               hom_induced (&1) (subtopology euclidean a,{})
                           (subtopology euclidean (a UNION b),{}) (\x. x) x =
               hom_induced (&1) (subtopology euclidean b,{})
                           (subtopology euclidean (a UNION b),{}) (\x. x) y
               ==> ?z. z IN group_carrier(homology_group(&1,subtopology euclidean
                                                              (a INTER b))) /\
                       hom_induced (&1) (subtopology euclidean (a INTER b),{})
                                   (subtopology euclidean a,{}) (\x. x) z = x /\
                       hom_induced (&1) (subtopology euclidean (a INTER b),{})
                                   (subtopology euclidean b,{}) (\x. x) z = y`;;

(* 3.4 The carrier of 31.4 (unit s31_carrier; p.221, the cycle Y'_{j+1},     *)
(* in DG's asymmetric form).  zm lies in both interiors and carries both    *)
(* pi_1, zo lies in the interior of sb outside sa and carries pi_1(sb):     *)
(* cutting the homology between them in sb (minus a small neighbourhood of  *)
(* the given compact gg in frontier sb) along frontier sa gives a polyhedral *)
(* carrier of H_1(sa) in frontier sa missing gg.                            *)

let MOI_S31_CARRIER = mk_imp(moi_n3 MOI_S31_MV_POLY,
 `!(sa:real^3->bool) sb zm zo gg.
     pl_solid_torus sa /\ pl_solid_torus sb /\
     zm SUBSET interior sa INTER interior sb /\ zo SUBSET interior sb DIFF sa /\
     zm homeomorphic sphere(vec 0:real^2,&1) /\
     zo homeomorphic sphere(vec 0:real^2,&1) /\
     loops_carried zm sa /\ loops_carried zm sb /\ loops_carried zo sb /\
     compact gg /\ gg SUBSET frontier sb
     ==> ?k. pl_polyhedron k /\ k SUBSET frontier sa DIFF gg /\ carries_h1 k sa`);;

(* 3.5 The meridian lemma (unit s31_link; DG exists_isPLCell_frontier_of_    *)
(* polygon_nullhomotopic): a polygon in the boundary torus, null-homotopic  *)
(* in the solid torus and bounding a PL disk missing a pi_1-carrier of the  *)
(* interior, bounds a disk in the boundary (a meridian would link the PL    *)
(* circle gg with H_1(R^3 - gg) = Z, while H_1(R^3 - d) = 0; Mayer-Vietoris *)
(* with regular neighbourhoods).  Needed because the book's symmetric       *)
(* argument (p.222) uses the hidden condition P_j not in D_{j+1}.           *)

let MOI_S31_NULL_POLYGON =
  mk_imp(list_mk_conj [moi_n3 MOI_S31_MV_POLY; MOI_FND_POLYGON_SOLID_TORUS_3;
                       moi_n3 MOI_FND_DERIVED_NBHD_BALL],
 `!(sb:real^3->bool) gg d zm.
     pl_solid_torus sb /\ pl_sphere 1 gg /\ gg SUBSET frontier sb /\
     pl_cell_with_boundary 2 d gg /\ DISJOINT d zm /\ ~(zm = {}) /\
     path_connected zm /\ zm SUBSET interior sb /\ loops_carried zm sb /\
     (?z. homotopic_with (\f. T)
            (subtopology euclidean gg,subtopology euclidean sb) (\x. x) (\x. z))
     ==> ?d'. d' SUBSET frontier sb /\ pl_cell_with_boundary 2 d' gg`);;

(* 3.6 Spines and transfer in a canonical configuration (unit s31_axis).   *)
(* SPINES: the circles h(rev{p k}) of the end points of segment j lie in    *)
(* the interior of s2 j and carry its loops (30.8 with the inner solid tori *)
(* of REV_SHELL; Theorem 31.2).  TRANSFER: for a polygon in s2 j and        *)
(* s2 (j+1), carrying H_1 of one of them gives carrying pi_1 of both, and   *)
(* null-homotopy in one is null-homotopy in the other (the angle around the *)
(* x2 axis pulled back by h detects pi_1 of each s2 k, since the common     *)
(* circle h(rev{p (j+1)}) has angle winding 1; replaces the book's use of   *)
(* the solid torus S'_j UNION S'_(j+1), p.222).                             *)

let MOI_S31_SPINES =
  mk_imp(list_mk_conj [`MOISE_308_STATEMENT`; MOI_S31_REV_SHELL;
                       moi_n3 MOI_FND_PL_SOLID_TORUS_BASIC],
 `!(p:num->real^3) dd (h:real^3->real^3) s2 j k.
     canonical_configuration p dd h s2 /\ j < 3 /\ (k = j \/ k = j + 1)
     ==> IMAGE h (revolution {p k}) SUBSET interior (s2 j) /\
         loops_carried (IMAGE h (revolution {p k})) (s2 j) /\
         IMAGE h (revolution {p k}) homeomorphic sphere(vec 0:real^2,&1)`);;

let MOI_S31_TRANSFER =
  mk_imp(list_mk_conj [`MOISE_308_STATEMENT`; MOI_S31_REV_SHELL;
                       moi_n3 MOI_FND_PL_SOLID_TORUS_BASIC; moi_n3 MOI_FND_H1_SPINE;
                       MOI_FND_LOOPS_SOLID_TORUS_MODEL],
 `!(p:num->real^3) dd (h:real^3->real^3) s2 j gg.
     canonical_configuration p dd h s2 /\ j < 2 /\ pl_sphere 1 gg /\
     gg SUBSET s2 j INTER s2 (j + 1)
     ==> ((carries_h1 gg (s2 j) \/ carries_h1 gg (s2 (j + 1)))
          ==> loops_carried gg (s2 j) /\ loops_carried gg (s2 (j + 1))) /\
         ((?z. homotopic_with (\f. T)
                 (subtopology euclidean gg,subtopology euclidean (s2 j))
                 (\x. x) (\x. z)) <=>
          (?z. homotopic_with (\f. T)
                 (subtopology euclidean gg,subtopology euclidean (s2 (j + 1)))
                 (\x. x) (\x. z)))`);;

map type_of [MOI_S31_REV_SHELL; MOI_S31_RECROSS; MOI_S31_MV_POLY; MOI_S31_CARRIER;
             MOI_S31_NULL_POLYGON; MOI_S31_SPINES; MOI_S31_TRANSFER];;

(* ========================================================================= *)
(* 4. Sec 32: definitions.                                                   *)
(* The model of 32.1-32.2 (p.224: we may regard D as a closed circular       *)
(* region with center at the origin): the solid cylinder around the x2 axis, *)
(* its lower and upper halves (the cells C_1, C_2), the middle disk D in the *)
(* plane x2 = 0 (the revolution of the segment from 0 to e1 about the x2     *)
(* axis, as in revolution of pc_moi_core_stmt.ml), its rim, the two          *)
(* hemispheres of the boundary, two axis points qlo, qhi separated by D, and *)
(* the axis.                                                                 *)
(* ------------------------------------------------------------------------- *)

let moi_s32_cyl = new_definition
 `moi_s32_cyl = {x:real^3 | x$1 pow 2 + x$3 pow 2 <= &1 /\ abs(x$2) <= &1}`;;

let moi_s32_lo = new_definition
 `moi_s32_lo = {x:real^3 | x IN moi_s32_cyl /\ x$2 <= &0}`;;

let moi_s32_hi = new_definition
 `moi_s32_hi = {x:real^3 | x IN moi_s32_cyl /\ &0 <= x$2}`;;

let moi_s32_disk = new_definition
 `moi_s32_disk = {x:real^3 | x IN moi_s32_cyl /\ x$2 = &0}`;;

let moi_s32_rim = new_definition
 `moi_s32_rim = {x:real^3 | x IN moi_s32_disk /\ x$1 pow 2 + x$3 pow 2 = &1}`;;

let moi_s32_lohemi = new_definition
 `moi_s32_lohemi =
    {x:real^3 | x IN moi_s32_lo /\ (x$1 pow 2 + x$3 pow 2 = &1 \/ x$2 = -- &1)}`;;

let moi_s32_hihemi = new_definition
 `moi_s32_hihemi =
    {x:real^3 | x IN moi_s32_hi /\ (x$1 pow 2 + x$3 pow 2 = &1 \/ x$2 = &1)}`;;

let moi_s32_qlo = new_definition
 `moi_s32_qlo = vector[&0; -- &1 / &2; &0]:real^3`;;

let moi_s32_qhi = new_definition
 `moi_s32_qhi = vector[&0; &1 / &2; &0]:real^3`;;

let moi_s32_axis = new_definition
 `moi_s32_axis = {x:real^3 | x$1 = &0 /\ x$3 = &0}`;;

(* The data of one application: g = h o (chart) continuous and injective on *)
(* the model, v an open set inside the model interior, off the axis,        *)
(* containing the disk minus centre and rim (the solid tori S_i lie in v;   *)
(* the user takes v inside the preimage of W and off chosen compact sets).  *)

let moi_s32_model = new_definition
 `moi_s32_model (g:real^3->real^3) (v:real^3->bool) <=>
    g continuous_on moi_s32_cyl /\
    (!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ g x = g y ==> x = y) /\
    open v /\ v SUBSET interior moi_s32_cyl /\ DISJOINT v moi_s32_axis /\
    moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim) SUBSET v`;;

(* The tower (p.224): points P_i = r_i e1 on the x1 axis (i an integer),     *)
(* radii increasing from 0 to 1, planar 2-cells D_i (dd i), PL solid tori    *)
(* S''_i (s2 i); every three consecutive indices form a canonical            *)
(* configuration for g (so consecutive boundaries cross); the revolved D_i  *)
(* lie in v, D_i and D_k are disjoint for k >= i + 2, and the revolved D_i  *)
(* accumulate only at the centre and the rim (Lemma 1, p.225).              *)

let moi_s32_tower = new_definition
 `moi_s32_tower (g:real^3->real^3) (v:real^3->bool) (pp:int->real^3)
                (dd:int->real^3->bool) (s2:int->real^3->bool) <=>
    (!i. canonical_configuration (\k. pp(i + &k)) (\k. dd(i + &k)) g
                                 (\k. s2(i + &k))) /\
    (!i. ?r. &0 < r /\ r < &1 /\ pp i = r % basis 1) /\
    (!i. (pp i)$1 < (pp(i + &1))$1) /\
    (!e. &0 < e ==> (?i. (pp i)$1 < e) /\ (?i. &1 - e < (pp i)$1)) /\
    (!i. revolution (dd i) SUBSET v) /\
    (!i k. i + &2 <= k ==> DISJOINT (dd i) (dd k)) /\
    (!c. compact c /\ DISJOINT c (vec 0 INSERT moi_s32_rim)
         ==> FINITE {i:int | ~(revolution (dd i) INTER c = {})})`;;

(* K = the union of the even boundaries T''_(2i); the level region of the   *)
(* odd torus T''_(2i+1) (S'_(2i) UNION S'_(2i+1) UNION S'_(2i+2), the bound *)
(* (2) of p.227); the open set M = Int (C'_1 UNION C'_2) of the separations. *)

let moi_s32_evens = new_definition
 `moi_s32_evens (s2:int->real^3->bool) =
    UNIONS {frontier (s2 (&2 * i)) | i IN (:int)}`;;

let moi_s32_lvl = new_definition
 `moi_s32_lvl (g:real^3->real^3) (dd:int->real^3->bool) (i:int) =
    IMAGE g (revolution (dd (&2 * i))) UNION
    IMAGE g (revolution (dd (&2 * i + &1))) UNION
    IMAGE g (revolution (dd (&2 * i + &2)))`;;

let moi_s32_open = new_definition
 `moi_s32_open (g:real^3->real^3) = interior (IMAGE g moi_s32_cyl)`;;

(* The barrier sets: K, the surfaces of a family fam, and the centre P'.    *)

let moi_s32_set = new_definition
 `moi_s32_set (g:real^3->real^3) (s2:int->real^3->bool) (fam:(real^3->bool)->bool) =
    moi_s32_evens s2 UNION UNIONS fam UNION {g (vec 0)}`;;

(* An essential polygon of the even torus T''_k.                            *)

let moi_s32_ess = new_definition
 `moi_s32_ess (s2:int->real^3->bool) (k:int) (j:real^3->bool) <=>
    pl_sphere 1 j /\ j SUBSET frontier (s2 k) /\
    ~(?d. d SUBSET frontier (s2 k) /\ pl_cell_with_boundary 2 d j)`;;

(* A state of Step 1 (pp.225-226) after the levels in lev are processed: a  *)
(* disjoint family of compact connected PL surfaces (the components of L,   *)
(* p.225, after splittings), each inside one level region with its boundary *)
(* exactly its trace on K, lying on the two even tori of the level, every   *)
(* boundary polygon on a processed even torus essential there; finitely     *)
(* many per level; the barrier set closed in M and separating qlo from qhi. *)

let moi_s32_state = new_definition
 `moi_s32_state (g:real^3->real^3) (dd:int->real^3->bool) (s2:int->real^3->bool)
                (lev:int->bool) (fam:(real^3->bool)->bool) <=>
    pairwise DISJOINT fam /\
    (!c. c IN fam
         ==> ?i cc. c SUBSET moi_s32_lvl g dd i /\
                    FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
                    UNIONS cc = c /\ connected c /\ ~(c = {}) /\
                    surface_boundary cc = c INTER moi_s32_evens s2 /\
                    c INTER moi_s32_evens s2 SUBSET
                      frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2)) /\
                    (i IN lev
                     ==> !jj. jj IN components (c INTER frontier (s2 (&2 * i)))
                              ==> moi_s32_ess s2 (&2 * i) jj) /\
                    ((i + &1) IN lev
                     ==> !jj. jj IN components (c INTER frontier (s2 (&2 * i + &2)))
                              ==> moi_s32_ess s2 (&2 * i + &2) jj)) /\
    (!i. FINITE {c | c IN fam /\ c SUBSET moi_s32_lvl g dd i}) /\
    closed_in (subtopology euclidean (moi_s32_open g)) (moi_s32_set g s2 fam) /\
    separates_in (moi_s32_open g) (moi_s32_set g s2 fam)
                 {g moi_s32_qlo} {g moi_s32_qhi}`;;

(* After Step 1 (p.226, Types 1-3): every surface is closed and disjoint     *)
(* from K (Type 1) or a PL annulus whose two ends are its trace on K,       *)
(* essential polygons of the even tori of its level (Types 2 and 3).        *)

let moi_s32_reduced = new_definition
 `moi_s32_reduced (g:real^3->real^3) (dd:int->real^3->bool) (s2:int->real^3->bool)
                  (fam:(real^3->bool)->bool) <=>
    moi_s32_state g dd s2 (:int) fam /\
    (!c. c IN fam
         ==> ?i. c SUBSET moi_s32_lvl g dd i /\
                 (DISJOINT c (moi_s32_evens s2) \/
                  ?j j'. pl_annulus_with_ends c j j' /\
                         c INTER moi_s32_evens s2 = j UNION j' /\
                         (moi_s32_ess s2 (&2 * i) j \/ moi_s32_ess s2 (&2 * i + &2) j) /\
                         (moi_s32_ess s2 (&2 * i) j' \/
                          moi_s32_ess s2 (&2 * i + &2) j')))`;;

(* The annular chain M_6 minus one annulus of each T''_(2i) (p.227): annuli *)
(* hh i in T''_(2i) from jl i to jh i and bridges bb i from jh i to         *)
(* jl (i + 1) in the level region; the set U = chain plus the centre is     *)
(* closed in M and separates qlo from qhi.                                  *)

let moi_s32_chainset = new_definition
 `moi_s32_chainset (g:real^3->real^3) (hh:int->real^3->bool) (bb:int->real^3->bool) =
    UNIONS {hh i UNION bb i | i IN (:int)} UNION {g (vec 0)}`;;

let moi_s32_chain = new_definition
 `moi_s32_chain (g:real^3->real^3) (dd:int->real^3->bool) (s2:int->real^3->bool)
                (hh:int->real^3->bool) (bb:int->real^3->bool)
                (jl:int->real^3->bool) (jh:int->real^3->bool) <=>
    (!i. pl_annulus_with_ends (hh i) (jl i) (jh i) /\
         hh i SUBSET frontier (s2 (&2 * i)) /\
         pl_annulus_with_ends (bb i) (jh i) (jl (i + &1)) /\
         bb i SUBSET moi_s32_lvl g dd i /\
         bb i INTER moi_s32_evens s2 = jh i UNION jl (i + &1)) /\
    (!i k. ~(i = k) ==> DISJOINT (bb i) (bb k)) /\
    closed_in (subtopology euclidean (moi_s32_open g)) (moi_s32_chainset g hh bb) /\
    separates_in (moi_s32_open g) (moi_s32_chainset g hh bb)
                 {g moi_s32_qlo} {g moi_s32_qhi}`;;

(* Model points and halves of the slab of the s35 edge charts (32.3).      *)

let moi_s32_slab_lo = new_definition
 `moi_s32_slab_lo = {x:real^3 | x IN moi_s35_slab /\ x$3 <= &0}`;;

let moi_s32_slab_hi = new_definition
 `moi_s32_slab_hi = {x:real^3 | x IN moi_s35_slab /\ &0 <= x$3}`;;

let moi_s32_slo = new_definition
 `moi_s32_slo = vector[&0; &0; -- &1 / &16]:real^3`;;

let moi_s32_shi = new_definition
 `moi_s32_shi = vector[&0; &0; &1 / &16]:real^3`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s32_cyl; moi_s32_lo; moi_s32_hi; moi_s32_disk; moi_s32_rim; moi_s32_lohemi;
   moi_s32_hihemi; moi_s32_qlo; moi_s32_qhi; moi_s32_axis; moi_s32_model;
   moi_s32_tower; moi_s32_evens; moi_s32_lvl; moi_s32_open; moi_s32_set;
   moi_s32_ess; moi_s32_state; moi_s32_reduced; moi_s32_chainset; moi_s32_chain;
   moi_s32_slab_lo; moi_s32_slab_hi; moi_s32_slo; moi_s32_shi];;

(* ========================================================================= *)
(* 5. Sec 32 statements.                                                     *)
(* ========================================================================= *)

(* 5.1 The chart (unit s32_chart): a ball split by a proper disk into two   *)
(* balls is homeomorphic to the model cylinder split by its middle disk,    *)
(* the centre going to a given interior point of the disk (PL standardiza-  *)
(* tion of both halves by MOI_SCD_COR_EXTEND_BALL and the 2D disk facts,    *)
(* composed with a fixed homeomorphism of the double cube onto the          *)
(* cylinder); the hemispheres go to the two halves of the boundary sphere.  *)

let MOI_S32_CHART =
  mk_imp(list_mk_conj [MOI_SCH3_DISK_COMPLEMENT; MOI_SCH3_SPHERE_SPLIT],
 `!c1 c2 dd jj (p:real^3).
     pl_ball 3 c1 /\ pl_ball 3 c2 /\ pl_ball 3 (c1 UNION c2) /\
     c1 INTER c2 = dd /\ pl_cell_with_boundary 2 dd jj /\
     dd INTER frontier (c1 UNION c2) = jj /\ p IN dd DIFF jj
     ==> ?(psi:real^3->real^3) psi'.
           homeomorphism (moi_s32_cyl,c1 UNION c2) (psi,psi') /\
           IMAGE psi moi_s32_lo = c1 /\ IMAGE psi moi_s32_hi = c2 /\
           IMAGE psi moi_s32_disk = dd /\ IMAGE psi moi_s32_rim = jj /\
           IMAGE psi moi_s32_lohemi = frontier c1 DIFF (dd DIFF jj) /\
           IMAGE psi moi_s32_hihemi = frontier c2 DIFF (dd DIFF jj) /\
           psi (vec 0) = p`);;

(* MODEL_V (unit s32_chart): the open set v of moi_s32_model for a given     *)
(* closed w around g(disk - centre - rim), avoiding two connected sets that *)
(* join qlo and qhi to given points a1, a2 of the two halves off the disk   *)
(* (segments; v = the open cylinder meeting g^-1(Int w) minus the axis and   *)
(* the segments); g(centre) lies in w (closedness).  Used to put h q1 and   *)
(* h q2 of MOISE_322_CELLS on the right sides.                              *)

let MOI_S32_MODEL_V =
 `!(g:real^3->real^3) w a1 a2.
     g continuous_on moi_s32_cyl /\
     (!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ g x = g y ==> x = y) /\
     closed w /\
     IMAGE g (moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim)) SUBSET interior w /\
     a1 IN moi_s32_lo DIFF moi_s32_disk /\ a2 IN moi_s32_hi DIFF moi_s32_disk
     ==> g (vec 0) IN w /\
         ?v k1 k2. moi_s32_model g v /\ IMAGE g v SUBSET interior w /\
                   connected k1 /\ moi_s32_qlo IN k1 /\ a1 IN k1 /\
                   connected k2 /\ moi_s32_qhi IN k2 /\ a2 IN k2 /\
                   k1 UNION k2 SUBSET
                   moi_s32_cyl DIFF (vec 0 INSERT (moi_s32_rim UNION v))`;;

(* 5.2 Separation passes to locally eventually constant limits (unit        *)
(* s32_iter; the limit arguments of Steps 1-4, pp.226-227; DG               *)
(* separates_of_locally_eventually_eq).                                     *)

let MOI_S32_LIMIT =
 `!(m:real^N->bool) (ms:num->real^N->bool) mm hs ks q.
     open m /\ connected hs /\ connected ks /\ hs SUBSET m /\ ks SUBSET m /\
     closed_in (subtopology euclidean m) mm /\ DISJOINT mm (hs UNION ks) /\
     (!n. closed_in (subtopology euclidean m) (ms n) /\ separates_in m (ms n) hs ks) /\
     q IN mm /\ (!n. q IN ms n) /\
     (!x. x IN m /\ ~(x = q)
          ==> ?u n0. open u /\ x IN u /\ !n. n0 <= n ==> ms n INTER u = mm INTER u)
     ==> separates_in m mm hs ks`;;

(* 5.3 The tower (unit s32_tower; p.224): radii, stadium disks D_i around    *)
(* the segments, PL solid tori from 31.1 for every triple, then the even    *)
(* ones moved by RECROSS to cross their odd neighbours.                     *)

let MOI_S32_TOWER =
  mk_imp(list_mk_conj [`MOISE_311_STATEMENT`; moi_std_csq MOI_S31_RECROSS;
                       moi_n3 MOI_FND_PL_SOLID_TORUS_BASIC],
 `!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> ?pp dd s2. moi_s32_tower g v pp dd s2`);;

(* 5.4 The initial barrier M_1 = K UNION L UNION {P'} (unit s32_init;       *)
(* Lemmas 1-3, p.225): the components of L are compact PL surfaces in the   *)
(* odd tori with boundary on K (crossing), M_1 is closed in M and separates *)
(* (Int D' separates, the union of the S''_i is a neighbourhood of          *)
(* Int D' - P', and Fr V lies in M_1).                                      *)

let MOI_S32_INITIAL =
  mk_imp(list_mk_conj [moi_std_csq (moi_n3 MOI_S30_SURFACE_TRIANG);
                       moi_n3 MOI_FND_PL_SOLID_TORUS_BASIC],
 `!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> ?fam. moi_s32_state g dd s2 {} fam /\
               moi_s32_set g s2 fam =
               moi_s32_evens s2 UNION
               (UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} DIFF
                UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) UNION
               {g (vec 0)}`);;

(* 5.5 Step 1 at one level (unit s32_level; pp.225-226): the finitely many  *)
(* polygons of the even torus T''_(2i) bounding disks in it are removed     *)
(* inmost first by 30.3 inside Int S'_(2i), keeping T''_(2i) fixed.         *)

let MOI_S32_LEVEL =
  mk_imp(list_mk_conj [`MOISE_303_STATEMENT`; `MOISE_268_STATEMENT`;
                       moi_n3 MOI_FND_BICOLLAR_CURVE_2;
                       moi_std_csq (moi_n3 MOI_S30_SURFACE_TRIANG)],
 `!(g:real^3->real^3) v pp dd s2 lev fam i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\ ~(i IN lev)
     ==> ?fam'. moi_s32_state g dd s2 (i INSERT lev) fam' /\
                moi_s32_set g s2 fam' DIFF interior (IMAGE g (revolution (dd (&2 * i)))) =
                moi_s32_set g s2 fam DIFF interior (IMAGE g (revolution (dd (&2 * i))))`);;

(* 5.6 Step 1 for all levels (unit s32_iter; p.226 in the order i = 0, 1,  *)
(* -1, 2, -2, ..., the limit argument) and the classification of the       *)
(* resulting surfaces into Types 1-3 (p.226-227: 31.4, 28.6, and the        *)
(* impossibility of one or more than two essential boundary polygons).      *)

let MOI_S32_ITERATE =
  mk_imp(list_mk_conj [moi_std_csq MOI_S32_LEVEL; moi_n3 MOI_S32_LIMIT],
 `!(g:real^3->real^3) v pp dd s2 fam.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 {} fam
     ==> ?fam'. moi_s32_state g dd s2 (:int) fam'`);;

let MOI_S32_CLASSIFY =
  mk_imp(list_mk_conj [`MOISE_314_STATEMENT`; `MOISE_286_STATEMENT`;
                       `MOISE_268_STATEMENT`; moi_n3 MOI_FND_BICOLLAR_CURVE_2],
 `!(g:real^3->real^3) v pp dd s2 fam.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 (:int) fam
     ==> moi_s32_reduced g dd s2 fam`);;

(* 5.7 Steps 2-4 and the final deletion (unit s32_steps; pp.226-227):       *)
(* delete Type 1 surfaces (30.1), Type 2 annuli (26.7), all but one Type 3  *)
(* bridge per level (at least one exists: otherwise the barrier splits into *)
(* two non-separating closed parts, 30.1), then one of the two annuli of    *)
(* each T''_(2i) (28.6).                                                    *)

let MOI_S32_STEPS24 =
  mk_imp(list_mk_conj [`MOISE_301_STATEMENT`; `MOISE_267_STATEMENT`;
                       `MOISE_286_STATEMENT`; moi_n3 MOI_S32_LIMIT],
 `!(g:real^3->real^3) v pp dd s2 fam.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_reduced g dd s2 fam
     ==> ?hh bb jl jh. moi_s32_chain g dd s2 hh bb jl jh`);;

(* 5.8 The pseudo-cell (unit s32_cell; end of the proof of 32.1, p.227):    *)
(* the annular chain plus the centre is an open 2-cell whose closure adds   *)
(* exactly the rim, and it is locally polyhedral off the centre; the chain *)
(* lies in g(v) plus the centre (the tori S''_i lie in g(v)).              *)

let MOI_S32_CELL =
 `!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> pseudo_cell (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim)
                     (IMAGE g moi_s32_rim) (g (vec 0)) /\
         moi_s32_chainset g hh bb SUBSET g (vec 0) INSERT IMAGE g v`;;

(* 5.9 Two sides (unit s32_sides; 32.2, pp.227-228).                        *)

let MOI_S32_SIDES =
 `!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     pseudo_cell (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim)
                 (IMAGE g moi_s32_rim) (g (vec 0))
     ==> ?u1 u2.
           components (IMAGE g moi_s32_cyl DIFF
                       (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim)) =
           {u1,u2} /\
           g moi_s32_qlo IN u1 /\ g moi_s32_qhi IN u2 /\ ~(u1 = u2) /\
           moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim SUBSET frontier u1 /\
           moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim SUBSET frontier u2 /\
           IMAGE g moi_s32_lohemi SUBSET frontier u1 /\
           IMAGE g moi_s32_hihemi SUBSET frontier u2`;;

(* 5.10 32.3 (unit s32_handles; p.228).  SLAB_W: the two halves of the thin *)
(* slab of the s35 edge chart are cells meeting in the splitting disk, as   *)
(* in MOISE_322_CELLS, with a closed neighbourhood W of the open splitting  *)
(* disk minus its centre pinched at the centre (W meets h|l| only there).    *)
(* HANDLES: the pseudo-cells of 32.1-32.2 in the slabs give the handle      *)
(* decomposition (7)-(10).                                                  *)

let moi_s32_c1 = `IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo`;;
let moi_s32_c2 = `IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s32_slab_hi`;;

let MOI_S32_SLAB_W =
  mk_imp(list_mk_conj [moi_n3 MOI_FND_GRAPH_TUBE; MOI_FND_GRAPH_TUBE_FRONTIER_3;
                       moi_n3 MOI_S35_TUBE_TRIPLE],
 `!(t:(real^3->bool)->bool) l (h:real^3->real^3) g av bv psi e.
     FINITE t /\ graph_in_complex t l /\ h continuous_on UNIONS t /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
     moi_s35_charts t l g av bv psi /\ moi_s35_edge l e
     ==> pl_ball 3 (IMAGE (psi e) moi_s32_slab_lo) /\
         pl_ball 3 (IMAGE (psi e) moi_s32_slab_hi) /\
         pl_ball 3 (IMAGE (psi e) moi_s32_slab_lo UNION IMAGE (psi e) moi_s32_slab_hi) /\
         IMAGE (psi e) moi_s32_slab_lo INTER IMAGE (psi e) moi_s32_slab_hi =
         derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) /\
         (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e)) INTER
         frontier (IMAGE (psi e) moi_s32_slab_lo UNION IMAGE (psi e) moi_s32_slab_hi) =
         derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) INTER
         derived_frontier t l /\
         midpoint(av e,bv e) IN
           (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e)) DIFF
           (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) INTER
            derived_frontier t l) /\
         psi e moi_s32_slo IN
           IMAGE (psi e) moi_s32_slab_lo DIFF
           (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e)) /\
         psi e moi_s32_shi IN
           IMAGE (psi e) moi_s32_slab_hi DIFF
           (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e)) /\
         IMAGE (psi e) moi_s32_slab_lo UNION IMAGE (psi e) moi_s32_slab_hi SUBSET
         UNIONS t /\
         ?w. closed w /\
             w SUBSET IMAGE h (IMAGE (psi e) moi_s32_slab_lo UNION
                               IMAGE (psi e) moi_s32_slab_hi) /\
             (IMAGE h ((derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e))
                       DIFF (derived_dual_cell t l (av e) INTER
                             derived_dual_cell t l (bv e) INTER derived_frontier t l))
              DELETE h(midpoint(av e,bv e))) SUBSET interior w /\
             w INTER frontier (IMAGE h (IMAGE (psi e) moi_s32_slab_lo UNION
                                        IMAGE (psi e) moi_s32_slab_hi)) =
             IMAGE h (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) INTER
                      derived_frontier t l) /\
             w INTER IMAGE h (UNIONS l) = {h(midpoint(av e,bv e))}`);;

(* HANDLES takes, for every edge e, the slab cells (as in SLAB_W), its W    *)
(* (ww e) and the conclusion of MOISE_322_CELLS for them (pseudo-cell ee e, *)
(* components uu1 e, uu2 e), and gives the conclusion of MOISE_323 with the *)
(* pieces c v = closure of the component of h(N) - UNIONS E containing h v. *)

let moi_s32_edge_facts =
 `!e:real^3->bool. moi_s35_edge (l:(real^3->bool)->bool) e
      ==> closed ((ww:(real^3->bool)->real^3->bool) e) /\
          ww e SUBSET IMAGE (h:real^3->real^3)
                         (IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo UNION
                               IMAGE (psi e) moi_s32_slab_hi) /\
          (IMAGE h ((derived_dual_cell (t:(real^3->bool)->bool) l ((av:(real^3->bool)->real^3) e) INTER
                     derived_dual_cell t l ((bv:(real^3->bool)->real^3) e))
                    DIFF (derived_dual_cell t l (av e) INTER
                          derived_dual_cell t l (bv e) INTER derived_frontier t l))
           DELETE h(midpoint(av e,bv e))) SUBSET interior (ww e) /\
          ww e INTER frontier (IMAGE h (IMAGE (psi e) moi_s32_slab_lo UNION
                                        IMAGE (psi e) moi_s32_slab_hi)) =
          IMAGE h (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) INTER
                   derived_frontier t l) /\
          ww e INTER IMAGE h (UNIONS l) = {h(midpoint(av e,bv e))} /\
          pseudo_cell ((ee:(real^3->bool)->real^3->bool) e)
            (IMAGE h (derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) INTER
                      derived_frontier t l))
            (h(midpoint(av e,bv e))) /\
          ee e SUBSET ww e /\
          components (IMAGE h (IMAGE (psi e) moi_s32_slab_lo UNION
                               IMAGE (psi e) moi_s32_slab_hi) DIFF ee e) =
          {(uu1:(real^3->bool)->real^3->bool) e,
           (uu2:(real^3->bool)->real^3->bool) e} /\
          h(psi e moi_s32_slo) IN uu1 e /\ h(psi e moi_s32_shi) IN uu2 e /\
          ~(uu1 e = uu2 e) /\ ee e SUBSET frontier (uu1 e) /\
          ee e SUBSET frontier (uu2 e) /\
          IMAGE h (frontier (IMAGE (psi e) moi_s32_slab_lo) DIFF
                   ((derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e))
                    DIFF (derived_dual_cell t l (av e) INTER
                          derived_dual_cell t l (bv e) INTER derived_frontier t l)))
          SUBSET frontier (uu1 e) /\
          IMAGE h (frontier (IMAGE (psi e) moi_s32_slab_hi) DIFF
                   ((derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e))
                    DIFF (derived_dual_cell t l (av e) INTER
                          derived_dual_cell t l (bv e) INTER derived_frontier t l)))
          SUBSET frontier (uu2 e)`;;

(* The conclusion of MOISE_323 instantiated with the pseudo-cells ee and   *)
(* the pieces c v (extracted from the definition of MOISE_323 in             *)
(* pc_moi_core_stmt.ml, so that the text is exactly that one).               *)

let moi_s32_323_parts =
  let tm = rhs(concl MOISE_323_STATEMENT) in
  let vs,body = strip_forall tm in
  let hyp,concl0 = dest_imp body in
  let ev,b1 = dest_exists concl0 in
  let cv,b2 = dest_exists b1 in
  vs,hyp,ev,cv,b2;;

let moi_s32_pieces =
 `\v. closure (connected_component
                 (IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF
                  UNIONS {(ee:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})
                 (h v))`;;

let MOI_S32_HANDLES =
  let vs,hyp,ev,cv,b2 = moi_s32_323_parts in
  let eev = `ee:(real^3->bool)->real^3->bool` in
  let concl1 = rhs(concl(TOP_DEPTH_CONV BETA_CONV
                 (vsubst [eev,ev; moi_s32_pieces,cv] b2))) in
  let extra = [`(!v. {v} IN l ==> (g:real^3->real^3->bool) v =
                                  {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v})`;
               `moi_s35_charts t l g av bv (psi:(real^3->bool)->real^3->real^3)`;
               moi_s32_edge_facts] in
  let allv = vs @ [`g:real^3->real^3->bool`; `av:(real^3->bool)->real^3`;
                   `bv:(real^3->bool)->real^3`;
                   `psi:(real^3->bool)->real^3->real^3`;
                   `ww:(real^3->bool)->real^3->bool`; eev;
                   `uu1:(real^3->bool)->real^3->bool`;
                   `uu2:(real^3->bool)->real^3->bool`] in
  mk_imp(list_mk_conj [moi_n3 MOI_FND_GRAPH_TUBE; MOI_FND_GRAPH_TUBE_FRONTIER_3;
                       moi_n3 MOI_S35_TUBE_TRIPLE; moi_n3 MOI_FND_DERIVED_NBHD_BASIC],
         list_mk_forall(allv, mk_imp(list_mk_conj (hyp :: extra), concl1)));;

(* 5.11 32.4 (units s32_cap_a, s32_cap_b; pp.228-229).  CAP_SETUP: a small *)
(* PL 3-ball c around the centre (inside ball(p,d), off the rim j) whose   *)
(* boundary crosses the pseudo-cell (off the centre) in finitely many       *)
(* disjoint polygons, with c INTER e inside a small topological disk dz of  *)
(* e - j around p (general position of a cube boundary, MOI_FND_GP_         *)
(* SURFACES_3, on a locally finite combinatorial triangulation of e - j -   *)
(* p).  CAP_SURGERY: the separating polygon bounds a disk in the sphere     *)
(* frontier c; an irreducible such disk is cleared of the other polygons by *)
(* inmost splittings (the polygons bound PL disks in e - p: POLY_DISK, with *)
(* the planar Jordan-Schoenflies theorem of cauchy.ml in the chart of e - j; *)
(* push-offs in DISK_CHART boxes); the result and the disk of e it bounds    *)
(* lie in ball(p,d) (the conclusion missing from the printed 32.4).         *)

let moi_s32_cap_data =
 `pl_ball 3 c /\ c SUBSET ball(p:real^3,d) /\ p IN interior c /\ DISJOINT c j /\
  homeomorphism (cball(vec 0:real^2,&1),dz) (fz:real^2->real^3,gz) /\
  fz(vec 0) = p /\ dz SUBSET (e DIFF j) INTER ball(p,d) /\
  c INTER e SUBSET IMAGE fz (ball(vec 0,&1)) /\
  FINITE ff /\ pairwise DISJOINT ff /\ (!jj. jj IN ff ==> pl_sphere 1 jj) /\
  frontier c INTER e = UNIONS ff /\
  (!x. x IN frontier c INTER e
       ==> pl_crossing_at (frontier c) ((e DIFF j) DELETE p) x)`;;

let moi_s32_cap_vars =
  [`c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`; `gz:real^3->real^2`;
   `ff:(real^3->bool)->bool`];;

let MOI_S32_CAP_SETUP =
  mk_imp(list_mk_conj [MOI_FND_GP_SURFACES_3; moi_std_csq (moi_n3 MOI_S30_SURFACE_TRIANG)],
   mk_forall(`e:real^3->bool`, mk_forall(`j:real^3->bool`,
   mk_forall(`p:real^3`, mk_forall(`d:real`,
     mk_imp(`pseudo_cell (e:real^3->bool) j p /\ &0 < d`,
            list_mk_exists(moi_s32_cap_vars, moi_s32_cap_data)))))));;

let MOI_S32_CAP_SURGERY =
  let tm = rhs(concl MOISE_324_STATEMENT) in
  let vs,body = strip_forall tm in
  let hyp,concl0 = dest_imp body in
  mk_imp(list_mk_conj [moi_std_csq (moi_n3 MOI_S30_POLY_DISK); moi_std_csq MOI_S30_DISK_CHART;
                       MOI_SCH3_SPHERE_SPLIT;
                       `PL_SCHOENFLIES_3_STATEMENT`],
         list_mk_forall(vs @ moi_s32_cap_vars,
                        mk_imp(mk_conj(hyp, moi_s32_cap_data), concl0)));;

map type_of [MOI_S32_CHART; MOI_S32_MODEL_V; MOI_S32_LIMIT; MOI_S32_TOWER; MOI_S32_INITIAL;
             MOI_S32_LEVEL; MOI_S32_ITERATE; MOI_S32_CLASSIFY; MOI_S32_STEPS24;
             MOI_S32_CELL; MOI_S32_SIDES; MOI_S32_SLAB_W; MOI_S32_HANDLES;
             MOI_S32_CAP_SETUP; MOI_S32_CAP_SURGERY];;

(* ========================================================================= *)
(* 6. Glue.  For a statement T = (A ==> C) the core glue theorems use C.     *)
(* The full glue theorem of an item takes as hypotheses the dependency       *)
(* closure of its core (computed below: every statement whose consequent is  *)
(* needed, with its antecedents, down to the leaves, foundation terms and    *)
(* statements of other parts) and concludes the item (a MOI_PROD term of     *)
(* pc_moi_core_stmt.ml, or the leaf statement); the antecedents of the       *)
(* producer implication are not expanded.                                    *)
(* ========================================================================= *)

(* The statements of this file.                                             *)

let moi_std_targets =
  [ "MOI_S30_ANNULUS_2D",MOI_S30_ANNULUS_2D; "MOI_S30_DISK_CHART",MOI_S30_DISK_CHART;
    "MOI_S30_CUTCAP",MOI_S30_CUTCAP; "MOI_S30_EULER_NAT",MOI_S30_EULER_NAT;
    "MOI_S30_BOUNDS",MOI_S30_BOUNDS; "MOI_S30_EULER_EVEN",MOI_S30_EULER_EVEN;
    "MOI_S30_INIT_SURFACE",MOI_S30_INIT_SURFACE; "MOI_S30_SPLIT_ESSENTIAL",MOI_S30_SPLIT_ESSENTIAL;
    "MOI_S30_COMPRESS",MOI_S30_COMPRESS;
    "MOI_S30_Z2_SC_CLOSED",MOI_S30_Z2_SC_CLOSED; "MOI_S30_Z2_SC_BOUNDARY",MOI_S30_Z2_SC_BOUNDARY;
    "MOI_S30_Z2_TORUS_BOUND",MOI_S30_Z2_TORUS_BOUND; "MOI_S30_SURFACE_TRIANG",MOI_S30_SURFACE_TRIANG;
    "MOI_S30_POLY_DISK",MOI_S30_POLY_DISK; "MOI_S30_PL_TORUS_COMPLEX",MOI_S30_PL_TORUS_COMPLEX;
    "MOI_S30_SPHERICAL_SHELL_FACTS",MOI_S30_SPHERICAL_SHELL_FACTS;
    "MOI_S30_TOROIDAL_SHELL_FACTS",MOI_S30_TOROIDAL_SHELL_FACTS;
    "MOI_S30_SHELL_NO_SPHERE",MOI_S30_SHELL_NO_SPHERE; "MOI_S30_SHELL_CORE_ESSENTIAL",MOI_S30_SHELL_CORE_ESSENTIAL;
    "MOI_S30_TORUS_REGION",MOI_S30_TORUS_REGION; "MOI_S30_TORUS_LOOP",MOI_S30_TORUS_LOOP;
    "MOI_S30_HANDLE_SOLID_TORUS",MOI_S30_HANDLE_SOLID_TORUS; "MOI_S30_307_OUTSIDE",MOI_S30_307_OUTSIDE;
    "MOI_S30_307_INSIDE",MOI_S30_307_INSIDE;
    "MOI_S31_REV_SHELL",MOI_S31_REV_SHELL; "MOI_S31_RECROSS",MOI_S31_RECROSS;
    "MOI_S31_MV_POLY",MOI_S31_MV_POLY; "MOI_S31_CARRIER",MOI_S31_CARRIER;
    "MOI_S31_NULL_POLYGON",MOI_S31_NULL_POLYGON; "MOI_S31_SPINES",MOI_S31_SPINES;
    "MOI_S31_TRANSFER",MOI_S31_TRANSFER;
    "MOI_S32_CHART",MOI_S32_CHART; "MOI_S32_MODEL_V",MOI_S32_MODEL_V; "MOI_S32_LIMIT",MOI_S32_LIMIT; "MOI_S32_TOWER",MOI_S32_TOWER;
    "MOI_S32_INITIAL",MOI_S32_INITIAL; "MOI_S32_LEVEL",MOI_S32_LEVEL; "MOI_S32_ITERATE",MOI_S32_ITERATE;
    "MOI_S32_CLASSIFY",MOI_S32_CLASSIFY; "MOI_S32_STEPS24",MOI_S32_STEPS24; "MOI_S32_CELL",MOI_S32_CELL;
    "MOI_S32_SIDES",MOI_S32_SIDES; "MOI_S32_SLAB_W",MOI_S32_SLAB_W; "MOI_S32_HANDLES",MOI_S32_HANDLES;
    "MOI_S32_CAP_SETUP",MOI_S32_CAP_SETUP; "MOI_S32_CAP_SURGERY",MOI_S32_CAP_SURGERY];;

(* Statements of other parts with antecedents used by the glue.             *)

let moi_std_ext_targets = [MOI_S35_CHARTS; MOI_S26_COMPACT_NBHD; MOI_S26_CUT];;

let moi_std_find_target a =
  let ts = map snd moi_std_targets @ moi_std_ext_targets in
  let cands = ts @ map moi_n3 ts in
  try Some(find (fun t -> aconv (moi_std_csq t) a) cands) with Failure _ -> None;;

let rec moi_std_closure stop acc tms =
  match tms with
    [] -> acc
  | a::rest ->
      if exists (aconv a) stop || exists (aconv a) acc
      then moi_std_closure stop acc rest else
      match moi_std_find_target a with
        Some t ->
          if exists (aconv t) acc then moi_std_closure stop acc rest else
          let ants = if is_imp t then conjuncts(fst(dest_imp t)) else [] in
          moi_std_closure stop (t::acc) (ants @ rest)
      | None -> moi_std_closure stop (a::acc) rest;;

let moi_std_full_stmt hyps prod =
  let stop = if is_imp prod then conjuncts(fst(dest_imp prod)) else [] in
  mk_imp(list_mk_conj(rev(moi_std_closure stop [] hyps)), prod);;

let moi_std_full core prod =
  moi_std_full_stmt (conjuncts(fst(dest_imp(concl core)))) prod;;

(* Discharge a needed consequent from the hypotheses: accept it, or match    *)
(* the consequent of a statement (with backtracking over the assumptions)    *)
(* and discharge its antecedents recursively.                                *)

let rec MOI_STD_DISCHARGE_TAC g =
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   FIRST_ASSUM (fun th -> MATCH_MP_TAC th THEN REPEAT CONJ_TAC THEN
                          MOI_STD_DISCHARGE_TAC)) g;;

let MOI_STD_FULL_TAC core =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC core THEN REPEAT CONJ_TAC THEN
  MOI_STD_DISCHARGE_TAC;;

(* The revolution about the x2 axis commutes with intersections (the point *)
(* of the half plane over a point is unique).                               *)

let MOI_STD_REV_INTER = prove
 (`!x y:real^3->bool. revolution x INTER revolution y = revolution (x INTER y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[revolution; EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `p:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `q':real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q':real^3 = q` (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH_EQ];
    MESON_TAC[]]);;

let MOI_STD_REV_EMPTY = prove
 (`revolution ({}:real^3->bool) = {}`,
  REWRITE_TAC[revolution; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM]);;

let MOI_STD_REV_MONO = prove
 (`!x y:real^3->bool. x SUBSET y ==> revolution x SUBSET revolution y`,
  REWRITE_TAC[revolution; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

(* 6.1 Leaf 30.3.                                                           *)

let MOI_STD_303 = prove
 (moi_std_full_stmt [`MOISE_303_STATEMENT`] `MOISE_303_STATEMENT`,
  REPEAT STRIP_TAC THEN MOI_STD_DISCHARGE_TAC);;

(* 6.2 Leaf 32.4 (the setup and the surgery).                               *)

let MOI_STD_324_CORE = prove
 (mk_imp(mk_conj(moi_std_csq MOI_S32_CAP_SETUP, moi_std_csq MOI_S32_CAP_SURGERY),
         `MOISE_324_STATEMENT`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "setup") (LABEL_TAC "surg")) THEN
  REWRITE_TAC[MOISE_324_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "setup" (MP_TAC o SPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`;
                                       `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` (X_CHOOSE_THEN `dz:real^3->bool`
    (X_CHOOSE_THEN `fz:real^2->real^3` (X_CHOOSE_THEN `gz:real^3->real^2`
    (X_CHOOSE_THEN `ff:(real^3->bool)->bool` STRIP_ASSUME_TAC))))) THEN
  REMOVE_THEN "surg" (MP_TAC o SPECL
    [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
     `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
     `gz:real^3->real^2`; `ff:(real^3->bool)->bool`]) THEN
  ASM_REWRITE_TAC[]);;

let MOI_STD_324 = prove
 (moi_std_full MOI_STD_324_CORE `MOISE_324_STATEMENT`,
  MOI_STD_FULL_TAC MOI_STD_324_CORE);;

(* 6.3 Producer of 31.1.  For each j < 3 an inner solid torus with a shell  *)
(* (REV_SHELL), a PL solid torus between by 30.7, then the middle one moved *)
(* by RECROSS to cross the two outer boundaries (disjoint because D_0 and   *)
(* D_2 are).                                                                 *)

let MOI_STD_SOLID_TORUS_COMPACT = prove
 (`!x:real^N->bool. solid_torus x ==> compact x`,
  GEN_TAC THEN REWRITE_TAC[solid_torus] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_COMPACTNESS th]) THEN
  SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_SPHERE]);;

let MOI_STD_PL_SOLID_TORUS_COMPACT = prove
 (`!s:real^N->bool. pl_solid_torus s ==> compact s`,
  GEN_TAC THEN REWRITE_TAC[pl_solid_torus; pl_homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^(2,1)finite_sum->real^N`; `g:real^N->real^(2,1)finite_sum`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
      interval(--vector[&1;&1]:real^2,vector[&1;&1])) PCROSS
     interval[--vec 1:real^1,vec 1]) homeomorphic (s:real^N->bool)`
  MP_TAC THENL [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP HOMEOMORPHIC_COMPACTNESS th)]) THEN
  MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
  MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL]);;

let MOI_STD_IMAGE_REV_DISJOINT = prove
 (`!(h:real^3->real^3) n x y.
     (!a b. a IN n /\ b IN n /\ h a = h b ==> a = b) /\
     revolution x SUBSET n /\ revolution y SUBSET n /\ x INTER y = {}
     ==> IMAGE h (revolution x) INTER IMAGE h (revolution y) = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `y:real^3->bool`] MOI_STD_REV_INTER) THEN
  ASM_REWRITE_TAC[MOI_STD_REV_EMPTY] THEN ASM SET_TAC[]);;

let MOI_STD_311_CORE = prove
 (mk_imp(list_mk_conj [`MOISE_307_STATEMENT`; MOI_S31_REV_SHELL;
                       moi_std_csq MOI_S31_RECROSS],
         `MOISE_311_STATEMENT`),
  REWRITE_TAC[MOISE_307_STATEMENT; MOISE_311_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "307")
    (CONJUNCTS_THEN2 (LABEL_TAC "rev") (LABEL_TAC "cross"))) THEN
  MAP_EVERY X_GEN_TAC [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `n = UNIONS {revolution ((dd:num->real^3->bool) j) | j < 3}` THEN
  SUBGOAL_THEN `!j. j < 3 ==> revolution ((dd:num->real^3->bool) j) SUBSET n`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ASSUME `planar_cell_chain (p:num->real^3) dd`) THEN
  REWRITE_TAC[planar_cell_chain] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pc1")
    (CONJUNCTS_THEN2 (LABEL_TAC "pc2") ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!j. j < 3
        ==> ?s1 s. solid_torus s1 /\ pl_solid_torus s /\
                   IMAGE (h:real^3->real^3) (revolution (segment[p j,p (j + 1)]))
                   SUBSET interior s1 /\
                   s1 SUBSET interior s /\
                   s SUBSET interior (IMAGE h (revolution ((dd:num->real^3->bool) j)))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "pc1" (MP_TAC o C MP (ASSUME `j < 3`) o SPEC `j:num`) THEN
    STRIP_TAC THEN
    REMOVE_THEN "rev" (fun th -> MP_TAC(SPECL
      [`(dd:num->real^3->bool) j`; `h:real^3->real^3`] th) THEN LABEL_TAC "rev" th) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `n:real^3->bool` THEN
        ASM_SIMP_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (MP_TAC o SPEC `segment[(p:num->real^3) j,p (j + 1)]`)
                       (K ALL_TAC))) THEN
    ASM_REWRITE_TAC[COMPACT_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^3->bool` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "307" (fun th -> MP_TAC(SPECL
      [`s1:real^3->bool`; `IMAGE (h:real^3->real^3) (revolution ((dd:num->real^3->bool) j))`]
      th) THEN LABEL_TAC "307" th) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`s1:real^3->bool`; `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s1:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ss1:num->real^3->bool`
    (X_CHOOSE_THEN `ss:num->real^3->bool` (LABEL_TAC "ss"))) THEN
  USE_THEN "ss" (MP_TAC o SPEC `0`) THEN
  USE_THEN "ss" (MP_TAC o SPEC `1`) THEN
  USE_THEN "ss" (MP_TAC o SPEC `2`) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  REMOVE_THEN "cross" (MP_TAC o SPECL
   [`(ss:num->real^3->bool) 1`; `(ss1:num->real^3->bool) 1`;
    `interior (IMAGE (h:real^3->real^3) (revolution ((dd:num->real^3->bool) 1)))`;
    `{frontier((ss:num->real^3->bool) 0), frontier(ss 2)}`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_STD_SOLID_TORUS_COMPACT; OPEN_INTERIOR; FINITE_INSERT;
                 FINITE_EMPTY] THEN
    CONJ_TAC THENL [REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
                    ALL_TAC] THEN
    REWRITE_TAC[PAIRWISE_INSERT; PAIRWISE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    SUBGOAL_THEN
     `IMAGE (h:real^3->real^3) (revolution ((dd:num->real^3->bool) 0)) INTER
      IMAGE h (revolution (dd 2)) = {}`
    MP_TAC THENL
     [MATCH_MP_TAC MOI_STD_IMAGE_REV_DISJOINT THEN EXISTS_TAC `n:real^3->bool` THEN
      ASM_SIMP_TAC[ARITH] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `!k. k = 0 \/ k = 2
                      ==> frontier ((ss:num->real^3->bool) k) SUBSET
                          IMAGE (h:real^3->real^3) (revolution ((dd:num->real^3->bool) k))`
    MP_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `pl_solid_torus ((ss:num->real^3->bool) k) /\
                    ss k SUBSET interior (IMAGE (h:real^3->real^3)
                                (revolution ((dd:num->real^3->bool) k)))`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(ss:num->real^3->bool) k` THEN
      ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED;
                   MOI_STD_PL_SOLID_TORUS_COMPACT] THEN
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS];
      DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `2` th)) THEN
      REWRITE_TAC[ARITH_EQ] THEN
      UNDISCH_TAC `IMAGE (h:real^3->real^3) (revolution ((dd:num->real^3->bool) 0)) INTER
                   IMAGE h (revolution (dd 2)) = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "crs"))))) THEN
  EXISTS_TAC `\j:num. if j = 1 then s' else (ss:num->real^3->bool) j` THEN
  REWRITE_TAC[canonical_configuration] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j = 1` THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `(ss1:num->real^3->bool) 1` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `IMAGE (h:real^3->real^3) (revolution (segment [p 1,p 2])) SUBSET
                   interior ((ss1:num->real^3->bool) 1)` THEN
      UNDISCH_TAC `(ss1:num->real^3->bool) 1 SUBSET interior s'` THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN SET_TAC[];
      USE_THEN "ss" (MP_TAC o C MP (ASSUME `j < 3`) o SPEC `j:num`) THEN
      MP_TAC(ISPEC `(ss1:num->real^3->bool) j` INTERIOR_SUBSET) THEN SET_TAC[]];
    REWRITE_TAC[ARITH_RULE `j < 2 <=> j = 0 \/ j = 1`] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THENL
     [USE_THEN "crs" (MP_TAC o SPECL [`frontier((ss:num->real^3->bool) 0)`; `x:real^3`]);
      USE_THEN "crs" (MP_TAC o SPECL [`frontier((ss:num->real^3->bool) 2)`; `x:real^3`])] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT; IN_INTER]; SIMP_TAC[]])]);;

let MOI_STD_311 = prove
 (moi_std_full MOI_STD_311_CORE MOI_PROD_311,
  MOI_STD_FULL_TAC MOI_STD_311_CORE);;

(* 6.4 Producer of 31.4.  The pair lemma: the carrier of H_1(sa) in        *)
(* frontier sa away from gg (cutting the homology between zm and zo in sb), *)
(* 28.10 in sa, transfer between sa and sb, and the meridian lemma in sb.   *)
(* For j = 0 the pair is (s2 0, s2 1) with zm, zo the circles of p 1, p 2;  *)
(* for j = 1 it is (s2 2, s2 1) with the circles of p 2, p 1 (DG's          *)
(* asymmetric argument; the middle torus is always sb).                     *)

let MOI_STD_PL_SPHERE_COMPACT = prove
 (`!n s:real^N->bool. pl_sphere n s ==> compact s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier (k:real^N->bool) homeomorphic (s:real^N->bool)` MP_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP HOMEOMORPHIC_COMPACTNESS th)]) THEN
  MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]);;

let MOI_STD_DISK_NULL = prove
 (`!d j s:real^N->bool.
     pl_cell_with_boundary 2 d j /\ d SUBSET s
     ==> ?z. homotopic_with (\f. T) (subtopology euclidean j,subtopology euclidean s)
                            (\x. x) (\x. z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool`
    (X_CHOOSE_THEN `f:real^N->real^N` (X_CHOOSE_THEN `g:real^N->real^N`
      STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  SUBGOAL_THEN `contractible (d:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(k:real^N->bool) homeomorphic (d:real^N->bool)` MP_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP HOMEOMORPHIC_CONTRACTIBLE_EQ th)]) THEN
    ASM_MESON_TAC[CONVEX_IMP_CONTRACTIBLE; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^N->bool) SUBSET d` ASSUME_TAC THENL
   [SUBGOAL_THEN `relative_frontier (k:real^N->bool) SUBSET k /\
                  IMAGE (f:real^N->real^N) k = d`
    MP_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[relative_frontier] THEN
        ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; CLOSURE_CLOSED; SUBSET_DIFF];
        ASM_MESON_TAC[homeomorphism]];
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `j:real^N->bool`; `d:real^N->bool`]
    NULLHOMOTOPIC_INTO_CONTRACTIBLE) THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID; ASSUME `(j:real^N->bool) SUBSET d`;
              ASSUME `contractible (d:real^N->bool)`] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^N`) THEN EXISTS_TAC `c:real^N` THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_RIGHT THEN EXISTS_TAC `d:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_STD_314_PAIR = prove
 (mk_imp(list_mk_conj [`MOISE_2810_STATEMENT`; moi_std_csq MOI_S31_CARRIER;
                       moi_std_csq MOI_S31_NULL_POLYGON],
  `!sa sb zm zo gg:real^3->bool.
     pl_solid_torus sa /\ pl_solid_torus sb /\
     zm SUBSET interior sa INTER interior sb /\ zo SUBSET interior sb DIFF sa /\
     zm homeomorphic sphere(vec 0:real^2,&1) /\
     zo homeomorphic sphere(vec 0:real^2,&1) /\
     loops_carried zm sa /\ loops_carried zm sb /\ loops_carried zo sb /\
     pl_sphere 1 gg /\ gg SUBSET frontier sa INTER frontier sb /\
     ((carries_h1 gg sa \/ carries_h1 gg sb)
      ==> loops_carried gg sa /\ loops_carried gg sb) /\
     ((?z. homotopic_with (\f. T) (subtopology euclidean gg,subtopology euclidean sa)
                          (\x. x) (\x. z)) <=>
      (?z. homotopic_with (\f. T) (subtopology euclidean gg,subtopology euclidean sb)
                          (\x. x) (\x. z)))
     ==> (loops_carried gg sa /\ loops_carried gg sb) \/
         ((?d. d SUBSET frontier sa /\ pl_cell_with_boundary 2 d gg) /\
          (?d. d SUBSET frontier sb /\ pl_cell_with_boundary 2 d gg))`),
  REWRITE_TAC[MOISE_2810_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "2810")
    (CONJUNCTS_THEN2 (LABEL_TAC "carrier") (LABEL_TAC "null"))) THEN
  MAP_EVERY X_GEN_TAC [`sa:real^3->bool`; `sb:real^3->bool`; `zm:real^3->bool`;
                       `zo:real^3->bool`; `gg:real^3->bool`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "carrier" (MP_TAC o SPECL
    [`sa:real^3->bool`; `sb:real^3->bool`; `zm:real^3->bool`; `zo:real^3->bool`;
     `gg:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_STD_PL_SPHERE_COMPACT]; ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact (sa:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_STD_PL_SOLID_TORUS_COMPACT]; ALL_TAC] THEN
  ASM_CASES_TAC `?d:real^3->bool. d SUBSET frontier sa /\ pl_cell_with_boundary 2 d gg`
  THENL
   [ALL_TAC;
    DISJ1_TAC THEN
    REMOVE_THEN "2810" (MP_TAC o SPECL [`sa:real^3->bool`; `k:real^3->bool`;
                                        `gg:real^3->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ASM_MESON_TAC[]]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC) THEN
  DISJ2_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "null" MATCH_MP_TAC THEN EXISTS_TAC `d:real^3->bool` THEN
  EXISTS_TAC `zm:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MP_TAC(ISPEC `sa:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET frontier sa` THEN
    UNDISCH_TAC `(zm:real^3->bool) SUBSET interior sa INTER interior sb` THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ASM_MESON_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY;
                  REAL_ARITH `~(&1 < &0)`];
    ASM_MESON_TAC[HOMEOMORPHIC_PATH_CONNECTEDNESS; PATH_CONNECTED_SPHERE;
                  DIMINDEX_2; LE_REFL];
    ASM SET_TAC[];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
    MATCH_MP_TAC MOI_STD_DISK_NULL THEN EXISTS_TAC `d:real^3->bool` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier(sa:real^3->bool)` THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED]]);;

let MOI_STD_314_CORE = prove
 (mk_imp(list_mk_conj [`MOISE_2810_STATEMENT`; moi_std_csq MOI_S31_SPINES;
                       moi_std_csq MOI_S31_CARRIER; moi_std_csq MOI_S31_NULL_POLYGON;
                       moi_std_csq MOI_S31_TRANSFER],
         `MOISE_314_STATEMENT`),
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "spines")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "transfer"))))) THEN
  MP_TAC MOI_STD_314_PAIR THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pair") THEN
  REWRITE_TAC[MOISE_314_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`p:num->real^3`; `dd:num->real^3->bool`; `h:real^3->real^3`;
                       `s2:num->real^3->bool`; `j:num`; `gg:real^3->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ASSUME `canonical_configuration (p:num->real^3) dd (h:real^3->real^3) s2`) THEN
  REWRITE_TAC[canonical_configuration] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tori") (K ALL_TAC))))) THEN
  MP_TAC(ASSUME `planar_cell_chain (p:num->real^3) dd`) THEN
  REWRITE_TAC[planar_cell_chain] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pc1") (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
  ABBREV_TAC `n = UNIONS {revolution ((dd:num->real^3->bool) j) | j < 3}` THEN
  SUBGOAL_THEN `!j. j < 3 ==> revolution ((dd:num->real^3->bool) j) SUBSET n`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. k < 3 ==> compact ((s2:num->real^3->bool) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_STD_PL_SOLID_TORUS_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a < 3 /\ b < 4 /\ ~((p:num->real^3) b IN dd a) /\
          (?c. c < 3 /\ p b IN dd c)
          ==> DISJOINT (IMAGE (h:real^3->real^3) (revolution {p b})) (s2 a)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) b}) INTER
                  IMAGE h (revolution ((dd:num->real^3->bool) a)) = {}`
    MP_TAC THENL
     [MATCH_MP_TAC MOI_STD_IMAGE_REV_DISJOINT THEN EXISTS_TAC `n:real^3->bool` THEN
      ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `revolution ((dd:num->real^3->bool) c)` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_STD_REV_MONO THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (revolution ((dd:num->real^3->bool) a))`
             INTERIOR_SUBSET) THEN
      USE_THEN "tori" (MP_TAC o C MP (ASSUME `a < 3`) o SPEC `a:num`) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < 4 ==> ?c. c < 3 /\ (p:num->real^3) i IN dd c` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < 3 \/ i = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [EXISTS_TAC `i:num` THEN
      USE_THEN "pc1" (MP_TAC o C MP (ASSUME `i < 3`) o SPEC `i:num`) THEN
      MP_TAC(ISPEC `(dd:num->real^3->bool) i` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPECL [`(p:num->real^3) i`; `(p:num->real^3) (i + 1)`] ENDS_IN_SEGMENT) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH] THEN
      USE_THEN "pc1" (MP_TAC o C MP (ARITH_RULE `2 < 3`) o SPEC `2`) THEN
      MP_TAC(ISPEC `(dd:num->real^3->bool) 2` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPECL [`(p:num->real^3) 2`; `(p:num->real^3) 3`] ENDS_IN_SEGMENT) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:num->real^3) 2 IN dd 0) /\ ~(p 1 IN dd 2)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:num->real^3) 1 IN dd 0 /\ p 2 IN dd 2` MP_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "pc1" (MP_TAC o C MP (ARITH_RULE `0 < 3`) o SPEC `0`) THEN
        MP_TAC(ISPEC `(dd:num->real^3->bool) 0` RELATIVE_INTERIOR_SUBSET) THEN
        MP_TAC(ISPECL [`(p:num->real^3) 0`; `(p:num->real^3) 1`] ENDS_IN_SEGMENT);
        USE_THEN "pc1" (MP_TAC o C MP (ARITH_RULE `2 < 3`) o SPEC `2`) THEN
        MP_TAC(ISPEC `(dd:num->real^3->bool) 2` RELATIVE_INTERIOR_SUBSET) THEN
        MP_TAC(ISPECL [`(p:num->real^3) 2`; `(p:num->real^3) 3`] ENDS_IN_SEGMENT)] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `gg SUBSET (s2:num->real^3->bool) j INTER s2 (j + 1)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(s2:num->real^3->bool) j` FRONTIER_SUBSET_CLOSED) THEN
    MP_TAC(ISPEC `(s2:num->real^3->bool) (j + 1)` FRONTIER_SUBSET_CLOSED) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; ARITH_RULE `j < 2 ==> j < 3 /\ j + 1 < 3`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "transfer" (MP_TAC o SPECL [`p:num->real^3`; `dd:num->real^3->bool`;
     `h:real^3->real^3`; `s2:num->real^3->bool`; `j:num`; `gg:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY (fun (a,b) ->
     USE_THEN "spines" (MP_TAC o SPECL [`p:num->real^3`; `dd:num->real^3->bool`;
        `h:real^3->real^3`; `s2:num->real^3->bool`; a; b]) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; STRIP_TAC])
    [`0`,`1`; `1`,`1`; `1`,`2`; `2`,`2`] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 2}))
             ((s2:num->real^3->bool) 0) /\
    DISJOINT (IMAGE h (revolution {p 1})) (s2 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
      MATCH_MP_TAC th THEN ASSUME_TAC th) THEN ASM_REWRITE_TAC[ARITH] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_solid_torus ((s2:num->real^3->bool) 0) /\ pl_solid_torus (s2 1) /\
                pl_solid_torus (s2 2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    USE_THEN "tori" (fun th -> MP_TAC(MATCH_MP th (ARITH_RULE `0 < 3`)) THEN
                              MP_TAC(MATCH_MP th (ARITH_RULE `1 < 3`)) THEN
                              MP_TAC(MATCH_MP th (ARITH_RULE `2 < 3`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "spines" (K ALL_TAC) THEN REMOVE_THEN "tori" (K ALL_TAC) THEN
  REMOVE_THEN "pc1" (K ALL_TAC) THEN
  SUBGOAL_THEN `j = 0 \/ j = 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THENL
   [REMOVE_THEN "pair" (MP_TAC o SPECL
     [`(s2:num->real^3->bool) 0`; `(s2:num->real^3->bool) 1`;
      `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 1})`;
      `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 2})`; `gg:real^3->bool`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 1}) SUBSET
                 interior ((s2:num->real^3->bool) 0)` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 1}) SUBSET
                 interior ((s2:num->real^3->bool) 1)` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 2}) SUBSET
                 interior ((s2:num->real^3->bool) 1)` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 2}))
                          ((s2:num->real^3->bool) 0)` THEN
    SET_TAC[];
    REMOVE_THEN "pair" (MP_TAC o SPECL
     [`(s2:num->real^3->bool) 2`; `(s2:num->real^3->bool) 1`;
      `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 2})`;
      `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 1})`; `gg:real^3->bool`]) THEN
    ANTS_TAC THENL
     [ALL_TAC;
      CONV_TAC TAUT] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 2}) SUBSET
                   interior ((s2:num->real^3->bool) 2)` THEN
      UNDISCH_TAC `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 2}) SUBSET
                   interior ((s2:num->real^3->bool) 1)` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 1}) SUBSET
                   interior ((s2:num->real^3->bool) 1)` THEN
      UNDISCH_TAC `DISJOINT (IMAGE (h:real^3->real^3) (revolution {(p:num->real^3) 1}))
                            ((s2:num->real^3->bool) 2)` THEN SET_TAC[];
      ASM SET_TAC[];
      UNDISCH_TAC `carries_h1 gg ((s2:num->real^3->bool) 1) \/ carries_h1 gg (s2 2)
                   ==> loops_carried gg (s2 1) /\ loops_carried gg (s2 2)` THEN
      CONV_TAC TAUT;
      UNDISCH_TAC `(?z. homotopic_with (\f. T)
                          (subtopology euclidean gg,
                           subtopology euclidean ((s2:num->real^3->bool) 1))
                          (\x. x) (\x. z:real^3)) <=>
                   (?z. homotopic_with (\f. T)
                          (subtopology euclidean gg,subtopology euclidean (s2 2))
                          (\x. x) (\x. z:real^3))` THEN
      CONV_TAC TAUT]]);;

let MOI_STD_314 = prove
 (moi_std_full MOI_STD_314_CORE MOI_PROD_314,
  MOI_STD_FULL_TAC MOI_STD_314_CORE);;

(* 6.5 Producer of 30.4 (p.216).  Among the closed connected surfaces in    *)
(* Int X separating the ends take one of largest chi (EULER_NAT: chi = 2 -  *)
(* n, n minimal); if it were not a PL sphere it would carry a loop that is  *)
(* not null-homotopic (Z2_SC_CLOSED) but null-homotopic in the simply       *)
(* connected Int X, so 26.4 and COMPRESS would give one of larger chi.      *)

let MOI_STD_SEP_INSIDE = prove
 (`!x b0 b1 c:real^3->bool.
     compact x /\ connected x /\ b0 UNION b1 SUBSET x /\ ~(b0 = {}) /\ ~(b1 = {}) /\
     interior x = x DIFF (b0 UNION b1) /\
     connected c /\ DISJOINT c (b0 UNION b1) /\ euclidean_separates c b0 b1
     ==> c SUBSET interior x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier x = (b0 UNION b1:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `c SUBSET interior (x:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT c (x:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^3->bool`; `x:real^3->bool`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `x:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `euclidean_separates c (b0:real^3->bool) b1` THEN
  REWRITE_TAC[euclidean_separates; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN STRIP_TAC THEN
  UNDISCH_TAC `connected (x:real^3->bool)` THEN
  REWRITE_TAC[CONNECTED_OPEN_IN; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`x INTER u:real^3->bool`; `x INTER v:real^3->bool`]) THEN
  REWRITE_TAC[] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER] THEN ASM SET_TAC[]);;

let MOI_STD_304_CORE = prove
 (mk_imp(list_mk_conj
   [`MOISE_264_OPEN_STATEMENT`; MOI_S30_SPHERICAL_SHELL_FACTS;
    moi_std_csq MOI_S30_INIT_SURFACE; moi_std_csq MOI_S30_COMPRESS;
    moi_std_csq (moi_n3 MOI_S30_Z2_SC_CLOSED); moi_n3 MOI_FND_SURFACE_SPHERE;
    moi_std_csq MOI_S30_EULER_NAT],
   `MOISE_304_STATEMENT`),
  REWRITE_TAC[MOISE_264_OPEN_STATEMENT; MOISE_304_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "264") (CONJUNCTS_THEN2 (LABEL_TAC "shell")
   (CONJUNCTS_THEN2 (LABEL_TAC "init") (CONJUNCTS_THEN2 (LABEL_TAC "comp")
   (CONJUNCTS_THEN2 (LABEL_TAC "sc") (CONJUNCTS_THEN2 (LABEL_TAC "sph")
    (LABEL_TAC "nat"))))))) THEN
  MAP_EVERY X_GEN_TAC [`x:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`] THEN
  DISCH_TAC THEN
  USE_THEN "shell" (MP_TAC o SPECL [`x:real^3->bool`; `b0:real^3->bool`;
                                    `b1:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `?v:real^3->bool. open v /\ b0 SUBSET v /\ DISJOINT v b1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`b0:real^3->bool`; `b1:real^3->bool`] SEPARATION_NORMAL) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; GSYM DISJOINT] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` (X_CHOOSE_THEN `w:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `v:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b1:real^3->bool) SUBSET w` THEN
    UNDISCH_TAC `DISJOINT (v:real^3->bool) w` THEN SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "init" (MP_TAC o SPECL [`b0:real^3->bool`; `b1:real^3->bool`;
                                      `v:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?n m:(real^3->bool)->bool.
       FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
       ~(UNIONS m = {}) /\ UNIONS m SUBSET interior x /\
       euclidean_separates (UNIONS m) b0 b1 /\ complex_euler m = &2 - &n`
  MP_TAC THENL
   [USE_THEN "nat" (MP_TAC o SPEC `m0:(real^3->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    EXISTS_TAC `m0:(real^3->bool)->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MOI_STD_SEP_INSIDE THEN
    MAP_EVERY EXISTS_TAC [`b0:real^3->bool`; `b1:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `UNIONS m0 SUBSET (v:real^3->bool) DIFF b0` THEN
    UNDISCH_TAC `DISJOINT (v:real^3->bool) b1` THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:(real^3->bool)->bool` STRIP_ASSUME_TAC) (LABEL_TAC "min"))) THEN
  EXISTS_TAC `UNIONS m:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(complex_euler (m:(real^3->bool)->bool) = &2)` ASSUME_TAC THENL
   [USE_THEN "sph" (MP_TAC o SPEC `m:(real^3->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `~pl_sphere 2 (UNIONS (m:(real^3->bool)->bool))`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?p:real^1->real^3. path p /\ pathfinish p = pathstart p /\
                       path_image p SUBSET UNIONS m /\
                       ~homotopic_loops (UNIONS m) p (linepath(pathstart p,pathstart p))`
  STRIP_ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(complex_euler (m:(real^3->bool)->bool) = &2)` THEN
    REWRITE_TAC[] THEN USE_THEN "sc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops (interior x) (p:real^1->real^3)
                  (linepath(pathstart p,pathstart p))` ASSUME_TAC THENL
   [UNDISCH_TAC `simply_connected (interior (x:real^3->bool))` THEN
    REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[ASSUME `path (p:real^1->real^3)`;
                ASSUME `pathfinish (p:real^1->real^3) = pathstart p`] THEN
    MP_TAC(ISPEC `p:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    UNDISCH_TAC `path_image (p:real^1->real^3) SUBSET UNIONS m` THEN
    UNDISCH_TAC `UNIONS (m:(real^3->bool)->bool) SUBSET interior x` THEN SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "264" (MP_TAC o SPECL [`interior x:real^3->bool`;
                                     `m:(real^3->bool)->bool`; `p:real^1->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `d:real^3->bool`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  REMOVE_THEN "comp" (MP_TAC o SPECL
    [`m:(real^3->bool)->bool`; `b0:real^3->bool`; `b1:real^3->bool`;
     `interior x:real^3->bool`; `s:real^3->bool`; `d:real^3->bool`;
     `f:real^3->real^3`; `g:real^3->real^3`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_SIMP_TAC[OPEN_INTERIOR; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "nat" (MP_TAC o SPEC `m':(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n':num`) THEN
  REMOVE_THEN "min" (MP_TAC o SPEC `n':num`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [UNDISCH_TAC `complex_euler (m:(real^3->bool)->bool) < complex_euler (m':(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&2 - a < &2 - b <=> b < a`; REAL_OF_NUM_LT];
    EXISTS_TAC `m':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_STD_304 = prove
 (moi_std_full MOI_STD_304_CORE MOI_PROD_304,
  MOI_STD_FULL_TAC MOI_STD_304_CORE);;

(* 6.6 Producer of 30.6 (pp.216-217).  As for 30.4, a separating closed    *)
(* connected surface in Int Y of largest chi is incompressible (26.4 and    *)
(* COMPRESS); then chi >= 0 (Z2_TORUS_BOUND with the shell coordinate),    *)
(* chi <> 2 (no separating sphere, SHELL_NO_SPHERE), chi even (it bounds,   *)
(* BOUNDS and EULER_EVEN), so chi = 0; orientable (26.8), hence a PL torus  *)
(* (MOI_FND_SURFACE_TORUS).  Case (2) of the book is replaced by the Z/2    *)
(* count, case (1) by the winding argument of SHELL_NO_SPHERE.              *)

let MOI_STD_EULER_INTEGER = prove
 (`!c:(real^N->bool)->bool. integer (complex_euler c)`,
  GEN_TAC THEN REWRITE_TAC[complex_euler] THEN MATCH_MP_TAC INTEGER_SUM THEN
  SIMP_TAC[INTEGER_CLOSED]);;

let MOI_STD_NOT_HALF = prove
 (`!x. integer x ==> ~(&2 * x = &1)`,
  GEN_TAC THEN REWRITE_TAC[integer] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 * &n = &1` MP_TAC THENL
   [UNDISCH_TAC `abs x = &n` THEN UNDISCH_TAC `&2 * x = &1` THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN REWRITE_TAC[EVEN_MULT; ARITH]]);;

let MOI_STD_EULER_ZERO_LEMMA = prove
 (`!e z n. &0 <= e /\ e = &2 - &n /\ ~(e = &2) /\ e = &2 * z /\ ~(&2 * z = &1)
           ==> e = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n = 0 \/ n = 1 \/ n = 2` MP_TAC THENL
   [UNDISCH_TAC `&0 <= e` THEN ASM_REWRITE_TAC[REAL_ARITH `&0 <= &2 - x <=> x <= &2`] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_STD_306_CORE = prove
 (mk_imp(list_mk_conj
   [`MOISE_264_OPEN_STATEMENT`; `MOISE_268_STATEMENT`; MOI_S30_TOROIDAL_SHELL_FACTS;
    moi_std_csq MOI_S30_INIT_SURFACE; moi_std_csq MOI_S30_COMPRESS;
    moi_std_csq (moi_n3 MOI_S30_Z2_TORUS_BOUND); MOI_S30_SHELL_NO_SPHERE;
    moi_std_csq MOI_S30_BOUNDS; moi_n3 MOI_S30_EULER_EVEN;
    moi_n3 MOI_FND_SURFACE_SPHERE; moi_n3 MOI_FND_SURFACE_TORUS;
    moi_std_csq MOI_S30_EULER_NAT],
   `MOISE_306_STATEMENT`),
  REWRITE_TAC[MOISE_264_OPEN_STATEMENT; MOISE_268_STATEMENT; MOISE_306_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "264") (CONJUNCTS_THEN2 (LABEL_TAC "268")
   (CONJUNCTS_THEN2 (LABEL_TAC "shell") (CONJUNCTS_THEN2 (LABEL_TAC "init")
   (CONJUNCTS_THEN2 (LABEL_TAC "comp") (CONJUNCTS_THEN2 (LABEL_TAC "bound")
   (CONJUNCTS_THEN2 (LABEL_TAC "nosph") (CONJUNCTS_THEN2 (LABEL_TAC "bounds")
   (CONJUNCTS_THEN2 (LABEL_TAC "even") (CONJUNCTS_THEN2 (LABEL_TAC "sph")
   (CONJUNCTS_THEN2 (LABEL_TAC "torus") (LABEL_TAC "nat")))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`y:real^3->bool`; `t0:real^3->bool`; `t1:real^3->bool`] THEN
  DISCH_TAC THEN
  USE_THEN "shell" (MP_TAC o SPECL [`y:real^3->bool`; `t0:real^3->bool`;
                                    `t1:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "inty")
     (X_CHOOSE_THEN `gc:real^3->real^(2,2)finite_sum`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (LABEL_TAC "detect"))))))))))))))) THEN
  SUBGOAL_THEN `?v:real^3->bool. open v /\ t0 SUBSET v /\ DISJOINT v t1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t0:real^3->bool`; `t1:real^3->bool`] SEPARATION_NORMAL) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; GSYM DISJOINT] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` (X_CHOOSE_THEN `w:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `v:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(t1:real^3->bool) SUBSET w` THEN
    UNDISCH_TAC `DISJOINT (v:real^3->bool) w` THEN SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "init" (MP_TAC o SPECL [`t0:real^3->bool`; `t1:real^3->bool`;
                                      `v:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?n m:(real^3->bool)->bool.
       FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
       ~(UNIONS m = {}) /\ UNIONS m SUBSET interior y /\
       euclidean_separates (UNIONS m) t0 t1 /\ complex_euler m = &2 - &n`
  MP_TAC THENL
   [USE_THEN "nat" (MP_TAC o SPEC `m0:(real^3->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    EXISTS_TAC `m0:(real^3->bool)->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MOI_STD_SEP_INSIDE THEN
    MAP_EVERY EXISTS_TAC [`t0:real^3->bool`; `t1:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `UNIONS m0 SUBSET (v:real^3->bool) DIFF t0` THEN
    UNDISCH_TAC `DISJOINT (v:real^3->bool) t1` THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:(real^3->bool)->bool` STRIP_ASSUME_TAC) (LABEL_TAC "min"))) THEN
  REMOVE_THEN "inty" (fun th ->
    ASSUME_TAC(MATCH_MP (SET_RULE `!a b c:real^3->bool. a = b DIFF c ==> DISJOINT a c`) th) THEN
    ASSUME_TAC(MATCH_MP (SET_RULE `!a b c:real^3->bool. a = b DIFF c ==> a SUBSET b`) th)) THEN
  (* incompressibility *)
  SUBGOAL_THEN
   `!p:real^1->real^3.
      path p /\ pathfinish p = pathstart p /\ path_image p SUBSET UNIONS m /\
      homotopic_loops (interior y) p (linepath(pathstart p,pathstart p))
      ==> homotopic_loops (UNIONS m) p (linepath(pathstart p,pathstart p))`
  (LABEL_TAC "incomp") THENL
   [X_GEN_TAC `p:real^1->real^3` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    REMOVE_THEN "264" (MP_TAC o SPECL [`interior y:real^3->bool`;
                                       `m:(real^3->bool)->bool`; `p:real^1->real^3`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[OPEN_INTERIOR];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `d:real^3->bool`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
        STRIP_ASSUME_TAC)))) THEN
    REMOVE_THEN "comp" (MP_TAC o SPECL
      [`m:(real^3->bool)->bool`; `t0:real^3->bool`; `t1:real^3->bool`;
       `interior y:real^3->bool`; `s:real^3->bool`; `d:real^3->bool`;
       `f:real^3->real^3`; `g:real^3->real^3`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      ASM_SIMP_TAC[OPEN_INTERIOR; COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `m':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "nat" (MP_TAC o SPEC `m':(real^3->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `n':num`) THEN
    REMOVE_THEN "min" (MP_TAC o SPEC `n':num`) THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [UNDISCH_TAC `complex_euler (m:(real^3->bool)->bool) <
                   complex_euler (m':(real^3->bool)->bool)` THEN
      ASM_REWRITE_TAC[REAL_ARITH `&2 - a < &2 - b <=> b < a`; REAL_OF_NUM_LT];
      EXISTS_TAC `m':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* chi >= 0 *)
  SUBGOAL_THEN `&0 <= complex_euler (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [USE_THEN "bound" (MP_TAC o SPECL [`m:(real^3->bool)->bool`;
                                      `gc:real^3->real^(2,2)finite_sum`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `y:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `y:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `UNIONS (m:(real^3->bool)->bool) SUBSET interior y` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (gc:real^3->real^(2,2)finite_sum) y` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MP_TAC(ISPEC `y:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `UNIONS (m:(real^3->bool)->bool) SUBSET interior y` THEN SET_TAC[];
      X_GEN_TAC `p:real^1->real^3` THEN STRIP_TAC THEN
      USE_THEN "incomp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "detect" (MP_TAC o SPEC `p:real^1->real^3`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS (m:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* chi <> 2 *)
  SUBGOAL_THEN `~(complex_euler (m:(real^3->bool)->bool) = &2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "sph" (MP_TAC o SPEC `m:(real^3->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `complex_euler (m:(real^3->bool)->bool) = &2`; REAL_LE_REFL] THEN
    DISCH_TAC THEN
    USE_THEN "nosph" (MP_TAC o SPECL [`y:real^3->bool`; `t0:real^3->bool`;
                                      `t1:real^3->bool`; `UNIONS m:real^3->bool`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `euclidean_separates (UNIONS m) (t0:real^3->bool) t1`];
    ALL_TAC] THEN
  (* chi even *)
  SUBGOAL_THEN `?z. integer z /\ complex_euler (m:(real^3->bool)->bool) = &2 * z`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "bounds" (MP_TAC o SPEC `m:(real^3->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `complex_euler (x:(real^3->bool)->bool)` THEN
    REWRITE_TAC[MOI_STD_EULER_INTEGER] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    USE_THEN "even" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (m:(real^3->bool)->bool) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_STD_EULER_ZERO_LEMMA THEN
    MAP_EVERY EXISTS_TAC [`z:real`; `n:num`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MOI_STD_NOT_HALF THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  USE_THEN "torus" (MP_TAC o SPEC `m:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    USE_THEN "268" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_TAC `g:real^3->real^(2,2)finite_sum`)) THEN
  MAP_EVERY EXISTS_TAC [`UNIONS m:real^3->bool`; `f:real^(2,2)finite_sum->real^3`;
                        `g:real^3->real^(2,2)finite_sum`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_STD_306 = prove
 (moi_std_full MOI_STD_306_CORE MOI_PROD_306,
  MOI_STD_FULL_TAC MOI_STD_306_CORE);;

(* 6.7 Producer of 30.7 (pp.217-218).  30.6 gives a PL torus |m| in the     *)
(* shell separating its ends; it bounds a 3-manifold x (BOUNDS) with s1 in  *)
(* its interior and x in Int s2 (TORUS_REGION); TORUS_LOOP and 26.4 give a  *)
(* PL disk d with essential rim meeting |m| in its rim; the open disk is    *)
(* connected and misses Fr |x| = |m|, so d lies in x or meets x only in its *)
(* rim (DISK_SIDES); the first case gives a PL solid torus (307_INSIDE),    *)
(* the second is impossible (307_OUTSIDE).                                  *)

let MOI_STD_PL_TORUS_COMPACT = prove
 (`!t (f:real^(2,2)finite_sum->real^N) g.
     pl_homeomorphism (pl_torus_model,t) (f,g) ==> compact t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_torus_model homeomorphic (t:real^N->bool)` MP_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP HOMEOMORPHIC_COMPACTNESS th)]) THEN
  REWRITE_TAC[pl_torus_model] THEN MATCH_MP_TAC COMPACT_PCROSS THEN
  SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED; BOUNDED_INTERVAL]);;

let MOI_STD_DISK_SIDES = prove
 (`!k d (f:real^N->real^N) g w.
     &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\ closed w /\
     d INTER frontier w = IMAGE f (relative_frontier k)
     ==> d SUBSET w \/ d INTER w = IMAGE f (relative_frontier k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (k:real^N->bool) /\ convex k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior k UNION relative_frontier k = k:real^N->bool /\
                DISJOINT (relative_interior k) (relative_frontier k:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN
    MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `d = IMAGE (f:real^N->real^N) (relative_interior k) UNION
        IMAGE f (relative_frontier k) /\
    DISJOINT (IMAGE (f:real^N->real^N) (relative_interior k))
             (IMAGE f (relative_frontier k)) /\
    connected (IMAGE (f:real^N->real^N) (relative_interior k))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM IMAGE_UNION] THEN
      REWRITE_TAC[ASSUME `relative_interior k UNION relative_frontier k = k:real^N->bool`];
      UNDISCH_TAC `!x. x IN k ==> (g:real^N->real^N) (f x) = x` THEN
      UNDISCH_TAC `relative_interior k UNION relative_frontier k = k:real^N->bool` THEN
      UNDISCH_TAC `DISJOINT (relative_interior k) (relative_frontier k:real^N->bool)` THEN
      SET_TAC[];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
        ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET];
        MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^N->real^N) (relative_interior k)`; `w:real^N->bool`]
    CONNECTED_INTER_FRONTIER) THEN
  REWRITE_TAC[ASSUME `connected (IMAGE (f:real^N->real^N) (relative_interior k))`] THEN
  MP_TAC(MATCH_MP FRONTIER_SUBSET_CLOSED (ASSUME `closed (w:real^N->bool)`)) THEN
  UNDISCH_TAC `d INTER frontier w = IMAGE (f:real^N->real^N) (relative_frontier k)` THEN
  UNDISCH_TAC `DISJOINT (IMAGE (f:real^N->real^N) (relative_interior k))
                        (IMAGE f (relative_frontier k))` THEN
  UNDISCH_TAC `d = IMAGE (f:real^N->real^N) (relative_interior k) UNION
                   IMAGE f (relative_frontier k)` THEN
  SPEC_TAC(`IMAGE (f:real^N->real^N) (relative_interior k)`,`a:real^N->bool`) THEN
  SPEC_TAC(`IMAGE (f:real^N->real^N) (relative_frontier k)`,`b:real^N->bool`) THEN
  SPEC_TAC(`frontier w:real^N->bool`,`fw:real^N->bool`) THEN
  SET_TAC[]);;

let MOI_STD_307_CORE = prove
 (mk_imp(list_mk_conj
   [`MOISE_306_STATEMENT`; `MOISE_264_OPEN_STATEMENT`;
    moi_std_csq (moi_n3 MOI_S30_PL_TORUS_COMPLEX); moi_std_csq MOI_S30_BOUNDS;
    moi_std_csq MOI_S30_TORUS_REGION; MOI_S30_TORUS_LOOP;
    moi_std_csq MOI_S30_307_OUTSIDE; moi_std_csq MOI_S30_307_INSIDE],
   `MOISE_307_STATEMENT`),
  REWRITE_TAC[MOISE_306_STATEMENT; MOISE_264_OPEN_STATEMENT; MOISE_307_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "306") (CONJUNCTS_THEN2 (LABEL_TAC "264")
   (CONJUNCTS_THEN2 (LABEL_TAC "tcx") (CONJUNCTS_THEN2 (LABEL_TAC "bounds")
   (CONJUNCTS_THEN2 (LABEL_TAC "region") (CONJUNCTS_THEN2 (LABEL_TAC "loop")
   (CONJUNCTS_THEN2 (LABEL_TAC "out") (LABEL_TAC "in")))))))) THEN
  MAP_EVERY X_GEN_TAC [`s1:real^3->bool`; `s2:real^3->bool`] THEN STRIP_TAC THEN
  REMOVE_THEN "306" (MP_TAC o SPECL [`closure((s2:real^3->bool) DIFF s1)`;
                                     `frontier(s1:real^3->bool)`;
                                     `frontier(s2:real^3->bool)`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool`
    (X_CHOOSE_THEN `ft:real^(2,2)finite_sum->real^3`
      (X_CHOOSE_THEN `gt:real^3->real^(2,2)finite_sum` STRIP_ASSUME_TAC))) THEN
  REMOVE_THEN "tcx" (MP_TAC o SPECL [`t:real^3->bool`; `ft:real^(2,2)finite_sum->real^3`;
                                     `gt:real^3->real^(2,2)finite_sum`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `UNIONS (m:(real^3->bool)->bool) = t` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `closed (UNIONS (m:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_STD_PL_TORUS_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`ft:real^(2,2)finite_sum->real^3`;
                          `gt:real^3->real^(2,2)finite_sum`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  USE_THEN "bounds" (MP_TAC o SPEC `m:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "region" (MP_TAC o SPECL [`s1:real^3->bool`; `s2:real^3->bool`;
                                        `m:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (x:(real^3->bool)->bool) SUBSET interior s2` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `UNIONS (x:(real^3->bool)->bool) = UNIONS m UNION inside (UNIONS m)`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (m:(real^3->bool)->bool) SUBSET interior s2` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS m UNION inside (UNIONS m) SUBSET interior (s2:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 SUBSET interior (UNIONS (x:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `inside (UNIONS (m:(real^3->bool)->bool))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[ASSUME `UNIONS (x:(real^3->bool)->bool) = UNIONS m UNION inside (UNIONS m)`] THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_INSIDE THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  USE_THEN "loop" (MP_TAC o SPECL [`UNIONS (m:(real^3->bool)->bool)`; `s2:real^3->bool`;
                                   `ft:real^(2,2)finite_sum->real^3`;
                                   `gt:real^3->real^(2,2)finite_sum`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^3` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "264" (MP_TAC o SPECL [`interior s2:real^3->bool`;
                                     `m:(real^3->bool)->bool`; `p:real^1->real^3`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `d:real^3->bool`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `d:real^3->bool`; `f:real^3->real^3`;
                 `g:real^3->real^3`; `UNIONS (x:(real^3->bool)->bool)`] MOI_STD_DISK_SIDES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[GSYM FRONTIER_SUBSET_EQ;
                  ASSUME `frontier (UNIONS (x:(real^3->bool)->bool)) = UNIONS m`;
                  ASSUME `UNIONS (x:(real^3->bool)->bool) = UNIONS m UNION inside (UNIONS m)`] THEN
      SET_TAC[];
      REWRITE_TAC[ASSUME `frontier (UNIONS (x:(real^3->bool)->bool)) = UNIONS m`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [USE_THEN "in" (MP_TAC o SPECL
      [`s1:real^3->bool`; `s2:real^3->bool`; `m:(real^3->bool)->bool`;
       `x:(real^3->bool)->bool`; `k:real^3->bool`; `d:real^3->bool`;
       `f:real^3->real^3`; `g:real^3->real^3`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_TAC THEN EXISTS_TAC `UNIONS (x:(real^3->bool)->bool)` THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "out" (MP_TAC o SPECL
      [`s1:real^3->bool`; `s2:real^3->bool`; `m:(real^3->bool)->bool`;
       `x:(real^3->bool)->bool`; `k:real^3->bool`; `d:real^3->bool`;
       `f:real^3->real^3`; `g:real^3->real^3`]) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_STD_307 = prove
 (moi_std_full MOI_STD_307_CORE MOI_PROD_307,
  MOI_STD_FULL_TAC MOI_STD_307_CORE);;

(* 6.8 Producer of 32.2 for two cells (MOISE_322_CELLS, pp.223-228).  The   *)
(* chart standardizes the two cells as the halves of the model cylinder;    *)
(* MODEL_V chooses v in the preimage of Int w, avoiding connected sets that *)
(* join qlo, qhi to the preimages of q1, q2; then the tower, Step 1          *)
(* (INITIAL, ITERATE, CLASSIFY), Steps 2-4, the pseudo-cell and its two     *)
(* sides.  The connected sets keep h q1, h q2 on the sides of qlo, qhi.     *)

let MOI_STD_S32_MODEL_FACTS = prove
 (`moi_s32_lo SUBSET moi_s32_cyl /\ moi_s32_hi SUBSET moi_s32_cyl /\
   moi_s32_disk SUBSET moi_s32_cyl /\ moi_s32_rim SUBSET moi_s32_disk /\
   vec 0 IN moi_s32_disk /\ ~(vec 0 IN moi_s32_rim)`,
  REWRITE_TAC[moi_s32_lo; moi_s32_hi; moi_s32_disk; moi_s32_rim; moi_s32_cyl;
              SUBSET; IN_ELIM_THM; VEC_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[]);;

let MOI_STD_322_TRANSFER = prove
 (`!(psi:real^3->real^3) psi' (h:real^3->real^3) c1 c2 dd jj p q1 q2 w.
     homeomorphism (moi_s32_cyl,c1 UNION c2) (psi,psi') /\
     IMAGE psi moi_s32_lo = c1 /\ IMAGE psi moi_s32_hi = c2 /\
     IMAGE psi moi_s32_disk = dd /\ IMAGE psi moi_s32_rim = jj /\ psi (vec 0) = p /\
     q1 IN c1 DIFF dd /\ q2 IN c2 DIFF dd /\
     h continuous_on (c1 UNION c2) /\
     (!x y. x IN c1 UNION c2 /\ y IN c1 UNION c2 /\ h x = h y ==> x = y) /\
     (IMAGE h (dd DIFF jj) DELETE h p) SUBSET interior w
     ==> (h o psi) continuous_on moi_s32_cyl /\
         (!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (h o psi) x = (h o psi) y
                ==> x = y) /\
         IMAGE (h o psi) (moi_s32_disk DIFF (vec 0 INSERT moi_s32_rim))
           SUBSET interior w /\
         psi' q1 IN moi_s32_lo DIFF moi_s32_disk /\
         psi' q2 IN moi_s32_hi DIFF moi_s32_disk /\
         psi (psi' q1) = q1 /\ psi (psi' q2) = q2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC MOI_STD_S32_MODEL_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN moi_s32_cyl ==> (psi:real^3->real^3) x IN c1 UNION c2`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s32_cyl = c1 UNION c2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\
                      (psi:real^3->real^3) x = psi y ==> x = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN c1 UNION c2` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_DIFF; IN_INSERT; DE_MORGAN_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (dd DIFF jj) DELETE h p SUBSET interior w` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_DELETE; IN_IMAGE; IN_DIFF] THEN CONJ_TAC THENL
     [EXISTS_TAC `(psi:real^3->real^3) x` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "dd" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        EXPAND_TAC "jj" THEN REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[]];
      DISCH_TAC THEN
      SUBGOAL_THEN `(psi:real^3->real^3) x = p` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          free_in `h:real^3->real^3` (concl th) && is_forall (concl th))) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `vec 0:real^3 IN moi_s32_cyl` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    UNDISCH_TAC `(q1:real^3) IN c1 DIFF dd` THEN EXPAND_TAC "c1" THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    UNDISCH_TAC `(q2:real^3) IN c2 DIFF dd` THEN EXPAND_TAC "c2" THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      free_in `psi':real^3->real^3` (concl th) && is_forall (concl th) &&
      free_in `c1:real^3->bool` (concl th))) THEN
    ASM SET_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      free_in `psi':real^3->real^3` (concl th) && is_forall (concl th) &&
      free_in `c1:real^3->bool` (concl th))) THEN
    ASM SET_TAC[]]);;

let MOI_STD_322_SIDE = prove
 (`!(g:real^3->real^3) v c k q a u.
     g continuous_on moi_s32_cyl /\
     (!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ g x = g y ==> x = y) /\
     v SUBSET moi_s32_cyl /\ c SUBSET g (vec 0) INSERT IMAGE g v /\
     connected k /\ q IN k /\ a IN k /\
     k SUBSET moi_s32_cyl DIFF (vec 0 INSERT (moi_s32_rim UNION v)) /\
     u IN components (IMAGE g moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim)) /\
     g q IN u
     ==> g a IN u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_STD_S32_MODEL_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected (IMAGE (g:real^3->real^3) k)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) k SUBSET
                IMAGE g moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s32_cyl /\ ~(x = vec 0) /\ ~(x IN moi_s32_rim) /\
                  ~(x IN v)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^3->real^3) x IN g (vec 0) INSERT IMAGE g v` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THENL
       [SUBGOAL_THEN `vec 0:real^3 IN moi_s32_cyl` ASSUME_TAC THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[]];
        SUBGOAL_THEN `(y:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[]]];
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  UNDISCH_TAC `u IN components (IMAGE (g:real^3->real^3) moi_s32_cyl DIFF
                                (c UNION IMAGE g moi_s32_rim))` THEN
  REWRITE_TAC[IN_COMPONENTS] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `u = connected_component (IMAGE (g:real^3->real^3) moi_s32_cyl DIFF
                             (c UNION IMAGE g moi_s32_rim)) (g q)`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENT_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim)`;
                 `IMAGE (g:real^3->real^3) k`; `(g:real^3->real^3) q`]
    CONNECTED_COMPONENT_MAXIMAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let MOI_STD_322_CORE = prove
 (mk_imp(list_mk_conj
   [moi_std_csq MOI_S32_CHART; MOI_S32_MODEL_V; moi_std_csq MOI_S32_TOWER;
    moi_std_csq MOI_S32_INITIAL; moi_std_csq MOI_S32_ITERATE;
    moi_std_csq MOI_S32_CLASSIFY; moi_std_csq MOI_S32_STEPS24;
    MOI_S32_CELL; MOI_S32_SIDES],
   `MOISE_322_CELLS_STATEMENT`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "chart") (CONJUNCTS_THEN2 (LABEL_TAC "modv")
   (CONJUNCTS_THEN2 (LABEL_TAC "tower") (CONJUNCTS_THEN2 (LABEL_TAC "init")
   (CONJUNCTS_THEN2 (LABEL_TAC "iter") (CONJUNCTS_THEN2 (LABEL_TAC "class")
   (CONJUNCTS_THEN2 (LABEL_TAC "steps") (CONJUNCTS_THEN2 (LABEL_TAC "cell")
    (LABEL_TAC "sides"))))))))) THEN
  REWRITE_TAC[MOISE_322_CELLS_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`c1:real^3->bool`; `c2:real^3->bool`; `dd:real^3->bool`;
    `jj:real^3->bool`; `p:real^3`; `q1:real^3`; `q2:real^3`; `h:real^3->real^3`;
    `w:real^3->bool`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "chart" (MP_TAC o SPECL [`c1:real^3->bool`; `c2:real^3->bool`;
    `dd:real^3->bool`; `jj:real^3->bool`; `p:real^3`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `psi':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`psi:real^3->real^3`; `psi':real^3->real^3`; `h:real^3->real^3`;
    `c1:real^3->bool`; `c2:real^3->bool`; `dd:real^3->bool`; `jj:real^3->bool`;
    `p:real^3`; `q1:real^3`; `q2:real^3`; `w:real^3->bool`] MOI_STD_322_TRANSFER) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REMOVE_THEN "modv" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `w:real^3->bool`; `(psi':real^3->real^3) q1`; `(psi':real^3->real^3) q2`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real^3->bool`
    (X_CHOOSE_THEN `k1:real^3->bool` (X_CHOOSE_THEN `k2:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(v:real^3->bool) SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [MP_TAC(ASSUME `moi_s32_model ((h:real^3->real^3) o (psi:real^3->real^3)) v`) THEN
    REWRITE_TAC[moi_s32_model] THEN MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "tower" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
                                       `v:real^3->bool`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:int->real^3` (X_CHOOSE_THEN `di:int->real^3->bool`
    (X_CHOOSE_THEN `s2:int->real^3->bool` ASSUME_TAC))) THEN
  REMOVE_THEN "init" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`]) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fam0:(real^3->bool)->bool` (ASSUME_TAC o CONJUNCT1)) THEN
  REMOVE_THEN "iter" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `fam0:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `fam:(real^3->bool)->bool`) THEN
  REMOVE_THEN "class" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  REMOVE_THEN "steps" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hh:int->real^3->bool` (X_CHOOSE_THEN `bb:int->real^3->bool`
    (X_CHOOSE_THEN `jl:int->real^3->bool` (X_CHOOSE_THEN `jh:int->real^3->bool`
      ASSUME_TAC)))) THEN
  REMOVE_THEN "cell" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `hh:int->real^3->bool`; `bb:int->real^3->bool`;
    `jl:int->real^3->bool`; `jh:int->real^3->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REMOVE_THEN "sides" (MP_TAC o SPECL [`(h:real^3->real^3) o (psi:real^3->real^3)`;
    `v:real^3->bool`; `pp:int->real^3`; `di:int->real^3->bool`;
    `s2:int->real^3->bool`; `hh:int->real^3->bool`; `bb:int->real^3->bool`;
    `jl:int->real^3->bool`; `jh:int->real^3->bool`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3->bool` (X_CHOOSE_THEN `u2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->real^3) moi_s32_cyl = c1 UNION c2` ASSUME_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^3->real^3) (c1 UNION c2) = IMAGE (h o psi) moi_s32_cyl /\
    IMAGE h jj = IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_rim /\
    h p = ((h:real^3->real^3) o (psi:real^3->real^3)) (vec 0) /\
    IMAGE h (frontier c1 DIFF (dd DIFF jj)) =
    IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_lohemi /\
    IMAGE h (frontier c2 DIFF (dd DIFF jj)) =
    IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_hihemi`
  (fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THENL
   [REWRITE_TAC[IMAGE_o; o_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`moi_s32_chainset ((h:real^3->real^3) o (psi:real^3->real^3)) hh bb UNION
     IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_rim`;
    `u1:real^3->bool`; `u2:real^3->bool`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `((h:real^3->real^3) o (psi:real^3->real^3)) (vec 0) INSERT
                  IMAGE (h o psi) v` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior w:real^3->bool` THEN
        REWRITE_TAC[INTERIOR_SUBSET] THEN FIRST_ASSUM ACCEPT_TAC];
      UNDISCH_TAC `w INTER frontier (IMAGE (h:real^3->real^3) (c1 UNION c2)) = IMAGE h jj` THEN
      REWRITE_TAC[ASSUME `IMAGE (h:real^3->real^3) jj =
                          IMAGE ((h:real^3->real^3) o (psi:real^3->real^3)) moi_s32_rim`] THEN
      SET_TAC[]];
    SUBGOAL_THEN `(h:real^3->real^3) q1 = (h o psi) ((psi':real^3->real^3) q1)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_STD_322_SIDE THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`;
      `moi_s32_chainset ((h:real^3->real^3) o (psi:real^3->real^3)) hh bb`;
      `k1:real^3->bool`; `moi_s32_qlo`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `k1 UNION k2 SUBSET moi_s32_cyl DIFF (vec 0 INSERT (moi_s32_rim UNION v))` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[IN_INSERT]];
    SUBGOAL_THEN `(h:real^3->real^3) q2 = (h o psi) ((psi':real^3->real^3) q2)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_STD_322_SIDE THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`;
      `moi_s32_chainset ((h:real^3->real^3) o (psi:real^3->real^3)) hh bb`;
      `k2:real^3->bool`; `moi_s32_qhi`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `k1 UNION k2 SUBSET moi_s32_cyl DIFF (vec 0 INSERT (moi_s32_rim UNION v))` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[IN_INSERT]]]);;

let MOI_STD_322 = prove
 (moi_std_full MOI_STD_322_CORE MOI_PROD_322_CELLS,
  MOI_STD_FULL_TAC MOI_STD_322_CORE);;

(* 6.9 Producer of 32.3 (p.228).  The s35 charts for the open sets         *)
(* g v = h^-1(nb v); for every edge the slab cells and W (SLAB_W) and       *)
(* MOISE_322_CELLS for them, chosen for all edges at once (Skolem); then    *)
(* HANDLES.  moi_std_edge_ex is moi_s32_edge_facts with ww e, ee e, uu1 e,  *)
(* uu2 e existentially quantified.                                          *)

let moi_std_edge_ex =
  let e = `e:real^3->bool` in
  let _,body = dest_forall moi_s32_edge_facts in
  let ant,cns = dest_imp body in
  let subs = [`w0:real^3->bool`, `(ww:(real^3->bool)->real^3->bool) e`;
              `e0:real^3->bool`, `(ee:(real^3->bool)->real^3->bool) e`;
              `a0:real^3->bool`, `(uu1:(real^3->bool)->real^3->bool) e`;
              `b0:real^3->bool`, `(uu2:(real^3->bool)->real^3->bool) e`] in
  mk_forall(e, mk_imp(ant, list_mk_exists(map fst subs, subst subs cns)));;

let MOI_STD_323_CORE = prove
 (mk_imp(list_mk_conj
   [`MOISE_322_CELLS_STATEMENT`; moi_n3 MOI_FND_GRAPH_TUBE;
    moi_std_csq (moi_n3 MOI_S35_CHARTS); moi_std_csq MOI_S32_SLAB_W;
    moi_std_csq MOI_S32_HANDLES],
   `MOISE_323_STATEMENT`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "322") (CONJUNCTS_THEN2 (LABEL_TAC "tube")
   (CONJUNCTS_THEN2 (LABEL_TAC "charts") (CONJUNCTS_THEN2 (LABEL_TAC "slab")
    (LABEL_TAC "handles"))))) THEN
  REMOVE_THEN "322" (LABEL_TAC "322" o REWRITE_RULE[MOISE_322_CELLS_STATEMENT]) THEN
  REWRITE_TAC[MOISE_323_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `nb:real^3->real^3->bool`] THEN
  DISCH_TAC THEN FIRST_ASSUM STRIP_ASSUME_TAC THEN
  USE_THEN "tube" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "tv")
    (CONJUNCTS_THEN2 (LABEL_TAC "te") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `!v. {v} IN l ==> derived_dual_cell t l v SUBSET UNIONS (t:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "tv" (MP_TAC o CONJUNCT1 o C MP (ASSUME `{v:real^3} IN l`) o SPEC `v:real^3`) THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "charts" (MP_TAC o BETA_RULE o SPECL
    [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
     `\v:real^3. {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v}`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MESON_TAC[ASSUME `{v:real^3} IN l`;
          ASSUME `!v. {v} IN l ==> open ((nb:real^3->real^3->bool) v) /\
                      IMAGE (h:real^3->real^3) (derived_dual_cell t l v) SUBSET nb v`]];
      SUBGOAL_THEN `derived_dual_cell t l v SUBSET UNIONS (t:(real^3->bool)->bool) /\
                    IMAGE (h:real^3->real^3) (derived_dual_cell t l v) SUBSET nb v`
      MP_TAC THENL
       [MESON_TAC[ASSUME `{v:real^3} IN l`;
          ASSUME `!v. {v} IN l ==> derived_dual_cell t l v SUBSET UNIONS (t:(real^3->bool)->bool)`;
          ASSUME `!v. {v} IN l ==> open ((nb:real^3->real^3->bool) v) /\
                      IMAGE (h:real^3->real^3) (derived_dual_cell t l v) SUBSET nb v`];
        SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `av:(real^3->bool)->real^3`
    (X_CHOOSE_THEN `bv:(real^3->bool)->real^3`
      (X_CHOOSE_THEN `psi:(real^3->bool)->real^3->real^3` ASSUME_TAC))) THEN
  SUBGOAL_THEN moi_std_edge_ex MP_TAC THENL
   [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ASSUME `moi_s35_charts t l
                     (\v:real^3. {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v})
                     av bv psi`) THEN
    REWRITE_TAC[moi_s35_charts] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `moi_s35_edge l (e:real^3->bool)`) o
               SPEC `e:real^3->bool` o CONJUNCT1) THEN
    STRIP_TAC THEN
    USE_THEN "te" (MP_TAC o SPECL [`(av:(real^3->bool)->real^3) e`;
                                   `(bv:(real^3->bool)->real^3) e`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `moi_s35_edge l (e:real^3->bool)` THEN REWRITE_TAC[moi_s35_edge] THEN
      UNDISCH_TAC `e = segment[(av:(real^3->bool)->real^3) e,(bv:(real^3->bool)->real^3) e]` THEN
      MESON_TAC[];
      STRIP_TAC] THEN
    USE_THEN "slab" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
      `h:real^3->real^3`; `\v:real^3. {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v}`;
      `av:(real^3->bool)->real^3`; `bv:(real^3->bool)->real^3`;
      `psi:(real^3->bool)->real^3->real^3`; `e:real^3->bool`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "322" (MP_TAC o SPECL
      [`IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo`;
       `IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s32_slab_hi`;
       `derived_dual_cell t l ((av:(real^3->bool)->real^3) e) INTER
        derived_dual_cell t l ((bv:(real^3->bool)->real^3) e)`;
       `derived_dual_cell t l ((av:(real^3->bool)->real^3) e) INTER
        derived_dual_cell t l ((bv:(real^3->bool)->real^3) e) INTER derived_frontier t l`;
       `midpoint((av:(real^3->bool)->real^3) e,(bv:(real^3->bool)->real^3) e)`;
       `(psi:(real^3->bool)->real^3->real^3) e moi_s32_slo`;
       `(psi:(real^3->bool)->real^3->real^3) e moi_s32_shi`;
       `h:real^3->real^3`; `w:real^3->bool`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `IMAGE ((psi:(real^3->bool)->real^3->real^3) e) moi_s32_slab_lo UNION
                     IMAGE (psi e) moi_s32_slab_hi SUBSET UNIONS (t:(real^3->bool)->bool)` THEN
        UNDISCH_TAC `!x y. x IN UNIONS t /\ y IN UNIONS t /\ (h:real^3->real^3) x = h y
                           ==> x = y` THEN
        REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e0:real^3->bool` (X_CHOOSE_THEN `a0:real^3->bool`
      (X_CHOOSE_THEN `b0:real^3->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`w:real^3->bool`; `e0:real^3->bool`; `a0:real^3->bool`;
                          `b0:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ww:(real^3->bool)->real^3->bool`
    (X_CHOOSE_THEN `ee:(real^3->bool)->real^3->bool`
      (X_CHOOSE_THEN `uu1:(real^3->bool)->real^3->bool`
        (X_CHOOSE_THEN `uu2:(real^3->bool)->real^3->bool` ASSUME_TAC)))) THEN
  REMOVE_THEN "handles" (MP_TAC o BETA_RULE o SPECL
    [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
     `nb:real^3->real^3->bool`;
     `\v:real^3. {x | x IN UNIONS t /\ (h:real^3->real^3) x IN nb v}`;
     `av:(real^3->bool)->real^3`; `bv:(real^3->bool)->real^3`;
     `psi:(real^3->bool)->real^3->real^3`; `ww:(real^3->bool)->real^3->bool`;
     `ee:(real^3->bool)->real^3->bool`; `uu1:(real^3->bool)->real^3->bool`;
     `uu2:(real^3->bool)->real^3->bool`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`ee:(real^3->bool)->real^3->bool`; moi_s32_pieces] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN FIRST_ASSUM ACCEPT_TAC);;

let MOI_STD_323 = prove
 (moi_std_full MOI_STD_323_CORE MOI_PROD_323,
  MOI_STD_FULL_TAC MOI_STD_323_CORE);;

(* ========================================================================= *)
(* 7. Sanity theorems for the new definitions: the model points and sets,   *)
(* the middle disk as the revolution of the radius (the comment of the      *)
(* definitions), non-vacuity of moi_s32_model, the empty family in          *)
(* moi_s32_state, the inner square.                                         *)
(* ========================================================================= *)

let MOI_STD_SAN_Q = prove
 (`moi_s32_qlo IN moi_s32_lo DIFF moi_s32_disk /\
   moi_s32_qhi IN moi_s32_hi DIFF moi_s32_disk /\
   moi_s32_qlo IN moi_s32_axis /\ moi_s32_qhi IN moi_s32_axis`,
  REWRITE_TAC[moi_s32_qlo; moi_s32_qhi; moi_s32_lo; moi_s32_hi; moi_s32_disk;
              moi_s32_cyl; moi_s32_axis; IN_DIFF; IN_ELIM_THM; VECTOR_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_STD_SAN_DISK_REV = prove
 (`moi_s32_disk = revolution(segment[vec 0,basis 1])`,
  REWRITE_TAC[moi_s32_disk; moi_s32_cyl; revolution; EXTENSION; IN_ELIM_THM;
              IN_SEGMENT; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  X_GEN_TAC `p:real^3` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (p:real^3)$1 pow 2 + p$3 pow 2` ASSUME_TAC THENL
     [MP_TAC(SPEC `(p:real^3)$1` REAL_LE_POW_2) THEN
      MP_TAC(SPEC `(p:real^3)$3` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt((p:real^3)$1 pow 2 + p$3 pow 2) /\
                  sqrt((p:real^3)$1 pow 2 + p$3 pow 2) <= &1 /\
                  sqrt((p:real^3)$1 pow 2 + p$3 pow 2) pow 2 = p$1 pow 2 + p$3 pow 2`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `sqrt((p:real^3)$1 pow 2 + p$3 pow 2) % basis 1:real^3` THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID] THEN
    EXISTS_TAC `sqrt((p:real^3)$1 pow 2 + p$3 pow 2)` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `q:real^3` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `q = u % basis 1:real^3` THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(SIMP_RULE[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH;
                             REAL_MUL_RZERO; REAL_MUL_RID]) THEN
    SUBGOAL_THEN `u pow 2 <= &1` ASSUME_TAC THENL
     [REWRITE_TAC[ABS_SQUARE_LE_1] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_STD_SAN_MODEL = prove
 (`moi_s32_model (\x:real^3. x) (ball(vec 0,&1) DIFF moi_s32_axis)`,
  REWRITE_TAC[moi_s32_model; CONTINUOUS_ON_ID] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,&1) SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; moi_s32_cyl; IN_ELIM_THM; NORM_LT_SQUARE; DOT_3] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM ABS_SQUARE_LE_1] THEN
    MP_TAC(SPEC `(x:real^3)$1` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `(x:real^3)$2` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `(x:real^3)$3` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `(x:real^3)$1 * x$1 + x$2 * x$2 + x$3 * x$3 < &1 pow 2` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL] THEN
    SUBGOAL_THEN `moi_s32_axis = {x:real^3 | x$1 = &0} INTER {x | x$3 = &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_s32_axis; EXTENSION; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    SIMP_TAC[CLOSED_INTER; CLOSED_STANDARD_HYPERPLANE];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
    REWRITE_TAC[SUBSET_DIFF] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_INSERT] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[moi_s32_disk; moi_s32_rim; moi_s32_cyl; moi_s32_axis; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~((x:real^3)$1 pow 2 + x$3 pow 2 = &1) /\ ~(x = vec 0)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_BALL_0; NORM_LT_SQUARE; DOT_3] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3)$1 pow 2 + x$3 pow 2 <= &1` THEN
      UNDISCH_TAC `~((x:real^3)$1 pow 2 + x$3 pow 2 = &1)` THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN UNDISCH_TAC `~(x:real^3 = vec 0)` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_STD_SAN_STATE_EMPTY = prove
 (`!(g:real^3->real^3) dd s2 lev.
     moi_s32_state g dd s2 lev {} <=>
     closed_in (subtopology euclidean (moi_s32_open g))
               (moi_s32_evens s2 UNION {g (vec 0)}) /\
     separates_in (moi_s32_open g) (moi_s32_evens s2 UNION {g (vec 0)})
                  {g moi_s32_qlo} {g moi_s32_qhi}`,
  REWRITE_TAC[moi_s32_state; moi_s32_set; PAIRWISE_EMPTY; NOT_IN_EMPTY; UNIONS_0;
              UNION_EMPTY; EMPTY_GSPEC; FINITE_EMPTY]);;

let MOI_STD_SAN_INNER = prove
 (`moi_s30_inner SUBSET moi_s35_mid /\ vec 0 IN moi_s30_inner`,
  REWRITE_TAC[moi_s30_inner; SUBSET; IN_ELIM_THM] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s35_mid; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL; VEC_COMPONENT;
              VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* 8. Final checks: every statement term is a closed boolean term; every     *)
(* glue theorem has no hypotheses and concludes exactly its item.            *)
(* ========================================================================= *)

let moi_std_glue =
  ["MOISE_303_STATEMENT",MOI_STD_303,`MOISE_303_STATEMENT`;
   "MOISE_324_STATEMENT",MOI_STD_324,`MOISE_324_STATEMENT`;
   "MOI_PROD_304",MOI_STD_304,MOI_PROD_304;
   "MOI_PROD_306",MOI_STD_306,MOI_PROD_306;
   "MOI_PROD_307",MOI_STD_307,MOI_PROD_307;
   "MOI_PROD_311",MOI_STD_311,MOI_PROD_311;
   "MOI_PROD_314",MOI_STD_314,MOI_PROD_314;
   "MOI_PROD_322_CELLS",MOI_STD_322,MOI_PROD_322_CELLS;
   "MOI_PROD_323",MOI_STD_323,MOI_PROD_323];;

let moi_std_check =
  forall (fun (_,t) -> type_of t = bool_ty && frees t = []) moi_std_targets &&
  forall (fun (_,th,t) -> hyp th = [] && aconv (rand(concl th)) t) moi_std_glue;;

if not moi_std_check then failwith "moi_std_check";;

map (fun (n,th,_) -> n, length(conjuncts(lhand(concl th)))) moi_std_glue;;
length moi_std_targets;;


