(* ========================================================================= *)
(* pc_moi_core_stmt: the statements of the PL core MOISE_352_COMPLEX (Moise  *)
(* GTM 47 Secs 25-35): definitions, statement constants of every level, the  *)
(* producer implications as terms (MOI_CORE_GLUE_, MOI_PROD_), and the       *)
(* closure theorem MOI_CD_BLUEPRINT_CLOSURE (producers and leaves imply      *)
(* MOISE_352_COMPLEX_STATEMENT (:7)).  It builds on the statements of        *)
(* pc_moi_stmt.ml.  The producers and leaves are proved in the later Moise   *)
(* files (collected in pc_moi_core_status).                                  *)
(* ========================================================================= *)

needs "src/pc_moi_stmt.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_bary.ml";;
needs "src/pc_moi_tridef.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* D1. Subcomplexes, subdivisions, skeleta (Moise Sec 1, p.3-4).             *)
(* ------------------------------------------------------------------------- *)

let simplicial_subcomplex = new_definition
 `simplicial_subcomplex (k:(real^N->bool)->bool) (c:(real^N->bool)->bool) <=>
    k SUBSET c /\ !s f. s IN k /\ f face_of s ==> f IN k`;;

let subdivides = new_definition
 `subdivides (c':(real^N->bool)->bool) (c:(real^N->bool)->bool) <=>
    UNIONS c' = UNIONS c /\
    (!s. s IN c' ==> ?t. t IN c /\ s SUBSET t) /\
    (!t. t IN c ==> ?d. d SUBSET c' /\ UNIONS d = t)`;;

let skeleton = new_definition
 `skeleton n (c:(real^N->bool)->bool) = {s | s IN c /\ aff_dim s <= &n}`;;

(* ------------------------------------------------------------------------- *)
(* D2. Regular (second-derived) neighbourhoods, Moise p.155: the union of   *)
(* the simplices of the second barycentric subdivision meeting |l|; dual    *)
(* cells of a graph (p.223): the part of the neighbourhood in the closed    *)
(* star of a vertex in the first barycentric subdivision.  Splitting disks  *)
(* are intersections of two dual cells.                                      *)
(* ------------------------------------------------------------------------- *)

let derived_nbhd = new_definition
 `derived_nbhd (t:(real^N->bool)->bool) (l:(real^N->bool)->bool) =
    UNIONS {s | s IN barycentric_subdivision (barycentric_subdivision t) /\
                ~(s INTER UNIONS l = {})}`;;

let derived_dual_cell = new_definition
 `derived_dual_cell (t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (v:real^N) =
    derived_nbhd t l INTER
    UNIONS {s | s IN barycentric_subdivision t /\ v IN s}`;;

(* ------------------------------------------------------------------------- *)
(* D3. Graphs in combinatorial 3-manifolds and the tube approximation       *)
(* property (book p.223 tubes; DG IsTube PL/PseudoCell.lean:218 and         *)
(* Moise331OnTube PL/Section33TubeApproximation.lean:13).  graph_in_complex *)
(* t l: l is a 1-dimensional subcomplex of the lf complex t whose vertices  *)
(* are interior vertices of t (links PL 2-spheres).  graph_approximable t l *)
(* h: for all open w v containing h(C_v) there is a PL embedding f of the   *)
(* regular neighbourhood N with f(C_v) inside w v and f(N) a neighbourhood  *)
(* of h|l|.                                                                  *)
(* ------------------------------------------------------------------------- *)

let graph_in_complex = new_definition
 `graph_in_complex (t:(real^N->bool)->bool) (l:(real^N->bool)->bool) <=>
    lf_simplicial_complex t /\ simplicial_subcomplex l t /\
    (!s. s IN l ==> aff_dim s <= &1) /\
    (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v)))`;;

let graph_approximable = new_definition
 `graph_approximable (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
                     (h:real^N->real^3) <=>
    !w:real^N->real^3->bool.
      (!v. {v} IN l
           ==> open (w v) /\ IMAGE h (derived_dual_cell t l v) SUBSET w v)
      ==> ?f. pl_map_on (derived_nbhd t l) f /\
              (!x y. x IN derived_nbhd t l /\ y IN derived_nbhd t l /\
                     f x = f y ==> x = y) /\
              IMAGE h (UNIONS l) SUBSET interior (IMAGE f (derived_nbhd t l)) /\
              (!v. {v} IN l ==> IMAGE f (derived_dual_cell t l v) SUBSET w v)`;;

(* ------------------------------------------------------------------------- *)
(* L33. Moise 33.1 (p.230) in tube form (DG Moise331OnTube): a finite       *)
(* connected graph in real^3 with an edge and no vertex of degree 1.        *)
(* ------------------------------------------------------------------------- *)

let MOISE_331_STATEMENT = new_definition
 `MOISE_331_STATEMENT <=>
    !(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3).
        FINITE t /\ graph_in_complex t l /\ connected (UNIONS l) /\
        (?e. e IN l /\ aff_dim e = &1) /\
        (!v. {v} IN l ==> ~(CARD {e | e IN l /\ aff_dim e = &1 /\ v IN e} = 1)) /\
        h continuous_on UNIONS t /\
        (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y)
        ==> graph_approximable t l h`;;

(* ------------------------------------------------------------------------- *)
(* L35a. Moise 35.1 (p.248) in tube form, for locally finite graphs in a    *)
(* locally finite complex in real^N (DG ControlledGraphNeighborhood-       *)
(* Statement, PL/Section34Statements.lean:25).                              *)
(* ------------------------------------------------------------------------- *)

let MOISE_351_STATEMENT = new_definition
 `MOISE_351_STATEMENT (u:N->bool) <=>
    !(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (h:real^N->real^3).
        graph_in_complex t l /\
        h continuous_on UNIONS t /\
        (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y)
        ==> graph_approximable t l h`;;

(* ------------------------------------------------------------------------- *)
(* L34. The Sec 34 extension, stated once for locally finite complexes and  *)
(* used twice: for 34.1 (with 33.1) and for 35.2 (with 35.1, as virtually a   *)
(* repetition of 34.1, p.251).  Moise pp.239-246 (Lemmas 1-11, Operations  *)
(* 1-2, stages (1)-(7)); DG Section34CellDiagram / Section34Normal-         *)
(* FamilyStatement and the compact pipeline.  Given k (a combinatorial      *)
(* 3-manifold with boundary, subcomplex of t, vertices interior in t), h an  *)
(* embedding of |t| into real^3 and e > 0 on |k|, there are subdivisions t' *)
(* of t and k' of k such that the 1-skeleton of k' is a graph in t' and     *)
(* tube approximability of h on it gives a PL embedding of |k| e-close to h.*)
(* ------------------------------------------------------------------------- *)

let MOISE_34_EXT_STATEMENT = new_definition
 `MOISE_34_EXT_STATEMENT (u:N->bool) <=>
    !(t:(real^N->bool)->bool) (k:(real^N->bool)->bool) (h:real^N->real^3)
     (e:real^N->real).
        lf_simplicial_complex t /\ simplicial_subcomplex k t /\
        combinatorial_manifold_with_boundary 3 k /\
        (!v. {v} IN k ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
        h continuous_on UNIONS t /\
        (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
        (lift o e) continuous_on UNIONS k /\ (!x. x IN UNIONS k ==> &0 < e x)
        ==> ?t' k'. lf_simplicial_complex t' /\ subdivides t' t /\
                    simplicial_subcomplex k' t' /\ subdivides k' k /\
                    combinatorial_manifold_with_boundary 3 k' /\
                    graph_in_complex t' (skeleton 1 k') /\
                    (graph_approximable t' (skeleton 1 k') h
                     ==> ?f. pl_map_on (UNIONS k) f /\
                             (!x y. x IN UNIONS k /\ y IN UNIONS k /\ f x = f y
                                    ==> x = y) /\
                             !x. x IN UNIONS k ==> dist(f x,h x) < e x)`;;

(* 34.1 with h defined on an open neighbourhood (DG Moise341OnNeighborhood,  *)
(* PL/Section34Compact.lean:155; the reduction on p.239).                    *)

let MOISE_341_NBHD_STATEMENT = new_definition
 `MOISE_341_NBHD_STATEMENT <=>
    !(c:real^3->bool) (u:real^3->bool) (h:real^3->real^3) e.
        pl_ball 3 c /\ open u /\ c SUBSET u /\ h continuous_on u /\
        (!x y. x IN u /\ y IN u /\ h x = h y ==> x = y) /\ &0 < e
        ==> ?f g. pl_homeomorphism (c,IMAGE f c) (f,g) /\
                  !x. x IN c ==> dist(f x,h x) < e`;;

(* ------------------------------------------------------------------------- *)
(* Glue implications of the top levels (terms, proved in pc_moi_cglue).      *)
(* ------------------------------------------------------------------------- *)

let MOI_CORE_GLUE_352 =
 `!u:N->bool. MOISE_34_EXT_STATEMENT u /\ MOISE_351_STATEMENT u
              ==> MOISE_352_COMPLEX_STATEMENT u`;;

let MOI_CORE_GLUE_341_NBHD =
 `MOISE_34_EXT_STATEMENT (:3) /\ MOISE_331_STATEMENT
  ==> MOISE_341_NBHD_STATEMENT`;;

let MOI_CORE_GLUE_341 =
 `MOISE_341_NBHD_STATEMENT ==> MOISE_341_STATEMENT`;;

map type_of [MOI_CORE_GLUE_352; MOI_CORE_GLUE_341_NBHD; MOI_CORE_GLUE_341];;

(* ------------------------------------------------------------------------- *)
(* F. Foundation statements used by the top glue.                            *)
(* pl_cell_with_boundary n s b: s is a PL n-cell with (manifold) boundary b. *)
(* MOISE_CELL_ASSEMBLY: a locally finite family of PL cells and a family of  *)
(* target PL cells in real^3 with the same face combinatorics give a PL     *)
(* embedding mapping each cell onto its target (the stages (1)-(7) of       *)
(* p.245-246, the final steps of 33.1 and 35.1; DG exists_isPLHomeomorph-   *)
(* Into_of_labelledCells, PL/LabelledCellAssembly.lean:357).                *)
(* ------------------------------------------------------------------------- *)

let pl_cell_with_boundary = new_definition
 `pl_cell_with_boundary n (s:real^N->bool) (b:real^N->bool) <=>
    ?k:real^N->bool f g. &n simplex k /\ pl_homeomorphism (k,s) (f,g) /\
                         b = IMAGE f (relative_frontier k)`;;

let MOISE_CELL_ASSEMBLY_STATEMENT = new_definition
 `MOISE_CELL_ASSEMBLY_STATEMENT (i:L->bool) (u:N->bool) <=>
    !(a:L->real^N->bool) (b:L->real^3->bool) (d:L->num) (face:L->L->bool).
        (!l. d l <= 3) /\ (!l. face l l) /\
        (!l m. face l m ==> m = l \/ d m < d l) /\
        (!l. pl_cell_with_boundary (d l) (a l)
                (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
        (!l. pl_cell_with_boundary (d l) (b l)
                (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
        (!l m. a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
        (!l m. b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
        (!x. x IN UNIONS {a l | l IN (:L)}
             ==> ?w. open w /\ x IN w /\ FINITE {l | ~(a l INTER w = {})}) /\
        (!y. y IN UNIONS {b l | l IN (:L)}
             ==> ?w. open w /\ y IN w /\ FINITE {l | ~(b l INTER w = {})})
        ==> ?f. pl_map_on (UNIONS {a l | l IN (:L)}) f /\
                (!x y. x IN UNIONS {a l | l IN (:L)} /\
                       y IN UNIONS {a l | l IN (:L)} /\ f x = f y ==> x = y) /\
                (!l. IMAGE f (a l) = b l)`;;

(* Set form: with every label of the whole type carrying a nonempty cell,    *)
(* local finiteness forces the label type to be countable, so the form above *)
(* is vacuous at label types of point sets.  The producers use this form,    *)
(* with an explicit label set lab.                                           *)

let MOISE_CELL_ASSEMBLY_ON_STATEMENT = new_definition
 `MOISE_CELL_ASSEMBLY_ON_STATEMENT (i:L->bool) (u:N->bool) <=>
    !(lab:L->bool) (a:L->real^N->bool) (b:L->real^3->bool) (d:L->num)
     (face:L->L->bool).
        (!l. l IN lab ==> d l <= 3 /\ face l l) /\
        (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
        (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                            (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
        (!l. l IN lab ==> pl_cell_with_boundary (d l) (b l)
                            (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
        (!l m. l IN lab /\ m IN lab
               ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
        (!l m. l IN lab /\ m IN lab
               ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
        (!x. x IN UNIONS {a l | l IN lab}
             ==> ?w. open w /\ x IN w /\
                     FINITE {l | l IN lab /\ ~(a l INTER w = {})}) /\
        (!y. y IN UNIONS {b l | l IN lab}
             ==> ?w. open w /\ y IN w /\
                     FINITE {l | l IN lab /\ ~(b l INTER w = {})})
        ==> ?f. pl_map_on (UNIONS {a l | l IN lab}) f /\
                (!x y. x IN UNIONS {a l | l IN lab} /\
                       y IN UNIONS {a l | l IN lab} /\ f x = f y ==> x = y) /\
                (!l. l IN lab ==> IMAGE f (a l) = b l)`;;

(* Small foundation lemmas needed by the glue (terms, MOI_FND_...).          *)

let MOI_FND_FINITE_SUBDIVISION =
 `!c c':(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c /\ lf_simplicial_complex c' /\
     subdivides c' c ==> FINITE c'`;;

let MOI_FND_CONNECTED_SKELETON =
 `!c:(real^N->bool)->bool.
     lf_simplicial_complex c /\ connected (UNIONS c)
     ==> connected (UNIONS (skeleton 1 c))`;;

let MOI_FND_DEGREE_3 =
 `!(c:(real^N->bool)->bool) v.
     combinatorial_manifold_with_boundary 3 c /\ {v} IN c
     ==> FINITE {e | e IN c /\ aff_dim e = &1 /\ v IN e} /\
         3 <= CARD {e | e IN c /\ aff_dim e = &1 /\ v IN e}`;;

let MOI_FND_BALL_TRIANGULATION =
 `!(c:real^3->bool) u.
     pl_ball 3 c /\ open u /\ c SUBSET u
     ==> ?t k. simplicial_complex t /\ UNIONS t SUBSET u /\
               simplicial_subcomplex k t /\ UNIONS k = c /\
               combinatorial_manifold_with_boundary 3 k /\
               (!v. {v} IN k ==> pl_sphere 2 (UNIONS (simplicial_link t v)))`;;

let MOI_FND_PL_INVERSE =
 `!(c:real^M->bool) (f:real^M->real^N).
     pl_polyhedron c /\ pl_map_on c f /\
     (!x y. x IN c /\ y IN c /\ f x = f y ==> x = y)
     ==> ?g. pl_homeomorphism (c,IMAGE f c) (f,g)`;;

let MOI_FND_PUSH_IN =
 `!(c:real^3->bool) e.
     pl_ball 3 c /\ &0 < e
     ==> ?p q. pl_homeomorphism (c,IMAGE p c) (p,q) /\
               IMAGE p c SUBSET interior c /\
               !x. x IN c ==> dist(p x,x) < e`;;

map type_of [MOI_FND_FINITE_SUBDIVISION; MOI_FND_CONNECTED_SKELETON;
             MOI_FND_DEGREE_3; MOI_FND_BALL_TRIANGULATION;
             MOI_FND_PL_INVERSE; MOI_FND_PUSH_IN];;

(* ------------------------------------------------------------------------- *)
(* D4. Notions of Secs 24, 30-32.  separates_in x c s t: Moise p.214 inside  *)
(* the subspace x (euclidean_separates of pc_moi_stmt.ml is the case x =     *)
(* whole space).  Solid tori, tori and spines follow p.178 and p.218 (A x    *)
(* S^1 with A a 2-cell); a PL solid torus (CST, p.178; 24.9-24.10) is PL     *)
(* homeomorphic to a square annulus times an interval.  A toroidal shell     *)
(* (p.216) is a homeomorphic image of T^2 x [0,1] with labelled ends.        *)
(* loops_carried j s: every loop in s is freely homotopic in s to a loop in  *)
(* j (for s with abelian pi_1, the book's j carries a generator of pi(s)).   *)
(* pseudo_cell e j p (p.223): e minus j is an open 2-cell with closure e, j  *)
(* a 1-sphere, p in e minus j, and e minus j minus p locally polyhedral.     *)
(* ------------------------------------------------------------------------- *)

let separates_in = new_definition
 `separates_in (x:real^N->bool) (c:real^N->bool) (s:real^N->bool) (t:real^N->bool) <=>
    ?u v. open_in (subtopology euclidean x) u /\
          open_in (subtopology euclidean x) v /\
          DISJOINT u v /\ u UNION v = x DIFF c /\ s SUBSET u /\ t SUBSET v`;;

let solid_torus = new_definition
 `solid_torus (s:real^N->bool) <=>
    s homeomorphic (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`;;

let torus_surface = new_definition
 `torus_surface (s:real^N->bool) <=>
    s homeomorphic (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`;;

let pl_torus = new_definition
 `pl_torus (s:real^N->bool) <=> pl_polyhedron s /\ torus_surface s`;;

let pl_solid_torus = new_definition
 `pl_solid_torus (s:real^N->bool) <=>
    ?f g. pl_homeomorphism
            ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
              interval(--vector[&1;&1]:real^2,vector[&1;&1])) PCROSS
             interval[--vec 1:real^1,vec 1],s) (f,g)`;;

let toroidal_shell = new_definition
 `toroidal_shell (y:real^N->bool) (t0:real^N->bool) (t1:real^N->bool) <=>
    ?f g. homeomorphism
            ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
             interval[vec 0:real^1,vec 1],y) (f,g) /\
          t0 = IMAGE f ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                        PCROSS {vec 0:real^1}) /\
          t1 = IMAGE f ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                        PCROSS {vec 1:real^1})`;;

let spine = new_definition
 `spine (j:real^N->bool) (s:real^N->bool) <=>
    ?f g p. homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),s)
                          (f,g) /\
            p IN ball(vec 0:real^2,&1) /\
            j = IMAGE f ({p} PCROSS sphere(vec 0:real^2,&1))`;;

let loops_carried = new_definition
 `loops_carried (j:real^N->bool) (s:real^N->bool) <=>
    !p:real^1->real^N.
        path p /\ pathfinish p = pathstart p /\ path_image p SUBSET s
        ==> ?q:real^1->real^N.
              path q /\ pathfinish q = pathstart q /\ path_image q SUBSET j /\
              homotopic_loops s p q`;;

let disk_with_boundary = new_definition
 `disk_with_boundary (d:real^N->bool) (j:real^N->bool) <=>
    ?f g. homeomorphism (cball(vec 0:real^2,&1),d) (f,g) /\
          j = IMAGE f (sphere(vec 0:real^2,&1))`;;

let pseudo_cell = new_definition
 `pseudo_cell (e:real^N->bool) (j:real^N->bool) (p:real^N) <=>
    j SUBSET e /\ (e DIFF j) homeomorphic ball(vec 0:real^2,&1) /\
    j homeomorphic sphere(vec 0:real^2,&1) /\ closure(e DIFF j) = e /\
    p IN e DIFF j /\ locally_polyhedral ((e DIFF j) DELETE p)`;;

(* ------------------------------------------------------------------------- *)
(* L30. Moise Sec 30 (pp.214-218).  30.4 and 30.5 are stated in              *)
(* pc_moi_stmt.ml (MOISE_304_STATEMENT, MOISE_305_STATEMENT).                *)
(* ------------------------------------------------------------------------- *)

(* 30.1-30.2 (p.214-215): if a closed set with finitely many components     *)
(* separates H from K in a simply connected locally connected space whose   *)
(* connected open sets are path connected, one component separates.  Used   *)
(* in 30.4, 30.6, 32.1 and 33.1 (Lemmas 5, 6, 10) with X = R^3 or an open   *)
(* subset: stated for X open in real^3 and simply connected.                *)

let MOISE_302_STATEMENT = new_definition
 `MOISE_302_STATEMENT <=>
    !(x:real^3->bool) c h k.
        open x /\ simply_connected x /\
        closed_in (subtopology euclidean x) c /\
        closed_in (subtopology euclidean x) h /\
        closed_in (subtopology euclidean x) k /\
        connected h /\ connected k /\ ~(h = {}) /\ ~(k = {}) /\
        DISJOINT h k /\ DISJOINT c h /\ DISJOINT c k /\
        FINITE (components c) /\ separates_in x c h k
        ==> ?d. d IN components c /\ separates_in x d h k`;;

(* 30.6 (p.216): toroidal shells contain separating PL tori (DG Moise306).   *)

(* The model torus: the product of two square boundaries in                  *)
(* real^(2,2)finite_sum; MOISE_306 concludes a torus PL homeomorphic to it,  *)
(* so the producer of 30.7 needs no 2D Hauptvermutung.                       *)

let pl_torus_model = new_definition
 `pl_torus_model =
    relative_frontier(interval[--vec 1:real^2,vec 1]) PCROSS
    relative_frontier(interval[--vec 1:real^2,vec 1])`;;

let MOISE_306_STATEMENT = new_definition
 `MOISE_306_STATEMENT <=>
    !y t0 t1:real^3->bool.
        toroidal_shell y t0 t1
        ==> ?t (f:real^(2,2)finite_sum->real^3) g.
                pl_homeomorphism (pl_torus_model,t) (f,g) /\
                t SUBSET interior y /\ euclidean_separates t t0 t1`;;

(* 30.7 (p.217): between nested solid tori with a toroidal shell between     *)
(* them lies a PL solid torus (DG Moise307, cylindrical-diagram form).      *)

let MOISE_307_STATEMENT = new_definition
 `MOISE_307_STATEMENT <=>
    !s1 s2:real^3->bool.
        solid_torus s1 /\ solid_torus s2 /\ s1 SUBSET interior s2 /\
        toroidal_shell (closure(s2 DIFF s1)) (frontier s1) (frontier s2)
        ==> ?s. pl_solid_torus s /\ s1 SUBSET interior s /\ s SUBSET interior s2`;;

(* 30.8 (p.218): a spine of the inner torus carries pi_1 of every solid      *)
(* torus between (DG Moise308Nested, PL/Moise308Nested.lean:299, there      *)
(* bijective; the book needs only that p_J generates).  The book takes s as  *)
(* in 30.7 (a CST); its proof uses only that pi_1(s) is cyclic.             *)

let MOISE_308_STATEMENT = new_definition
 `MOISE_308_STATEMENT <=>
    !s1 s s2 j:real^3->bool.
        solid_torus s1 /\ solid_torus s /\ solid_torus s2 /\
        s1 SUBSET interior s /\ s SUBSET interior s2 /\
        toroidal_shell (closure(s2 DIFF s1)) (frontier s1) (frontier s2) /\
        spine j s1
        ==> loops_carried j s`;;

(* ------------------------------------------------------------------------- *)
(* L32. Moise Sec 32 (pp.223-229) for tubes given by (t,l): N = derived_nbhd *)
(* t l, dual cells C_v, splitting disk D_e = C_u INTER C_v at the midpoint P *)
(* of the edge e = segment[u,v], Bd D_e = D_e INTER frontier N, h an        *)
(* embedding of |t| into real^3 (DG IsTube, IsHandleDecompositionOfTube).    *)
(* ------------------------------------------------------------------------- *)

let MOISE_322_STATEMENT = new_definition
 `MOISE_322_STATEMENT <=>
    !(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
     (u:real^3) (v:real^3) (w:real^3->bool).
        FINITE t /\ graph_in_complex t l /\
        h continuous_on UNIONS t /\
        (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
        ~(u = v) /\ segment[u,v] IN l /\
        closed w /\
        w SUBSET IMAGE h (derived_dual_cell t l u UNION derived_dual_cell t l v) /\
        (IMAGE h ((derived_dual_cell t l u INTER derived_dual_cell t l v) DIFF
                  frontier (derived_nbhd t l)) DELETE h(midpoint(u,v)))
        SUBSET interior w /\
        w INTER frontier (IMAGE h (derived_dual_cell t l u UNION
                                   derived_dual_cell t l v)) =
        IMAGE h (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                 frontier (derived_nbhd t l)) /\
        w INTER IMAGE h (UNIONS l) = {h(midpoint(u,v))}
        ==> ?e u1 u2.
              pseudo_cell e
                (IMAGE h (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                          frontier (derived_nbhd t l)))
                (h(midpoint(u,v))) /\
              e SUBSET w /\
              e INTER IMAGE h (UNIONS l) = {h(midpoint(u,v))} /\
              components (IMAGE h (derived_dual_cell t l u UNION
                                   derived_dual_cell t l v) DIFF e) = {u1,u2} /\
              h u IN u1 /\ h v IN u2 /\ ~(u1 = u2) /\
              e SUBSET frontier u1 /\ e SUBSET frontier u2 /\
              IMAGE h (frontier (derived_dual_cell t l u) INTER
                       frontier (derived_nbhd t l)) SUBSET frontier u1 /\
              IMAGE h (frontier (derived_dual_cell t l v) INTER
                       frontier (derived_nbhd t l)) SUBSET frontier u2`;;

(* 32.3 (p.228): a handle decomposition of the tube N' = h(N) into          *)
(* pseudo-cells E_e and pieces C''_v inside given neighbourhoods nb v.        *)

let MOISE_323_STATEMENT = new_definition
 `MOISE_323_STATEMENT <=>
    !(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
     (nb:real^3->real^3->bool).
        FINITE t /\ graph_in_complex t l /\
        h continuous_on UNIONS t /\
        (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
        (!v. {v} IN l ==> open (nb v) /\ IMAGE h (derived_dual_cell t l v) SUBSET nb v)
        ==> ?(e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool).
              (!u v. ~(u = v) /\ segment[u,v] IN l
                     ==> pseudo_cell (e(segment[u,v]))
                           (IMAGE h (derived_dual_cell t l u INTER
                                     derived_dual_cell t l v INTER
                                     frontier (derived_nbhd t l)))
                           (h(midpoint(u,v))) /\
                         e(segment[u,v]) INTER IMAGE h (UNIONS l) =
                         {h(midpoint(u,v))} /\
                         e(segment[u,v]) INTER
                         frontier (IMAGE h (derived_nbhd t l)) =
                         IMAGE h (derived_dual_cell t l u INTER
                                  derived_dual_cell t l v INTER
                                  frontier (derived_nbhd t l))) /\
              (!s s'. s IN l /\ s' IN l /\ aff_dim s = &1 /\ aff_dim s' = &1 /\
                      ~(s = s') ==> DISJOINT (e s) (e s')) /\
              (!v. {v} IN l
                   ==> c v = closure (connected_component
                              (IMAGE h (derived_nbhd t l) DIFF
                               UNIONS {e s | s IN l /\ aff_dim s = &1}) (h v)) /\
                       c v INTER IMAGE h {w | {w} IN l} = {h v} /\
                       c v SUBSET nb v) /\
              IMAGE h (derived_nbhd t l) = UNIONS {c v | {v} IN l} /\
              (!v w. {v} IN l /\ {w} IN l /\ ~(v = w)
                     ==> c v INTER c w =
                         (if segment[v,w] IN l then e(segment[v,w]) else {}))`;;

(* Moise 32.1-32.2 for any two PL 3-cells meeting in a properly embedded PL  *)
(* disk: the form the book's proof of 32.3 (p.228) applies to its small      *)
(* cells around each splitting disk; MOISE_322 is the dual-cell case.        *)

let MOISE_322_CELLS_STATEMENT = new_definition
 `MOISE_322_CELLS_STATEMENT <=>
    !(c1:real^3->bool) (c2:real^3->bool) (dd:real^3->bool) (jj:real^3->bool)
     (p:real^3) (q1:real^3) (q2:real^3) (h:real^3->real^3) (w:real^3->bool).
        pl_ball 3 c1 /\ pl_ball 3 c2 /\ pl_ball 3 (c1 UNION c2) /\
        c1 INTER c2 = dd /\ pl_cell_with_boundary 2 dd jj /\
        dd INTER frontier (c1 UNION c2) = jj /\
        p IN dd DIFF jj /\ q1 IN c1 DIFF dd /\ q2 IN c2 DIFF dd /\
        h continuous_on (c1 UNION c2) /\
        (!x y. x IN c1 UNION c2 /\ y IN c1 UNION c2 /\ h x = h y ==> x = y) /\
        closed w /\ w SUBSET IMAGE h (c1 UNION c2) /\
        (IMAGE h (dd DIFF jj) DELETE h p) SUBSET interior w /\
        w INTER frontier (IMAGE h (c1 UNION c2)) = IMAGE h jj
        ==> ?e u1 u2.
              pseudo_cell e (IMAGE h jj) (h p) /\ e SUBSET w /\
              components (IMAGE h (c1 UNION c2) DIFF e) = {u1,u2} /\
              h q1 IN u1 /\ h q2 IN u2 /\ ~(u1 = u2) /\
              e SUBSET frontier u1 /\ e SUBSET frontier u2 /\
              IMAGE h (frontier c1 DIFF (dd DIFF jj)) SUBSET frontier u1 /\
              IMAGE h (frontier c2 DIFF (dd DIFF jj)) SUBSET frontier u2`;;

(* 32.4 (p.228): a pseudo-cell is cut near its centre by a polyhedral disk; *)
(* the conclusion dd SUBSET ball(p,d) is given by the proof and needed on    *)
(* pp.233, 238 (missing from the printed statement).                         *)

let MOISE_324_STATEMENT = new_definition
 `MOISE_324_STATEMENT <=>
    !(e:real^3->bool) j p d.
        pseudo_cell e j p /\ &0 < d
        ==> ?a jj dd. pl_cell_with_boundary 2 a jj /\ a SUBSET ball(p,d) /\
                      a INTER e = jj /\ dd SUBSET e INTER ball(p,d) /\
                      disk_with_boundary dd jj /\ p IN dd DIFF jj`;;

(* ------------------------------------------------------------------------- *)
(* L26-28. Moise 26.4 in open subsets of real^3 (the form used on pp.216,    *)
(* 217, 234), 26.6 (p.194), 27.3 (p.199, used by 35.1), 28.8 (used by 34.1, *)
(* Lemma 11).  Combinatorial surfaces: |c| for a finite combinatorial_       *)
(* manifold 2 c.                                                             *)
(* ------------------------------------------------------------------------- *)

let MOISE_264_OPEN_STATEMENT = new_definition
 `MOISE_264_OPEN_STATEMENT <=>
    !(u:real^3->bool) (c:(real^3->bool)->bool) (p:real^1->real^3).
        open u /\ FINITE c /\ combinatorial_manifold 2 c /\
        connected (UNIONS c) /\ UNIONS c SUBSET u /\
        path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p /\
        homotopic_loops u p (linepath(pathstart p,pathstart p)) /\
        ~homotopic_loops (UNIONS c) p (linepath(pathstart p,pathstart p))
        ==> ?(k:real^3->bool) d f g.
              &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\ d SUBSET u /\
              d INTER UNIONS c = IMAGE f (relative_frontier k) /\
              ~(?a. homotopic_with (\h. T)
                      (subtopology euclidean (IMAGE f (relative_frontier k)),
                       subtopology euclidean (UNIONS c))
                      (\x. x) (\x. a))`;;

let MOISE_266_STATEMENT = new_definition
 `MOISE_266_STATEMENT <=>
    !c:(real^3->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
        ~(UNIONS c = {})
        ==> ?b. components ((:real^3) DIFF UNIONS c) = {b, outside (UNIONS c)} /\
                bounded b /\ ~(b = outside (UNIONS c)) /\
                frontier b = UNIONS c /\ frontier (outside (UNIONS c)) = UNIONS c`;;

let pl_annulus = new_definition
 `pl_annulus (a:real^N->bool) <=>
    ?f g. pl_homeomorphism
            (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
             interval(--vector[&1;&1]:real^2,vector[&1;&1]),a) (f,g)`;;

let MOISE_273_STATEMENT = new_definition
 `MOISE_273_STATEMENT (u:N->bool) <=>
    !a j:real^N->bool.
        pl_annulus a /\ pl_sphere 1 j /\ j SUBSET a
        ==> (?d. pl_cell_with_boundary 2 d j /\ d SUBSET a) \/ loops_carried j a`;;

map type_of [`MOISE_302_STATEMENT`; `MOISE_306_STATEMENT`; `MOISE_307_STATEMENT`;
             `MOISE_308_STATEMENT`; `MOISE_322_STATEMENT`; `MOISE_323_STATEMENT`;
             `MOISE_324_STATEMENT`; `MOISE_264_OPEN_STATEMENT`;
             `MOISE_266_STATEMENT`; `MOISE_273_STATEMENT (:3)`];;

(* ------------------------------------------------------------------------- *)
(* D5. Combinatorial 3-manifolds: the boundary (union of the                 *)
(* 2-simplices that are faces of exactly one 3-simplex; DG boundaryComplex, *)
(* PL/ManifoldWithBoundary.lean:91) and coherent orientations (signs on     *)
(* ordered vertex quadruples of 3-simplices, alternating, opposite on two   *)
(* 3-simplices with a common 2-face; Moise p.170, DG IsOrientable,          *)
(* PL/Orientation.lean:439).  In real^3 the sign of a determinant works.    *)
(* ------------------------------------------------------------------------- *)

let complex_boundary = new_definition
 `complex_boundary (c:(real^N->bool)->bool) =
    UNIONS {s | s IN c /\ aff_dim s = &2 /\
                CARD {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1}`;;

let orientable_complex = new_definition
 `orientable_complex (c:(real^N->bool)->bool) <=>
    ?sg:real^N->real^N->real^N->real^N->real.
      (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                 ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                     sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                     sg a b e d = --(sg a b d e)) /\
      (!a b d e e'. ~(e = e') /\
                    convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
                    convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3
                    ==> sg a b d e' = --(sg a b d e))`;;

(* ------------------------------------------------------------------------- *)
(* L25. The loop theorem.  LOOP_THEOREM_3_STATEMENT (pc_moi_stmt.ml) is      *)
(* the case of complexes in real^3; the internal form is for orientable     *)
(* finite complexes in real^N, 7 <= dimindex(:N), where covers and doubles  *)
(* are re-realized.  Moise 25.2 (p.183; orientability is a hypothesis of    *)
(* the printed 25.2 and of DG Moise252, MoiseChain.lean:33).                *)
(* ------------------------------------------------------------------------- *)

let LOOP_THEOREM_N_STATEMENT = new_definition
 `LOOP_THEOREM_N_STATEMENT (u:N->bool) <=>
    7 <= dimindex(:N)
    ==> !(c:(real^N->bool)->bool) b (p:real^1->real^N).
          FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
          orientable_complex c /\ b IN components (complex_boundary c) /\
          path p /\ path_image p SUBSET b /\ pathfinish p = pathstart p /\
          homotopic_loops (UNIONS c) p (linepath(pathstart p,pathstart p)) /\
          ~homotopic_loops b p (linepath(pathstart p,pathstart p))
          ==> ?(k:real^N->bool) d f g.
                &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\
                d SUBSET UNIONS c /\
                d INTER complex_boundary c = IMAGE f (relative_frontier k) /\
                IMAGE f (relative_frontier k) SUBSET b /\
                ~(?a. homotopic_with (\h. T)
                        (subtopology euclidean (IMAGE f (relative_frontier k)),
                         subtopology euclidean b)
                        (\x. x) (\x. a))`;;

(* The source triangle of singular disks and its boundary loop.             *)

let std_triangle = new_definition
 `std_triangle = convex hull {vec 0:real^2, basis 1, basis 2}`;;

let std_triangle_loop = new_definition
 `std_triangle_loop =
    linepath(vec 0:real^2,basis 1) ++ linepath(basis 1,basis 2) ++
    linepath(basis 2,vec 0)`;;

let simplicial_map_on = new_definition
 `simplicial_map_on (k:(real^M->bool)->bool) (c:(real^N->bool)->bool)
                    (f:real^M->real^N) <=>
    !s. s IN k ==> IMAGE f s IN c /\
                   ?l y. linear l /\ !x. x IN s ==> f x = l x + y`;;

(* Moise Lemma 25.3 (p.188) in map form: the statement proved by strong     *)
(* induction on the number of vertex pairs identified by f (the tower of    *)
(* double covers, pp.188-190).  A normal system: c a finite orientable      *)
(* combinatorial 3-manifold with boundary carrying all loops of |c| on the  *)
(* image of the simplicial singular disk f (the book: c a regular           *)
(* neighbourhood of the image), f proper (its preimage of the boundary is   *)
(* the boundary of the triangle), b1 the boundary simplices meeting the     *)
(* boundary loop, and g a continuous map of b1 into a set v.  The normal    *)
(* subgroup N_1 of the book is the kernel of the map induced by g: the       *)
(* loop condition is that g of the loop is not null-homotopic in             *)
(* v.  For the original theorem g is the inclusion of b1 into the boundary  *)
(* component; covers compose g with the covering projection.                *)

let LOOP_NORMAL_SYSTEM_STATEMENT = new_definition
 `LOOP_NORMAL_SYSTEM_STATEMENT (u:N->bool) (w:M->bool) <=>
    7 <= dimindex(:N)
    ==> !(c:(real^N->bool)->bool) (k:(real^2->bool)->bool) (f:real^2->real^N)
         (b1:real^N->bool) (g:real^N->real^M) (v:real^M->bool).
          FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
          orientable_complex c /\
          simplicial_complex k /\ UNIONS k = std_triangle /\
          simplicial_map_on k c f /\
          {x | x IN std_triangle /\ f x IN complex_boundary c} =
          relative_frontier std_triangle /\
          loops_carried (IMAGE f std_triangle) (UNIONS c) /\
          b1 = UNIONS {s | s IN c /\ s SUBSET complex_boundary c /\
                           ~(s INTER IMAGE f (relative_frontier std_triangle) = {})} /\
          g continuous_on b1 /\ IMAGE g b1 SUBSET v /\
          ~homotopic_loops v (g o f o std_triangle_loop)
                             (linepath(g(f(vec 0)),g(f(vec 0))))
          ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
                pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
                d INTER complex_boundary c = IMAGE e (relative_frontier std_triangle) /\
                IMAGE e (relative_frontier std_triangle) SUBSET b1 /\
                ~homotopic_loops v (g o e o std_triangle_loop)
                                   (linepath(g(e(vec 0)),g(e(vec 0))))`;;

(* Glue: the R^3 form LOOP_THEOREM_3_STATEMENT from the internal form        *)
(* (embedding real^3 into real^7; orientation by the sign of a determinant;  *)
(* boundary = frontier).                                                     *)

let MOI_CORE_GLUE_LOOP3 =
 `LOOP_THEOREM_N_STATEMENT (:7) ==> LOOP_THEOREM_3_STATEMENT`;;

let MOI_CORE_GLUE_LOOPN =
 `!u:N->bool. LOOP_NORMAL_SYSTEM_STATEMENT u u ==> LOOP_THEOREM_N_STATEMENT u`;;

let MOI_CORE_GLUE_264 =
 `LOOP_THEOREM_3_STATEMENT ==> MOISE_264_OPEN_STATEMENT`;;

map type_of [MOI_CORE_GLUE_LOOP3; MOI_CORE_GLUE_LOOPN; MOI_CORE_GLUE_264];;

(* ------------------------------------------------------------------------- *)
(* L30-3. Moise 30.3 (p.215), the cut-and-cap of a separating set across a  *)
(* disk with two adjacent sheets, in the explicit form of DG Moise303       *)
(* (MoiseChain.lean:272): inside a small open w the annulus a1 of d1 around *)
(* the disk a is replaced by a disk delta1 capping its outer boundary.      *)
(* Used by 30.4, 30.6, 30.7 and in the proof of 32.1 (p.226).               *)
(* ------------------------------------------------------------------------- *)

let pl_annulus_with_ends = new_definition
 `pl_annulus_with_ends (a:real^N->bool) (j0:real^N->bool) (j1:real^N->bool) <=>
    ?f g. pl_homeomorphism
            (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
             interval(--vector[&1;&1]:real^2,vector[&1;&1]),a) (f,g) /\
          j0 = IMAGE f (relative_frontier (interval[--vector[&1;&1]:real^2,
                                                    vector[&1;&1]])) /\
          j1 = IMAGE f (relative_frontier (interval[--vector[&2;&2]:real^2,
                                                    vector[&2;&2]]))`;;

let MOISE_303_STATEMENT = new_definition
 `MOISE_303_STATEMENT <=>
    !(m:real^3->bool) h k c a ja d1 jd1 d2 jd2 w.
        open m /\ connected m /\
        closed_in (subtopology euclidean m) h /\
        closed_in (subtopology euclidean m) k /\
        closed_in (subtopology euclidean m) c /\
        DISJOINT h k /\ DISJOINT c (h UNION k) /\ separates_in m c h k /\
        pl_cell_with_boundary 2 a ja /\ pl_cell_with_boundary 2 d1 jd1 /\
        pl_cell_with_boundary 2 d2 jd2 /\
        d1 INTER d2 = a /\ d1 UNION d2 SUBSET c /\
        a SUBSET (subtopology euclidean c) interior_of (d1 UNION d2) /\
        DISJOINT a jd1 /\ DISJOINT a jd2 /\
        open w /\ a SUBSET w /\ w SUBSET m /\ DISJOINT w (h UNION k)
        ==> ?c' a1 j1 delta1.
              closed_in (subtopology euclidean m) c' /\ separates_in m c' h k /\
              c' DIFF w = c DIFF w /\ d2 SUBSET c' /\
              pl_annulus_with_ends a1 ja j1 /\ a1 SUBSET d1 INTER w /\
              a1 INTER a = ja /\
              pl_cell_with_boundary 2 delta1 j1 /\ delta1 SUBSET w /\
              delta1 INTER c = j1 /\
              c' = (c DIFF (a1 DIFF (ja UNION j1))) UNION delta1`;;

(* 28.6 (p.205): disjoint essential polygons in the boundary of a PL solid  *)
(* torus cut it into PL annuli (DG Moise286, MoiseChain.lean:295).          *)

let MOISE_286_STATEMENT = new_definition
 `MOISE_286_STATEMENT <=>
    !(s:real^3->bool) (gg:(real^3->bool)->bool).
        pl_solid_torus s /\ FINITE gg /\ 2 <= CARD gg /\
        (!j. j IN gg ==> pl_sphere 1 j /\ j SUBSET frontier s) /\
        pairwise DISJOINT gg /\
        (!j d. j IN gg /\ d SUBSET frontier s ==> ~pl_cell_with_boundary 2 d j)
        ==> !x. x IN frontier s DIFF UNIONS gg
                ==> ?j0 j1. j0 IN gg /\ j1 IN gg /\ ~(j0 = j1) /\
                            pl_annulus_with_ends
                              (closure (connected_component
                                          (frontier s DIFF UNIONS gg) x)) j0 j1`;;

(* 26.7 (p.195; DG Moise267, MoiseChain.lean:306, with the compactness and  *)
(* nonempty common boundary that the printed statement omits): three       *)
(* connected compact surfaces with common boundary and disjoint interiors. *)
(* Surfaces with boundary: |c| for finite combinatorial 2-manifolds with   *)
(* boundary; their boundary is the union of the edges in one triangle.     *)

let surface_boundary = new_definition
 `surface_boundary (c:(real^N->bool)->bool) =
    UNIONS {s | s IN c /\ aff_dim s = &1 /\
                CARD {r | r IN c /\ aff_dim r = &2 /\ s SUBSET r} = 1}`;;

let MOISE_267_STATEMENT = new_definition
 `MOISE_267_STATEMENT <=>
    !(c:num->(real^3->bool)->bool) x.
        (!i. i < 3 ==> FINITE (c i) /\ combinatorial_manifold_with_boundary 2 (c i) /\
                       connected (UNIONS (c i))) /\
        (!i j. i < 3 /\ j < 3 ==> surface_boundary (c i) = surface_boundary (c j)) /\
        ~(surface_boundary (c 0) = {}) /\
        (!i j. i < 3 /\ j < 3 /\ ~(i = j)
               ==> DISJOINT (UNIONS (c i) DIFF surface_boundary (c i))
                            (UNIONS (c j) DIFF surface_boundary (c j))) /\
        ~(x IN UNIONS {UNIONS (c i) | i < 3}) /\
        ~bounded (connected_component ((:real^3) DIFF UNIONS {UNIONS (c i) | i < 3}) x)
        ==> ?i j k. i < 3 /\ j < 3 /\ k < 3 /\ ~(i = j) /\ ~(j = k) /\ ~(i = k) /\
                    frontier (connected_component
                                ((:real^3) DIFF UNIONS {UNIONS (c i) | i < 3}) x) =
                    UNIONS (c i) UNION UNIONS (c j) /\
                    !y. y IN UNIONS (c k) DIFF surface_boundary (c k)
                        ==> bounded (connected_component
                                       ((:real^3) DIFF (UNIONS (c i) UNION UNIONS (c j)))
                                       y)`;;

(* ------------------------------------------------------------------------- *)
(* L31. Canonical configurations (pp.220-221): planar 2-cells dd 0..2 with  *)
(* points p 0..3 in the half plane x3 = 0, x1 > 0, revolved about the x2    *)
(* axis; an embedding h of the union; PL solid tori s2 j between h(A_j) and *)
(* h(S_j) with boundaries crossing transversally.  31.1 (existence, from    *)
(* 30.7) and 31.4 (the dichotomy used in the proof of 32.1, p.225).         *)
(* ------------------------------------------------------------------------- *)

let revolution = new_definition
 `revolution (x:real^3->bool) =
    {p:real^3 | ?q. q IN x /\ q$3 = &0 /\ &0 <= q$1 /\ q$2 = p$2 /\
                    q$1 pow 2 = p$1 pow 2 + p$3 pow 2}`;;

let pl_crossing_at = new_definition
 `pl_crossing_at (s:real^3->bool) (t:real^3->bool) (x:real^3) <=>
    ?u f g. open u /\ x IN u /\ pl_homeomorphism (u,IMAGE f u) (f,g) /\
            open (IMAGE f u) /\ f x = vec 0 /\
            IMAGE f (s INTER u) = IMAGE f u INTER {y:real^3 | y$1 = &0} /\
            IMAGE f (t INTER u) = IMAGE f u INTER {y:real^3 | y$2 = &0}`;;

let planar_cell_chain = new_definition
 `planar_cell_chain (p:num->real^3) (dd:num->real^3->bool) <=>
    (!j. j < 3 ==> dd j SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
                   disk_with_boundary (dd j) (dd j DIFF relative_interior (dd j)) /\
                   ~(p j = p (j + 1)) /\
                   segment[p j,p (j + 1)] SUBSET relative_interior (dd j)) /\
    (!j. j < 2 ==> ?jj. disk_with_boundary (dd j INTER dd (j + 1)) jj) /\
    dd 0 INTER dd 2 = {}`;;

let canonical_configuration = new_definition
 `canonical_configuration (p:num->real^3) (dd:num->real^3->bool)
                          (h:real^3->real^3) (s2:num->real^3->bool) <=>
    planar_cell_chain p dd /\
    h continuous_on UNIONS {revolution (dd j) | j < 3} /\
    (!x y. x IN UNIONS {revolution (dd j) | j < 3} /\
           y IN UNIONS {revolution (dd j) | j < 3} /\ h x = h y ==> x = y) /\
    (!j. j < 3 ==> pl_solid_torus (s2 j) /\
                   IMAGE h (revolution (segment[p j,p (j + 1)])) SUBSET interior (s2 j) /\
                   s2 j SUBSET interior (IMAGE h (revolution (dd j)))) /\
    (!j x. j < 2 /\ x IN frontier (s2 j) INTER frontier (s2 (j + 1))
           ==> pl_crossing_at (frontier (s2 j)) (frontier (s2 (j + 1))) x)`;;

let MOISE_311_STATEMENT = new_definition
 `MOISE_311_STATEMENT <=>
    !(p:num->real^3) (dd:num->real^3->bool) (h:real^3->real^3).
        planar_cell_chain p dd /\
        h continuous_on UNIONS {revolution (dd j) | j < 3} /\
        (!x y. x IN UNIONS {revolution (dd j) | j < 3} /\
               y IN UNIONS {revolution (dd j) | j < 3} /\ h x = h y ==> x = y)
        ==> ?s2. canonical_configuration p dd h s2`;;

let MOISE_314_STATEMENT = new_definition
 `MOISE_314_STATEMENT <=>
    !(p:num->real^3) (dd:num->real^3->bool) (h:real^3->real^3) s2 j gg.
        canonical_configuration p dd h s2 /\ j < 2 /\ pl_sphere 1 gg /\
        gg SUBSET frontier (s2 j) INTER frontier (s2 (j + 1))
        ==> (loops_carried gg (s2 j) /\ loops_carried gg (s2 (j + 1))) \/
            ((?d. d SUBSET frontier (s2 j) /\ pl_cell_with_boundary 2 d gg) /\
             (?d. d SUBSET frontier (s2 (j + 1)) /\ pl_cell_with_boundary 2 d gg))`;;

map type_of [`MOISE_303_STATEMENT`; `MOISE_286_STATEMENT`; `MOISE_267_STATEMENT`;
             `MOISE_311_STATEMENT`; `MOISE_314_STATEMENT`];;

(* ------------------------------------------------------------------------- *)
(* D6. Integral H_1 statements via HOL singular homology (homology.ml):     *)
(* carries_h1 j s: the inclusion induces a surjection H_1(j) -> H_1(s); for  *)
(* s with H_1 infinite cyclic this is the book's j carries a generator of    *)
(* H_1(s) (p.198).  Surface orientability as for 3-complexes.                *)
(* ------------------------------------------------------------------------- *)

let carries_h1 = new_definition
 `carries_h1 (j:real^N->bool) (s:real^N->bool) <=>
    group_image (homology_group(&1,subtopology euclidean j),
                 homology_group(&1,subtopology euclidean s))
                (hom_induced (&1) (subtopology euclidean j,{})
                                  (subtopology euclidean s,{}) (\x. x)) =
    group_carrier (homology_group(&1,subtopology euclidean s))`;;

let orientable_surface_complex = new_definition
 `orientable_surface_complex (c:(real^N->bool)->bool) <=>
    ?sg:real^N->real^N->real^N->real.
      (!a b d. convex hull {a,b,d} IN c /\ aff_dim(convex hull {a,b,d}) = &2
               ==> (sg a b d = &1 \/ sg a b d = -- &1) /\
                   sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)) /\
      (!a b d d'. ~(d = d') /\
                  convex hull {a,b,d} IN c /\ aff_dim(convex hull {a,b,d}) = &2 /\
                  convex hull {a,b,d'} IN c /\ aff_dim(convex hull {a,b,d'}) = &2
                  ==> sg a b d' = --(sg a b d))`;;

(* 26.8 (p.195): compact connected polyhedral surfaces in real^3 are        *)
(* orientable (used in 33.1, Lemmas 11-13, pp.236-238).                     *)

let MOISE_268_STATEMENT = new_definition
 `MOISE_268_STATEMENT <=>
    !c:(real^3->bool)->bool.
        FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c)
        ==> orientable_surface_complex c`;;

(* 28.8 in the form used in 34.1, Lemma 11 (p.244): if disjoint polygons in *)
(* the boundary of a PL solid torus together carry a generator of H_1, then *)
(* each carries a generator or bounds a PL disk in the boundary (the printed *)
(* 28.8, p.204, assumes no polygon is null-homologous in the solid torus;   *)
(* the used form also needs 28.6 and 28.9).                                  *)

let MOISE_288_STATEMENT = new_definition
 `MOISE_288_STATEMENT <=>
    !(s:real^3->bool) (jj:(real^3->bool)->bool).
        pl_solid_torus s /\ FINITE jj /\ pairwise DISJOINT jj /\
        (!j. j IN jj ==> pl_sphere 1 j /\ j SUBSET frontier s) /\
        carries_h1 (UNIONS jj) s
        ==> !j. j IN jj
                ==> carries_h1 j s \/
                    ?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d j`;;

map type_of [`MOISE_268_STATEMENT`; `MOISE_288_STATEMENT`];;

(* ------------------------------------------------------------------------- *)
(* 30.1 (p.214) and 28.10 (p.204; cited as 28.9 on p.222), used inside 32.1 *)
(* (Type 1, p.226) and 31.4.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOISE_301_STATEMENT = new_definition
 `MOISE_301_STATEMENT <=>
    !(x:real^3->bool) c d h k.
        open x /\ simply_connected x /\
        closed_in (subtopology euclidean x) c /\
        closed_in (subtopology euclidean x) d /\
        closed_in (subtopology euclidean x) h /\
        closed_in (subtopology euclidean x) k /\
        connected h /\ connected k /\ ~(h = {}) /\ ~(k = {}) /\
        DISJOINT c d /\ DISJOINT h k /\
        DISJOINT c h /\ DISJOINT c k /\ DISJOINT d h /\ DISJOINT d k /\
        separates_in x (c UNION d) h k
        ==> separates_in x c h k \/ separates_in x d h k`;;

let MOISE_2810_STATEMENT = new_definition
 `MOISE_2810_STATEMENT <=>
    !(s:real^3->bool) k j.
        pl_solid_torus s /\ pl_polyhedron k /\ k SUBSET frontier s /\
        carries_h1 k s /\ pl_sphere 1 j /\ j SUBSET frontier s DIFF k /\
        ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d j)
        ==> carries_h1 j s`;;

(* ------------------------------------------------------------------------- *)
(* P. The producer graph: each producer is one implication, from statement   *)
(* constants of lower levels and foundation lemmas; with the producers and   *)
(* the leaves, MOISE_352_COMPLEX_STATEMENT (:7) follows                      *)
(* (MOI_CD_BLUEPRINT_CLOSURE below).                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_PROD_351 =
 `!u:N->bool. MOISE_341_STATEMENT /\ MOISE_305_STATEMENT /\
              MOISE_273_STATEMENT (:3) /\ PL_SCHOENFLIES_3_STATEMENT /\
              MOISE_CELL_ASSEMBLY_ON_STATEMENT (:real^N->bool) u
              ==> MOISE_351_STATEMENT u`;;

let MOI_PROD_34_EXT =
 `!u:N->bool. MOISE_305_STATEMENT /\ MOISE_308_STATEMENT /\ MOISE_288_STATEMENT /\
              PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\
              MOISE_CELL_ASSEMBLY_ON_STATEMENT (:real^N->bool) u
              ==> MOISE_34_EXT_STATEMENT u`;;

let MOI_PROD_331 =
 `MOISE_323_STATEMENT /\ MOISE_324_STATEMENT /\ MOISE_264_OPEN_STATEMENT /\
  MOISE_302_STATEMENT /\ MOISE_266_STATEMENT /\ MOISE_268_STATEMENT /\
  PL_SCHOENFLIES_3_STATEMENT /\ MOISE_CELL_ASSEMBLY_ON_STATEMENT (:real^3->bool) (:3)
  ==> MOISE_331_STATEMENT`;;

let MOI_PROD_323 = `MOISE_322_CELLS_STATEMENT ==> MOISE_323_STATEMENT`;;

let MOI_PROD_322_CELLS =
 `MOISE_311_STATEMENT /\ MOISE_314_STATEMENT /\ MOISE_303_STATEMENT /\
  MOISE_301_STATEMENT /\ MOISE_286_STATEMENT /\ MOISE_267_STATEMENT
  ==> MOISE_322_CELLS_STATEMENT`;;

let MOI_PROD_322 = `MOISE_322_CELLS_STATEMENT ==> MOISE_322_STATEMENT`;;

let MOI_PROD_311 = `MOISE_307_STATEMENT ==> MOISE_311_STATEMENT`;;

let MOI_PROD_314 =
 `MOISE_308_STATEMENT /\ MOISE_2810_STATEMENT ==> MOISE_314_STATEMENT`;;

let MOI_PROD_302 = `MOISE_301_STATEMENT ==> MOISE_302_STATEMENT`;;

let MOI_PROD_304 =
 `MOISE_264_OPEN_STATEMENT /\ MOISE_302_STATEMENT /\ MOISE_303_STATEMENT
  ==> MOISE_304_STATEMENT`;;

let MOI_PROD_305 =
 `MOISE_304_STATEMENT /\ PL_SCHOENFLIES_3_STATEMENT ==> MOISE_305_STATEMENT`;;

let MOI_PROD_306 =
 `MOISE_264_OPEN_STATEMENT /\ MOISE_302_STATEMENT /\ MOISE_303_STATEMENT
  ==> MOISE_306_STATEMENT`;;

let MOI_PROD_307 =
 `MOISE_306_STATEMENT /\ MOISE_264_OPEN_STATEMENT /\ MOISE_303_STATEMENT /\
  MOISE_266_STATEMENT /\ PL_SCHOENFLIES_3_STATEMENT
  ==> MOISE_307_STATEMENT`;;

let MOI_PROD_264 = `LOOP_THEOREM_3_STATEMENT ==> MOISE_264_OPEN_STATEMENT`;;

map type_of [MOI_PROD_351; MOI_PROD_34_EXT; MOI_PROD_331; MOI_PROD_323;
             MOI_PROD_322; MOI_PROD_311; MOI_PROD_314; MOI_PROD_302;
             MOI_PROD_304; MOI_PROD_305; MOI_PROD_306; MOI_PROD_307;
             MOI_PROD_264];;

(* ------------------------------------------------------------------------- *)
(* L25b. The three steps of the tower (Moise pp.183-190) in map form.       *)
(* LOOP_SPHERE_CASE: Lemma 25.1 (p.183): if the boundary component through  *)
(* the loop is a PL 2-sphere, a hole of the boundary neighbourhood b1 gives *)
(* the disk (in map form: if g killed every hole loop it would kill the     *)
(* loop, since the sphere is simply connected; no van Kampen needed).        *)
(* DOUBLE_COVER: 24.8 (p.178) with 23.19: a connected orientable compact    *)
(* combinatorial 3-manifold with a non-spherical boundary component has a   *)
(* connected orientable 2-sheeted simplicial covering, re-realized in       *)
(* real^N.  LOOP_DESCENT: Lemma 25.2 (p.184), orientable                     *)
(* case (Case 1 cannot occur): a locally injective, at most two-to-one PL   *)
(* singular disk with boundary in the interior of b1 gives an embedded one; *)
(* general position (normal singular disks) and the cut and paste of Cases  *)
(* 2-4 are inside its proof (DG does them in the double 2V).                *)
(* ------------------------------------------------------------------------- *)

let LOOP_SPHERE_CASE_STATEMENT = new_definition
 `LOOP_SPHERE_CASE_STATEMENT (u:N->bool) (w:M->bool) <=>
    !(c:(real^N->bool)->bool) b (cb:(real^N->bool)->bool) (p:real^1->real^N)
     (g:real^N->real^M) (v:real^M->bool).
        FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
        b IN components (complex_boundary c) /\ pl_sphere 2 b /\
        cb SUBSET c /\ UNIONS cb SUBSET b /\
        path p /\ pathfinish p = pathstart p /\
        path_image p SUBSET (subtopology euclidean b) interior_of (UNIONS cb) /\
        g continuous_on UNIONS cb /\ IMAGE g (UNIONS cb) SUBSET v /\
        ~homotopic_loops v (g o p) (linepath(g(pathstart p),g(pathstart p)))
        ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
              pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
              d INTER complex_boundary c = IMAGE e (relative_frontier std_triangle) /\
              IMAGE e (relative_frontier std_triangle) SUBSET UNIONS cb /\
              ~homotopic_loops v (g o e o std_triangle_loop)
                                 (linepath(g(e(vec 0)),g(e(vec 0))))`;;

let DOUBLE_COVER_STATEMENT = new_definition
 `DOUBLE_COVER_STATEMENT (u:N->bool) <=>
    7 <= dimindex(:N)
    ==> !c:(real^N->bool)->bool.
          FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
          orientable_complex c /\ connected (UNIONS c) /\
          (?b. b IN components (complex_boundary c) /\ ~pl_sphere 2 b)
          ==> ?(c':(real^N->bool)->bool) (q:real^N->real^N).
                FINITE c' /\ combinatorial_manifold_with_boundary 3 c' /\
                orientable_complex c' /\ connected (UNIONS c') /\
                simplicial_map_on c' c q /\
                covering_space (UNIONS c',q) (UNIONS c) /\
                (!y. y IN UNIONS c
                     ==> {x | x IN UNIONS c' /\ q x = y} HAS_SIZE 2)`;;

let LOOP_DESCENT_STATEMENT = new_definition
 `LOOP_DESCENT_STATEMENT (u:N->bool) (w:M->bool) <=>
    7 <= dimindex(:N)
    ==> !(c:(real^N->bool)->bool) (f:real^2->real^N) (b1:real^N->bool)
         (g:real^N->real^M) (v:real^M->bool).
          FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
          orientable_complex c /\
          pl_map_on std_triangle f /\ IMAGE f std_triangle SUBSET UNIONS c /\
          {x | x IN std_triangle /\ f x IN complex_boundary c} =
          relative_frontier std_triangle /\
          (!x. x IN std_triangle
               ==> ?n. open n /\ x IN n /\
                       !y z. y IN n INTER std_triangle /\ z IN n INTER std_triangle /\
                             f y = f z ==> y = z) /\
          (!y. FINITE {x | x IN std_triangle /\ f x = y} /\
               CARD {x | x IN std_triangle /\ f x = y} <= 2) /\
          b1 SUBSET complex_boundary c /\ closed b1 /\
          IMAGE f (relative_frontier std_triangle) SUBSET
          (subtopology euclidean (complex_boundary c)) interior_of b1 /\
          g continuous_on b1 /\ IMAGE g b1 SUBSET v /\
          ~homotopic_loops v (g o f o std_triangle_loop)
                             (linepath(g(f(vec 0)),g(f(vec 0))))
          ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
                pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
                d INTER complex_boundary c = IMAGE e (relative_frontier std_triangle) /\
                IMAGE e (relative_frontier std_triangle) SUBSET b1 /\
                ~homotopic_loops v (g o e o std_triangle_loop)
                                   (linepath(g(e(vec 0)),g(e(vec 0))))`;;

let MOI_PROD_LOOP_NS =
 `!(u:N->bool) (w:M->bool).
     LOOP_SPHERE_CASE_STATEMENT u w /\ DOUBLE_COVER_STATEMENT u /\
     LOOP_DESCENT_STATEMENT u w
     ==> LOOP_NORMAL_SYSTEM_STATEMENT u w`;;

map type_of [MOI_PROD_LOOP_NS];;

(* Small sanity checks of the definitions.                                  *)

let MOI_CD_SEPARATES_IN_UNIV = prove
 (`!c s t:real^N->bool.
     separates_in (:real^N) c s t <=> euclidean_separates c s t`,
  REWRITE_TAC[separates_in; euclidean_separates; SUBTOPOLOGY_UNIV; GSYM OPEN_IN]);;

let MOI_CD_DERIVED_NBHD_EMPTY = prove
 (`!t:(real^N->bool)->bool. derived_nbhd t {} = {}`,
  REWRITE_TAC[derived_nbhd; UNIONS_0; INTER_EMPTY; EMPTY_GSPEC] THEN
  REWRITE_TAC[UNIONS_0]);;

let MOI_CD_SKELETON_SUBSET = prove
 (`!n c:(real^N->bool)->bool. skeleton n c SUBSET c`,
  REWRITE_TAC[skeleton; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_CD_SOLID_TORUS_MODEL = prove
 (`solid_torus (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))`,
  REWRITE_TAC[solid_torus; HOMEOMORPHIC_REFL]);;

let MOI_CD_GRAPH_APPROXIMABLE_EMPTY = prove
 (`!(t:(real^N->bool)->bool) (h:real^N->real^3).
     graph_approximable t {} h`,
  REWRITE_TAC[graph_approximable; NOT_IN_EMPTY; MOI_CD_DERIVED_NBHD_EMPTY;
              UNIONS_0; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `\x:real^N. vec 0:real^3` THEN
  REWRITE_TAC[pl_map_on; NOT_IN_EMPTY]);;

map (fun th -> length (hyp th), concl th)
  [MOI_CD_SEPARATES_IN_UNIV; MOI_CD_DERIVED_NBHD_EMPTY; MOI_CD_SKELETON_SUBSET;
   MOI_CD_SOLID_TORUS_MODEL; MOI_CD_GRAPH_APPROXIMABLE_EMPTY];;

(* Closure of the producer graph: producer implications + leaves imply      *)
(* MOISE_352_COMPLEX_STATEMENT (:7).  Purely propositional; a check that the *)
(* statement constants fit together (types and names), not a proof of any  *)
(* mathematics.                                                              *)

let n7 t = inst [`:7`,`:N`] t;;
let n3 t = inst [`:3`,`:N`] t;;
let nm7 t = inst [`:7`,`:N`; `:7`,`:M`] t;;

let MOI_CD_IMPLS =
  [n7 MOI_CORE_GLUE_352; n7 MOI_PROD_351; n7 MOI_PROD_34_EXT; n3 MOI_PROD_34_EXT;
   MOI_CORE_GLUE_341; MOI_CORE_GLUE_341_NBHD; MOI_PROD_331; MOI_PROD_323;
   MOI_PROD_322_CELLS; MOI_PROD_311; MOI_PROD_314; MOI_PROD_302; MOI_PROD_304;
   MOI_PROD_305; MOI_PROD_306; MOI_PROD_307; MOI_PROD_264; MOI_CORE_GLUE_264;
   MOI_CORE_GLUE_LOOP3; n7 MOI_CORE_GLUE_LOOPN; nm7 MOI_PROD_LOOP_NS];;

let MOI_CD_LEAVES =
  [`MOISE_301_STATEMENT`; `MOISE_303_STATEMENT`; `MOISE_308_STATEMENT`;
   `MOISE_2810_STATEMENT`; `MOISE_286_STATEMENT`; `MOISE_267_STATEMENT`;
   `MOISE_266_STATEMENT`; `MOISE_268_STATEMENT`; `MOISE_324_STATEMENT`;
   `MOISE_273_STATEMENT (:3)`; `MOISE_288_STATEMENT`;
   `PL_SCHOENFLIES_3_STATEMENT`; `PL_SCHOENFLIES_3_AMBIENT_STATEMENT`;
   `MOISE_CELL_ASSEMBLY_ON_STATEMENT (:real^7->bool) (:7)`;
   `MOISE_CELL_ASSEMBLY_ON_STATEMENT (:real^3->bool) (:3)`;
   `LOOP_SPHERE_CASE_STATEMENT (:7) (:7)`; `DOUBLE_COVER_STATEMENT (:7)`;
   `LOOP_DESCENT_STATEMENT (:7) (:7)`];;

let MOI_CD_BLUEPRINT_CLOSURE = prove
 (mk_imp(list_mk_conj (MOI_CD_IMPLS @ MOI_CD_LEAVES),
         `MOISE_352_COMPLEX_STATEMENT (:7)`),
  STRIP_TAC THEN ASM_MESON_TAC[]);;

(length (hyp MOI_CD_BLUEPRINT_CLOSURE), length MOI_CD_IMPLS, length MOI_CD_LEAVES);;

