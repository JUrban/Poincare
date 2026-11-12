(* ========================================================================= *)
(* pc_moi_fnd_stmt3: two foundation terms for the split of                 *)
(* MOI_FND_SPLIT_DISK_R3 (Moise 28.19-28.20, p.209).                        *)
(*   MOI_FND_DERIVED_NBHD_POLYGON_2 : the second-derived neighbourhood N of *)
(*     a polygon l in a finite closed combinatorial surface m is a compact  *)
(*     connected surface with boundary its relative frontier, chi 0, one or *)
(*     two boundary circles (as many as the components of N minus l), an   *)
(*     annulus with these ends when there are two; the closure of the      *)
(*     complement is a surface with the same boundary.  Generic (real^N);  *)
(*     pc_moi_fnd_nb2 and pc_moi_fnd_nb2f prove it (DERIVED_NBHD_POLYGON_2). *)
(*   MOI_FND_SPLIT_TRACE_ANNULUS : (28.19, with a local two-sidedness       *)
(*     argument) a PL disk |ld| meeting a closed surface |lm| of the same   *)
(*     complex exactly in its rim, its vertices with PL 2-sphere links: the *)
(*     trace of N(|ld|) on |lm| is an annulus around the rim whose ends are *)
(*     the trace of the derived frontier.  In real^3; pc_moi_fnd_sptrace    *)
(*     proves MOI_FND_DERIVED_NBHD_POLYGON_2 (at N = 3) ==>                  *)
(*     MOI_FND_SPLIT_TRACE_ANNULUS (SPLIT_TRACE_ANNULUS).                    *)
(* pc_moi_fnd_split then proves MOI_FND_SPLIT_DISK_R3 from                 *)
(* MOI_FND_DERIVED_NBHD_BALL_2 and MOI_FND_SPLIT_TRACE_ANNULUS.             *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_FND_DERIVED_NBHD_POLYGON_2 =
 `!(m:(real^N->bool)->bool) (l:(real^N->bool)->bool).
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> FINITE (derived_nbhd_complex m l) /\
         combinatorial_manifold_with_boundary 2 (derived_nbhd_complex m l) /\
         surface_boundary (derived_nbhd_complex m l) = derived_frontier m l /\
         connected (derived_nbhd m l) /\
         complex_euler (derived_nbhd_complex m l) = &0 /\
         FINITE (components (derived_frontier m l)) /\
         (CARD (components (derived_frontier m l)) = 1 \/
          CARD (components (derived_frontier m l)) = 2) /\
         (!k. k IN components (derived_frontier m l) ==> pl_sphere 1 k) /\
         CARD (components (derived_nbhd m l DIFF UNIONS l)) =
         CARD (components (derived_frontier m l)) /\
         (CARD (components (derived_frontier m l)) = 2
          ==> ?j1 j2. pl_annulus_with_ends (derived_nbhd m l) j1 j2 /\
                      derived_frontier m l = j1 UNION j2) /\
         combinatorial_manifold_with_boundary 2
           {s | s IN barycentric_subdivision (barycentric_subdivision m) /\
                s SUBSET closure (UNIONS m DIFF derived_nbhd m l)} /\
         UNIONS {s | s IN barycentric_subdivision (barycentric_subdivision m) /\
                     s SUBSET closure (UNIONS m DIFF derived_nbhd m l)} =
         closure (UNIONS m DIFF derived_nbhd m l) /\
         surface_boundary
           {s | s IN barycentric_subdivision (barycentric_subdivision m) /\
                s SUBSET closure (UNIONS m DIFF derived_nbhd m l)} =
         derived_frontier m l`;;

let MOI_FND_SPLIT_TRACE_ANNULUS =
 `!(t:(real^3->bool)->bool) (ld:(real^3->bool)->bool) (lm:(real^3->bool)->bool).
     FINITE t /\ lf_simplicial_complex t /\
     simplicial_subcomplex ld t /\ simplicial_subcomplex lm t /\
     combinatorial_manifold 2 lm /\
     pl_cell_with_boundary 2 (UNIONS ld) (UNIONS ld INTER UNIONS lm) /\
     (!v. {v} IN ld ==> pl_sphere 2 (UNIONS (simplicial_link t v)))
     ==> ?j1 j2. pl_annulus_with_ends (derived_nbhd t ld INTER UNIONS lm) j1 j2 /\
                 derived_frontier t ld INTER UNIONS lm = j1 UNION j2 /\
                 UNIONS ld INTER UNIONS lm SUBSET
                 (derived_nbhd t ld INTER UNIONS lm) DIFF (j1 UNION j2)`;;

