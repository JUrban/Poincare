(* ========================================================================= *)
(* pc_moi_fnd_stmt2: two foundation terms split off from                     *)
(* MOI_FND_DERIVED_NBHD_BALL (pc_moi_fnd_stmt.ml) for the initial cells of   *)
(* Moise Sec 34 (pc_moi_s34_cellnba).                                        *)
(*   MOI_FND_DERIVED_NBHD_SIMPLEX : the derived neighbourhood of the faces  *)
(*     of a simplex s of dimension at most 2 whose vertex links are PL      *)
(*     2-spheres is a PL 3-cell bounded by its derived frontier (Moise      *)
(*     p.155; the case of MOI_FND_DERIVED_NBHD_BALL with l the faces of s); *)
(*   MOI_FND_SIMPLEX_SMALL_CELL : such a simplex lies in the image of the   *)
(*     open simplex under a PL embedding of a 3-simplex whose image lies in *)
(*     any given relatively open set containing s.                          *)
(* Both follow from MOI_FND_DERIVED_NBHD_BALL (pc_moi_s34_cellnba.ml:        *)
(* MOI_S4C_FND_NBHD_SIMPLEX, MOI_S4C_FND_SMALL_CELL); pc_moi_fnd_rnsc proves *)
(* both directly (DERIVED_NBHD_SIMPLEX, SIMPLEX_SMALL_CELL).                 *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_FND_DERIVED_NBHD_SIMPLEX =
 `!(t:(real^N->bool)->bool) (s:real^N->bool).
     lf_simplicial_complex t /\ s IN t /\ ~(s = {}) /\ aff_dim s <= &2 /\
     (!w. {w} IN t /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link t w)))
     ==> pl_cell_with_boundary 3 (derived_nbhd t {f | f face_of s})
                                 (derived_frontier t {f | f face_of s})`;;

let MOI_FND_SIMPLEX_SMALL_CELL =
 `!(t:(real^N->bool)->bool) (s:real^N->bool) (v:real^N->bool).
     lf_simplicial_complex t /\ s IN t /\ ~(s = {}) /\ aff_dim s <= &2 /\
     (!w. {w} IN t /\ w IN s ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
     open_in (subtopology euclidean (UNIONS t)) v /\ s SUBSET v
     ==> ?k (f:real^N->real^N) g.
           &3 simplex k /\ pl_homeomorphism (k,IMAGE f k) (f,g) /\
           IMAGE f k SUBSET v /\ s SUBSET IMAGE f (relative_interior k)`;;

