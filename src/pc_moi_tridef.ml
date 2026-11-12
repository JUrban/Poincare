(* ========================================================================= *)
(* pc_moi_tridef: the shared notion of a PL triangulation of a subset of a  *)
(* PL manifold (Moise Sec 7: a PL complex in a space, realized as a          *)
(* Euclidean complex in real^N, Thm 7.5).  c is a locally finite complex,   *)
(* t maps UNIONS c homeomorphically onto s (in the subspace topology), and  *)
(* t is PL in every chart: phi o t is PL where it is defined.               *)
(* Used by pc_moi_ptri (existence, compact case) and pc_moi_comb (vertex    *)
(* links are PL 2-spheres).                                                  *)
(* ========================================================================= *)

needs "src/pc_moi_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let pl_triangulation = new_definition
 `pl_triangulation (top:A topology) (atlas:((A->bool)#(A->real^M))->bool)
                   (c:(real^N->bool)->bool) (t:real^N->A) (s:A->bool) <=>
    lf_simplicial_complex c /\
    homeomorphic_map (subtopology euclidean (UNIONS c),subtopology top s) t /\
    !U phi. (U,phi) IN atlas
            ==> ?g. pl_map_on {x | x IN UNIONS c /\ t x IN U} g /\
                    !x. x IN UNIONS c /\ t x IN U ==> g x = phi(t x)`;;

