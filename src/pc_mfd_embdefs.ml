(* ========================================================================= *)
(* pc_mfd_embdefs: definitions for embeddings of manifolds into real^K:      *)
(* embeddings, the chart Jacobian of an embedding in the preferred chart,    *)
(* the orthogonal projection onto the tangent space of the image, and the    *)
(* inverse on the image.  Nearest points use the library constant            *)
(* closest_point.  Definitions only; the theory is in pc_mfd_embed and the   *)
(* files built on it.                                                        *)
(* ========================================================================= *)

needs "src/pc_mfd_maps.ml";;
needs "src/pc_mfd_riem.ml";;

prioritize_real();;
type_invention_error := true;;

(* Smooth embeddings: immersions that are homeomorphisms onto the image.    *)

let mfd_embedding = new_definition
 `mfd_embedding (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) <=>
    smooth_immersion_into atlas f /\
    homeomorphic_map (top,subtopology euclidean (IMAGE f (topspace top))) f`;;

(* The K x N Jacobian matrix of f in the preferred chart at x.              *)

let mfd_emb_jac = new_definition
 `mfd_emb_jac (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) (x:A) =
    matrix(frechet_derivative (f o chart_inv (chart_at atlas x))
                              (at (SND(chart_at atlas x) x)))`;;

(* The orthogonal projection J (J^T J)^-1 J^T onto the tangent space of the  *)
(* image at f x, J = mfd_emb_jac atlas f x.                                  *)

let mfd_tproj = new_definition
 `mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) (x:A) =
    mfd_emb_jac atlas f x **
    matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
    transp(mfd_emb_jac atlas f x)`;;

(* The inverse of f on its image.                                            *)

let mfd_emb_inv = new_definition
 `mfd_emb_inv (top:A topology) (f:A->real^K) (z:real^K) =
    @x. x IN topspace top /\ f x = z`;;

