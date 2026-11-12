(* ========================================================================= *)
(* pc_moi_fnd_nb2f: the unconditional second-derived neighbourhood theorem   *)
(* for polygons in finite closed combinatorial surfaces, the statement term  *)
(* of pc_moi_fnd_stmt3.ml:                                                   *)
(*   DERIVED_NBHD_POLYGON_2 = MOI_FND_DERIVED_NBHD_POLYGON_2                 *)
(* pc_moi_fnd_nb2 proves it conditionally (MOI_FN2_POLYGON_2_COND, on the   *)
(* planar surface theorem and the boundary-circles theorem); both are       *)
(* discharged here by pc_moi_fnd_surfb (SURFACE_EULER_PLANAR) and           *)
(* pc_moi_fnd_surfb0 (MOI_FSB_BD_CIRCLES).                                  *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_nb2.ml";;
needs "src/pc_moi_fnd_surfb.ml";;

prioritize_real();;
type_invention_error := true;;

let DERIVED_NBHD_POLYGON_2 = prove
 (MOI_FND_DERIVED_NBHD_POLYGON_2,
  ACCEPT_TAC(MATCH_MP MOI_FN2_POLYGON_2_COND
               (CONJ SURFACE_EULER_PLANAR MOI_FSB_BD_CIRCLES)));;

