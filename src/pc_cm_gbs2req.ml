(* ========================================================================= *)
(* Unit pc_cm_gbs2req (statement only, used in the proof of MT Prop 9.46):   *)
(* the Gauss-Bonnet bridge for surface pieces diffeomorphic to the standard  *)
(* sphere.  A piece S of a surface (real^2 charts, Riemannian metric g),     *)
(* open in the surface and the image of the standard S^2 (sphere2_atlas of   *)
(* pc_mfd_examples) under a diffeomorphism, whose Gauss curvature K = R/2    *)
(* satisfies K <= k0, has area a with 4 pi <= k0 a.  The relative form fits  *)
(* both producers of surfaces: the S2ENT setting (pc_p2b_s2entreq) with S    *)
(* the whole surface, and the leaves of pc_mfd_level (lvs_atlas, lvs_metric) *)
(* with S a component.  The proof is pc_cm_gbs2.                             *)
(* ========================================================================= *)

needs "src/pc_mfd_examples.ml";;
needs "src/pc_mfd_maps.ml";;
needs "src/pc_mfd_riem.ml";;
needs "src/pc_grg_voldefs.ml";;

prioritize_real();;
type_invention_error := true;;

let CM_GB_SPHERE_AREA_STATEMENT = new_definition
 `CM_GB_SPHERE_AREA_STATEMENT (u:A->bool) <=>
    !top atlas (g:A->real^2^2) S (psi:real^3->A) (psi':A->real^3) k0 a.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
       riemannian_metric atlas g /\
       mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                  (sphere(vec 0:real^3,&1)) top atlas S psi psi' /\
       (!x. x IN S ==> mfd_scalar atlas g x <= &2 * k0) /\
       mfd_has_volume (top,atlas) g S a
       ==> &4 * pi <= k0 * a`;;

