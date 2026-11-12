(* ========================================================================= *)
(* Unit pc_p2b_flatreq: the statement P2B_REQ_FLAT_KNC_STATEMENT, the        *)
(* flat-geometry fact used in Part 2B (MT Lemma 9.65, proof of Claim 9.66,   *)
(* pp. 226-227): a complete connected flat Riemannian 3-manifold that is     *)
(* kappa-noncollapsed on all scales has Euclidean ball volumes.  Flatness is *)
(* zero sectional curvature on every plane (non-collinear u, v, so no junk   *)
(* value is constrained); the noncollapsing is spatial, on every ball.       *)
(* Degenerate cases: Euclidean R^3 satisfies every hypothesis                *)
(* (kappa = 4/3 pi) and the conclusion; an empty manifold satisfies the      *)
(* conclusion vacuously.  Statement only; it is proved as P2B_REQ_FLAT_KNC   *)
(* (pc_p2b_flatknc).                                                         *)
(* ========================================================================= *)

needs "src/pc_grg_voldefs.ml";;
needs "src/pc_grg_dist.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_REQ_FLAT_KNC_STATEMENT = new_definition
 `P2B_REQ_FLAT_KNC_STATEMENT (w:B->bool) <=>
    !top atlas (g:B->real^3^3) kappa.
       hausdorff_space top /\ connected_space top /\
       smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
       mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> mfd_sectional atlas g x u v = &0) /\
       &0 < kappa /\
       (!p r. p IN topspace top /\ &0 < r
              ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r) v /\
                      kappa * r pow 3 <= v)
       ==> !p r. p IN topspace top /\ &0 < r
                 ==> mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r)
                                    (&4 / &3 * pi * r pow 3)`;;

