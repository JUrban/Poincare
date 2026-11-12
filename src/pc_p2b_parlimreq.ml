(* ========================================================================= *)
(* pc_p2b_parlimreq (statements only): two limit statements used by          *)
(* SPLIT_ROUND, the pointwise limit of unit vectors with Ric = 0 at the base *)
(* points of a slice limit (P2BPL_POINT_LIMIT_STATEMENT) and the local       *)
(* convergence of the rescaled geodesics from the base points                *)
(* (P2BPL_ORBIT_LIMIT_STATEMENT).  Proved in pc_p2b_parlim                   *)
(* (P2BPL_POINT_LIMIT, P2BPL_ORBIT_LIMIT); used in route form by pc_p2b_x0r. *)
(* The per-n conjunct of the orbit statement includes hausdorff_space of the *)
(* slices (the mfd_geo facts need it; the limit side has it in               *)
(* p2c_slice_limit_with).                                                    *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_geo_defs.ml";;
needs "src/pc_mfd_diff.ml";;

prioritize_real();;
type_invention_error := true;;


let P2BPL_POINT_LIMIT_STATEMENT = new_definition
 `P2BPL_POINT_LIMIT_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V x t Q top atlas g0 xl W phi (U:num->real^3).
       p2c_slice_limit_with V x t Q (top:B topology,atlas) g0 xl W phi /\
       (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                          (real->((A->bool)#(A->real^3))->bool)#
                                          (real->A->real^3^3)) (t n))
                                  (rfs_vatlas (V n) (t n)) /\
            riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
            U n dot (rfs_vmetric (V n) (t n) (x n) ** U n) = &1 /\
            mfd_ricci (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) (x n) (U n) (U n) = &0)
       ==> ?sub v. p3_subseq sub /\
                   v dot (g0 xl ** v) = &1 /\
                   mfd_ricci atlas g0 xl v v = &0 /\
                   !e. &0 < e
                       ==> ?n0. !n. n0 <= n
                                    ==> ?z. mfd_differential atlas
                                              (rfs_vatlas (V (sub n)) (t (sub n)))
                                              (phi (sub n)) xl z = U (sub n) /\
                                            norm(inv(sqrt(Q(sub n))) % z - v) < e`;;

let P2BPL_ORBIT_LIMIT_STATEMENT = new_definition
 `P2BPL_ORBIT_LIMIT_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V x t Q top atlas g0 xl W phi (U:num->real^3) sub v.
       p2c_slice_limit_with V x t Q (top:B topology,atlas) g0 xl W phi /\
       mfd_complete (top,atlas) g0 /\
       (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                          (real->((A->bool)#(A->real^3))->bool)#
                                          (real->A->real^3^3)) (t n))
                                  (rfs_vatlas (V n) (t n)) /\
            hausdorff_space (rfs_vtop (V n) (t n)) /\
            riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
            mfd_complete (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                         (rfs_vmetric (V n) (t n))) /\
       p3_subseq sub /\
       (!e. &0 < e
            ==> ?n0. !n. n0 <= n
                         ==> ?z. mfd_differential atlas (rfs_vatlas (V (sub n)) (t (sub n)))
                                   (phi (sub n)) xl z = U (sub n) /\
                                 norm(inv(sqrt(Q(sub n))) % z - v) < e)
       ==> ?d. &0 < d /\
               !s e. abs s <= d /\ &0 < e
                     ==> ?n0. !n. n0 <= n
                                  ==> ?y. y IN W (sub n) /\
                                          phi (sub n) y =
                                          mfd_geo (rfs_vtop (V (sub n)) (t (sub n)),
                                                   rfs_vatlas (V (sub n)) (t (sub n)))
                                                  (rfs_vmetric (V (sub n)) (t (sub n)))
                                                  (x (sub n)) (U (sub n))
                                                  (s / sqrt(Q(sub n))) /\
                                          mfd_dist (top,atlas) g0 y
                                                   (mfd_geo (top,atlas) g0 xl v s) < e`;;

