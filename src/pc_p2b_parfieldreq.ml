(* ========================================================================= *)
(* pc_p2b_parfieldreq (statement only): the limit parallel field used by     *)
(* SPLIT_ROUND, P2BPL_LIMIT_FIELD_STATEMENT: a unit parallel limit field Y   *)
(* on the limit of slice limits of unit parallel fields X n, with C^0        *)
(* convergence in the g0 norm uniformly on compact sets.  Proved in          *)
(* pc_p2b_parfield (P2BPL_LIMIT_FIELD).                                      *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_mfd_diff.ml";;
needs "src/pc_p2b_splitreq.ml";;

prioritize_real();;
type_invention_error := true;;


(* The statement of the limit parallel field. *)

let P2BPL_LIMIT_FIELD_STATEMENT = new_definition
 `P2BPL_LIMIT_FIELD_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V x t Q top atlas g0 xl W phi (X:num->A->real^3).
     p2c_slice_limit_with V x t Q (top:B topology,atlas) g0 xl W phi /\
     (!n. smooth_manifold_atlas (rfs_vtop (V n:(real->A topology)#
                                        (real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (t n))
                                (rfs_vatlas (V n) (t n)) /\
          riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
          p2b_parallel_on (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))
                          (IMAGE (phi n) (W n)) (X n) /\
          (!y. y IN IMAGE (phi n) (W n)
               ==> X n y dot (rfs_vmetric (V n) (t n) y ** X n y) = &1))
     ==> ?sub (Y:B->real^3).
            p3_subseq sub /\
            p2b_parallel_on atlas g0 (topspace top) Y /\
            (!y. y IN topspace top ==> Y y dot (g0 y ** Y y) = &1) /\
            !K e. compact_in top K /\ &0 < e
                  ==> ?n0. !n. n0 <= n
                               ==> !y. y IN K
                                       ==> ?z. mfd_differential atlas
                                                 (rfs_vatlas (V (sub n)) (t (sub n)))
                                                 (phi (sub n)) y z = X (sub n) (phi (sub n) y) /\
                                               (inv(sqrt(Q(sub n))) % z - Y y) dot
                                               (g0 y ** (inv(sqrt(Q(sub n))) % z - Y y)) < e`;;

