(* ========================================================================= *)
(* Unit pc_p2b_lcreqn: the statement P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT,  *)
(* the local-compactness statement used by the no-bad-tube half of           *)
(* MT Thm 10.2; it is proved in pc_p2c_lcn.  A local limit in ONE chart      *)
(* around the base points: the maps phi k are constructed (normal            *)
(* coordinates of the time-0 slices); the limit flow lives on ball(vec 0,r0) *)
(* in real^3 and is smooth up to time 0.  It is used instead of              *)
(* P2B_REQ_P2C_LOCAL_COMPACT_STATEMENT of pc_p2b_defs, which is false as     *)
(* stated; a form with given maps phi k would be false too (given maps are   *)
(* not controlled in C^1).  Statement only.                                  *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT = new_definition
 `P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT (u:A->bool) <=>
    !V (x:num->A) r1 a0 K v0.
       &0 < r1 /\ a0 < &0 /\ &0 < K /\ &0 < v0 /\
       (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) /\
            x n IN topspace (rfs_vtop (V n) (&0)) /\
            compact_in (rfs_vtop (V n) (&0))
              (rfs_vtop (V n) (&0) closure_of rfs_vball (V n) (&0) (x n) r1) /\
            rfs_persists (V n) (rfs_vball (V n) (&0) (x n) r1) a0 (&0) /\
            (!s y. a0 < s /\ s <= &0 /\ y IN rfs_vball (V n) (&0) (x n) r1
                   ==> mfd_rm_norm (rfs_vatlas (V n) s) (rfs_vmetric (V n) s) y <= K) /\
            (?v. mfd_has_volume (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                (rfs_vmetric (V n) (&0)) (rfs_vball (V n) (&0) (x n) r1) v /\
                 v0 <= v))
       ==> ?r0 sub (phi:num->real^3->A) (g:real->real^3->real^3^3).
              &0 < r0 /\ r0 < r1 /\ p3_subseq sub /\
              (!k. mfd_param (rfs_vtop (V (sub k)) (&0)) (rfs_vatlas (V (sub k)) (&0))
                             (ball(vec 0,r0)) (phi k) /\
                   phi k (vec 0) = x (sub k) /\
                   IMAGE (phi k) (ball(vec 0,r0)) = rfs_vball (V (sub k)) (&0) (x (sub k)) r0) /\
              (!s. a0 / &2 < s /\ s <= &0 ==> metric_field (ball(vec 0,r0)) (g s)) /\
              (!O. open O /\ O SUBSET ball(vec 0,r0)
                   ==> rfs_flow_upto (subtopology euclidean O,open_set_atlas O) (a0 / &2) (&0) g) /\
              (!Kc m eta. compact Kc /\ Kc SUBSET ball(vec 0,r0) /\ &0 < eta
                          ==> ?k0. !k s w. k0 <= k /\ a0 / &2 <= s /\ s <= &0 /\ w IN Kc
                                           ==> lck_dist2 m (g s)
                                                 (rfs_pullback (rfs_vatlas (V (sub k)) s) (phi k)
                                                               (rfs_vmetric (V (sub k)) s)) w
                                               < eta)`;;

