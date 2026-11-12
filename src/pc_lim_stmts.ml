(* ========================================================================= *)
(* The statements of the limit-geometry layer for flow limits                *)
(* p2c_flow_limit_with (pc_p3_iface), numbered L1-L6 below.  Statements      *)
(* only; the proofs are in the pc_lim_ units.  REG(V) below is the           *)
(* regular-slices clause of P2CO_P3_FLOW_RESTRICT.  VT, VA, VG at s are the  *)
(* slice of the view V k at the time t k + s / Q k.                          *)
(*   LIM_DIST: rescaled distances converge on compact sets (L1).            *)
(*   LIM_BALL: bounded rescaled balls about x k lie in images of a compact  *)
(*     set (L2).                                                             *)
(*   LIM_VOL: volumes of rescaled balls, sandwich form with radii r1 < r2   *)
(*     (L3; same-radius convergence would need distance spheres of volume  *)
(*     zero).                                                                *)
(*   LIM_KNC: kappa-noncollapsing passes to the limit (L4).                 *)
(*   LIM_CURV: scalar curvature converges after the 1/Q k scaling; lower    *)
(*     and upper sectional bounds pass to the limit (L5).                  *)
(*   LIM_FLOW_COMPLETE_BACK: a Ricci flow with sec >= 0 has complete slices *)
(*     before a complete final slice (L6, a single flow).                   *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;

prioritize_real();;
type_invention_error := true;;

let LIM_DIST_STATEMENT = new_definition
 `LIM_DIST_STATEMENT (u:A->bool) (w:B->bool) <=>
  !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (x:num->A) t Q J (top:B topology) atlas g (xl:B)
     W phi s K e.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k. hausdorff_space (rfs_vtop (V k) (t k + s / Q k))) /\
     s IN J /\ connected_space top /\ riemannian_metric atlas (g s) /\
     mfd_complete (top,atlas) (g s) /\ compact_in top K /\ &0 < e
     ==> ?k0. !k y z.
           k0 <= k /\ y IN K /\ z IN K
           ==> mfd_joinable (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                            (phi k y) (phi k z) /\
               abs(sqrt(Q k) *
                   mfd_dist (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                            (rfs_vmetric (V k) (t k + s / Q k)) (phi k y) (phi k z) -
                   mfd_dist (top,atlas) (g s) y z) < e`;;

let LIM_BALL_STATEMENT = new_definition
 `LIM_BALL_STATEMENT (u:A->bool) (w:B->bool) <=>
  !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (x:num->A) t Q J (top:B topology) atlas g (xl:B)
     W phi s r.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k. hausdorff_space (rfs_vtop (V k) (t k + s / Q k))) /\
     s IN J /\ riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\ &0 < r
     ==> ?K k0. compact_in top K /\
                !k z. k0 <= k /\
                      z IN mfd_ball (rfs_vtop (V k) (t k + s / Q k),
                                     rfs_vatlas (V k) (t k + s / Q k))
                                    (rfs_vmetric (V k) (t k + s / Q k))
                                    (x k) (r * inv(sqrt(Q k)))
                      ==> z IN IMAGE (phi k) (K INTER W k)`;;

let LIM_VOL_STATEMENT = new_definition
 `LIM_VOL_STATEMENT (u:A->bool) (w:B->bool) <=>
  !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (x:num->A) t Q J (top:B topology) atlas g (xl:B)
     W phi s y r1 r2 v1 v2 e.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k. hausdorff_space (rfs_vtop (V k) (t k + s / Q k))) /\
     s IN J /\ riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
     y IN topspace top /\ &0 < r1 /\ r1 < r2 /\ &0 < e /\
     mfd_has_volume (top,atlas) (g s) (mfd_ball (top,atlas) (g s) y r1) v1 /\
     mfd_has_volume (top,atlas) (g s) (mfd_ball (top,atlas) (g s) y r2) v2
     ==> ?k0. !k. k0 <= k
                  ==> ?vk1 vk2.
                        mfd_has_volume
                          (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                          (rfs_vmetric (V k) (t k + s / Q k))
                          (mfd_ball (rfs_vtop (V k) (t k + s / Q k),
                                     rfs_vatlas (V k) (t k + s / Q k))
                                    (rfs_vmetric (V k) (t k + s / Q k))
                                    (phi k y) (r1 * inv(sqrt(Q k)))) vk1 /\
                        mfd_has_volume
                          (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                          (rfs_vmetric (V k) (t k + s / Q k))
                          (mfd_ball (rfs_vtop (V k) (t k + s / Q k),
                                     rfs_vatlas (V k) (t k + s / Q k))
                                    (rfs_vmetric (V k) (t k + s / Q k))
                                    (phi k y) (r2 * inv(sqrt(Q k)))) vk2 /\
                        Q k * sqrt(Q k) * vk1 <= v2 + e /\
                        v1 <= Q k * sqrt(Q k) * vk2 + e`;;

let LIM_KNC_STATEMENT = new_definition
 `LIM_KNC_STATEMENT (u:A->bool) (w:B->bool) <=>
  !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (x:num->A) t Q J (top:B topology) atlas g (xl:B)
     W phi kappa r0.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k tau. hausdorff_space (rfs_vtop (V k) tau)) /\
     (!s. s IN J ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s)) /\
     (!k. rfs_kappa_noncollapsed (V k) kappa (r0 * inv(sqrt(Q k))))
     ==> rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) J g) kappa r0`;;

let LIM_CURV_STATEMENT = new_definition
 `LIM_CURV_STATEMENT (u:A->bool) (w:B->bool) <=>
  !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (x:num->A) t Q J (top:B topology) atlas g (xl:B)
     W phi s y.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     s IN J /\ y IN topspace top /\ riemannian_metric atlas (g s)
     ==> ((\k. mfd_scalar (rfs_vatlas (V k) (t k + s / Q k)) (rfs_vmetric (V k) (t k + s / Q k))
                          (phi k y) / Q k) ---> mfd_scalar atlas (g s) y) sequentially /\
         (!c. (?k0. !k z u v.
                 k0 <= k /\ z IN topspace (rfs_vtop (V k) (t k + s / Q k)) /\
                 ~collinear {vec 0,u,v}
                 ==> c <= mfd_sectional (rfs_vatlas (V k) (t k + s / Q k))
                                        (rfs_vmetric (V k) (t k + s / Q k)) z u v / Q k)
              ==> !u v. ~collinear {vec 0,u,v} ==> c <= mfd_sectional atlas (g s) y u v) /\
         (!c. (?k0. !k z u v.
                 k0 <= k /\ z IN topspace (rfs_vtop (V k) (t k + s / Q k)) /\
                 ~collinear {vec 0,u,v}
                 ==> mfd_sectional (rfs_vatlas (V k) (t k + s / Q k))
                                   (rfs_vmetric (V k) (t k + s / Q k)) z u v / Q k <= c)
              ==> !u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas (g s) y u v <= c)`;;

let LIM_FLOW_COMPLETE_BACK_STATEMENT = new_definition
 `LIM_FLOW_COMPLETE_BACK_STATEMENT (w:B->bool) <=>
  !(top:B topology) atlas (g:real->B->real^3^3) a b.
     hausdorff_space top /\ rfs_flow_upto (top,atlas) a b g /\
     (!s y u v. a < s /\ s <= b /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g s) y u v) /\
     mfd_complete (top,atlas) (g b)
     ==> !s. a < s /\ s <= b ==> mfd_complete (top,atlas) (g s)`;;

