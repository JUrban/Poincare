(* ========================================================================= *)
(* Unit pc_p2b_lcreqg: the statement P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT,  *)
(* the general local-compactness statement used by the bad-tube half of      *)
(* MT Thm 10.2 (MT Thm 5.6 with Shi, incomplete limits).  Compared with      *)
(* P2B_REQ_P2C_LOCAL_COMPACT_STATEMENT of pc_p2b_defs, which is false as     *)
(* stated and is not used: deep points are delta-regular in the sense of     *)
(* MT Def 5.1 (p2b_lc_deep: the closed delta-ball is compact and lies in U); *)
(* the flow clause converges on compact subsets K of X (Shi is interior);    *)
(* and delta-deep curves from z of length at most A lie in phi k (W m) for   *)
(* one m = m(delta, A), for all large k.  Statement only.                    *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;

prioritize_real();;
type_invention_error := true;;

let p2b_lc_deep = new_definition
 `p2b_lc_deep (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) (U:A->bool) (y:A) (delta:real) <=>
    compact_in (rfs_vtop V (&0)) (rfs_vtop V (&0) closure_of rfs_vball V (&0) y delta) /\
    rfs_vtop V (&0) closure_of rfs_vball V (&0) y delta SUBSET U`;;

let P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT = new_definition
 `P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V U z.
       (!n. p2c_regular_view (V n:(real->A topology)#
                                  (real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) /\
            open_in (rfs_vtop (V n) (&0)) (U n) /\ (z n:A) IN U n) /\
       (!delta. &0 < delta
                ==> ?K tau N. &0 < tau /\
                      !n y. N <= n /\ y IN U n /\ p2b_lc_deep (V n) (U n) y delta
                            ==> rfs_persists (V n) (rfs_vball (V n) (&0) y (delta / &2))
                                             (--tau) (&0) /\
                                !s y'. --tau < s /\ s <= &0 /\
                                       y' IN rfs_vball (V n) (&0) y (delta / &2)
                                       ==> mfd_rm_norm (rfs_vatlas (V n) s)
                                                       (rfs_vmetric (V n) s) y' <= K) /\
       (!delta. &0 < delta
                ==> ?kappa N. &0 < kappa /\
                      !n y. N <= n /\ y IN U n /\ p2b_lc_deep (V n) (U n) y delta
                            ==> ?v. mfd_has_volume (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                      (rfs_vmetric (V n) (&0))
                                      (rfs_vball (V n) (&0) y (delta / &2)) v /\
                                    kappa * (delta / &2) pow 3 <= v) /\
       (?delta0. &0 < delta0 /\ !n. p2b_lc_deep (V n) (U n) (z n) delta0)
       ==> ?sub (top:B topology) atlas g zl W phi Vl.
              p3_subseq sub /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              riemannian_metric atlas g /\ zl IN topspace top /\
              (!k. open_in top (W k) /\ zl IN W k /\ compact_in top (top closure_of W k) /\
                   top closure_of W k SUBSET W (SUC k)) /\
              UNIONS {W k | k IN (:num)} = topspace top /\
              (!k. phi k zl = z (sub k)) /\
              (!k. IMAGE (phi k) (W k) SUBSET U (sub k) /\
                   ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V (sub k)) (&0))
                                    (rfs_vatlas (V (sub k)) (&0))
                                    (IMAGE (phi k) (W k)) (phi k) psi) /\
              (!K m eta. compact_in top K /\ &0 < eta
                         ==> ?k0. !k. k0 <= k
                                      ==> K SUBSET W k /\
                                          !y. y IN K
                                              ==> lck_dist2 m
                                                    (metric_local atlas (chart_at atlas y) g)
                                                    (rfs_pullback (rfs_vatlas (V (sub k)) (&0))
                                                       (phi k o chart_inv (chart_at atlas y))
                                                       (rfs_vmetric (V (sub k)) (&0)))
                                                    (SND(chart_at atlas y) y) < eta) /\
              (!delta A. &0 < delta /\ &0 < A
                         ==> ?m k0. m <= k0 /\
                              !k gamma.
                                k0 <= k /\
                                mfd_c1_curve (rfs_vtop (V (sub k)) (&0),
                                              rfs_vatlas (V (sub k)) (&0)) gamma (&0) (&1) /\
                                gamma (&0) = z (sub k) /\
                                mfd_length (rfs_vatlas (V (sub k)) (&0))
                                           (rfs_vmetric (V (sub k)) (&0)) gamma (&0) (&1) <= A /\
                                (!s. &0 <= s /\ s <= &1
                                     ==> p2b_lc_deep (V (sub k)) (U (sub k)) (gamma s) delta)
                                ==> !s. &0 <= s /\ s <= &1
                                        ==> ?y'. y' IN W m /\ phi k y' = gamma s) /\
              p2c_regular_view Vl /\
              rfs_vtop Vl (&0) = top /\ rfs_vatlas Vl (&0) = atlas /\ rfs_vmetric Vl (&0) = g /\
              (!X a. open_in top X /\ compact_in top (top closure_of X) /\ a < &0 /\
                     (?Kb N. !k. N <= k
                                 ==> X SUBSET W k /\
                                     rfs_persists (V (sub k)) (IMAGE (phi k) X) a (&0) /\
                                     !s y. a < s /\ s <= &0 /\ y IN IMAGE (phi k) X
                                           ==> mfd_rm_norm (rfs_vatlas (V (sub k)) s)
                                                           (rfs_vmetric (V (sub k)) s) y <= Kb)
                     ==> p2c_vflow Vl X a (&0) /\
                         !K m eta b. compact_in top K /\ K SUBSET X /\ a < b /\ &0 < eta
                           ==> ?k0. !k s y. k0 <= k /\ b <= s /\ s <= &0 /\ y IN K
                                            ==> lck_dist2 m
                                                  (metric_local (rfs_vatlas Vl s)
                                                     (chart_at (rfs_vatlas Vl s) y)
                                                     (rfs_vmetric Vl s))
                                                  (rfs_pullback (rfs_vatlas (V (sub k)) s)
                                                     (phi k o chart_inv
                                                        (chart_at (rfs_vatlas Vl s) y))
                                                     (rfs_vmetric (V (sub k)) s))
                                                  (SND(chart_at (rfs_vatlas Vl s) y) y) < eta)`;;

