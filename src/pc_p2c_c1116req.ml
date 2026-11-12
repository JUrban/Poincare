(* ========================================================================= *)
(* Unit pc_p2c_c1116req (Part 2C, statements only):                          *)
(* MT Cor 11.16 (p. 277) in flow form, with Lemma 11.11 and Claims          *)
(* 11.12-11.15 (pp. 273-277).  One Ricci flow on (-Tm,0] of a connected      *)
(* 3-manifold whose neck spheres separate, complete slices of sec >= 0 with  *)
(* (C,eps)-canonical neighbourhoods where R > 4, abs Rm bounded on every     *)
(* [a,0], bounded curvature at bounded distance on the slices from base     *)
(* points with R >= 2 (MT's use of Thm 10.2 in the approximants at the end   *)
(* of the proof of Lemma 11.11, supplied by the blow-up limit; 2 as MT's     *)
(* 2 <= R(y_m)), R(xl,0) <= 1: R is bounded on                               *)
(* B(xl,0,A) x (-Tm,0] for every A (P2C_COR_11_16_FLOW_STATEMENT).  Used by  *)
(* the blow-up units (pc_p2c_blowup2, pc_p2c_blowup3) inside Prop 11.10      *)
(* (EXT) and for the Cor 11.16 clause of B6.  The proof (pc_p2c_c1116) uses  *)
(* the inputs listed in the route P2C_COR_11_16_FLOW_ROUTE_STATEMENT.        *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;

prioritize_real();;
type_invention_error := true;;

let P2C_COR_11_16_FLOW_STATEMENT = new_definition
 `P2C_COR_11_16_FLOW_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)
       Tm xl.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < Tm /\
         hausdorff_space top /\ smooth_manifold_atlas top atlas /\ connected_space top /\
         apx_sphere_sep top atlas /\ xl IN topspace top /\
         (!a b. --Tm < a /\ a < b /\ b <= &0 ==> ricci_flow_on (top,atlas) a b g) /\
         (!a. --Tm < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
         (!s. --Tm < s /\ s <= &0
              ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
                  (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                           ==> &0 <= mfd_sectional atlas (g s) y u v) /\
                  (!y. y IN topspace top /\ &4 < mfd_scalar atlas (g s) y
                       ==> ?U. rfs_canonical_nbhd (top,atlas) (g s) C eps y U)) /\
         (!a. --Tm < a ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                     ==> mfd_rm_norm atlas (g s) y <= K) /\
         (!A. ?D. !s y z. --Tm < s /\ s <= &0 /\ y IN topspace top /\ z IN topspace top /\
                          &2 <= mfd_scalar atlas (g s) y /\
                          mfd_dist (top,atlas) (g s) y z <=
                          A * inv(sqrt(mfd_scalar atlas (g s) y))
                          ==> mfd_scalar atlas (g s) z <= D * mfd_scalar atlas (g s) y) /\
         mfd_scalar atlas (g (&0)) xl <= &1
         ==> !A. ?K. !s y. --Tm < s /\ s <= &0 /\ y IN mfd_ball (top,atlas) (g (&0)) xl A
                           ==> mfd_scalar atlas (g s) y <= K`;;

let P2C_COR_11_16_FLOW_ROUTE_STATEMENT = new_definition
 `P2C_COR_11_16_FLOW_ROUTE_STATEMENT (w:B->bool) <=>
    P2C_REQ_HARNACK_STATEMENT w /\ P2C_REQ_DIST_DISTORTION_STATEMENT w /\
    P2C_REQ_LEMMA_11_13_STATEMENT w /\ P2C_REQ_SCALAR_MIN_STATEMENT w /\
    APX_NO_CAP_IN_NECK_STATEMENT w
    ==> P2C_COR_11_16_FLOW_STATEMENT w`;;

