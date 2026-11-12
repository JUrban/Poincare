(* ========================================================================= *)
(* Unit pc_p2b_conereq: the statement P2B_REQ_RFA_CONE_STATEMENT,            *)
(* MT Prop 4.22 as used in the final contradiction of MT Thm 10.2: a flow    *)
(* with sec >= 0 whose final slice is an open piece of a Riemannian cone     *)
(* is flat.  It is proved as RFA_P2B_REQ_CONE (pc_rfa_cone).  The cone       *)
(* structure is a positive smooth rho whose square has the homothetic        *)
(* Hessian Hess(rho^2/2) = g(0) (p2b_mfd_hess of pc_cmp_pdefs, the Hessian   *)
(* in the preferred chart).  Degenerate cases: an empty manifold is vacuous; *)
(* flat space minus a point with rho = norm satisfies the hypotheses and the *)
(* conclusion; a compact slice admits no such rho (rho^2 would have a        *)
(* maximum with Hess <= 0), so the statement is about noncompact or          *)
(* incomplete slices, as in its use.  Statement only.                        *)
(*                                                                           *)
(* The needs line loads pc_cmp_pdefs (p2b_mfd_hess); its load closure has    *)
(* rfs_flow_upto of pc_p3_defs and mfd_sectional of pc_mfd_riem.             *)
(* ========================================================================= *)

needs "src/pc_cmp_pdefs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* MT Prop 4.22.                                                             *)
(* ------------------------------------------------------------------------- *)

let P2B_REQ_RFA_CONE_STATEMENT = new_definition
 `P2B_REQ_RFA_CONE_STATEMENT (w:B->bool) <=>
    !top atlas (g:real->B->real^3^3) a rho.
       hausdorff_space top /\ connected_space top /\ a < &0 /\
       rfs_flow_upto (top,atlas) a (&0) g /\
       (!t x u v. a < t /\ t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas (g t) x u v) /\
       mfd_smooth_on atlas (topspace top) (\x. lift(rho x)) /\
       (!x. x IN topspace top ==> &0 < rho x) /\
       (!x u v. x IN topspace top
                ==> p2b_mfd_hess atlas (g(&0)) (\y. rho y pow 2 / &2) x u v =
                    u dot (g (&0) x ** v))
       ==> !t x u v. a < t /\ t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                     ==> mfd_sectional atlas (g t) x u v = &0`;;

