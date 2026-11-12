(* ========================================================================= *)
(* Unit pc_p2b_conestmts: statements only.  The route statement of the       *)
(* no-bad-tube half of MT Thm 10.2 (Secs 10.4-10.6) and the two internal     *)
(* interfaces of the units pc_p2b_cone, pc_p2b_cone2, ...                    *)
(*                                                                           *)
(* P2B_NO_BAD_TUBE_ROUTE_STATEMENT: the local compactness of regular views   *)
(* (the statement P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT of unit              *)
(* pc_p2b_lcreqn, at the tube type B) implies P2B_NO_BAD_TUBE_STATEMENT.     *)
(* That statement gives the limit on a ball in real^3, so there is no free   *)
(* limit type and CONE_REGULAR is used at (:real^3).  Proved as              *)
(* P2BK_NO_BAD_TUBE_ROUTE (pc_p2b_cone10).                                   *)
(*                                                                           *)
(* P2BK_END_CONE_STATEMENT: on a bad tube with eps small there is a distance *)
(* to the end E (dE, positive, 1-Lipschitz, with infimum 0) such that every  *)
(* point with dE x <= s1 is the centre of the evolving 2eps-neck and has     *)
(* 1/(4 eps) <= sqrt(R x) dE x <= c2 (MT Claim 10.31), has ray points (a     *)
(* point at distance t whose dE is dE x - t), and the comparison angles at E *)
(* (p2bk_cang of the triangle E, a, b) satisfy the triangle inequality up to *)
(* delta at comparable small scales (MT Lemmas 10.21, 10.22, 10.27).  Proved *)
(* as P2BK_END_CONE (pc_p2b_cone4).                                          *)
(*                                                                           *)
(* P2BK_CONE_REGULAR_STATEMENT (library style): on an open set O of a        *)
(* Riemannian 3-manifold, a positive function rho that is 1-Lipschitz, has   *)
(* ray points, and whose comparison angles satisfy the triangle inequality   *)
(* exactly is smooth, and rho^2/2 has the homothetic Hessian g in every      *)
(* chart (p2bk_chart_hess is the body of p2b_mfd_hess for an arbitrary chart *)
(* c), as MT Prop 4.22 in the form P2B_REQ_RFA_CONE_STATEMENT                *)
(* (pc_p2b_conereq) needs.  Degenerate cases: O empty is vacuous; Euclidean  *)
(* space minus a point with rho = norm satisfies the hypotheses and the      *)
(* conclusion; p2bk_cang uses acs of the cosine law, whose junk values       *)
(* (sides 0, or a non-triangle) never occur in the uses (rho > 0 and rho     *)
(* 1-Lipschitz make the cosine lie in [-1,1]).  Proved as P2BK_CONE_REGULAR  *)
(* (pc_p2b_cone5).                                                           *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;
needs "src/pc_p2b_lcreqn.ml";;

prioritize_real();;
type_invention_error := true;;

(* Comparison angle of a triangle with sides a, b and opposite side d.       *)

let p2bk_cang = new_definition
 `p2bk_cang (a:real) (b:real) (d:real) =
    acs((a pow 2 + b pow 2 - d pow 2) / (&2 * a * b))`;;

(* The chart Hessian of f at x for an arbitrary chart c (p2b_mfd_hess is     *)
(* the case c = chart_at atlas x).                                           *)

let p2bk_chart_hess = new_definition
 `p2bk_chart_hess (atlas:((B->bool)#(B->real^N))->bool) (c:(B->bool)#(B->real^N))
                  (g:B->real^N^N) (f:B->real) (x:B) (u:real^N) (v:real^N) =
    lnabla 1 (metric_local atlas c g)
      (\z w. drop(frechet_derivative (\y. lift(f(chart_inv c y))) (at z) (w 1)))
      (SND c x) (\m. if m = 1 then u else v)`;;

let P2B_NO_BAD_TUBE_ROUTE_STATEMENT = new_definition
 `P2B_NO_BAD_TUBE_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT w ==> P2B_NO_BAD_TUBE_STATEMENT w`;;

let P2BK_END_CONE_STATEMENT = new_definition
 `P2BK_END_CONE_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps top atlas g V H.
         &0 < eps /\ eps <= eps0 /\ p2b_bad_tube eps (top:B topology,atlas) g V H
         ==> ?dE s1 c2.
               &0 < s1 /\ &0 < c2 /\
               (!x. x IN topspace top ==> &0 < dE x) /\
               (!x y. x IN topspace top /\ y IN topspace top
                      ==> abs(dE x - dE y) <= mfd_dist (top,atlas) g x y) /\
               (!s. &0 < s ==> ?x. x IN topspace top /\ dE x < s) /\
               (!x. x IN topspace top /\ dE x <= s1
                    ==> (?e. rfs_evolving_neck V (&2 * eps) x (&0) (&1 / &2) e) /\
                        inv(&4 * eps) <= sqrt(mfd_scalar atlas g x) * dE x /\
                        sqrt(mfd_scalar atlas g x) * dE x <= c2) /\
               (!x t. x IN topspace top /\ dE x <= s1 /\ &0 < t /\ t <= dE x / &2
                      ==> ?z. z IN topspace top /\ mfd_dist (top,atlas) g x z = t /\
                              dE z = dE x - t) /\
               (!delta. &0 < delta
                  ==> ?s0. &0 < s0 /\
                        !a b c. a IN topspace top /\ b IN topspace top /\
                                c IN topspace top /\
                                dE a <= s0 /\ dE b <= s0 /\ dE c <= s0 /\
                                dE a <= &2 * dE b /\ dE b <= &2 * dE a /\
                                dE b <= &2 * dE c /\ dE c <= &2 * dE b
                                ==> p2bk_cang (dE a) (dE c) (mfd_dist (top,atlas) g a c) <=
                                    p2bk_cang (dE a) (dE b) (mfd_dist (top,atlas) g a b) +
                                    p2bk_cang (dE b) (dE c) (mfd_dist (top,atlas) g b c) +
                                    delta)`;;

let P2BK_CONE_REGULAR_STATEMENT = new_definition
 `P2BK_CONE_REGULAR_STATEMENT (w:B->bool) <=>
    !top atlas (g:B->real^3^3) O rho.
       hausdorff_space top /\ smooth_manifold_atlas top atlas /\
       riemannian_metric atlas g /\ open_in top O /\
       (!x. x IN O ==> &0 < rho x) /\
       (!x y. x IN O /\ y IN O
              ==> mfd_joinable (top,atlas) x y /\
                  abs(rho x - rho y) <= mfd_dist (top,atlas) g x y) /\
       (!x. x IN O
            ==> ?r. &0 < r /\
                    !t. &0 < t /\ t < r
                        ==> ?y. y IN O /\ mfd_dist (top,atlas) g x y = t /\
                                rho y = rho x - t) /\
       (!x y z. x IN O /\ y IN O /\ z IN O
                ==> p2bk_cang (rho x) (rho z) (mfd_dist (top,atlas) g x z) <=
                    p2bk_cang (rho x) (rho y) (mfd_dist (top,atlas) g x y) +
                    p2bk_cang (rho y) (rho z) (mfd_dist (top,atlas) g y z))
       ==> mfd_smooth_on atlas O (\x. lift(rho x)) /\
           !c x u v. c IN atlas /\ x IN FST c /\ x IN O
                     ==> p2bk_chart_hess atlas c g (\y. rho y pow 2 / &2) x u v =
                         u dot (metric_local atlas c g (SND c x) ** v)`;;

(* The assembly of the route from the three parts (proved by MESON).        *)

let P2BK_NO_BAD_TUBE_PARTS = prove
 (`!w:B->bool.
     (P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT w /\ P2BK_END_CONE_STATEMENT w /\
      P2BK_CONE_REGULAR_STATEMENT (:real^3) ==> P2B_NO_BAD_TUBE_STATEMENT w) /\
     P2BK_END_CONE_STATEMENT w /\ P2BK_CONE_REGULAR_STATEMENT (:real^3)
     ==> P2B_NO_BAD_TUBE_ROUTE_STATEMENT w`,
  REWRITE_TAC[P2B_NO_BAD_TUBE_ROUTE_STATEMENT] THEN MESON_TAC[]);;

