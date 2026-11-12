(* ========================================================================= *)
(* pc_p2b_gaussreq: statements of the Part 2B route to P2B_SOLITON_FROM_LINF *)
(* (pc_p2b_chainstmts, MT Sections 2.7-2.8).                                 *)
(*                                                                           *)
(* P2B_REQ_FLAT_GAUSS_STATEMENT (route input, MT Claim 9.36 flat case): a    *)
(* nonempty complete connected flat Riemannian 3-manifold with a smooth f,   *)
(* Hess f = g/(2 tau) and |grad f|^2 = f/tau (the Gaussian soliton)          *)
(* has reduced volume at least (4 pi)^(3/2) (in fact equal: exp at the       *)
(* minimum of f is an isometry from R^3 and f = |x|^2/(4 tau)).  It is       *)
(* proved as P2AU_FLAT_GAUSS (pc_p2b_flatg).                                 *)
(*                                                                           *)
(* P2B_SOLITON_FROM_LINF_FIX_STATEMENT (defined in pc_p2b_chainstmts):       *)
(* P2B_SOLITON_FROM_LINF_STATEMENT with the extra hypothesis                 *)
(* ~(topspace top = {}).  Without it the statement is false for the empty    *)
(* manifold: every hypothesis holds vacuously (p2bg_rvol with V = 0) while   *)
(* its second conclusion asks for a point.  P2B_SOLITON_FROM_LINF_STATEMENT  *)
(* implies the FIX form (P2B_SOLITON_FROM_LINF_ORIG_IMP_FIX, below); the     *)
(* route form P2B_SOLITON_FROM_LINF_FIX_ROUTE_STATEMENT is proved in         *)
(* pc_p2b_sol.                                                               *)
(* ========================================================================= *)

needs "src/pc_p2b_chainstmts.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_REQ_FLAT_GAUSS_STATEMENT = new_definition
 `P2B_REQ_FLAT_GAUSS_STATEMENT (w:B->bool) <=>
    !top atlas (g:B->real^3^3) (f:B->real) tau.
      ~(topspace top = {}) /\ hausdorff_space top /\ connected_space top /\
      smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
      mfd_complete (top,atlas) g /\ &0 < tau /\
      (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
               ==> mfd_sectional atlas g x u v = &0) /\
      mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
      (!x u v. x IN topspace top
               ==> p2b_mfd_hess atlas g f x u v = inv(&2 * tau) * (u dot (g x ** v))) /\
      (!x. x IN topspace top
           ==> lgrad2 (metric_local atlas (chart_at atlas x) g)
                      (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x) =
               f x / tau) /\
      mfd_integrable_on (top,atlas) g (\y. exp(--(f y)) / sqrt tau pow 3) (topspace top)
      ==> sqrt(&4 * pi) pow 3 <=
          mfd_integral (top,atlas) g (topspace top) (\y. exp(--(f y)) / sqrt tau pow 3)`;;


let P2B_SOLITON_FROM_LINF_FIX_ROUTE_STATEMENT = new_definition
 `P2B_SOLITON_FROM_LINF_FIX_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_REQ_FLAT_GAUSS_STATEMENT w ==> P2B_SOLITON_FROM_LINF_FIX_STATEMENT w`;;

let P2B_SOLITON_FROM_LINF_ORIG_IMP_FIX = prove
 (`!w:B->bool. P2B_SOLITON_FROM_LINF_STATEMENT w ==> P2B_SOLITON_FROM_LINF_FIX_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_SOLITON_FROM_LINF_STATEMENT; P2B_SOLITON_FROM_LINF_FIX_STATEMENT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  FIRST_X_ASSUM MATCH_ACCEPT_TAC);;

