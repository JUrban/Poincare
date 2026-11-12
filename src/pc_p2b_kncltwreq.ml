(* ========================================================================= *)
(* Unit pc_p2b_kncltwreq (statement only): the statement                     *)
(* P2B_KNCL_TWISTED_CANON_STATEMENT, the twisted-model case (M2) of          *)
(* COR_9_94_L piece (d): the Z/2 quotient of the cylinder model is canonical *)
(* at time 0.  It is used in pc_p2b_kncl4 and proved as                      *)
(* RFA_P2B_KNCL_TWISTED_CANON (pc_rfa_ktw).                                  *)
(* ========================================================================= *)

(* The statement for the twisted-model case of COR_9_94_L piece (d).  The   *)
(* Z/2 quotient of the cylinder model at time 0 (the second alternative of  *)
(* p2b_cyl_model): for 0 < eps <= eps2 and L >= 1 there is C0 > 1 such that *)
(* every point of every such model has a canonical neighbourhood            *)
(* p2b_canon_L at time 0: an evolving eps-neck of length L (far from the    *)
(* RP^2 core) or an explicit twisted (C0,eps)-cap (rfs_twisted_chart; the   *)
(* necks are P o dilations, exact since the cylinder metric is dilation     *)
(* invariant).  No inputs.  Needs: pc_p2b_kreq.ml (p2b_canon_L),            *)
(* pc_p2b_defs.ml (p2b_kview).                                              *)

needs "src/pc_p2b_kreq.ml";;
needs "src/pc_p2b_defs.ml";;
needs "src/pc_rfs_geom.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_KNCL_TWISTED_CANON_STATEMENT = new_definition
 `P2B_KNCL_TWISTED_CANON_STATEMENT (w:B->bool) <=>
    ?eps2. &0 < eps2 /\
      !eps L. &0 < eps /\ eps <= eps2 /\ &1 <= L
        ==> ?C0. &1 < C0 /\
              !top atlas (g:real->B->real^3^3) p lam x.
                 hausdorff_space top /\
                 smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                 &0 < lam /\
                 (!t. t <= &0 ==> riemannian_metric atlas (g t)) /\
                 IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
                 (!y. ~(y = vec 0)
                      ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
                 (!y z. ~(y = vec 0) /\ ~(z = vec 0)
                        ==> (p y = p z <=> z = y \/ z = rfs_twist y)) /\
                 (!t y. t <= &0 /\ ~(y = vec 0)
                        ==> rfs_pullback atlas p (g t) y = lam %% cylinder_flow (t / lam) y) /\
                 x IN topspace top
                 ==> p2b_canon_L (p2b_kview (top,atlas) g) C0 eps L x (&0)`;;

