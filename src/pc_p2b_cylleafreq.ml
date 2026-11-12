(* ========================================================================= *)
(* Unit pc_p2b_cylleafreq (statement only): the statement                    *)
(* P2B_REQ_CYL_FROM_LEAF_STATEMENT, the cylinder model from the round leaf   *)
(* flow, a step of the proof of P2B_SPLIT_ROUND_STATEMENT.  It is proved as  *)
(* P2B_CYL_FROM_LEAF (pc_p2b_cylleaf).                                       *)
(*                                                                           *)
(* A Ricci flow g(s), s < b, on a connected Hausdorff 3-manifold with       *)
(* p2b_lorient, complete slices, positive scalar curvature, and a vector    *)
(* field X that is unit and parallel for a complete reference metric gs and *)
(* parallel for every g(s) with g(s) X = gs X; a compact connected leaf     *)
(* L = lvs_set V0 h0 u0 of a primitive h0 of gs(X,.) (and of every g(s)(X,.)) *)
(* on an open V0, diffeomorphic to the round S^2, on which R(g s) is        *)
(* constant at every time; and the orbit bijection L x R -> M of the        *)
(* X-flow of gs.  Then every time shift g(t + s0), s0 < b, is the round     *)
(* cylinder model p2b_cyl_model.                                             *)
(* ========================================================================= *)

needs "src/pc_p2b_kglob.ml";;
needs "src/pc_p2b_defs.ml";;
needs "src/pc_mfd_examples.ml";;
needs "src/pc_rf_basic.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_REQ_CYL_FROM_LEAF_STATEMENT = new_definition
 `P2B_REQ_CYL_FROM_LEAF_STATEMENT (w:B->bool) <=>
    !top atlas (g:real->B->real^3^3) (gs:B->real^3^3) b (X:B->real^3) V0 h0 u0.
       hausdorff_space top /\ connected_space top /\
       smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       p2b_lorient top atlas /\
       (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\
       (!s. s < b ==> mfd_complete (top,atlas) (g s)) /\
       riemannian_metric atlas gs /\ mfd_complete (top,atlas) gs /\
       p2b_parallel_on atlas gs (topspace top) X /\
       (!y. y IN topspace top ==> X y dot (gs y ** X y) = &1) /\
       (!s. s < b ==> p2b_parallel_on atlas (g s) (topspace top) X) /\
       (!s y. s < b /\ y IN topspace top ==> g s y ** X y = gs y ** X y) /\
       (!s y. s < b /\ y IN topspace top ==> &0 < mfd_scalar atlas (g s) y) /\
       open_in top V0 /\ p2bkg_prim atlas gs X V0 h0 /\
       (!s. s < b ==> p2bkg_prim atlas (g s) X V0 h0) /\
       compact_in top (lvs_set V0 h0 u0) /\ connected_in top (lvs_set V0 h0 u0) /\
       (?psi1 psi1'. mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                                (sphere(vec 0,&1)) (subtopology top (lvs_set V0 h0 u0))
                                (lvs_atlas top atlas V0 h0 u0) (lvs_set V0 h0 u0) psi1 psi1') /\
       (!s y z. s < b /\ y IN lvs_set V0 h0 u0 /\ z IN lvs_set V0 h0 u0
                ==> mfd_scalar atlas (g s) y = mfd_scalar atlas (g s) z) /\
       (!y. y IN topspace top
            ==> ?r z. z IN lvs_set V0 h0 u0 /\ p2bkf_phi (top,atlas) gs X r z = y) /\
       (!z z' r r'. z IN lvs_set V0 h0 u0 /\ z' IN lvs_set V0 h0 u0 /\
                    p2bkf_phi (top,atlas) gs X r z = p2bkf_phi (top,atlas) gs X r' z'
                    ==> z = z' /\ r = r')
       ==> !s0. s0 < b ==> p2b_cyl_model (top,atlas) (\t. g(t + s0))`;;

