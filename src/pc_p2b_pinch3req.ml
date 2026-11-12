(* ========================================================================= *)
(* pc_p2b_pinch3req (statement only): P2B_REQ_PINCH_ROUND3_STATEMENT,        *)
(* Hamilton's pinching for ancient compact 3-d Ricci flows: positive         *)
(* sectional curvature and backward pinching sup sec <= (1 + e) inf sec at   *)
(* arbitrarily negative times force constant curvature at every time         *)
(* (Hamilton 1982; Einstein by the estimate of the traceless Ricci tensor,   *)
(* then Schur).  Used by the COR_9_44 route (MT Cor 9.44 in shift form,      *)
(* where roundness at t = b follows by continuity); proved in pc_rfa_pinch3  *)
(* (RFA_P2B_REQ_PINCH_ROUND3).  The flow clause uses ricci_flow_on on (a,b)  *)
(* and the conclusion inlines the body of p2b_round, so the unit needs only  *)
(* pc_rf_basic and pc_mfd_riem.                                              *)
(* ========================================================================= *)

needs "src/pc_mfd_riem.ml";;
needs "src/pc_rf_basic.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_REQ_PINCH_ROUND3_STATEMENT = new_definition
 `P2B_REQ_PINCH_ROUND3_STATEMENT (w:B->bool) <=>
    !top atlas (g:real->B->real^3^3) b.
       hausdorff_space top /\ compact_space top /\ connected_space top /\
       (!a. a < b ==> ricci_flow_on (top,atlas:((B->bool)#(B->real^3))->bool) a b g) /\
       (!t x u v. t < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 < mfd_sectional atlas (g t) x u v) /\
       (!e T. &0 < e
              ==> ?t. t < T /\ t < b /\
                      !x y u v u' v'. x IN topspace top /\ y IN topspace top /\
                                      ~collinear {vec 0,u,v} /\ ~collinear {vec 0,u',v'}
                                      ==> mfd_sectional atlas (g t) x u v <=
                                          (&1 + e) * mfd_sectional atlas (g t) y u' v')
       ==> !t. t < b
               ==> ?k. &0 < k /\
                       !x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                               ==> mfd_sectional atlas (g t) x u v = k`;;

