(* ========================================================================= *)
(* Unit pc_p2b_distreq: the statement P2B_REQ_RFA_DIST_LOCAL_STATEMENT, used *)
(* in Part 2B (MT Lemma 9.25 / Cor 9.26): MT Prop 3.21 in LOCAL form with a  *)
(* BACKWARD difference in t.  For a Ricci flow with complete slice at t and  *)
(* Ric <= (n-1)K on the two balls of radius r0 about x0 and x1 at time t,    *)
(* the distance at the earlier time t - s exceeds the distance at t by at    *)
(* most s (2(n-1)(K r0 + 1/r0) + e) for small s > 0.  Comparing with one     *)
(* minimal geodesic of g(t) needs no compactness of minimal geodesics.       *)
(* Degenerate cases: x0 = x1 gives 0 <= s(...); dimension 1 (Ric = 0, static *)
(* flows) gives d_{t-s} = d_t; K = 0 is allowed.  Statement only; it is      *)
(* proved as RFA_P2B_REQ_RFA_DIST_LOCAL (pc_rfa_dist).                       *)
(* ========================================================================= *)

needs "src/pc_grg_dist.ml";;
needs "src/pc_rf_basic.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The statement.                                                            *)
(* ------------------------------------------------------------------------- *)

let P2B_REQ_RFA_DIST_LOCAL_STATEMENT = new_definition
 `P2B_REQ_RFA_DIST_LOCAL_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b (g:real->A->real^N^N) t x0 x1 K r0.
       hausdorff_space top /\
       ricci_flow_on (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       a < t /\ t < b /\ mfd_complete (top,atlas) (g t) /\
       x0 IN topspace top /\ x1 IN topspace top /\ mfd_joinable (top,atlas) x0 x1 /\
       &0 < r0 /\ &0 <= K /\
       (!y w. y IN mfd_ball (top,atlas) (g t) x0 r0 UNION mfd_ball (top,atlas) (g t) x1 r0
              ==> mfd_ricci atlas (g t) y w w <=
                  &(dimindex(:N) - 1) * K * (w dot (g t y ** w)))
       ==> !e. &0 < e
               ==> ?d. &0 < d /\
                       !s. &0 < s /\ s < d
                           ==> mfd_dist (top,atlas) (g(t - s)) x0 x1 <=
                               mfd_dist (top,atlas) (g t) x0 x1 +
                               s * (&2 * &(dimindex(:N) - 1) * (K * r0 + inv r0) + e)`;;

