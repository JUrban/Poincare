(* ========================================================================= *)
(* pc_p2b_tubelimst (statements only): the limit side of the bad tube (MT    *)
(* Sec 10.3, the limit part of Prop 10.7 and Claims 10.8-10.11), five        *)
(* statements P2BT_LIM_CHAIN_STATEMENT, P2BT_LIM_SUMMABLE_STATEMENT,         *)
(* P2BT_LIM_BOXES_STATEMENT, P2BT_LIM_SEC_STATEMENT and                      *)
(* P2BT_LIM_ENECK_STATEMENT about the context p2bt_lctx.  Proved in          *)
(* pc_p2b_tubelim, pc_p2b_tubelim2 and pc_p2b_tubelim3; pc_p2b_tube4 uses    *)
(* them as hypotheses, and the route unit pc_p2b_tuberoute discharges them.  *)
(* ========================================================================= *)

needs "src/pc_p2b_tube2.ml";;

prioritize_real();;
type_invention_error := true;;


(* The data of the limit part: approximants, cut and limit in one predicate *)
(* (definitions p2bt_approx, p2bt_cut, p2bt_cutset, p2bt_zbase, p2bt_lim of  *)
(* unit pc_p2b_tube2).                                                        *)

let p2bt_lctx = new_definition
 `p2bt_lctx (eps:real) (C:real) (A:real)
    (V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (t:num->real) (Q:num->real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (gamma:num->real->A) (s0:num->real) (s1:num->real) (EN:num->real->real^3->A) (A1:real)
    (sub:num->num) (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
    (zl:B) (W:num->B->bool) (phi:num->B->A)
    (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) <=>
    &1 < C /\ &0 < A /\
    p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\
    p2bt_cut eps C A V gamma s0 s1 A1 /\
    p2bt_lim V (\n. p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1)
             (p2bt_zbase eps C V gamma s0) sub top atlas g zl W phi Vl`;;

(* The limit contains a one-sided infinite chain of 2 eps-necks. *)

let P2BT_LIM_CHAIN_STATEMENT = new_definition
 `P2BT_LIM_CHAIN_STATEMENT (u:A->bool) (w:B->bool) <=>
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl.
              &0 < eps /\ eps <= eps0 /\
              p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl
              ==> ?x e. apx_chain (top,atlas) g (&2 * eps) {i:int | &0 <= i} x
                                  (e:int->real^3->B)`;;

(* The scales of every such chain are summable (MT Claim 10.9). *)

let P2BT_LIM_SUMMABLE_STATEMENT = new_definition
 `P2BT_LIM_SUMMABLE_STATEMENT (u:A->bool) (w:B->bool) <=>
   ?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
      sub (top:B topology) atlas g zl W phi Vl x e.
        &0 < eps /\ eps <= eps0 /\
        p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl /\
        apx_chain (top,atlas) g (&2 * eps) {i:int | &0 <= i} x (e:int->real^3->B)
        ==> ?D. !n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D`;;

(* Boxes under every point with approximant control (Claim 10.10). *)

let P2BT_LIM_BOXES_STATEMENT = new_definition
 `P2BT_LIM_BOXES_STATEMENT (u:A->bool) (w:B->bool) <=>
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl.
              &0 < eps /\ eps <= eps0 /\
              p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl
              ==> !y s1'. y IN topspace top /\ --inv(mfd_scalar atlas g y) < s1' /\ s1' < &0
                          ==> ?X a. open_in top X /\ compact_in top (top closure_of X) /\
                                    y IN X /\ a < s1' /\
                                    (!z. z IN X ==> --inv(mfd_scalar atlas g z) < a) /\
                                    (?Kb N. !k. N <= k
                                        ==> X SUBSET W k /\
                                            rfs_persists (V (sub k)) (IMAGE (phi k) X) a (&0) /\
                                            !s y'. a < s /\ s <= &0 /\ y' IN IMAGE (phi k) X
                                                   ==> mfd_rm_norm (rfs_vatlas (V (sub k)) s)
                                                                   (rfs_vmetric (V (sub k)) s) y'
                                                       <= Kb)`;;

(* Sectional curvature >= 0 on the box points (Claim 10.11). *)

let P2BT_LIM_SEC_STATEMENT = new_definition
 `P2BT_LIM_SEC_STATEMENT (u:A->bool) (w:B->bool) <=>
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl.
              &0 < eps /\ eps <= eps0 /\
              p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl
              ==> !s y w1 w2. s <= &0 /\ y IN topspace top /\
                              --inv(mfd_scalar atlas g y) < s /\ ~collinear {vec 0,w1,w2}
                              ==> &0 <= mfd_sectional (rfs_vatlas Vl s) (rfs_vmetric Vl s)
                                                      y w1 w2`;;

(* Evolving 2 eps-necks of normalized length 1/2 in the limit view at the   *)
(* points of large curvature (Claim 10.8 in corrected form).                *)

let P2BT_LIM_ENECK_STATEMENT = new_definition
 `P2BT_LIM_ENECK_STATEMENT (u:A->bool) (w:B->bool) <=>
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl.
              &0 < eps /\ eps <= eps0 /\
              p2bt_lctx eps C A V0 t Q V gamma s0 s1 EN A1 sub top atlas g zl W phi Vl
              ==> ?K. !y. y IN topspace top /\ K <= mfd_scalar atlas g y
                          ==> ?e. rfs_evolving_neck Vl (&2 * eps) y (&0) (&1 / &2) e`;;

