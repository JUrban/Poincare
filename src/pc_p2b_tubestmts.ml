(* ========================================================================= *)
(* pc_p2b_tubestmts (statements and one assembly theorem): the route         *)
(* statement of the bad-tube half of MT Thm 10.2 (Sec 10.3, Claims           *)
(* 10.3-10.11, Prop 10.7) and two statements on the Appendix layer, in the   *)
(* style of P2B_APX_A6_CS_STATEMENT of pc_p2b_defs.                          *)
(*                                                                           *)
(* P2BT_REQ_A21_CH_STATEMENT: MT Prop A.21 for a compact connected X whose *)
(* points are centres of NK-necks or lie in cap cores, with the chains of  *)
(* the proof exposed: X lies in a compact component, or in one cap, or     *)
(* in a cap followed by a balanced chain whose first neck is the cap's end *)
(* neck (inner end at the core, lower half of compact closure) and whose   *)
(* other necks are X-centred NK-necks, or in the union of a balanced chain *)
(* of X-centred NK-necks.  Used for the confinement of minimizing curves   *)
(* (MT Claim 10.3), whose case split needs the chain centres.  Proved in    *)
(* pc_apx_a21ch.                                                            *)
(*                                                                           *)
(* P2BT_REQ_CHAIN_CHART_STATEMENT: the union of a one-sided infinite chain  *)
(* (sphere separation) is the image of one parametrization of the region   *)
(* beyond the inner sphere of the first neck, equal to the first neck near *)
(* that sphere, and each finite union lies in the image of a bounded part. *)
(* Used for the chart H of the bad tube; proved in pc_apx_chchart.          *)
(*                                                                           *)
(* P2B_BAD_TUBE_ROUTE_STATEMENT: the general local-limit statement          *)
(* (pc_p2b_lcreqg), A.1, A.6 and A.8 for constant-speed minimizers and the  *)
(* two statements above imply P2B_BAD_TUBE_FROM_FAILURE_STATEMENT.  The     *)
(* limit type B is that of the bad tube.                                    *)
(* ========================================================================= *)

needs "src/pc_p2b_lcreqg.ml";;
needs "src/pc_apx_csreq.ml";;

prioritize_real();;
type_invention_error := true;;

let P2BT_REQ_A21_CH_STATEMENT = new_definition
 `P2BT_REQ_A21_CH_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas g NK X.
         &0 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas (g:A->real^3^3) /\ apx_sphere_sep top atlas /\
         compact_in top X /\ connected_in top X /\ ~(X = {}) /\
         (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
         (!x. x IN X
              ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y))
         ==> (?V. V IN connected_components_of top /\ compact_in top V /\ X SUBSET V) \/
             (?U Y. rfs_cap (top,atlas) g C eps U Y /\ X SUBSET U) \/
             (?U Y a b x e.
                  rfs_cap (top,atlas) g C eps U Y /\ a < b /\
                  apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
                  IMAGE (e a) (rfs_neck_dom eps) = U DIFF top closure_of Y /\
                  ~(top closure_of (IMAGE (e a) (apx_slab (--inv eps) (&0))) INTER
                    top closure_of Y = {}) /\
                  compact_in top (top closure_of (IMAGE (e a) (apx_slab (--inv eps) (&0)))) /\
                  (!i. a < i /\ i <= b
                       ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
                  X SUBSET U UNION apx_chain_union eps {i:int | a <= i /\ i <= b} e /\
                  ~DISJOINT X (top closure_of Y)) \/
             (?a b x e.
                 a <= b /\
                 apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
                 (!i. a <= i /\ i <= b
                      ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
                 X SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e)`;;

let P2BT_REQ_CHAIN_CHART_STATEMENT = new_definition
 `P2BT_REQ_CHAIN_CHART_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !top atlas g eps x e.
         &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
         riemannian_metric atlas (g:B->real^3^3) /\ apx_sphere_sep top atlas /\
         apx_chain (top,atlas) g eps {i:int | &0 <= i} x (e:int->real^3->B)
         ==> ?E. mfd_param top atlas {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} E /\
                 (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
                 IMAGE E {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} =
                 apx_chain_union eps {i:int | &0 <= i} e /\
                 (!n. ?rho. apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e SUBSET
                            IMAGE E (apx_slab (--inv eps) rho))`;;

let P2B_BAD_TUBE_ROUTE_STATEMENT = new_definition
 `P2B_BAD_TUBE_ROUTE_STATEMENT (u:A->bool) (w:B->bool) <=>
    P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT u w /\
    APX_A1_STATEMENT u /\ P2B_APX_A6_CS_STATEMENT u /\ APX_A8_CS_STATEMENT u /\
    P2BT_REQ_A21_CH_STATEMENT u /\ P2BT_REQ_CHAIN_CHART_STATEMENT w
    ==> P2B_BAD_TUBE_FROM_FAILURE_STATEMENT u w`;;

(* Assembly with the other half (P2B_THM_10_2_FROM_PARTS): the route, its   *)
(* inputs and the no-bad-tube half give P2C_REQ_THM_10_2_VIEW_STATEMENT at  *)
(* type u.                                                                  *)

let P2BT_THM_10_2_FROM_ROUTE = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_BAD_TUBE_ROUTE_STATEMENT u w /\
     P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT u w /\
     APX_A1_STATEMENT u /\ P2B_APX_A6_CS_STATEMENT u /\ APX_A8_CS_STATEMENT u /\
     P2BT_REQ_A21_CH_STATEMENT u /\ P2BT_REQ_CHAIN_CHART_STATEMENT w /\
     P2B_NO_BAD_TUBE_STATEMENT w
     ==> P2C_REQ_THM_10_2_VIEW_STATEMENT u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_BAD_TUBE_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2B_THM_10_2_FROM_PARTS THEN EXISTS_TAC `w:B->bool` THEN
  ASM_MESON_TAC[]);;

