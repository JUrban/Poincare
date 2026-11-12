(* ========================================================================= *)
(* Unit pc_p2c_e994s (Part 2C): the statements of two steps of the proof of  *)
(* MT Thm 9.89 (2) for compact kappa-solutions (used for COR_9_94_L).        *)
(*                                                                           *)
(* P2KC_CLAIM_9_90: MT Claim 9.90 (p. 240) in a uniform form with length L.  *)
(* For eps small and L at least 1 there are C0 and D1 such that every point  *)
(* of a compact kappa-solution with ksep has p2b_canon_L C0 eps L at time 0  *)
(* as soon as d(p,q)^2 R(z) > D1^2 at time 0 for some points p, q, z (an     *)
(* existential form of diam^2 max R > D1^2).  Proof idea: contradiction with *)
(* C0 = the constant of P2B_KSOL_NONCOMPACT_CANON_L at length L + 1.  Bad    *)
(* points x_k with D1 = k; round slices are excluded (an eps-round           *)
(* component, P2KC_ROUND_CANON); otherwise kappa0 from PROP_9_58, normalise  *)
(* R(x_k,0) = 1 (R > 0 by P2KC_COMPACT_R_POS from PROP_9_83K; then           *)
(* RFA_C971_KSOL_SCALE, P2KC_CANON_L_RESCALE), THM_9_64.  Noncompact limit:  *)
(* canon_L at length L + 1 at the limit base point, then                     *)
(* P2B_LIMIT_TRANSFER_VIEW.  Compact limit: the image of the limit is all of *)
(* M_k (P2BL_COMPONENT_IMAGE), the metrics are close (P2BL_FLOW_LIMIT_CLOSE, *)
(* LIM_DIST_COMPARE), so d^2 R stays bounded: a contradiction.               *)
(*                                                                           *)
(* P2KC_LARGE_DR: a compact kappa-solution with ksep that is not round at    *)
(* time 0 has times t <= 0 with d(p,q)^2 R(z) at time t as large as wanted.  *)
(* Proof idea: ASYM_SOLITON; the limit is not compact and round (COR_9_44    *)
(* with t0 = 0), so it is the cylinder model, which is not compact           *)
(* (P2BSK_CYL_NOT_COMPACT); at a limit time s in (0,1), say 1/2, far points  *)
(* of the complete noncompact limit and R > 0 at a nonflat point of the      *)
(* shifted limit kappa-solution (P2BX0_RM_NORM_LE_HALF_SCALAR) pass to the   *)
(* rescaled slices at -tau_k + s tau_k (P2BL_FLOW_LIMIT_CLOSE,               *)
(* LIM_DIST_COMPARE), and d^2 R is scale invariant.                          *)
(*                                                                           *)
(* Both are used in the proof of P2B_KSOL_COMPACT_CANON_L_ROUTE              *)
(* (pc_p2c_e994; MT Thm 9.89 (2), the topology clause of the C-component, MT *)
(* p. 241); they are proved in pc_p2c_c990 and pc_p2b_largedr.               *)
(* ========================================================================= *)

needs "src/pc_p2b_c994req.ml";;

prioritize_real();;
type_invention_error := true;;

let P2KC_CLAIM_9_90_STATEMENT = new_definition
 `P2KC_CLAIM_9_90_STATEMENT (w:B->bool) <=>
    ?eps4. &0 < eps4 /\
      !eps L. &0 < eps /\ eps <= eps4 /\ &1 <= L
        ==> ?C0 D1. &1 < C0 /\ &0 < D1 /\
              !kappa top atlas (g:real->B->real^3^3) x p q z.
                 p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                 compact_space top /\ x IN topspace top /\
                 p IN topspace top /\ q IN topspace top /\ z IN topspace top /\
                 D1 pow 2 < mfd_dist (top,atlas) (g (&0)) p q pow 2 *
                            mfd_scalar atlas (g (&0)) z
                 ==> p2b_canon_L (p2b_kview (top,atlas) g) C0 eps L x (&0)`;;

let P2KC_CLAIM_9_90_ROUTE_STATEMENT = new_definition
 `P2KC_CLAIM_9_90_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_PROP_9_83K_STATEMENT w /\ P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT w /\
    P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w
    ==> P2KC_CLAIM_9_90_STATEMENT w`;;

let P2KC_LARGE_DR_STATEMENT = new_definition
 `P2KC_LARGE_DR_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) D.
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
       compact_space top /\ ~p2b_round (top,atlas) (g (&0))
       ==> ?t p q z. t <= &0 /\
                     p IN topspace top /\ q IN topspace top /\ z IN topspace top /\
                     D pow 2 < mfd_dist (top,atlas) (g t) p q pow 2 *
                               mfd_scalar atlas (g t) z`;;

let P2KC_LARGE_DR_ROUTE_STATEMENT = new_definition
 `P2KC_LARGE_DR_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_ASYM_SOLITON_STATEMENT w /\ P2B_COR_9_44_STATEMENT w
    ==> P2KC_LARGE_DR_STATEMENT w`;;

