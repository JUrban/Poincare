(* ========================================================================= *)
(* pc_p2b_s2entreq (statement only): P2B_REQ_S2_ENTROPY_STATEMENT,           *)
(* Hamilton's entropy for 2-d Ricci flows on a surface parametrized by the   *)
(* standard S^2.  Used by SPLIT_ROUND; proved in pc_s2ent_flow.              *)
(* ========================================================================= *)

needs "src/pc_mfd_examples.ml";;
needs "src/pc_mfd_maps.ml";;
needs "src/pc_mfd_riem.ml";;
needs "src/pc_rf_basic.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The statement: Hamilton's entropy for 2-d Ricci flows on a surface        *)
(* parametrized by the standard S^2 (MT Cor 9.50(3) without the forward      *)
(* convergence: Chow-Knopf Prop 5.39 and Hamilton 1988).                     *)
(*                                                                           *)
(* A Ricci flow h(t), t < b (ancient), on a surface (top,atlas) with real^2 *)
(* charts that is diffeomorphic to the standard sphere (sphere2_atlas of    *)
(* pc_mfd_examples), with positive scalar curvature, which is backward      *)
(* asymptotically round in the weak sense that at arbitrarily negative      *)
(* times the scalar curvature is pinched, sup R <= (1 + e) inf R for every  *)
(* e > 0, has spatially constant scalar curvature at every time.            *)
(*                                                                           *)
(* Proof (pc_s2ent_calc, pc_s2ent_heat, pc_s2ent_flow): m = int R dA is      *)
(* constant in t; with A the area and r = m / A, E(t) =                      *)
(* int R log(R A / m) dA is >= 0 (pointwise x log x >= x - 1) with equality  *)
(* iff R is constant; dE/dt =                                                *)
(* int (R - r)^2 dA - int abs(grad R)^2 / R dA <= 0 (Hamilton's inequality,  *)
(* from an approximate Poisson equation for R - r obtained by the heat flow, *)
(* Cauchy-Schwarz and the 2-d Bochner identity); E is scale invariant and    *)
(* E(t) <= m log(1 + e) at a pinched time, so E = 0 later.                   *)
(*                                                                           *)
(* Degenerate cases: the shrinking round sphere h(t) = 2 (c - t) g_round     *)
(* (c >= b) satisfies every hypothesis (pinching 1 at all times) and the    *)
(* conclusion; the hypotheses force compactness and connectedness through   *)
(* the diffeomorphism; the pinching clause asks for times below every T, so *)
(* it is not satisfied by flows that are round only at late times (the     *)
(* statement would be false without it: start from a non-round metric).    *)
(* The King-Rosenau ancient solutions have R > 0 but are not pinched at     *)
(* early times, so they do not contradict the statement.                    *)
(* ========================================================================= *)

let P2B_REQ_S2_ENTROPY_STATEMENT = new_definition
 `P2B_REQ_S2_ENTROPY_STATEMENT (w:B->bool) <=>
    !top atlas (h:real->B->real^2^2) b (psi:real^3->B) (psi':B->real^3).
       hausdorff_space top /\
       mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                  (sphere(vec 0:real^3,&1))
                  top (atlas:((B->bool)#(B->real^2))->bool) (topspace top) psi psi' /\
       (!a. a < b ==> ricci_flow_on (top,atlas) a b h) /\
       (!t x. t < b /\ x IN topspace top ==> &0 < mfd_scalar atlas (h t) x) /\
       (!e T. &0 < e
              ==> ?t. t < T /\ t < b /\
                      !x y. x IN topspace top /\ y IN topspace top
                            ==> mfd_scalar atlas (h t) x <= (&1 + e) * mfd_scalar atlas (h t) y)
       ==> !t x y. t < b /\ x IN topspace top /\ y IN topspace top
                   ==> mfd_scalar atlas (h t) x = mfd_scalar atlas (h t) y`;;

