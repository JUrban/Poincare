(* ========================================================================= *)
(* pc_p2b_shrinkreq (statement only): P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT,  *)
(* compact gradient shrinking solitons of positive curvature are round, in   *)
(* dimensions 3 (MT 9.43 / Thm 4.24) and 2 (MT Cor 9.50(2)); proved in       *)
(* pc_rfa_s2 (RFA_P2B_REQ_SHRINKER_ROUND).  The definitions are shared by    *)
(* Part 2B and the pc_rfa units.  p2b_shrinker is a slice normalized as at   *)
(* time -1 of MT Thm 9.11: Ric + Hess f = g/2 with f smooth; p2b_mfd_hess is *)
(* the Hessian of pc_cmp_pdefs and p2b_round (constant positive sectional    *)
(* curvature) is from pc_p2b_defs.  Degenerate cases: the Gaussian soliton   *)
(* (Euclidean metric, f = |x|^2/4) satisfies p2b_shrinker but is not         *)
(* compact; an empty manifold has no compact-connected-shrinker issue since  *)
(* the hypotheses only quantify over topspace (vacuous conclusion holds for  *)
(* any k > 0).  The 2-d sign clause is sec > 0 (the split route of Part 2B   *)
(* makes K > 0 by the strong maximum principle).                             *)
(* ========================================================================= *)

needs "src/pc_cmp_pdefs.ml";;
needs "src/pc_p2b_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The shrinker slice and the statement.                                    *)
(* ------------------------------------------------------------------------- *)

let p2b_shrinker = new_definition
 `p2b_shrinker (top:B topology,atlas:((B->bool)#(B->real^N))->bool)
               (g:B->real^N^N) (f:B->real) <=>
    smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
    mfd_smooth_on atlas (topspace top) (\x:B. lift(f x)) /\
    !x u v. x IN topspace top
            ==> mfd_ricci atlas g x u v + p2b_mfd_hess atlas g f x u v =
                inv(&2) * (u dot (g x ** v))`;;

let P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT = new_definition
 `P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT (w:B->bool) <=>
    (!top atlas g f.
        hausdorff_space top /\ compact_space top /\ connected_space top /\
        p2b_shrinker (top,atlas:((B->bool)#(B->real^3))->bool) g f /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 < mfd_sectional atlas g x u v)
        ==> p2b_round (top,atlas) g) /\
    (!top atlas g f.
        hausdorff_space top /\ compact_space top /\ connected_space top /\
        p2b_shrinker (top,atlas:((B->bool)#(B->real^2))->bool) g f /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 < mfd_sectional atlas g x u v)
        ==> p2b_round (top,atlas) g)`;;

