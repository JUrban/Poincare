(* ========================================================================= *)
(* Unit pc_cmp_pdefs (comparison-geometry layer CMP): the Part 2B vocabulary *)
(* of the comparison-geometry statements, defined here once for all users    *)
(* (the Part 2B chain and the CMP proofs): the Hessian p2b_mfd_hess, the     *)
(* regular points p2b_dist_regular of a distance function and the line       *)
(* functions p2b_line_fn.  p2b_parallel_on and p2b_locally_split come from   *)
(* pc_p2b_splitreq, p2c_fgrad2 from pc_p2c_views, mfd_exp_dom, mfd_exp and   *)
(* mfd_tnorm from pc_geo_defs.  Definitions only.                            *)
(* ========================================================================= *)

needs "src/pc_p2b_splitreq.ml";;
needs "src/pc_p2c_views.ml";;
needs "src/pc_geo_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* Hessian of f at x in the preferred chart: the covariant derivative of df *)
(* for the local metric (lnabla of pc_lrg), evaluated on (u,v).             *)

let p2b_mfd_hess = new_definition
 `p2b_mfd_hess (atlas:((B->bool)#(B->real^N))->bool) (g:B->real^N^N) (f:B->real)
               (x:B) (u:real^N) (v:real^N) =
    lnabla 1 (metric_local atlas (chart_at atlas x) g)
      (\z w. drop(frechet_derivative (\y. lift(f(chart_inv (chart_at atlas x) y)))
                                    (at z) (w 1)))
      (SND(chart_at atlas x) x) (\m. if m = 1 then u else v)`;;

(* Regular points of d_p (Grove-Shiohama): a direction v at x making an     *)
(* obtuse angle with every minimizing direction w from x to p.             *)

let p2b_dist_regular = new_definition
 `p2b_dist_regular (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                   (g:B->real^3^3) (p:B) (x:B) <=>
    ?v. !w. w IN mfd_exp_dom (top,atlas) g x /\
            mfd_exp (top,atlas) g x w = p /\
            mfd_tnorm g x w = mfd_dist (top,atlas) g x p
            ==> v dot (g x ** w) < &0`;;

(* Line functions: smooth, |grad b| = 1 and Hess b = 0 on W.               *)

let p2b_line_fn = new_definition
 `p2b_line_fn (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (W:A->bool)
              (b:A->real) <=>
    mfd_smooth_on atlas W (\x. lift(b x)) /\
    (!x. x IN W ==> p2c_fgrad2 atlas g b x = &1) /\
    (!x u v. x IN W ==> p2b_mfd_hess atlas g b x u v = &0)`;;

