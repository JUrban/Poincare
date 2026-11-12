(* ========================================================================= *)
(* Unit pc_p2a_lxreq: two statements on minimizing L-geodesics in a chart,   *)
(* hypotheses of the proof of FL8 (MT Prop 9.9) in pc_p2a_fl99 and proved in *)
(* pc_p2a_wk3.  P2AW_FLOW_LX_DERIV_STATEMENT: at a point where the reduced   *)
(* length l (in a chart c, space-first z = pastecart x (lift tau)) is        *)
(* differentiable, every minimizer gamma to (chart_inv c x, tau) has chart   *)
(* velocity X at tau (d/ds of SND c (gamma(s^2)) at s = sqrt tau is 2        *)
(* sqrt(tau) X) with dl = G X (grad l = X) and 2 l_tau + |X|^2 - R + l / tau *)
(* = 0 (Perelman (7.6)).  P2AW_FLOW_MIN_END_STATEMENT: near its end a        *)
(* minimizer stays in the chart and its velocity A solves the L-geodesic     *)
(* equation (p2a_lacc).  Dimension 3.  Definitions only.                     *)
(* ========================================================================= *)

needs "src/pc_p2a_wk2.ml";;
needs "src/pc_p2a_smz.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AW_FLOW_LX_DERIV_STATEMENT = new_definition
 `P2AW_FLOW_LX_DERIV_STATEMENT (u:A->bool) <=>
   !top atlas a b (g:real->A->real^3^3) p (c:(A->bool)#(A->real^3)) x tau (gamma:real->A).
        p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ c IN atlas /\
        x IN IMAGE (SND c) (FST c) /\ &0 < tau /\ tau < b - a /\
        p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
        gamma tau = chart_inv c x /\
        (\w. lift(p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p) w))
          differentiable (at (pastecart x (lift tau)))
        ==> ?X. ((\v. SND c (gamma(drop v pow 2))) has_vector_derivative (&2 * sqrt tau) % X)
                  (at (lift(sqrt tau)) within {v | &0 <= drop v /\ drop v pow 2 <= tau}) /\
                (!i. 1 <= i /\ i <= 3
                     ==> wan_xder i
                           (p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                                b p))
                           (pastecart x (lift tau)) =
                         (p2bw_cmet atlas c b g (pastecart x (lift tau)) ** X)$i) /\
                wan_tder
                  (p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                  (pastecart x (lift tau)) =
                (p2bw_cscal atlas c b g (pastecart x (lift tau)) -
                 X dot (p2bw_cmet atlas c b g (pastecart x (lift tau)) ** X)) / &2 -
                p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)
                          (pastecart x (lift tau)) / (&2 * tau)`;;

let P2AW_FLOW_MIN_END_STATEMENT = new_definition
 `P2AW_FLOW_MIN_END_STATEMENT (u:A->bool) <=>
   !top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) (c:(A->bool)#(A->real^3)).
        p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ c IN atlas /\
        p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
        tau < b - a /\ gamma tau IN FST c
        ==> ?s0 A. &0 < s0 /\ s0 < sqrt tau /\
                   (!s. s0 <= s /\ s <= sqrt tau ==> gamma(s pow 2) IN FST c) /\
                   A continuous_on interval[lift s0,lift(sqrt tau)] /\
                   (!s. s0 < s /\ s < sqrt tau
                        ==> ((\v. SND c (gamma(drop v pow 2))) has_vector_derivative A(lift s))
                              (at (lift s))) /\
                   ((\v. SND c (gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
                     (at (lift(sqrt tau)) within {v | &0 <= drop v /\ drop v pow 2 <= tau}) /\
                   (!s. s0 <= s /\ s <= sqrt tau
                        ==> (A has_vector_derivative
                               p2a_lacc (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                                    (FST c) b c) b s
                                        (SND c (gamma(s pow 2))) (A(lift s)))
                            (at (lift s) within interval[lift s0,lift(sqrt tau)]))`;;

