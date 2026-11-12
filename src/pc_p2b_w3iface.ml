(* ========================================================================= *)
(* Unit pc_p2b_w3iface (Part 2B): the statement W3,                          *)
(* P2B_REQ_P2A_WEAK_STATEMENT (MT Prop 7.5, Thm 7.13 in weak form, Cor 6.51  *)
(* at the smooth points; proved in pc_p2a_weak as P2AW_W3), and the shared   *)
(* vocabulary of the Prop 9.20 layer (unit pc_p2b_w920 loads this one).      *)
(*                                                                           *)
(* Space-time points z of real^(N,1)finite_sum (time is the last            *)
(* coordinate), backward time tau = drop(sndcart z) > 0.  In a              *)
(* chart, rho = sqrt(det G) is the density and A = rho G^-1, so that        *)
(* |grad u|^2 dvol = p2bw_bil A u u dx and <grad u, grad v> dvol =          *)
(* p2bw_bil A u v dx.  n = dimindex(:N).  p2bw_t1, p2bw_t2: the two         *)
(* inequalities of MT Thm 7.13 (MT p. 156, second display) integrated over  *)
(* tau against nonnegative space-time test functions; p2bw_tid: the         *)
(* identity l_tau = (R - |grad l|^2)/2 - l/(2 tau) of Cor 6.51 (sum of the  *)
(* two equalities with delta) almost everywhere.                            *)
(* P2B_REQ_P2A_WEAK_STATEMENT: for the hypotheses of p2a_cbflow plus        *)
(* connected_space (without it l is junk on components                      *)
(* without p) and any chart c, l = p2a_lx ... b p is locally Lipschitz on   *)
(* the space-time chart domain and satisfies p2bw_t1, p2bw_t2, p2bw_tid.     *)
(* ========================================================================= *)

needs "src/pc_wan_defs.ml";;
needs "src/pc_p2a_defs.ml";;

prioritize_real();;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The divergence-form bilinear expression and the weak inequalities.        *)
(* ------------------------------------------------------------------------- *)

let p2bw_bil = new_definition
 `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) (u:real^(N,1)finite_sum->real)
           (v:real^(N,1)finite_sum->real) (z:real^(N,1)finite_sum) =
    sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N)) (\j. A z$i$j * wan_xder i u z * wan_xder j v z))`;;

(* MT Thm 7.13 in the space-time weak form (the slice inequalities          *)
(* integrated against space-time tests), and the identity of Cor 6.51 at    *)
(* smooth points (almost everywhere).  n = dimindex(:N).                     *)

let p2bw_t1 = new_definition
 `p2bw_t1 (om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N)
          (rho:real^(N,1)finite_sum->real) (R:real^(N,1)finite_sum->real)
          (l:real^(N,1)finite_sum->real) <=>
    !phi. wan_test om phi /\ (!z. &0 <= phi z)
          ==> &0 <= drop(integral om
                       (\z. lift(phi z * (wan_tder l z * rho z + p2bw_bil A l l z +
                                          (&(dimindex(:N)) / (&2 * drop(sndcart z)) - R z) *
                                          rho z) +
                                 p2bw_bil A l phi z)))`;;

let p2bw_t2 = new_definition
 `p2bw_t2 (om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N)
          (rho:real^(N,1)finite_sum->real) (R:real^(N,1)finite_sum->real)
          (l:real^(N,1)finite_sum->real) <=>
    !phi. wan_test om phi /\ (!z. &0 <= phi z)
          ==> drop(integral om
                (\z. lift(phi z * (--(p2bw_bil A l l z) +
                                   (R z + (l z - &(dimindex(:N))) / drop(sndcart z)) * rho z) -
                          &2 * p2bw_bil A l phi z))) <= &0`;;

let p2bw_tid = new_definition
 `p2bw_tid (om:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N)
           (rho:real^(N,1)finite_sum->real) (R:real^(N,1)finite_sum->real)
           (l:real^(N,1)finite_sum->real) <=>
    negligible {z | z IN om /\
                    ~(wan_tder l z * rho z =
                      (R z * rho z - p2bw_bil A l l z) / &2 -
                      l z / (&2 * drop(sndcart z)) * rho z)}`;;

(* ------------------------------------------------------------------------- *)
(* Chart data of a flow in backward time tau = b - t: the space-time chart  *)
(* domain, the chart metric, density, divergence-form coefficient, scalar   *)
(* curvature, and functions of (tau, point) read in the chart.               *)
(* ------------------------------------------------------------------------- *)

let p2bw_cdom = new_definition
 `p2bw_cdom (c:(A->bool)#(A->real^N)) (tmax:real) =
    {z:real^(N,1)finite_sum | fstcart z IN IMAGE (SND c) (FST c) /\
                              &0 < drop(sndcart z) /\ drop(sndcart z) < tmax}`;;

let p2bw_cmet = new_definition
 `p2bw_cmet (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N)) (b:real)
            (g:real->A->real^N^N) (z:real^(N,1)finite_sum) =
    metric_local atlas c (g(b - drop(sndcart z))) (fstcart z)`;;

let p2bw_crho = new_definition
 `p2bw_crho (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N)) (b:real)
            (g:real->A->real^N^N) (z:real^(N,1)finite_sum) =
    sqrt(det(p2bw_cmet atlas c b g z))`;;

let p2bw_cA = new_definition
 `p2bw_cA (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N)) (b:real)
          (g:real->A->real^N^N) (z:real^(N,1)finite_sum) =
    p2bw_crho atlas c b g z %% matrix_inv(p2bw_cmet atlas c b g z)`;;

let p2bw_cscal = new_definition
 `p2bw_cscal (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N)) (b:real)
             (g:real->A->real^N^N) (z:real^(N,1)finite_sum) =
    mfd_scalar atlas (g(b - drop(sndcart z))) (chart_inv c (fstcart z))`;;

let p2bw_cfun = new_definition
 `p2bw_cfun (c:(A->bool)#(A->real^N)) (f:real->A->real) (z:real^(N,1)finite_sum) =
    f (drop(sndcart z)) (chart_inv c (fstcart z))`;;

(* ------------------------------------------------------------------------- *)
(* The statement W3, proved in pc_p2a_weak.                                  *)
(* ------------------------------------------------------------------------- *)

let P2B_REQ_P2A_WEAK_STATEMENT = new_definition
 `P2B_REQ_P2A_WEAK_STATEMENT (u:A->bool) <=>
    !top atlas a b (g:real->A->real^3^3) p c.
       hausdorff_space top /\ connected_space top /\ a < b /\
       ricci_flow_from (top,atlas) a b g /\ rfs_flow_upto (top,atlas) a b g /\
       (!t. a <= t /\ t <= b ==> mfd_complete (top,atlas) (g t)) /\
       (?K. !t y. a <= t /\ t <= b /\ y IN topspace top ==> mfd_rm_norm atlas (g t) y <= K) /\
       p IN topspace top /\ c IN atlas
       ==> wan_loclip (p2bw_cdom c (b - a))
             (p2bw_cfun c (p2a_lx (rfs_flow_view (top,atlas) (real_interval[a,b]) g) b p)) /\
           p2bw_t1 (p2bw_cdom c (b - a)) (p2bw_cA atlas c b g) (p2bw_crho atlas c b g)
             (p2bw_cscal atlas c b g)
             (p2bw_cfun c (p2a_lx (rfs_flow_view (top,atlas) (real_interval[a,b]) g) b p)) /\
           p2bw_t2 (p2bw_cdom c (b - a)) (p2bw_cA atlas c b g) (p2bw_crho atlas c b g)
             (p2bw_cscal atlas c b g)
             (p2bw_cfun c (p2a_lx (rfs_flow_view (top,atlas) (real_interval[a,b]) g) b p)) /\
           p2bw_tid (p2bw_cdom c (b - a)) (p2bw_cA atlas c b g) (p2bw_crho atlas c b g)
             (p2bw_cscal atlas c b g)
             (p2bw_cfun c (p2a_lx (rfs_flow_view (top,atlas) (real_interval[a,b]) g) b p))`;;

