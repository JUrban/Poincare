(* ========================================================================= *)
(* pc_p2a_fldefs: the flow interface of the P2A layer.  MT Ch 7 for ordinary *)
(* Ricci flows that are complete with bounded curvature (MT Def 7.1) on      *)
(* [a,b], base point x = (p,b), as statement constants FL0-FL9 and FL5R.     *)
(* Statements only.                                                          *)
(*                                                                           *)
(* Everything is generic in the dimension N: the view is p2a_flow_view and   *)
(* the smoothness up to b is p2a_flow_upto (pc_p2a_defs, the real^N copies   *)
(* of rfs_flow_view and rfs_flow_upto), so the 2-d instances for Cor 9.50    *)
(* are the same constants at N = 2.  Each statement constant takes           *)
(* (u:A->bool) (n:N->bool), which only fix the types; an instance may be     *)
(* proved for one N alone.  n = dimindex(:N): min l <= n/2 (FL4),            *)
(* (4 pi)^(n/2) written sqrt(4 pi) pow n (FL5, FL5R), kappa r^n (FL6).       *)
(* FL8 assumes dimindex(:N) <= 3, where sec >= 0 is the nonnegative          *)
(* curvature operator of MT Prop 9.9 (Hamilton's Harnack).                   *)
(*                                                                           *)
(* FL7 uses connected_space: for q off the component of p both sides are the *)
(* junk inf of the empty set, scaled differently.  FL8 and FL5R are the      *)
(* forms used in Part 2B, made generic.  FL9 is the L-geometry part of MT    *)
(* Lemma 9.25 (minimizers whose velocity is grad l, Cor 6.29).  At N = 3:    *)
(* P2AF_CBFLOW_3, P2AF_FRV_3, P2AF_4PI_3 (and P2A_FLOW_VIEW_3).              *)
(*                                                                           *)
(* The first part: needs lines, the two definitions, the 3-d bridges.        *)
(* ========================================================================= *)

needs "src/pc_p2a_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* MT Def 7.1 on the closed interval [a,b]: a Ricci flow smooth on [a,b]    *)
(* (from a, ricci_flow_from; up to b, p2a_flow_upto), complete at every     *)
(* time, with bounded curvature.                                             *)

let p2a_cbflow = new_definition
 `p2a_cbflow (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (a:real) (b:real)
             (g:real->A->real^N^N) <=>
    hausdorff_space top /\ a < b /\
    ricci_flow_from (top,atlas) a b g /\ p2a_flow_upto (top,atlas) a b g /\
    (!t. a <= t /\ t <= b ==> mfd_complete (top,atlas) (g t)) /\
    (?K. !t y. a <= t /\ t <= b /\ y IN topspace top ==> mfd_rm_norm atlas (g t) y <= K)`;;

(* The reduced volume of the slice at backward time tau from (p,b): the     *)
(* integral of tau^(-n/2) exp(-l) over M for g(b - tau) (MT Def 6.70 with   *)
(* A = M, Thm 7.26; no (4 pi)^(-n/2) factor).                               *)

let p2a_frv = new_definition
 `p2a_frv (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (a:real) (b:real)
          (g:real->A->real^N^N) (p:A) (tau:real) =
    mfd_integral (top,atlas) (g (b - tau)) (topspace top)
      (\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q)) /
           sqrt tau pow dimindex(:N))`;;

(* At N = 3: the hypotheses of W3 (pc_p2b_w3iface) are p2a_cbflow; the      *)
(* reduced volume and the constant in their 3-d forms, as used in Part 2B.  *)

let P2AF_CBFLOW_3 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) a b g.
     p2a_cbflow (top,atlas) a b g <=>
     hausdorff_space top /\ a < b /\
     ricci_flow_from (top,atlas) a b g /\ rfs_flow_upto (top,atlas) a b g /\
     (!t. a <= t /\ t <= b ==> mfd_complete (top,atlas) (g t)) /\
     (?K. !t y. a <= t /\ t <= b /\ y IN topspace top ==> mfd_rm_norm atlas (g t) y <= K)`,
  REWRITE_TAC[p2a_cbflow; P2A_FLOW_UPTO_3]);;

let P2AF_FRV_3 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) a b g p tau.
     &0 <= tau
     ==> p2a_frv (top,atlas) a b g p tau =
         mfd_integral (top,atlas) (g (b - tau)) (topspace top)
           (\q. exp(--(p2a_lx (rfs_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q)) /
                (tau * sqrt tau))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p2a_frv; P2A_FLOW_VIEW_3; DIMINDEX_3;
              REAL_ARITH `x pow 3 = x pow 2 * x`] THEN
  ASM_SIMP_TAC[SQRT_POW_2]);;

let P2AF_4PI_3 = prove
 (`sqrt(&4 * pi) pow dimindex(:3) = (&4 * pi) * sqrt(&4 * pi)`,
  REWRITE_TAC[DIMINDEX_3; REAL_ARITH `x pow 3 = x pow 2 * x`] THEN
  SIMP_TAC[SQRT_POW_2; REAL_LE_MUL; REAL_POS; PI_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* The statement constants FL0-FL9 and FL5R.  Throughout, the flow is       *)
(* p2a_cbflow (top,atlas) a b g, the view is p2a_flow_view (top,atlas)      *)
(* (real_interval[a,b]) g, the base point is (p,b), and backward time tau   *)
(* runs in (0, b - a).                                                      *)
(* ------------------------------------------------------------------------- *)

(* FL0 (bridge): the view of such a flow is a smooth view setting; every    *)
(* open set is a region on every subinterval, interior times are smooth,    *)
(* the top time is backward-smooth.                                          *)

let P2A_FLOW_VIEW_STATEMENT = new_definition
 `P2A_FLOW_VIEW_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g.
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g
       ==> p2a_svs (p2a_flow_view (top,atlas) (real_interval[a,b]) g) /\
           (!W a' b'. open_in top W /\ a <= a' /\ a' < b' /\ b' <= b
                      ==> p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b]) g) W a' b') /\
           (!y t. y IN topspace top /\ a < t /\ t < b
                  ==> p2a_smooth (p2a_flow_view (top,atlas) (real_interval[a,b]) g) y t) /\
           (!y. y IN topspace top
                ==> p2a_bsmooth (p2a_flow_view (top,atlas) (real_interval[a,b]) g) y b)`;;

(* FL1 (MT Lemma 7.2 proof, Claim 7.11 proof): curves of bounded L-length   *)
(* from (p,b) stay in a compact set.                                         *)

let P2A_FLOW_PROPER_STATEMENT = new_definition
 `P2A_FLOW_PROPER_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g p Lb.
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\ p IN topspace top
       ==> ?C. compact_in top C /\
               !tau gamma.
                  &0 < tau /\ tau < b - a /\
                  p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
                  p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau
                  <= Lb
                  ==> !s. &0 <= s /\ s <= tau ==> gamma s IN C`;;

(* FL2 (MT Lemma 7.2): minimizers exist from (p,b) to every point at every  *)
(* backward time in (0, b - a), on a connected manifold.                    *)

let P2A_FLOW_MIN_EXISTS_STATEMENT = new_definition
 `P2A_FLOW_MIN_EXISTS_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g p q tau.
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       connected_space top /\ p IN topspace top /\ q IN topspace top /\
       &0 < tau /\ tau < b - a
       ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
                   gamma tau = q`;;

(* FL3 (MT Prop 7.5(1), Cor 7.6): l is continuous on M x (0, b - a).        *)

let P2A_FLOW_LX_CONT_STATEMENT = new_definition
 `P2A_FLOW_LX_CONT_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g p tau0 q0 e.
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       connected_space top /\ p IN topspace top /\ q0 IN topspace top /\
       &0 < tau0 /\ tau0 < b - a /\ &0 < e
       ==> ?d O. &0 < d /\ open_in top O /\ q0 IN O /\
                 !tau q. abs(tau - tau0) < d /\ q IN O
                         ==> abs(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                        b p tau q -
                                 p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                        b p tau0 q0) < e`;;

(* FL4 (MT Thm 7.10 with Claim 7.11): l(., tau) has a minimum, at most n/2. *)

let P2A_FLOW_THM_7_10_STATEMENT = new_definition
 `P2A_FLOW_THM_7_10_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g p tau.
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       connected_space top /\ p IN topspace top /\ &0 < tau /\ tau < b - a
       ==> ?q. q IN topspace top /\
               (!q'. q' IN topspace top
                     ==> p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q <=
                         p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q') /\
               p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q <=
               &(dimindex(:N)) / &2`;;

(* FL5 (MT Thm 7.26): the reduced volume is finite (absolutely integrable   *)
(* integrand), positive, at most (4 pi)^(n/2), non-increasing in tau, and   *)
(* tends to (4 pi)^(n/2) as tau tends to 0.                                  *)

let P2A_FLOW_RV_STATEMENT = new_definition
 `P2A_FLOW_RV_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g p.
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       connected_space top /\ p IN topspace top
       ==> (!tau. &0 < tau /\ tau < b - a
                  ==> mfd_integrable_on (top,atlas) (g (b - tau))
                        (\q. exp(--(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                           b p tau q)) / sqrt tau pow dimindex(:N))
                        (topspace top) /\
                      &0 < p2a_frv (top,atlas) a b g p tau /\
                      p2a_frv (top,atlas) a b g p tau <= sqrt(&4 * pi) pow dimindex(:N)) /\
           (!tau1 tau2. &0 < tau1 /\ tau1 <= tau2 /\ tau2 < b - a
                        ==> p2a_frv (top,atlas) a b g p tau2 <=
                            p2a_frv (top,atlas) a b g p tau1) /\
           ((\tau. p2a_frv (top,atlas) a b g p tau) ---> sqrt(&4 * pi) pow dimindex(:N))
           (atreal (&0) within {tau | &0 < tau})`;;

(* FL5R (MT Prop 7.27 in the form MT Cor 9.14 uses): reduced volume equal   *)
(* to (4 pi)^(n/2) at some tau0 forces flatness on [b - tau0, b].            *)

let P2A_FLOW_RV_RIGID_STATEMENT = new_definition
 `P2A_FLOW_RV_RIGID_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g p tau0.
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       connected_space top /\ p IN topspace top /\ &0 < tau0 /\ tau0 < b - a /\
       p2a_frv (top,atlas) a b g p tau0 = sqrt(&4 * pi) pow dimindex(:N)
       ==> !t x v1 v2. b - tau0 <= t /\ t <= b /\ x IN topspace top /\
                       ~collinear {vec 0,v1,v2}
                       ==> mfd_sectional atlas (g t) x v1 v2 = &0`;;

(* FL6 (MT Thm 8.1 for complete flows): kappa-noncollapsing at scale r      *)
(* from an open set of volume at least V0 at backward time tau0 on which    *)
(* l <= l0.                                                                   *)

let P2A_FLOW_THM_8_1_STATEMENT = new_definition
 `P2A_FLOW_THM_8_1_STATEMENT (u:A->bool) (n:N->bool) <=>
    !taub l0 V0. &0 < taub /\ &0 < V0
      ==> ?kappa. &0 < kappa /\
            !top atlas a b g p r tau0 B.
               p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
               connected_space top /\ p IN topspace top /\
               &0 < tau0 /\ tau0 <= taub /\ tau0 < b - a /\ &0 < r /\ r pow 2 <= tau0 /\
               (!s y. b - r pow 2 < s /\ s <= b /\ y IN mfd_ball (top,atlas) (g b) p r
                      ==> mfd_rm_norm atlas (g s) y <= inv(r pow 2)) /\
               open_in top B /\
               (?v. mfd_has_volume (top,atlas) (g (b - tau0)) B v /\ V0 <= v) /\
               (!q. q IN B
                    ==> p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 q
                        <= l0)
               ==> ?v. mfd_has_volume (top,atlas) (g b) (mfd_ball (top,atlas) (g b) p r) v /\
                       kappa * r pow dimindex(:N) <= v`;;

(* FL7 (MT Lemmas 6.72-6.75, Cor 6.74): the reduced length is invariant     *)
(* under parabolic rescaling, g'(t) = Q g(t / Q) on [Q a, Q b], base time   *)
(* Q b, backward time Q tau.                                                  *)

let P2A_FLOW_SCALING_STATEMENT = new_definition
 `P2A_FLOW_SCALING_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g p Q tau q.
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       connected_space top /\ p IN topspace top /\ q IN topspace top /\
       &0 < Q /\ &0 < tau /\ tau < b - a
       ==> p2a_lx (p2a_flow_view (top,atlas) (real_interval[Q * a,Q * b])
                                 (\t. \y. Q %% g (t / Q) y)) (Q * b) p (Q * tau) q =
           p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q`;;

(* FL8 (MT Prop 9.9; input Hamilton's Harnack inequality): for sec >= 0 on  *)
(* [a,b] and 0 < c < 1, at every (q,tau) with tau <= (1 - c)(b - a) where   *)
(* l is differentiable in (tau, chart coordinates of chart_at atlas q),     *)
(* z = pastecart (lift tau) y, the bounds on |grad l|^2 + R and on dl/dtau. *)

let P2A_FLOW_PROP_9_9_STATEMENT = new_definition
 `P2A_FLOW_PROP_9_9_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g p c.
       dimindex(:N) <= 3 /\
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       connected_space top /\ p IN topspace top /\ &0 < c /\ c < &1 /\
       (!t x v1 v2. a <= t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,v1,v2}
                    ==> &0 <= mfd_sectional atlas (g t) x v1 v2)
       ==> !tau q d1.
              &0 < tau /\ tau <= (&1 - c) * (b - a) /\ q IN topspace top /\
              ((\z. lift(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                               (drop(fstcart z)) (chart_inv (chart_at atlas q) (sndcart z))))
               has_derivative d1) (at (pastecart (lift tau) (SND(chart_at atlas q) q)))
              ==> lgrad2 (metric_local atlas (chart_at atlas q) (g(b - tau)))
                         (\y. p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                                     (chart_inv (chart_at atlas q) y))
                         (SND(chart_at atlas q) q) +
                  mfd_scalar atlas (g(b - tau)) q
                  <= (&1 + &2 / c) *
                     p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q / tau /\
                  mfd_scalar atlas (g(b - tau)) q -
                  (&1 + &1 / c) *
                  p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau q / tau
                  <= drop(d1 (pastecart (lift(&1)) (vec 0)))`;;

(* FL9 (the L-geometry part of MT Lemma 9.25 and Cor 9.26: Lemma 7.2,       *)
(* Props 6.30, 6.31 and Cor 6.29 along minimizers): to every (q,tau) there  *)
(* is a minimizer gamma from (p,b) such that (i) for 0 < s <= tau,          *)
(* 2 sqrt(s) l(gamma s, s) is the integral over [0,s] of the L-integrand of *)
(* gamma (the restrictions are minimizers); (ii) for 0 < s < tau, l is      *)
(* differentiable at (gamma s, s) in (tau, chart coordinates of             *)
(* chart_at atlas (gamma s)), the convention of FL8, and the velocity v of  *)
(* gamma at s is grad l there: dl(w) = v . G w, G the chart metric.         *)

let P2A_FLOW_MIN_GRAD_STATEMENT = new_definition
 `P2A_FLOW_MIN_GRAD_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b g p tau q.
       p2a_cbflow (top,atlas:((A->bool)#(A->real^N))->bool) a b g /\
       connected_space top /\ p IN topspace top /\ q IN topspace top /\
       &0 < tau /\ tau < b - a
       ==> ?gamma.
             p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
             gamma tau = q /\
             (!s. &0 < s /\ s <= tau
                  ==> &2 * sqrt s *
                      p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p s (gamma s) =
                      real_integral (real_interval[&0,s])
                        (p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                         b gamma tau)) /\
             (!s. &0 < s /\ s < tau
                  ==> (?d1. ((\z. lift(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                             b p (drop(fstcart z))
                                             (chart_inv (chart_at atlas (gamma s)) (sndcart z))))
                             has_derivative d1)
                            (at (pastecart (lift s) (SND(chart_at atlas (gamma s)) (gamma s))))) /\
                      (?v. ((\r. SND(chart_at atlas (gamma s)) (gamma(drop r)))
                            has_vector_derivative v) (at (lift s)) /\
                           ((\y. lift(p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                             b p s (chart_inv (chart_at atlas (gamma s)) y)))
                            has_derivative
                            (\w. lift(v dot
                                      (metric_local atlas (chart_at atlas (gamma s)) (g(b - s))
                                         (SND(chart_at atlas (gamma s)) (gamma s)) ** w))))
                           (at (SND(chart_at atlas (gamma s)) (gamma s)))))`;;

