(* ========================================================================= *)
(* Unit pc_p2b_w920g (Part 2B): the global layer of MT Prop 9.20 (Ch 9       *)
(* Sections 2.2-2.6), statements: vocabulary; the claims Cor 9.10, Lemma     *)
(* 9.25 (G2), Cor 9.14, the leaf FLOW_CHART, G1, G3 and the statement        *)
(* P2B_PROP_9_20_STATEMENT (G4); the six route obligations and their         *)
(* composition P2B_W920G_CHAIN (a theorem).  The local layer is the unit     *)
(* pc_p2b_w920 (theorems P2BW_LIMIT, P2BW_REG, P2BW_COEFF_BRIDGE).           *)
(*                                                                           *)
(* Inputs: W3 = P2B_REQ_P2A_WEAK_STATEMENT (pc_p2b_w3iface); from            *)
(* pc_p2a_fldefs: FL2 (minimizers exist), FL5 (reduced volume), FL5R         *)
(* (rigidity), FL8 (MT Prop 9.9), FL9 (gradient minimizers, Lemma 9.25);     *)
(* P2B_REQ_RFA_DIST_LOCAL_STATEMENT (pc_p2b_distreq); Bishop-Gromov          *)
(* P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT (CMP_T3_BISHOP_GROMOV_P2B,            *)
(* pc_cmp_bg).  FL4 is used by the Thm 9.11 route (choice of the points q k  *)
(* with l <= 3/2).                                                           *)
(*                                                                           *)
(* Conventions.  The flow (top,atlas,g) on A is a kappa-solution, base      *)
(* point (p,0); l(q,t) = p2b_klx (top,atlas) g p t q is its reduced length  *)
(* at backward time t.  tau k tends to infinity; the rescaled flows         *)
(* g(tau k s)/tau k based at (q k,-1) converge (p2c_flow_limit_with, limit  *)
(* time s < 1, MT time s - 1) to (top',atlas',g') on B with exhaustion W k *)
(* and embeddings phi k.  On the limit, backward time t > 0 is limit time   *)
(* 1 - t, so the chart data of the limit are the W3 vocabulary at b = 1:    *)
(* p2bw_cmet atlas' c (&1) g', p2bw_cscal atlas' c (&1) g', and the chart   *)
(* reading p2bw_cfun c linf of a function linf t y.  Space-time points z of *)
(* real^(3,1)finite_sum: space fstcart z, backward time drop(sndcart z).    *)
(* ========================================================================= *)

needs "src/pc_p2b_w920.ml";;
needs "src/pc_p2a_fldefs.ml";;
needs "src/pc_p2b_distreq.ml";;
needs "src/pc_p2b_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* V1. Reduced length and reduced volume of a flow defined for t <= 0, from *)
(* (p,0) at backward time tau, read on the view of [-2 tau, 0].  Every      *)
(* interval [a,0] with a < -tau gives the same values (the L-geometry of    *)
(* backward times up to tau only sees the flow on [-tau,0]); this locality  *)
(* is P2BX_KLX_VIEW of pc_p2b_c914.                                         *)
(* ------------------------------------------------------------------------- *)

let p2b_klx = new_definition
 `p2b_klx (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:real->A->real^N^N)
          (p:A) (tau:real) (q:A) =
    p2a_lx (p2a_flow_view (top,atlas) (real_interval[--(&2 * tau),&0]) g) (&0) p tau q`;;

let p2b_kfrv = new_definition
 `p2b_kfrv (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:real->A->real^N^N)
           (p:A) (tau:real) =
    p2a_frv (top,atlas) (--(&2 * tau)) (&0) g p tau`;;

(* ------------------------------------------------------------------------- *)
(* V2. The rescaled flows read in a chart c of the limit, along an index    *)
(* map ix (a tail of a subsequence): the m-th member is the flow            *)
(* g(tau k s)/tau k, k = ix m, pulled back by phi k o chart_inv c; at the   *)
(* space-time point z its metric, scalar curvature and reduced length.      *)
(* ------------------------------------------------------------------------- *)

let p2bg_smet = new_definition
 `p2bg_smet (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (tau:num->real)
            (phi:num->B->A) (c:(B->bool)#(B->real^3)) (ix:num->num) (m:num)
            (z:real^(3,1)finite_sum) =
    inv(tau(ix m)) %%
    rfs_pullback atlas (phi(ix m) o chart_inv c) (g(--(tau(ix m) * drop(sndcart z))))
                 (fstcart z)`;;

let p2bg_sscal = new_definition
 `p2bg_sscal (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (tau:num->real)
             (phi:num->B->A) (c:(B->bool)#(B->real^3)) (ix:num->num) (m:num)
             (z:real^(3,1)finite_sum) =
    tau(ix m) * mfd_scalar atlas (g(--(tau(ix m) * drop(sndcart z))))
                           (phi(ix m) (chart_inv c (fstcart z)))`;;

let p2bg_sfun = new_definition
 `p2bg_sfun (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3)
            (p:A) (tau:num->real) (phi:num->B->A) (c:(B->bool)#(B->real^3))
            (ix:num->num) (m:num) (z:real^(3,1)finite_sum) =
    p2b_klx (top,atlas) g p (tau(ix m) * drop(sndcart z)) (phi(ix m) (chart_inv c (fstcart z)))`;;

(* Chart boxes: open bounded space-time sets whose closure lies in the      *)
(* chart domain at positive backward times (they lie in W k for k large).   *)

let p2bg_cbox = new_definition
 `p2bg_cbox (c:(B->bool)#(B->real^3)) (om:real^(3,1)finite_sum->bool) <=>
    open om /\ bounded om /\
    closure om SUBSET {z | fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)}`;;

(* ------------------------------------------------------------------------- *)
(* V3. The setting of MT Thm 9.11, Sections 2.1-2.2 (the limit flow is      *)
(* given; Cor 9.17 and its proof are the Thm 9.11 route): a kappa-solution, *)
(* tau k -> infinity, l(q k, tau k) <= 3/2 (MT Thm 7.10, FL4), the          *)
(* rescaled based flows converge with exhaustion W and embeddings phi to a  *)
(* connected limit that is a Ricci flow for s < 1 with complete slices of   *)
(* nonnegative sectional curvature.                                          *)
(* ------------------------------------------------------------------------- *)

let p2bg_setup = new_definition
 `p2bg_setup (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3)
             (p:A) (tau:num->real) (q:num->A)
             (top':B topology,atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
             (xl:B) (W:num->B->bool) (phi:num->B->A) <=>
    (?kappa. p2b_kappa_solution kappa (top,atlas) g) /\ p IN topspace top /\
    (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
    (!k. q k IN topspace top /\ p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2) /\
    p2c_flow_limit_with (\k. p2b_kview (top,atlas) g) q (\k. --(tau k)) (\k. inv(tau k))
                        {s | s < &1} (top',atlas') g' xl W phi /\
    connected_space top' /\
    (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\
    (!s. s < &1 ==> mfd_complete (top',atlas') (g' s)) /\
    (!s y v1 v2. s < &1 /\ y IN topspace top' /\ ~collinear {vec 0,v1,v2}
                 ==> &0 <= mfd_sectional atlas' (g' s) y v1 v2)`;;

(* The pulled back reduced lengths converge to linf uniformly on compact    *)
(* sets of the limit times compact backward-time intervals in (0,inf).      *)

let p2bg_conv = new_definition
 `p2bg_conv (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3)
            (p:A) (tau:num->real) (top':B topology) (W:num->B->bool) (phi:num->B->A)
            (sub:num->num) (linf:real->B->real) <=>
    !K t1 t2 e. compact_in top' K /\ &0 < t1 /\ t1 <= t2 /\ &0 < e
                ==> ?m0. !m y t. m0 <= m /\ y IN K /\ t1 <= t /\ t <= t2
                                 ==> y IN W (sub m) /\
                                     abs(p2b_klx (top,atlas) g p (tau(sub m) * t)
                                                 (phi (sub m) y) - linf t y) < e`;;

(* ------------------------------------------------------------------------- *)
(* V4. G1 output: the hypotheses of P2BW_LIMIT_STATEMENT (with             *)
(* P2BW_COEFF_BRIDGE_STATEMENT for the coefficients) in every chart box of *)
(* the limit, for a tail of the subsequence.                                 *)
(* ------------------------------------------------------------------------- *)

let p2bg_cdata = new_definition
 `p2bg_cdata (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3)
             (p:A) (tau:num->real) (atlas':((B->bool)#(B->real^3))->bool)
             (g':real->B->real^3^3) (phi:num->B->A) (c:(B->bool)#(B->real^3))
             (om:real^(3,1)finite_sum->bool) (ix:num->num) (linf:real->B->real) <=>
    (!m. (\z. (vectorize:real^3^3->real^(3,3)finite_prod) (p2bg_smet atlas g tau phi c ix m z))
         continuous_on om /\
         (!z. z IN om
              ==> transp(p2bg_smet atlas g tau phi c ix m z) = p2bg_smet atlas g tau phi c ix m z /\
                  !v. ~(v = vec 0) ==> &0 < v dot (p2bg_smet atlas g tau phi c ix m z ** v)) /\
         (\z. lift(p2bg_sscal atlas g tau phi c ix m z)) continuous_on om) /\
    p2bw_locunif_m om (p2bg_smet atlas g tau phi c ix) (p2bw_cmet atlas' c (&1) g') /\
    p2bw_locunif om (p2bg_sscal atlas g tau phi c ix) (p2bw_cscal atlas' c (&1) g') /\
    p2bw_unilip om (p2bg_sfun (top,atlas) g p tau phi c ix) /\
    p2bw_locunif om (p2bg_sfun (top,atlas) g p tau phi c ix) (p2bw_cfun c linf) /\
    (!m. p2bw_t1 om (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)) %%
                         matrix_inv(p2bg_smet atlas g tau phi c ix m z))
                    (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)))
                    (p2bg_sscal atlas g tau phi c ix m) (p2bg_sfun (top,atlas) g p tau phi c ix m) /\
         p2bw_t2 om (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)) %%
                         matrix_inv(p2bg_smet atlas g tau phi c ix m z))
                    (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)))
                    (p2bg_sscal atlas g tau phi c ix m) (p2bg_sfun (top,atlas) g p tau phi c ix m) /\
         p2bw_tid om (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)) %%
                          matrix_inv(p2bg_smet atlas g tau phi c ix m z))
                     (\z. sqrt(det(p2bg_smet atlas g tau phi c ix m z)))
                     (p2bg_sscal atlas g tau phi c ix m) (p2bg_sfun (top,atlas) g p tau phi c ix m))`;;

let p2bg_g1out = new_definition
 `p2bg_g1out (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3)
             (p:A) (tau:num->real)
             (top':B topology,atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
             (W:num->B->bool) (phi:num->B->A) (sub:num->num) (linf:real->B->real) <=>
    p3_subseq sub /\
    p2bg_conv (top,atlas) g p tau top' W phi sub linf /\
    !c om. c IN atlas' /\ p2bg_cbox c om
           ==> ?m0. p2bg_cdata (top,atlas) g p tau atlas' g' phi c om (\j. sub(m0 + j)) linf`;;

(* ------------------------------------------------------------------------- *)
(* V5. G3 output: U = t^(-3/2) e^(-linf) solves the conjugate heat equation *)
(* weakly in every chart box (the hypothesis of P2BW_REG_STATEMENT at       *)
(* N = 3), and the reduced volume of linf is the constant V, the limit of   *)
(* the reduced volume of the kappa-solution (MT Section 2.6, Cor 9.14).     *)
(* ------------------------------------------------------------------------- *)

let p2bg_weq = new_definition
 `p2bg_weq (atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
           (c:(B->bool)#(B->real^3)) (om:real^(3,1)finite_sum->bool) (linf:real->B->real) <=>
    !psi. wan_test om psi
          ==> integral om
                (\z. lift((psi z * wan_tder (p2bw_uof (p2bw_cfun c linf)) z +
                           p2bw_cscal atlas' c (&1) g' z * psi z * p2bw_uof (p2bw_cfun c linf) z +
                           sum(1..dimindex(:3))
                              (\i. sum(1..dimindex(:3))
                                     (\j. matrix_inv(p2bw_cmet atlas' c (&1) g' z)$i$j *
                                          wan_xder i (p2bw_uof (p2bw_cfun c linf)) z *
                                          wan_xder j psi z))) *
                          sqrt(det(p2bw_cmet atlas' c (&1) g' z)))) = vec 0`;;

let p2bg_rvol = new_definition
 `p2bg_rvol (top':B topology,atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
            (linf:real->B->real) (V:real) <=>
    !t. &0 < t
        ==> mfd_integrable_on (top',atlas') (g'(&1 - t))
              (\y. exp(--(linf t y)) / sqrt t pow 3) (topspace top') /\
            mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
              (\y. exp(--(linf t y)) / sqrt t pow 3) = V`;;

let p2bg_g3out = new_definition
 `p2bg_g3out (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) (p:A)
             (top':B topology,atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
             (linf:real->B->real) <=>
    (!c om. c IN atlas' /\ p2bg_cbox c om ==> p2bg_weq atlas' g' c om linf) /\
    ?V. ((\t. p2b_kfrv (top,atlas) g p t) ---> V) at_posinfinity /\
        p2bg_rvol (top',atlas') g' linf V`;;

(* ========================================================================= *)
(* The claims (statement constants).                                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* S1. MT Cor 9.10 in integrated form for kappa-solutions (with Claim 9.15  *)
(* and Cor 9.16 as consequences): l >= 0; R <= 3 l / t; sqrt l is           *)
(* sqrt(3/(4t))-Lipschitz for the distance of g(-t) (|grad l|^2 <= 3l/t); *)
(* t^2 l is nondecreasing and l / t nonincreasing in t (from              *)
(* -2 l/t <= l_t <= l/t;                                                     *)
(* the upper bound from the identity of W3 and FL8, not by MT's             *)
(* concatenation).  Everywhere, not only almost everywhere (continuity).    *)
(* ------------------------------------------------------------------------- *)

let P2B_COR_9_10_STATEMENT = new_definition
 `P2B_COR_9_10_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) p.
       p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top
       ==> (!t q. &0 < t /\ q IN topspace top
                  ==> &0 <= p2b_klx (top,atlas) g p t q /\
                      mfd_scalar atlas (g(--t)) q <= &3 * p2b_klx (top,atlas) g p t q / t) /\
           (!t q0 q. &0 < t /\ q0 IN topspace top /\ q IN topspace top
                     ==> sqrt(p2b_klx (top,atlas) g p t q) <=
                         sqrt(p2b_klx (top,atlas) g p t q0) +
                         sqrt(&3 / (&4 * t)) * mfd_dist (top,atlas) (g(--t)) q0 q) /\
           (!q t1 t2. q IN topspace top /\ &0 < t1 /\ t1 <= t2
                      ==> t1 pow 2 * p2b_klx (top,atlas) g p t1 q <=
                          t2 pow 2 * p2b_klx (top,atlas) g p t2 q /\
                          t1 * p2b_klx (top,atlas) g p t2 q <= t2 * p2b_klx (top,atlas) g p t1 q)`;;

(* S2 = G2. MT Lemma 9.25 (scale invariant; any backward time t > 0). *)

let P2B_LEMMA_9_25_STATEMENT = new_definition
 `P2B_LEMMA_9_25_STATEMENT (w:B->bool) <=>
    ?c1. &0 < c1 /\
         !kappa top atlas (g:real->B->real^3^3) p t p1 q1.
            p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ &0 < t /\
            p1 IN topspace top /\ q1 IN topspace top
            ==> (c1 * mfd_dist (top,atlas) (g(--t)) p1 q1 pow 2) / t -
                p2b_klx (top,atlas) g p t q1 - &1
                <= p2b_klx (top,atlas) g p t p1`;;

(* S3. MT Cor 9.14: the reduced volume tends to a limit V < (4 pi)^(3/2). *)

let P2B_COR_9_14_STATEMENT = new_definition
 `P2B_COR_9_14_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) p.
       p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top
       ==> ?V. ((\t. p2b_kfrv (top,atlas) g p t) ---> V) at_posinfinity /\
               &0 <= V /\ V < sqrt(&4 * pi) pow 3`;;

(* S4. Chart regularity of a Ricci flow in the W3 vocabulary (a leaf,       *)
(* proved in pc_p2b_fchart from ricci_flow_on, MFD_SCALAR_CHART and         *)
(* LRG_LSCALAR_SMOOTH): metric and scalar curvature smooth on the           *)
(* space-time chart domain, metric positive definite.                       *)

let P2B_FLOW_CHART_STATEMENT = new_definition
 `P2B_FLOW_CHART_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas a b (g:real->A->real^N^N) c.
       ricci_flow_on (top,atlas) a b g /\ c IN atlas
       ==> smooth_map_on (p2bw_cdom c (b - a))
             ((vectorize:real^N^N->real^(N,N)finite_prod) o p2bw_cmet atlas c b g) /\
           smooth_map_on (p2bw_cdom c (b - a)) (\z. lift(p2bw_cscal atlas c b g z)) /\
           (!z. z IN p2bw_cdom c (b - a)
                ==> transp(p2bw_cmet atlas c b g z) = p2bw_cmet atlas c b g z /\
                    !v. ~(v = vec 0) ==> &0 < v dot (p2bw_cmet atlas c b g z ** v))`;;

(* ------------------------------------------------------------------------- *)
(* G1 (MT Section 2.2 with Claim 9.15, Cor 9.16): a subsequence and linf    *)
(* with locally uniform convergence, and in every chart box the hypotheses  *)
(* of the local limit lemma (Thm 7.13 and the identity moved to the limit   *)
(* charts by the embeddings and the parabolic rescaling; Arzela-Ascoli and  *)
(* a diagonal argument from the bounds of Cor 9.10).                        *)
(* ------------------------------------------------------------------------- *)

let P2B_W920_G1_STATEMENT = new_definition
 `P2B_W920_G1_STATEMENT (u:A->bool) (w:B->bool) <=>
    !top atlas (g:real->A->real^3^3) p tau q top' atlas' (g':real->B->real^3^3) xl W phi.
       p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi
       ==> ?sub linf. p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf`;;

(* G3 (MT Sections 2.5-2.6: Cor 9.26, Claims 9.27-9.31, Cor 9.30): for     *)
(* every output of G1, W = 0 weakly in every chart box and the reduced     *)
(* volume of linf is constant.                                               *)

let P2B_W920_G3_STATEMENT = new_definition
 `P2B_W920_G3_STATEMENT (u:A->bool) (w:B->bool) <=>
    !top atlas (g:real->A->real^3^3) p tau q top' atlas' (g':real->B->real^3^3) xl W phi
     sub linf.
       p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
       p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf
       ==> p2bg_g3out (top,atlas) g p (top',atlas') g' linf`;;

(* G4: MT Prop 9.20 with the Section 2.6 identity and Cor 9.14: linf        *)
(* is the limit of the pulled back reduced lengths, smooth in every chart, *)
(* satisfies (9.4) and (9.5) at every point, and its reduced volume is the  *)
(* constant V < (4 pi)^(3/2).                                                *)

let P2B_PROP_9_20_STATEMENT = new_definition
 `P2B_PROP_9_20_STATEMENT (u:A->bool) (w:B->bool) <=>
    !top atlas (g:real->A->real^3^3) p tau q top' atlas' (g':real->B->real^3^3) xl W phi.
       p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi
       ==> ?sub linf V.
              p3_subseq sub /\ p2bg_conv (top,atlas) g p tau top' W phi sub linf /\
              (!c tmax. c IN atlas'
                        ==> smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z))) /\
              (!c z. c IN atlas' /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
                     ==> wan_tder (p2bw_cfun c linf) z +
                         lgrad2 (p2bw_slice (p2bw_cmet atlas' c (&1) g') z)
                                (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                         p2bw_cscal atlas' c (&1) g' z + &3 / (&2 * drop(sndcart z)) -
                         llap (p2bw_slice (p2bw_cmet atlas' c (&1) g') z)
                              (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) = &0 /\
                         &2 * llap (p2bw_slice (p2bw_cmet atlas' c (&1) g') z)
                                   (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                         lgrad2 (p2bw_slice (p2bw_cmet atlas' c (&1) g') z)
                                (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) +
                         p2bw_cscal atlas' c (&1) g' z +
                         (p2bw_cfun c linf z - &3) / drop(sndcart z) = &0) /\
              ((\t. p2b_kfrv (top,atlas) g p t) ---> V) at_posinfinity /\
              V < sqrt(&4 * pi) pow 3 /\
              p2bg_rvol (top',atlas') g' linf V`;;

(* ========================================================================= *)
(* The route obligations and their composition.                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Route obligations.  u: the type of the kappa-solution, w: of the limit.  *)
(* ------------------------------------------------------------------------- *)

(* Cor 9.10: FL8 at the points of differentiability (almost all, W3 and     *)
(* Rademacher), the identity of W3 for the upper bound on l_t, Fubini and   *)
(* continuity for the integrated forms, FL2 for l >= 0 (a curve exists).    *)

let P2B_COR_9_10_ROUTE_STATEMENT = new_definition
 `P2B_COR_9_10_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_REQ_P2A_WEAK_STATEMENT w /\ P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
    P2A_FLOW_MIN_EXISTS_STATEMENT w (:3)
    ==> P2B_COR_9_10_STATEMENT w`;;

(* Lemma 9.25: minimizers with velocity grad l (FL9), the bounds of FL8     *)
(* along them, Cor 9.10 on the balls of radius r0(tau), the local distance  *)
(* distortion MT Prop 3.21 (DIST_LOCAL), a Dini-derivative integration.     *)

let P2B_LEMMA_9_25_ROUTE_STATEMENT = new_definition
 `P2B_LEMMA_9_25_ROUTE_STATEMENT (w:B->bool) <=>
    P2A_FLOW_MIN_GRAD_STATEMENT w (:3) /\ P2A_FLOW_PROP_9_9_STATEMENT w (:3) /\
    P2B_COR_9_10_STATEMENT w /\ P2B_REQ_RFA_DIST_LOCAL_STATEMENT w (:3)
    ==> P2B_LEMMA_9_25_STATEMENT w`;;

(* Cor 9.14: FL5 (monotone, positive, at most (4 pi)^(3/2)) gives the       *)
(* limit; FL5R and non-flatness exclude (4 pi)^(3/2).                       *)

let P2B_COR_9_14_ROUTE_STATEMENT = new_definition
 `P2B_COR_9_14_ROUTE_STATEMENT (w:B->bool) <=>
    P2A_FLOW_RV_STATEMENT w (:3) /\ P2A_FLOW_RV_RIGID_STATEMENT w (:3)
    ==> P2B_COR_9_14_STATEMENT w`;;

(* G1: W3 moved to the limit charts (diffeomorphism and scaling invariance  *)
(* of p2bw_t1, p2bw_t2, p2bw_tid); Cor 9.10 for the uniform bounds.         *)

let P2B_W920_G1_ROUTE_STATEMENT = new_definition
 `P2B_W920_G1_ROUTE_STATEMENT (u:A->bool) (w:B->bool) <=>
    P2B_REQ_P2A_WEAK_STATEMENT u /\ P2B_COR_9_10_STATEMENT u
    ==> P2B_W920_G1_STATEMENT u w`;;

(* G3: Gaussian lower bounds (Lemma 9.25 with Cor 9.10: Cor 9.26), volume  *)
(* growth (Bishop-Gromov on the slices of the flow and of the limit),       *)
(* reduced volume (FL5), the local limit lemma (P2BW_LIMIT, a theorem) on   *)
(* the chart data of the limit (P2B_FLOW_CHART).                             *)

let P2B_W920_G3_ROUTE_STATEMENT = new_definition
 `P2B_W920_G3_ROUTE_STATEMENT (u:A->bool) (w:B->bool) <=>
    P2B_LEMMA_9_25_STATEMENT u /\ P2B_COR_9_10_STATEMENT u /\ P2A_FLOW_RV_STATEMENT u (:3) /\
    P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT u /\ P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\
    P2B_FLOW_CHART_STATEMENT w (:3)
    ==> P2B_W920_G3_STATEMENT u w`;;

(* G4: assembly with the theorems P2BW_COEFF_BRIDGE, P2BW_LIMIT, P2BW_REG   *)
(* on chart boxes (smoothness and (9.4), (9.5) are local).                  *)

let P2B_PROP_9_20_ROUTE_STATEMENT = new_definition
 `P2B_PROP_9_20_ROUTE_STATEMENT (u:A->bool) (w:B->bool) <=>
    P2B_W920_G1_STATEMENT u w /\ P2B_W920_G3_STATEMENT u w /\ P2B_COR_9_14_STATEMENT u /\
    P2B_FLOW_CHART_STATEMENT w (:3)
    ==> P2B_PROP_9_20_STATEMENT u w`;;

(* ------------------------------------------------------------------------- *)
(* The composed chain: the six route obligations, the leaf FLOW_CHART      *)
(* and the inputs of the other layers give Prop 9.20 and Cor 9.10 (the      *)
(* Thm 9.11 route also uses Cor 9.10, for the curvature bounds of Cor 9.17).*)
(* ------------------------------------------------------------------------- *)

let P2B_W920G_CHAIN = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_COR_9_10_ROUTE_STATEMENT u /\ P2B_LEMMA_9_25_ROUTE_STATEMENT u /\
     P2B_COR_9_14_ROUTE_STATEMENT u /\ P2B_W920_G1_ROUTE_STATEMENT u w /\
     P2B_W920_G3_ROUTE_STATEMENT u w /\ P2B_PROP_9_20_ROUTE_STATEMENT u w /\
     P2B_FLOW_CHART_STATEMENT w (:3) /\
     P2B_REQ_P2A_WEAK_STATEMENT u /\ P2A_FLOW_PROP_9_9_STATEMENT u (:3) /\
     P2A_FLOW_MIN_EXISTS_STATEMENT u (:3) /\ P2A_FLOW_MIN_GRAD_STATEMENT u (:3) /\
     P2A_FLOW_RV_STATEMENT u (:3) /\ P2A_FLOW_RV_RIGID_STATEMENT u (:3) /\
     P2B_REQ_RFA_DIST_LOCAL_STATEMENT u (:3) /\
     P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT u /\ P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w
     ==> P2B_PROP_9_20_STATEMENT u w /\ P2B_COR_9_10_STATEMENT u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B_COR_9_10_ROUTE_STATEMENT; P2B_LEMMA_9_25_ROUTE_STATEMENT;
              P2B_COR_9_14_ROUTE_STATEMENT; P2B_W920_G1_ROUTE_STATEMENT;
              P2B_W920_G3_ROUTE_STATEMENT; P2B_PROP_9_20_ROUTE_STATEMENT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `P2B_COR_9_10_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2B_LEMMA_9_25_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2B_COR_9_14_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2B_W920_G1_STATEMENT (u:A->bool) (w:B->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2B_W920_G3_STATEMENT (u:A->bool) (w:B->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

