(* ========================================================================= *)
(* Unit pc_p2a_rigstmt: statements only.  The two lemmas of the FL5R route   *)
(* (MT Prop 7.27, equality case of the reduced-volume monotonicity), as      *)
(* statement constants at N = 3.                                             *)
(*                                                                           *)
(* P2AU_RIGID_CORE_STATEMENT: the a.e. equality case implies flatness.  If  *)
(* Smin(tau0) is conull and, for every tau1 in (0,tau0], the integrand      *)
(* rvi(tau1) equals the Gaussian 8 exp(-|Z|^2) almost everywhere on          *)
(* Smin(tau0), then g(t) is flat for t in [b - tau0,b].  pc_p2a_rigid       *)
(* proves P2AU_RIGID_CORE_STATEMENT u /\ W3 ==> FL5R.                        *)
(*                                                                           *)
(* P2AU_RIGID_R2_STATEMENT: the pointwise equality case implies flatness. On *)
(* a conull set E of initial vectors inside Smin(tau0), rvi(tau1,Z) is the   *)
(* Gaussian for all tau1 in (0,tau0], and along each such L-geodesic the     *)
(* Jacobi data have the soliton shape S = I/s - 2 s Ric (p2au_soliton_shape, *)
(* s = sqrt tau), with S = B Y^-1 + Gamma(A) the chart matrix of             *)
(* P2AL_GFUN_DERIV.  pc_p2a_rigcore proves R2 ==> CORE (the equality case of *)
(* P2AL_RICCATI_BOUND) and pc_p2a_rigr2 proves R2 (P2AU_RIGID_R2).           *)
(*                                                                           *)
(* Both statements assume W3 (P2B_REQ_P2A_WEAK_STATEMENT), the standing     *)
(* hypothesis of the FL3-FL5 headlines; FL2 is a theorem                     *)
(* (P2AK_FLOW_MIN_EXISTS_3) and FL3 follows from W3 (P2AU_FLOW_LX_CONT).    *)
(* ========================================================================= *)

needs "src/pc_p2a_fldefs.ml";;
needs "src/pc_p2b_w3iface.ml";;
needs "src/pc_p2a_ljac.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The definitions.  p2au_soliton_shape V tt x Z s: in every regular window  *)
(* at (Z,s) of pc_p2a_ljac (p2al_wok, Z in N, s inside the window, p2al_lin, *)
(* det Y <> 0) the chart matrix S = B Y^-1 + Gamma(A) of the L-Jacobi data   *)
(* along the L-geodesic of Z equals I/s - 2 s Ric at the chart point, Ric    *)
(* the (1,1) Ricci operator of the metric at time tt - s^2.                  *)
(* ------------------------------------------------------------------------- *)

let p2au_soliton_shape = new_definition
 `p2au_soliton_shape (V:p2alv) tt (x:A) (Z:real^N) (s:real) <=>
    !s1 r W a' b' U (phi:A->real^N) N Phi.
      p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z IN N /\ s1 < s /\ s < s1 + r /\
      p2al_lin V tt s1 r W b' U phi Phi Z s /\
      ~(det(p2al_jy V tt s1 r W b' U phi Phi Z s) = &0)
      ==> p2al_jb V tt s1 r W b' U phi Phi Z s **
          matrix_inv(p2al_jy V tt s1 r W b' U phi Phi Z s) +
          matrix(christoffel (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                             (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))
                             (sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))) =
          inv(s) %% mat 1 -
          (&2 * s) %% matrix(p2a_lricop (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))
                                        (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)))`;;

let P2AU_RIGID_CORE_STATEMENT = new_definition
 `P2AU_RIGID_CORE_STATEMENT (u:A->bool) <=>
    P2B_REQ_P2A_WEAK_STATEMENT u
    ==> !top atlas a b (g:real->A->real^3^3) p tau0.
          p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
          &0 < tau0 /\ tau0 < b - a /\
          negligible((:real^3) DIFF
                     p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0) /\
          (!tau1. &0 < tau1 /\ tau1 <= tau0
                  ==> negligible
                       {Z | Z IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                          b p tau0 /\
                            ~(p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                      b p tau1 Z =
                              &8 * exp(--(p2a_znorm2
                                           (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                           b p Z)))})
          ==> !t x v1 v2. b - tau0 <= t /\ t <= b /\ x IN topspace top /\
                          ~collinear {vec 0,v1,v2}
                          ==> mfd_sectional atlas (g t) x v1 v2 = &0`;;

let P2AU_RIGID_R2_STATEMENT = new_definition
 `P2AU_RIGID_R2_STATEMENT (u:A->bool) <=>
    P2B_REQ_P2A_WEAK_STATEMENT u
    ==> !top atlas a b (g:real->A->real^3^3) p tau0 E.
          p2a_cbflow (top,atlas) a b g /\ connected_space top /\ p IN topspace top /\
          &0 < tau0 /\ tau0 < b - a /\
          E SUBSET p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau0 /\
          negligible((:real^3) DIFF E) /\
          (!Z tau1. Z IN E /\ &0 < tau1 /\ tau1 <= tau0
                    ==> p2a_rvi (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                b p tau1 Z =
                        &8 * exp(--(p2a_znorm2
                                     (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                     b p Z))) /\
          (!Z s. Z IN E /\ &0 < s /\ s pow 2 < tau0
                 ==> p2au_soliton_shape (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                        b p Z s)
          ==> !t x v1 v2. b - tau0 <= t /\ t <= b /\ x IN topspace top /\
                          ~collinear {vec 0,v1,v2}
                          ==> mfd_sectional atlas (g t) x v1 v2 = &0`;;

