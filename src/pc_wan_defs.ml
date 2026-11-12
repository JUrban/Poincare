(* ========================================================================= *)
(* pc_wan_defs: definitions and statement constants of the weak analysis     *)
(* part (the pc_wan files), with sanity theorems.                            *)
(*                                                                           *)
(* Conventions. Open sets s in real^N; test functions are smooth on all of   *)
(* real^N and vanish off a compact subset of s. Maps are R^K valued          *)
(* (real^N->real^K), scalar functions are real^N->real and enter integrals   *)
(* through lift. Weak derivatives are relational (wan_wpd); wan_wd is the    *)
(* chosen weak partial, meaningful (unique up to a null set) only under      *)
(* wan_w12. Space-time points are z = pastecart x (lift t) in                *)
(* real^(N,1)finite_sum, as in the Navier_Stokes development; basis i       *)
(* (i <= N) is a space direction there.                                      *)
(* ========================================================================= *)

needs "src/pc_lrg_lap.ml";;
needs "src/pc_pde_torus.ml";;
needs "src/ns_cutoff.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* V1. Test functions, classical partials, local integrability, weak        *)
(* partial derivatives.                                                      *)
(* ------------------------------------------------------------------------- *)

let wan_test = new_definition
 `wan_test (s:real^N->bool) (phi:real^N->real) <=>
    smooth_map_on (:real^N) (\x. lift(phi x)) /\
    ?k. compact k /\ k SUBSET s /\ !x. ~(x IN k) ==> phi x = &0`;;

let wan_vtest = new_definition
 `wan_vtest (s:real^N->bool) (f:real^N->real^K) <=>
    smooth_map_on (:real^N) f /\
    ?k. compact k /\ k SUBSET s /\ !x. ~(x IN k) ==> f x = vec 0`;;

let wan_dpart = new_definition
 `wan_dpart (i:num) (phi:real^N->real) (x:real^N) =
    drop(frechet_derivative (\y. lift(phi y)) (at x) (basis i))`;;

let wan_lloc = new_definition
 `wan_lloc (s:real^N->bool) (u:real^N->real^K) <=>
    !k. compact k /\ k SUBSET s ==> u absolutely_integrable_on k`;;

let wan_l2loc = new_definition
 `wan_l2loc (s:real^N->bool) (u:real^N->real^K) <=>
    !k. compact k /\ k SUBSET s ==> u IN lspace k (&2)`;;

(* v is a weak i-th partial derivative of u on s. *)

let wan_wpd = new_definition
 `wan_wpd (s:real^N->bool) (i:num) (u:real^N->real^K) (v:real^N->real^K) <=>
    wan_lloc s u /\ wan_lloc s v /\
    !phi. wan_test s phi
          ==> integral s (\x. wan_dpart i phi x % u x) =
              --(integral s (\x. phi x % v x))`;;

(* ------------------------------------------------------------------------- *)
(* V2. Sobolev classes: W^{1,2}(s), the chosen weak partials, the Dirichlet *)
(* integral (sum of the squared L^2 norms of the weak partials, NOT halved), *)
(* W^{1,2}_0(s) (W^{1,2}-limits of vector test maps), H^k_loc(s).            *)
(* ------------------------------------------------------------------------- *)

let wan_w12 = new_definition
 `wan_w12 (s:real^N->bool) (u:real^N->real^K) <=>
    u IN lspace s (&2) /\
    !i. 1 <= i /\ i <= dimindex(:N)
        ==> ?v. v IN lspace s (&2) /\ wan_wpd s i u v`;;

let wan_wd = new_definition
 `wan_wd (s:real^N->bool) (i:num) (u:real^N->real^K) =
    @v. v IN lspace s (&2) /\ wan_wpd s i u v`;;

let wan_dir = new_definition
 `wan_dir (s:real^N->bool) (u:real^N->real^K) =
    sum(1..dimindex(:N))
       (\i. drop(integral s (\x. lift(norm(wan_wd s i u x) pow 2))))`;;

let wan_w120 = new_definition
 `wan_w120 (s:real^N->bool) (u:real^N->real^K) <=>
    wan_w12 s u /\
    ?f. (!n. wan_vtest s ((f:num->real^N->real^K) n)) /\
        ((\n. lnorm s (&2) (\x. f n x - u x)) ---> &0) sequentially /\
        ((\n. wan_dir s (\x. f n x - u x)) ---> &0) sequentially`;;

let wan_hk = define
 `(wan_hk (s:real^N->bool) 0 (u:real^N->real^K) <=> wan_l2loc s u) /\
  (wan_hk s (SUC k) u <=>
     wan_l2loc s u /\
     !i. 1 <= i /\ i <= dimindex(:N) ==> ?v. wan_wpd s i u v /\ wan_hk s k v)`;;

(* ------------------------------------------------------------------------- *)
(* V3. Local Lipschitz functions; space-time partials (time = coordinate    *)
(* N+1 of real^(N,1)finite_sum).  At points where a locally Lipschitz map  *)
(* is not differentiable the Frechet derivative is a choice value; these   *)
(* points form a null set (RADEMACHER_OPEN), so integrals do not see them. *)
(* ------------------------------------------------------------------------- *)

let wan_loclip = new_definition
 `wan_loclip (s:real^M->bool) (u:real^M->real) <=>
    !k. compact k /\ k SUBSET s
        ==> ?L. !x y. x IN k /\ y IN k ==> abs(u x - u y) <= L * norm(x - y)`;;

let wan_tder = new_definition
 `wan_tder (f:real^(N,1)finite_sum->real) (z:real^(N,1)finite_sum) =
    drop(frechet_derivative (\w. lift(f w)) (at z)
           (pastecart (vec 0:real^N) (lift(&1))))`;;

let wan_xder = new_definition
 `wan_xder (i:num) (f:real^(N,1)finite_sum->real) (z:real^(N,1)finite_sum) =
    drop(frechet_derivative (\w. lift(f w)) (at z)
           (pastecart (basis i:real^N) (vec 0:real^1)))`;;

(* ------------------------------------------------------------------------- *)
(* V4. Planar circles and the 2-sphere (through the radial extension to the *)
(* open shell 1/2 < |z| < 2, consistent with p4_s2_integral of pc_p4_defs). *)
(* ------------------------------------------------------------------------- *)

let wan_circ = new_definition
 `wan_circ (a:real^2) (r:real) (t:real) =
    a + r % (vector[cos t; sin t]:real^2)`;;

let wan_shell = new_definition
 `wan_shell = {z:real^3 | &1 / &2 < norm z /\ norm z < &2}`;;

let wan_rext = new_definition
 `wan_rext (u:real^3->real^K) = \z:real^3. u(inv(norm z) % z)`;;

let wan_s2_w12 = new_definition
 `wan_s2_w12 (u:real^3->real^K) <=> wan_w12 wan_shell (wan_rext u)`;;

(* The Dirichlet integral of u over S^2 with the round metric:             *)
(* int_shell |grad (radial extension)|^2 = (3/2) int_S2 |grad_T u|^2.       *)

let wan_s2_dir = new_definition
 `wan_s2_dir (u:real^3->real^K) = &2 / &3 * wan_dir wan_shell (wan_rext u)`;;

(* ========================================================================= *)
(* Coefficient classes and the statements for Part 2 (S1). The statement     *)
(* constants are proved in the other pc_wan files (WAN_LLAP_DIV_STATEMENT in *)
(* pc_p2b_w920), except the ones marked as stated only, which the proof does *)
(* not use. Dummy arguments (n:N->bool) etc. fix the dimension types.        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* S1.0 Coefficient classes and weak forms.                                 *)
(* Parabolic, divergence form, on an open space-time set om:                *)
(*   d/dt (rho U) = d_i (A_ij d_j U) + B_i d_i U + C U - Fs                *)
(* tested against phi (no time derivative on U; K j = spatial gradient).    *)
(* Elliptic, divergence form, on an open s:                                 *)
(*   d_i (A_ij d_j u) + B_i d_i u + C u = f   (v j = weak partials of u).   *)
(* ------------------------------------------------------------------------- *)

let wan_pcoeff = new_definition
 `wan_pcoeff (om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
             (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
             (C:real^(N,1)finite_sum->real) <=>
    open om /\
    smooth_map_on om (\z. lift(rho z)) /\ (!z. z IN om ==> &0 < rho z) /\
    smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o A) /\
    (!z. z IN om ==> transp(A z) = A z /\
                     !v. ~(v = vec 0) ==> &0 < v dot (A z ** v)) /\
    smooth_map_on om B /\ smooth_map_on om (\z. lift(C z))`;;

let wan_pweak = new_definition
 `wan_pweak (om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
            (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
            (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
            (U:real^(N,1)finite_sum->real) (K:num->real^(N,1)finite_sum->real) <=>
    !phi. wan_test om phi
          ==> integral om
                (\z. lift(rho z * U z * wan_tder phi z -
                          sum(1..dimindex(:N))
                             (\i. sum(1..dimindex(:N))
                                    (\j. A z$i$j * K j z * wan_xder i phi z)) +
                          (sum(1..dimindex(:N)) (\i. B z$i * K i z) + C z * U z) *
                          phi z)) =
              integral om (\z. lift(Fs z * phi z))`;;

let wan_ecoeff = new_definition
 `wan_ecoeff (s:real^N->bool) (A:real^N->real^N^N) (B:real^N->real^N)
             (C:real^N->real) <=>
    open s /\
    smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o A) /\
    (!x. x IN s ==> transp(A x) = A x /\
                    !v. ~(v = vec 0) ==> &0 < v dot (A x ** v)) /\
    smooth_map_on s B /\ smooth_map_on s (\x. lift(C x))`;;

let wan_eweak = new_definition
 `wan_eweak (s:real^N->bool) (A:real^N->real^N^N) (B:real^N->real^N)
            (C:real^N->real) (f:real^N->real) (u:real^N->real)
            (v:num->real^N->real) <=>
    !phi. wan_test s phi
          ==> integral s
                (\x. lift(--(sum(1..dimindex(:N))
                               (\i. sum(1..dimindex(:N))
                                      (\j. A x$i$j * v j x * wan_dpart i phi x))) +
                          (sum(1..dimindex(:N)) (\i. B x$i * v i x) + C x * u x) *
                          phi x)) =
              integral s (\x. lift(f x * phi x))`;;

(* ------------------------------------------------------------------------- *)
(* S1.1 Lipschitz functions: integration by parts against test functions   *)
(* (the a.e. derivative is the weak derivative) and H^1_loc membership.     *)
(* ------------------------------------------------------------------------- *)

let WAN_LIP_IBP_STATEMENT = new_definition
 `WAN_LIP_IBP_STATEMENT (m:M->bool) <=>
    !(s:real^M->bool) (u:real^M->real) (phi:real^M->real) (v:real^M).
       open s /\ wan_loclip s u /\ wan_test s phi
       ==> (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * phi x))
             absolutely_integrable_on s /\
           integral s (\x. lift(u x * drop(frechet_derivative (\y. lift(phi y)) (at x) v))) =
           --(integral s
                (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * phi x)))`;;

let WAN_LIP_W12_STATEMENT = new_definition
 `WAN_LIP_W12_STATEMENT (m:M->bool) <=>
    !(s:real^M->bool) (u:real^M->real).
       open s /\ wan_loclip s u
       ==> wan_hk s 1 (\x. lift(u x)) /\
           !i. 1 <= i /\ i <= dimindex(:M)
               ==> wan_wpd s i (\x. lift(u x)) (\x. lift(wan_dpart i u x))`;;

(* ------------------------------------------------------------------------- *)
(* S1.2 Parabolic interior regularity (MT Prop 9.20, parabolic regularity,   *)
(* p. 198). W: the L^2_t H^1_x weak class. Main form: locally Lipschitz U,   *)
(* a.e. spatial gradient. VW: continuous U, very weak form (FrenzyMath's     *)
(* form; stated only).                                                       *)
(* ------------------------------------------------------------------------- *)

let WAN_PAR_REG_W_STATEMENT = new_definition
 `WAN_PAR_REG_W_STATEMENT (n:N->bool) <=>
    !(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
     (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
     (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
     (U:real^(N,1)finite_sum->real) (K:num->real^(N,1)finite_sum->real).
       wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\
       wan_l2loc om (\z. lift(U z)) /\
       (!j. 1 <= j /\ j <= dimindex(:N)
            ==> wan_wpd om j (\z. lift(U z)) (\z. lift(K j z)) /\
                wan_l2loc om (\z. lift(K j z))) /\
       wan_pweak om rho A B C Fs U K
       ==> ?W. smooth_map_on om (\z. lift(W z)) /\
               negligible {z | z IN om /\ ~(U z = W z)}`;;

let WAN_PAR_REG_STATEMENT = new_definition
 `WAN_PAR_REG_STATEMENT (n:N->bool) <=>
    !(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
     (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
     (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
     (U:real^(N,1)finite_sum->real).
       wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\
       wan_loclip om U /\
       wan_pweak om rho A B C Fs U (\j z. wan_xder j U z)
       ==> smooth_map_on om (\z. lift(U z))`;;

let WAN_PAR_REG_VW_STATEMENT = new_definition
 `WAN_PAR_REG_VW_STATEMENT (n:N->bool) <=>
    !(om:real^(N,1)finite_sum->bool) (rho:real^(N,1)finite_sum->real)
     (A:real^(N,1)finite_sum->real^N^N) (B:real^(N,1)finite_sum->real^N)
     (C:real^(N,1)finite_sum->real) (Fs:real^(N,1)finite_sum->real)
     (U:real^(N,1)finite_sum->real).
       wan_pcoeff om rho A B C /\ smooth_map_on om (\z. lift(Fs z)) /\
       (\z. lift(U z)) continuous_on om /\
       (!phi. wan_test om phi
              ==> integral om
                    (\z. lift(U z *
                              (rho z * wan_tder phi z +
                               sum(1..dimindex(:N))
                                  (\i. sum(1..dimindex(:N))
                                         (\j. wan_xder i (\w. A w$i$j * wan_xder j phi w) z)) -
                               sum(1..dimindex(:N)) (\i. wan_xder i (\w. B w$i * phi w) z) +
                               C z * phi z))) =
                  integral om (\z. lift(Fs z * phi z)))
       ==> smooth_map_on om (\z. lift(U z))`;;

(* The form used in Part 2B (MT (9.14) written for U = tau^(-n/2) e^(-l)):   *)
(* in a chart, with time coordinate tau and metrics G(x,tau),               *)
(*   int [phi dU/dtau + R phi U + <grad U, grad phi>_G] dvol_G dtau = 0.    *)
(* No Ricci-flow identity is assumed (R is any smooth function).            *)

let WAN_CONJ_HEAT_REG_STATEMENT = new_definition
 `WAN_CONJ_HEAT_REG_STATEMENT (n:N->bool) <=>
    !(om:real^(N,1)finite_sum->bool) (G:real^(N,1)finite_sum->real^N^N)
     (R:real^(N,1)finite_sum->real) (U:real^(N,1)finite_sum->real).
       open om /\
       smooth_map_on om ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
       (!z. z IN om ==> transp(G z) = G z /\
                        !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
       smooth_map_on om (\z. lift(R z)) /\
       wan_loclip om U /\
       (!phi. wan_test om phi
              ==> integral om
                    (\z. lift((phi z * wan_tder U z + R z * phi z * U z +
                               sum(1..dimindex(:N))
                                  (\i. sum(1..dimindex(:N))
                                         (\j. matrix_inv(G z)$i$j * wan_xder i U z *
                                              wan_xder j phi z))) *
                              sqrt(det(G z)))) = vec 0)
       ==> smooth_map_on om (\z. lift(U z))`;;

(* ------------------------------------------------------------------------- *)
(* S1.3 Elliptic regularity: smooth data (ELL_REG), finite regularity        *)
(* (ELL_REG_K), local Sobolev embedding, the composition step, the           *)
(* divergence form of llap, and the semilinear statement that implies        *)
(* WAN_P2B_REQ_WREG_COPY. All are stated only, except the divergence form of *)
(* llap (WAN_LLAP_DIV_STATEMENT, proved in pc_p2b_w920).                     *)
(* ------------------------------------------------------------------------- *)

let WAN_ELL_REG_STATEMENT = new_definition
 `WAN_ELL_REG_STATEMENT (n:N->bool) <=>
    !(s:real^N->bool) (A:real^N->real^N^N) (B:real^N->real^N) (C:real^N->real)
     (f:real^N->real) (u:real^N->real) (v:num->real^N->real).
       wan_ecoeff s A B C /\ smooth_map_on s (\x. lift(f x)) /\
       wan_l2loc s (\x. lift(u x)) /\
       (!j. 1 <= j /\ j <= dimindex(:N)
            ==> wan_wpd s j (\x. lift(u x)) (\x. lift(v j x)) /\
                wan_l2loc s (\x. lift(v j x))) /\
       wan_eweak s A B C f u v
       ==> ?w. smooth_map_on s (\x. lift(w x)) /\
               negligible {x | x IN s /\ ~(u x = w x)}`;;

let WAN_ELL_REG_K_STATEMENT = new_definition
 `WAN_ELL_REG_K_STATEMENT (n:N->bool) <=>
    !k (s:real^N->bool) (A:real^N->real^N^N) (B:real^N->real^N) (C:real^N->real)
     (f:real^N->real) (u:real^N->real) (v:num->real^N->real).
       wan_ecoeff s A B C /\ wan_hk s k (\x. lift(f x)) /\
       wan_l2loc s (\x. lift(u x)) /\
       (!j. 1 <= j /\ j <= dimindex(:N)
            ==> wan_wpd s j (\x. lift(u x)) (\x. lift(v j x)) /\
                wan_l2loc s (\x. lift(v j x))) /\
       wan_eweak s A B C f u v
       ==> wan_hk s (k + 2) (\x. lift(u x))`;;

let WAN_SOBOLEV_LOC_STATEMENT = new_definition
 `WAN_SOBOLEV_LOC_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) m k (u:real^N->real^K).
       open s /\ wan_hk s k u /\ 2 * m + dimindex(:N) < 2 * k
       ==> ?w. continuously_differentiable m s w /\
               negligible {x | x IN s /\ ~(u x = w x)}`;;

let WAN_COMPOSE_HK_STATEMENT = new_definition
 `WAN_COMPOSE_HK_STATEMENT (n:N->bool) <=>
    !(s:real^N->bool) (W:real^(N,1)finite_sum->bool) (Fr:real^N->real->real)
     (u:real^N->real) m.
       open s /\ open W /\ (!y. y IN s ==> pastecart y (lift(u y)) IN W) /\
       smooth_map_on W (\z. lift(Fr (fstcart z) (drop(sndcart z)))) /\
       continuously_differentiable m s (\y. lift(u y)) /\
       wan_hk s (m + 1) (\y. lift(u y))
       ==> wan_hk s (m + 1) (\y. lift(Fr y (u y)))`;;

let WAN_LLAP_DIV_STATEMENT = new_definition
 `WAN_LLAP_DIV_STATEMENT (n:N->bool) <=>
    !(s:real^N->bool) (G:real^N->real^N^N) (phi:real^N->real) x.
       metric_field s G /\ smooth_map_on (:real^N) (\y. lift(phi y)) /\ x IN s
       ==> llap G phi x * sqrt(det(G x)) =
           sum(1..dimindex(:N))
              (\i. wan_dpart i
                     (\y. sqrt(det(G y)) *
                          sum(1..dimindex(:N))
                             (\j. matrix_inv(G y)$i$j * wan_dpart j phi y)) x)`;;

(* Semilinear elliptic regularity in dimension at most 3, in the form of     *)
(* WAN_P2B_REQ_WREG_COPY with weaker hypotheses: F smooth only near the      *)
(* graph of u, u locally Lipschitz, no positivity, any dimension N <= 3.     *)

let WAN_ELL_SEMI_STATEMENT = new_definition
 `WAN_ELL_SEMI_STATEMENT (n:N->bool) <=>
    !(G:real^N->real^N^N) (V:real^N->real) (Fr:real^N->real->real)
     (u:real^N->real) (s:real^N->bool) (W:real^(N,1)finite_sum->bool).
       dimindex(:N) <= 3 /\
       metric_field s G /\
       smooth_map_on s (\y. lift(V y)) /\
       open W /\ (!y. y IN s ==> pastecart y (lift(u y)) IN W) /\
       smooth_map_on W (\z. lift(Fr (fstcart z) (drop(sndcart z)))) /\
       wan_loclip s u /\
       (!phi. smooth_map_on (:real^N) (\y. lift(phi y)) /\
              (?k. compact k /\ k SUBSET s /\ !y. ~(y IN k) ==> phi y = &0)
              ==> integral s (\y. lift(u y * (&4 * llap G phi y - V y * phi y) *
                                       sqrt(det(G y)))) =
                  integral s (\y. lift(Fr y (u y) * phi y * sqrt(det(G y)))))
       ==> smooth_map_on s (\y. lift(u y))`;;

(* Semilinear elliptic regularity in dimension 3 in the form formulated for  *)
(* Part 2B.                                                                  *)

let WAN_P2B_REQ_WREG_COPY = new_definition
 `WAN_P2B_REQ_WREG_COPY (w:B->bool) <=>
    !(G:real^3->real^3^3) (V:real^3->real) (Fr:real^3->real->real) (u:real^3->real) s.
       metric_field s G /\
       smooth_map_on s (\y. lift(V y)) /\
       smooth_map_on (s PCROSS (:real^1)) (\z. lift(Fr (fstcart z) (drop(sndcart z)))) /\
       (\y. lift(u y)) continuous_on s /\
       (!y. y IN s ==> &0 < u y) /\
       (?L. !y z. y IN s /\ z IN s ==> abs(u y - u z) <= L * norm(y - z)) /\
       (!phi. smooth_map_on (:real^3) (\y. lift(phi y)) /\
              (?k. compact k /\ k SUBSET s /\ !y. ~(y IN k) ==> phi y = &0)
              ==> integral s (\y. lift(u y * (&4 * llap G phi y - V y * phi y) *
                                       sqrt(det(G y)))) =
                  integral s (\y. lift(Fr y (u y) * phi y * sqrt(det(G y)))))
       ==> smooth_map_on s (\y. lift(u y))`;;

(* ========================================================================= *)
(* The statements for Part 4 (S2, the Colding-Minicozzi analysis), for       *)
(* R^K-valued maps (embedding route). The S^2 bridge WAN_S2_DIR_C1 needs     *)
(* pc_p4_defs and is stated in pc_wan_p4defs.ml.                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* S2.0 Sanity and bridge: C^1 maps with L^2 derivatives are W^{1,2}, with *)
(* weak partials and Dirichlet integral given by the classical ones.        *)
(* ------------------------------------------------------------------------- *)

let WAN_W12_C1_STATEMENT = new_definition
 `WAN_W12_C1_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (u:real^N->real^K).
       open s /\ continuously_differentiable 1 s u /\ u IN lspace s (&2) /\
       (!i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. partial_derivative i u x) IN lspace s (&2))
       ==> wan_w12 s u /\
           (!i. 1 <= i /\ i <= dimindex(:N)
                ==> wan_wpd s i u (\x. partial_derivative i u x)) /\
           wan_dir s u =
           sum(1..dimindex(:N))
              (\i. drop(integral s (\x. lift(norm(partial_derivative i u x) pow 2))))`;;

(* ------------------------------------------------------------------------- *)
(* S2.1 Direct-method tools: closure and lower semicontinuity of the        *)
(* Dirichlet integral under L^2_loc convergence; Rellich with zero          *)
(* boundary values (bounded s) and interior Rellich; a.e. convergent        *)
(* subsequences (values in F(M) a.e. survive the limit).                    *)
(* ------------------------------------------------------------------------- *)

let WAN_DIR_LSC_STATEMENT = new_definition
 `WAN_DIR_LSC_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (u:num->real^N->real^K) v M.
       open s /\ (!n. wan_w12 s (u n) /\ wan_dir s (u n) <= M) /\
       v IN lspace s (&2) /\
       (!k. compact k /\ k SUBSET s
            ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially)
       ==> wan_w12 s v /\ wan_dir s v <= M`;;

let WAN_RELLICH0_STATEMENT = new_definition
 `WAN_RELLICH0_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (u:num->real^N->real^K) M.
       open s /\ bounded s /\ (!n. wan_w120 s (u n)) /\
       (!n. lnorm s (&2) (u n) pow 2 + wan_dir s (u n) <= M)
       ==> ?r v. (!m n. m < n ==> r m < r n) /\ wan_w120 s v /\
                 lnorm s (&2) v pow 2 + wan_dir s v <= M /\
                 ((\n. lnorm s (&2) (\x. u (r n) x - v x)) ---> &0) sequentially /\
                 (?S. negligible S /\
                      !x. x IN s DIFF S ==> ((\n. u (r n) x) --> v x) sequentially)`;;

let WAN_RELLICH_LOC_STATEMENT = new_definition
 `WAN_RELLICH_LOC_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (u:num->real^N->real^K) M.
       open s /\ (!n. wan_w12 s (u n)) /\
       (!n. lnorm s (&2) (u n) pow 2 + wan_dir s (u n) <= M)
       ==> ?r v. (!m n. m < n ==> r m < r n) /\ wan_w12 s v /\
                 lnorm s (&2) v pow 2 + wan_dir s v <= M /\
                 (!k. compact k /\ k SUBSET s
                      ==> ((\n. lnorm k (&2) (\x. u (r n) x - v x)) ---> &0)
                          sequentially) /\
                 (?S. negligible S /\
                      !x. x IN s DIFF S ==> ((\n. u (r n) x) --> v x) sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* S2.2 Poincare (zero boundary values; mean value on balls), Hardy on     *)
(* balls, Wirtinger on circles (vector form of WIRTINGER_INEQUALITY,        *)
(* 100/isoperimetric.ml).                                                    *)
(* ------------------------------------------------------------------------- *)

let WAN_POINCARE0_STATEMENT = new_definition
 `WAN_POINCARE0_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (a:real^N) R (u:real^N->real^K).
       open s /\ s SUBSET ball(a,R) /\ wan_w120 s u
       ==> lnorm s (&2) u pow 2 <= &4 * R pow 2 * wan_dir s u`;;

let WAN_POINCARE_BALL_STATEMENT = new_definition
 `WAN_POINCARE_BALL_STATEMENT (n:N->bool) (kk:K->bool) <=>
    ?C. &0 < C /\
        !(a:real^N) r (u:real^N->real^K).
           &0 < r /\ wan_w12 (ball(a,r)) u
           ==> drop(integral (ball(a,r))
                      (\x. lift(norm(u x - inv(measure(ball(a,r))) %
                                           integral (ball(a,r)) u) pow 2)))
               <= C * r pow 2 * wan_dir (ball(a,r)) u`;;

let WAN_HARDY_BALL_STATEMENT = new_definition
 `WAN_HARDY_BALL_STATEMENT (n:N->bool) (kk:K->bool) <=>
    ?C. &0 < C /\
        !(a:real^N) r (u:real^N->real^K).
           &0 < r /\ wan_w120 (ball(a,r)) u
           ==> (\x. lift(norm(u x) pow 2 / (r - norm(x - a)) pow 2))
                 integrable_on ball(a,r) /\
               drop(integral (ball(a,r))
                      (\x. lift(norm(u x) pow 2 / (r - norm(x - a)) pow 2)))
               <= C * wan_dir (ball(a,r)) u`;;

let WAN_WIRTINGER_VEC_STATEMENT = new_definition
 `WAN_WIRTINGER_VEC_STATEMENT (kk:K->bool) <=>
    !(f:real->real^K) (f':real->real^K).
       (!x. x IN real_interval[&0,&2 * pi]
            ==> ((\t. f'(drop t)) has_integral (f x - f(&0))) (interval[vec 0,lift x])) /\
       f(&2 * pi) = f(&0) /\
       ((\t. f(drop t)) has_integral vec 0) (interval[vec 0,lift(&2 * pi)]) /\
       (\t. lift(norm(f'(drop t)) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)]
       ==> (\t. lift(norm(f(drop t)) pow 2)) integrable_on interval[vec 0,lift(&2 * pi)] /\
           drop(integral (interval[vec 0,lift(&2 * pi)]) (\t. lift(norm(f(drop t)) pow 2)))
           <= drop(integral (interval[vec 0,lift(&2 * pi)])
                     (\t. lift(norm(f'(drop t)) pow 2)))`;;

(* ------------------------------------------------------------------------- *)
(* S2.3 Planar slicing: polar Fubini for the Dirichlet density, absolute    *)
(* continuity on almost every circle (traces on circles), Courant-Lebesgue. *)
(* ------------------------------------------------------------------------- *)

let WAN_POLAR_DIR_STATEMENT = new_definition
 `WAN_POLAR_DIR_STATEMENT (kk:K->bool) <=>
    !(a:real^2) R r1 r2 (u:real^2->real^K).
       wan_w12 (ball(a,R)) u /\ &0 <= r1 /\ r1 < r2 /\ r2 <= R
       ==> (\r. lift(drop r *
                     drop(integral (interval[vec 0,lift(&2 * pi)])
                            (\t. lift(norm(wan_wd (ball(a,R)) 1 u
                                             (wan_circ a (drop r) (drop t))) pow 2 +
                                      norm(wan_wd (ball(a,R)) 2 u
                                             (wan_circ a (drop r) (drop t))) pow 2)))))
             integrable_on interval[lift r1,lift r2] /\
           drop(integral (interval[lift r1,lift r2])
                  (\r. lift(drop r *
                            drop(integral (interval[vec 0,lift(&2 * pi)])
                                   (\t. lift(norm(wan_wd (ball(a,R)) 1 u
                                                    (wan_circ a (drop r) (drop t))) pow 2 +
                                             norm(wan_wd (ball(a,R)) 2 u
                                                    (wan_circ a (drop r) (drop t))) pow 2)))))) =
           drop(integral {x | r1 < norm(x - a) /\ norm(x - a) < r2}
                  (\x. lift(norm(wan_wd (ball(a,R)) 1 u x) pow 2 +
                            norm(wan_wd (ball(a,R)) 2 u x) pow 2)))`;;

let WAN_CIRCLE_ACL_STATEMENT = new_definition
 `WAN_CIRCLE_ACL_STATEMENT (kk:K->bool) <=>
    !(a:real^2) R (u:real^2->real^K).
       &0 < R /\ u continuous_on ball(a,R) /\ wan_w12 (ball(a,R)) u
       ==> ?S. negligible S /\
               !r. &0 < r /\ r < R /\ ~(lift r IN S)
                   ==> (!t. &0 <= t /\ t <= &2 * pi
                            ==> ((\s. r % (--(sin(drop s)) %
                                           wan_wd (ball(a,R)) 1 u (wan_circ a r (drop s)) +
                                           cos(drop s) %
                                           wan_wd (ball(a,R)) 2 u (wan_circ a r (drop s))))
                                 has_integral (u(wan_circ a r t) - u(wan_circ a r (&0))))
                                (interval[vec 0,lift t])) /\
                       (\s. lift(norm(wan_wd (ball(a,R)) 1 u (wan_circ a r (drop s))) pow 2 +
                                 norm(wan_wd (ball(a,R)) 2 u (wan_circ a r (drop s))) pow 2))
                       integrable_on interval[vec 0,lift(&2 * pi)]`;;

(* Courant-Lebesgue with E the energy (half the Dirichlet integral): for    *)
(* 0 < d < 1 some radius in (d R, sqrt d R) has oscillation at most        *)
(* sqrt(4 pi E / log(1/d)).                                                 *)

let WAN_COURANT_LEBESGUE_STATEMENT = new_definition
 `WAN_COURANT_LEBESGUE_STATEMENT (kk:K->bool) <=>
    !(a:real^2) R d E (u:real^2->real^K).
       &0 < R /\ &0 < d /\ d < &1 /\
       u continuous_on ball(a,R) /\ wan_w12 (ball(a,R)) u /\
       wan_dir (ball(a,R)) u <= &2 * E
       ==> ?r. d * R < r /\ r < sqrt d * R /\
               !t1 t2. norm(u(wan_circ a r t1) - u(wan_circ a r t2))
                       <= sqrt(&4 * pi * E / log(inv d))`;;

(* ------------------------------------------------------------------------- *)
(* S2.5 Laplace: Dirichlet principle (any bounded open set, R^K valued,      *)
(* minimizer smooth and harmonic; stated only), continuity up to the         *)
(* boundary on discs, mean value and sub-mean value in the plane, Weyl's     *)
(* lemma.                                                                    *)
(* ------------------------------------------------------------------------- *)

let WAN_DIRICHLET_STATEMENT = new_definition
 `WAN_DIRICHLET_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (g:real^N->real^K).
       open s /\ bounded s /\ wan_w12 s g
       ==> ?h. wan_w12 s h /\ wan_w120 s (\x. h x - g x) /\
               (!v. wan_w12 s v /\ wan_w120 s (\x. v x - g x)
                    ==> wan_dir s h <= wan_dir s v) /\
               (!v. wan_w12 s v /\ wan_w120 s (\x. v x - g x) /\
                    wan_dir s v <= wan_dir s h
                    ==> negligible {x | x IN s /\ ~(v x = h x)}) /\
               (?w. smooth_map_on s w /\
                    (!x j. x IN s /\ 1 <= j /\ j <= dimindex(:K)
                           ==> llap (\y:real^N. mat 1) (\y. w y$j) x = &0) /\
                    negligible {x | x IN s /\ ~(h x = w x)})`;;

let WAN_DIRICHLET_DISC_STATEMENT = new_definition
 `WAN_DIRICHLET_DISC_STATEMENT (kk:K->bool) <=>
    !(a:real^2) r (g:real^2->real^K).
       &0 < r /\ g continuous_on cball(a,r) /\ wan_w12 (ball(a,r)) g
       ==> ?h. h continuous_on cball(a,r) /\
               (!x. x IN sphere(a,r) ==> h x = g x) /\
               smooth_map_on (ball(a,r)) h /\
               (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
                      ==> llap (\y:real^2. mat 1) (\y. h y$j) x = &0) /\
               wan_w12 (ball(a,r)) h /\ wan_w120 (ball(a,r)) (\x. h x - g x) /\
               (!v. wan_w12 (ball(a,r)) v /\ wan_w120 (ball(a,r)) (\x. v x - g x)
                    ==> wan_dir (ball(a,r)) h <= wan_dir (ball(a,r)) v)`;;

let WAN_MEAN_VALUE_2D_STATEMENT = new_definition
 `WAN_MEAN_VALUE_2D_STATEMENT <=>
    !(s:real^2->bool) (h:real^2->real) a r.
       open s /\ &0 < r /\ cball(a,r) SUBSET s /\
       smooth_map_on s (\x. lift(h x)) /\
       (!x. x IN s ==> llap (\y:real^2. mat 1) h x = &0)
       ==> h a = inv(&2 * pi) *
                 drop(integral (interval[vec 0,lift(&2 * pi)])
                        (\t. lift(h(wan_circ a r (drop t))))) /\
           h a = inv(pi * r pow 2) * drop(integral (ball(a,r)) (\x. lift(h x)))`;;

let WAN_SUBMEAN_2D_STATEMENT = new_definition
 `WAN_SUBMEAN_2D_STATEMENT <=>
    !(s:real^2->bool) (h:real^2->real) a r.
       open s /\ &0 < r /\ cball(a,r) SUBSET s /\
       smooth_map_on s (\x. lift(h x)) /\
       (!x. x IN s ==> &0 <= llap (\y:real^2. mat 1) h x)
       ==> h a <= inv(&2 * pi) *
                  drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\t. lift(h(wan_circ a r (drop t))))) /\
           h a <= inv(pi * r pow 2) * drop(integral (ball(a,r)) (\x. lift(h x)))`;;

let WAN_WEYL_STATEMENT = new_definition
 `WAN_WEYL_STATEMENT (n:N->bool) <=>
    !(s:real^N->bool) (u:real^N->real).
       open s /\ wan_l2loc s (\x. lift(u x)) /\
       (!phi. wan_test s phi
              ==> integral s (\x. lift(u x * llap (\y:real^N. mat 1) phi x)) = vec 0)
       ==> ?w. smooth_map_on s (\x. lift(w x)) /\
               (!x. x IN s ==> llap (\y:real^N. mat 1) w x = &0) /\
               negligible {x | x IN s /\ ~(u x = w x)}`;;

(* ------------------------------------------------------------------------- *)
(* S2.6 Interior estimates (scale-invariant forms): derivative bounds for    *)
(* harmonic functions, Campanato decay of the Dirichlet density, Caccioppoli *)
(* for weakly harmonic maps, interior H^2 estimate for Poisson's equation,   *)
(* Hoelder gradient for bounded Laplacian in the plane (log potential). All  *)
(* are stated only.                                                          *)
(* ------------------------------------------------------------------------- *)

let WAN_HARM_DERIV_STATEMENT = new_definition
 `WAN_HARM_DERIV_STATEMENT (n:N->bool) <=>
    !m. ?C. &0 < C /\
            !(s:real^N->bool) (h:real^N->real) a r l.
               open s /\ &0 < r /\ cball(a,r) SUBSET s /\
               smooth_map_on s (\x. lift(h x)) /\
               (!x. x IN s ==> llap (\y:real^N. mat 1) h x = &0) /\
               LENGTH l = m /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
               ==> r pow (2 * m + dimindex(:N)) *
                   norm(iterated_partial l (\x. lift(h x)) a) pow 2
                   <= C * drop(integral (ball(a,r)) (\x. lift(h x pow 2)))`;;

let WAN_HARM_CAMPANATO_STATEMENT = new_definition
 `WAN_HARM_CAMPANATO_STATEMENT (n:N->bool) <=>
    ?C. &0 < C /\
        !(s:real^N->bool) (h:real^N->real) a r rho.
           open s /\ &0 < rho /\ rho <= r /\ cball(a,r) SUBSET s /\
           smooth_map_on s (\x. lift(h x)) /\
           (!x. x IN s ==> llap (\y:real^N. mat 1) h x = &0)
           ==> drop(integral (ball(a,rho)) (\x. lift(lgrad2 (\y:real^N. mat 1) h x)))
               <= C * (rho / r) pow dimindex(:N) *
                  drop(integral (ball(a,r)) (\x. lift(lgrad2 (\y:real^N. mat 1) h x)))`;;

let WAN_CACCIOPPOLI_STATEMENT = new_definition
 `WAN_CACCIOPPOLI_STATEMENT (n:N->bool) (kk:K->bool) <=>
    ?C. &0 < C /\
        !(a:real^N) r (u:real^N->real^K) c.
           &0 < r /\ wan_w12 (ball(a,r)) u /\
           (!phi. wan_test (ball(a,r)) phi
                  ==> vsum(1..dimindex(:N))
                        (\i. integral (ball(a,r))
                               (\x. wan_dpart i phi x % wan_wd (ball(a,r)) i u x)) = vec 0)
           ==> sum(1..dimindex(:N))
                  (\i. drop(integral (ball(a,r / &2))
                              (\x. lift(norm(wan_wd (ball(a,r)) i u x) pow 2))))
               <= C / r pow 2 * drop(integral (ball(a,r)) (\x. lift(norm(u x - c) pow 2)))`;;

let WAN_POISSON_H2_STATEMENT = new_definition
 `WAN_POISSON_H2_STATEMENT (n:N->bool) <=>
    ?C. &0 < C /\
        !(a:real^N) r (u:real^N->real) (f:real^N->real).
           &0 < r /\ wan_w12 (ball(a,r)) (\x. lift(u x)) /\
           (\x. lift(f x)) IN lspace (ball(a,r)) (&2) /\
           (!phi. wan_test (ball(a,r)) phi
                  ==> vsum(1..dimindex(:N))
                        (\i. integral (ball(a,r))
                               (\x. wan_dpart i phi x %
                                    wan_wd (ball(a,r)) i (\y. lift(u y)) x)) =
                      --(integral (ball(a,r)) (\x. lift(f x * phi x))))
           ==> (!i. 1 <= i /\ i <= dimindex(:N)
                    ==> wan_w12 (ball(a,r / &2)) (wan_wd (ball(a,r)) i (\y. lift(u y)))) /\
               sum(1..dimindex(:N))
                  (\i. wan_dir (ball(a,r / &2)) (wan_wd (ball(a,r)) i (\y. lift(u y))))
               <= C * (drop(integral (ball(a,r)) (\x. lift(f x pow 2))) +
                       drop(integral (ball(a,r)) (\x. lift(u x pow 2))) / r pow 4)`;;

let WAN_LOGPOT_C1A_STATEMENT = new_definition
 `WAN_LOGPOT_C1A_STATEMENT <=>
    !(a:real^2) r (u:real^2->real) (f:real^2->real) M al.
       &0 < r /\ &0 < al /\ al < &1 /\
       wan_w12 (ball(a,r)) (\x. lift(u x)) /\
       (\x. lift(f x)) measurable_on ball(a,r) /\
       (!x. x IN ball(a,r) ==> abs(f x) <= M) /\
       (!phi. wan_test (ball(a,r)) phi
              ==> vsum(1..2)
                    (\i. integral (ball(a,r))
                           (\x. wan_dpart i phi x % wan_wd (ball(a,r)) i (\y. lift(u y)) x)) =
                  --(integral (ball(a,r)) (\x. lift(f x * phi x))))
       ==> ?w H. continuously_differentiable 1 (ball(a,r / &2)) (\x. lift(w x)) /\
                 negligible {x | x IN ball(a,r / &2) /\ ~(u x = w x)} /\
                 !x y. x IN ball(a,r / &2) /\ y IN ball(a,r / &2)
                       ==> norm((lambda i. wan_dpart i w x):real^2 -
                                (lambda i. wan_dpart i w y)) <= H * norm(x - y) rpow al`;;

(* ------------------------------------------------------------------------- *)
(* S2.7 W^{1,2} calculus for harmonic replacement: chain rule through the   *)
(* nearest-point projection, products with cutoffs, zero trace of maps      *)
(* continuous on the closed ball and vanishing on the sphere, gluing.       *)
(* ------------------------------------------------------------------------- *)

let WAN_CHAIN_W12_STATEMENT = new_definition
 `WAN_CHAIN_W12_STATEMENT (n:N->bool) (kk:K->bool) (ll:L->bool) <=>
    !(s:real^N->bool) (u:real^N->real^K) (P:real^K->real^L).
       open s /\ bounded s /\ wan_w12 s u /\
       continuously_differentiable 1 (:real^K) P /\
       (?B. !y. onorm(frechet_derivative P (at y)) <= B)
       ==> wan_w12 s (\x. P(u x)) /\
           !i. 1 <= i /\ i <= dimindex(:N)
               ==> wan_wpd s i (\x. P(u x))
                     (\x. frechet_derivative P (at (u x)) (wan_wd s i u x))`;;

let WAN_MUL_W12_STATEMENT = new_definition
 `WAN_MUL_W12_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (u:real^N->real^K) (g:real^N->real).
       open s /\ wan_w12 s u /\
       smooth_map_on s (\x. lift(g x)) /\
       (?B. !x. x IN s ==> abs(g x) <= B) /\
       (?B. !x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> abs(wan_dpart i g x) <= B)
       ==> wan_w12 s (\x. g x % u x) /\
           !i. 1 <= i /\ i <= dimindex(:N)
               ==> wan_wpd s i (\x. g x % u x)
                     (\x. wan_dpart i g x % u x + g x % wan_wd s i u x)`;;

let WAN_W120_CONT_STATEMENT = new_definition
 `WAN_W120_CONT_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(a:real^N) r (w:real^N->real^K).
       &0 < r /\ w continuous_on cball(a,r) /\
       (!x. x IN sphere(a,r) ==> w x = vec 0) /\ wan_w12 (ball(a,r)) w
       ==> wan_w120 (ball(a,r)) w`;;

let WAN_GLUE_W12_STATEMENT = new_definition
 `WAN_GLUE_W12_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (a:real^N) r (u:real^N->real^K) v.
       open s /\ &0 < r /\ cball(a,r) SUBSET s /\
       wan_w12 s u /\ wan_w12 (ball(a,r)) v /\
       wan_w120 (ball(a,r)) (\x. v x - u x)
       ==> wan_w12 s (\x. if x IN ball(a,r) then v x else u x) /\
           wan_dir s (\x. if x IN ball(a,r) then v x else u x) =
           wan_dir (ball(a,r)) v + wan_dir (s DIFF cball(a,r)) u`;;

(* ========================================================================= *)
(* The bridge from WAN_ELL_SEMI_STATEMENT to WAN_P2B_REQ_WREG_COPY, and      *)
(* first sanity theorems (nontrivial test functions, the zero map).          *)
(* ========================================================================= *)

(* WAN_ELL_SEMI at dimension 3 implies WAN_P2B_REQ_WREG_COPY: take           *)
(* W = s PCROSS (:real^1); global Lipschitz implies local Lipschitz;         *)
(* positivity and continuity are not used.                                   *)

let WAN_ELL_SEMI_IMP_P2B_WREG = prove
 (`!w:B->bool. WAN_ELL_SEMI_STATEMENT (:3) ==> WAN_P2B_REQ_WREG_COPY w`,
  GEN_TAC THEN REWRITE_TAC[WAN_ELL_SEMI_STATEMENT; WAN_P2B_REQ_WREG_COPY] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`G:real^3->real^3^3`; `V:real^3->real`; `Fr:real^3->real->real`;
    `(s:real^3->bool) PCROSS (:real^1)`] THEN
  SUBGOAL_THEN `open(s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIMINDEX_3; LE_REFL] THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV] THEN
  REWRITE_TAC[wan_loclip] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `L:real` THEN ASM_MESON_TAC[SUBSET]);;

let WAN_TEST_BUMP = prove
 (`!(s:real^N->bool) x0.
     open s /\ x0 IN s
     ==> ?phi. wan_test s phi /\ phi x0 = &1 /\ (!x. &0 <= phi x /\ phi x <= &1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^N. smooth_bump (e / &2) e (x - x0)` THEN
  REWRITE_TAC[wan_test; SMOOTH_BUMP_BOUNDS] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N) (\x. lift(smooth_bump (e / &2) e (x - x0)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^N. lift(smooth_bump (e / &2) e (x - x0))) =
                  (\x. lift(smooth_bump (e / &2) e x)) o (\x. x - x0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
      MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `cball(x0:real^N,e)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_BUMP_0 THEN
    MP_TAC(ISPECL [`x0:real^N`; `x:real^N`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_SUB_REFL] THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN
    REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC]);;

let WAN_LSPACE2_ZERO = prove
 (`!s:real^N->bool. (\x. vec 0:real^K) IN lspace s (&2)`,
  GEN_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM; NORM_0; MEASURABLE_ON_0] THEN
  REWRITE_TAC[RPOW_ZERO; REAL_ARITH `~(&2 = &0)`; LIFT_NUM; INTEGRABLE_0]);;

let WAN_W12_ZERO = prove
 (`!s:real^N->bool. wan_w12 s (\x. vec 0:real^K)`,
  GEN_TAC THEN REWRITE_TAC[wan_w12; WAN_LSPACE2_ZERO] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `\x:real^N. vec 0:real^K` THEN
  REWRITE_TAC[WAN_LSPACE2_ZERO; wan_wpd; wan_lloc; ABSOLUTELY_INTEGRABLE_0] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; INTEGRAL_0; VECTOR_NEG_0]);;

(* ========================================================================= *)
(* Integrals of derivatives of compactly supported C^1 maps vanish. The      *)
(* proofs are adapted from earlier HOL Light work. They use                  *)
(* HAS_VECTOR_DERIVATIVE_PARAMETRIC_INTEGRAL from the Navier_Stokes          *)
(* development (github.com/hol-light-family/Navier_Stokes), loaded through   *)
(* pc_pde_torus.                                                             *)
(* ========================================================================= *)

let WAN_HVD_FRECHET_COMPOSE = prove
 (`!(f:real^1->real^M) (g:real^M->real^N) f' g' x.
        (f has_vector_derivative f') (at x) /\ (g has_derivative g') (at (f x))
        ==> ((g o f) has_vector_derivative g' f') (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(g':real^M->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^1->real^M`; `g:real^M->real^N`;
                 `\h:real^1. drop h % (f':real^M)`; `g':real^M->real^N`;
                 `x:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_MESON_TAC[LINEAR_CMUL]);;


let WAN_NT_DERIVATIVE_ZERO_LOCAL = prove
 (`!(f:real^M->real^N) f' u x.
     open u /\ x IN u /\ (!y. y IN u ==> f y = vec 0) /\
     (f has_derivative f') (at x)
     ==> f' = (\h. vec 0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `x:real^M`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`(\y:real^M. vec 0:real^N)`; `e:real`] THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN ASM_MESON_TAC[DIST_SYM]);;

let WAN_NT_ZERO_EXTENSION_CONTINUOUS = prove
 (`!(f:real^M->real^N) s k.
     open s /\ compact k /\ k SUBSET s /\ f continuous_on s /\
     (!x. x IN s /\ ~(x IN k) ==> f x = vec 0)
     ==> (\x. if x IN s then f x else vec 0) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(:real^M) = s UNION ((:real^M) DIFF k)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL_OPEN THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC OPEN_SUBSET THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ASM SET_TAC[]]);;

let WAN_NT_INTEGRABLE_COMPACT_SUPPORT = prove
 (`!(f:real^M->real^N) s k.
     open s /\ compact k /\ k SUBSET s /\ f continuous_on s /\
     (!x. x IN s /\ ~(x IN k) ==> f x = vec 0)
     ==> f integrable_on s`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUPERSET THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC WAN_NT_ZERO_EXTENSION_CONTINUOUS THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integrals of partial derivatives of compactly supported C^1 functions.    *)
(* ------------------------------------------------------------------------- *)

let WAN_NT_LINE_VECTOR_DERIVATIVE = prove
 (`!(s:real^M) v t.
     ((\t. s + drop t % v) has_vector_derivative v) (at t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV) [GSYM VECTOR_ADD_LID] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]);;

let WAN_NT_INTEGRAL_PARTIAL_UNIV = prove
 (`!(f:real^M->real^N) f' k i.
     compact k /\ (!x. (f has_derivative f' x) (at x)) /\
     (\x. f' x (basis i)) continuous_on (:real^M) /\
     (!x. ~(x IN k) ==> f x = vec 0)
     ==> ((\x. f' x (basis i)) has_integral vec 0) (:real^M)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^M. ~(x IN k) ==> f' x = (\h:real^M. vec 0:real^N)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_NT_DERIVATIVE_ZERO_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `(:real^M) DIFF k`; `x:real^M`] THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^M c:real^M. y IN k /\ norm c <= &1
     ==> y - c IN interval[--((R + &1) % vec 1),(R + &1) % vec 1]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; VECTOR_SUB_COMPONENT; REAL_MUL_RID] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^M`; `j:num`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`c:real^M`; `j:num`] COMPONENT_LE_NORM) THEN
    MP_TAC(MP (SPEC `y:real^M` (ASSUME `!x:real^M. x IN k ==> norm x <= R`))
              (ASSUME `(y:real^M) IN k`)) THEN
    UNDISCH_TAC `norm(c:real^M) <= &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B = interval[--((R + &1) % vec 1):real^M,(R + &1) % vec 1]` THEN
  SUBGOAL_THEN `(k:real^M->bool) SUBSET B` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^M`; `vec 0:real^M`]) THEN
    ASM_REWRITE_TAC[NORM_0; VECTOR_SUB_RZERO; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_ON_SUPERSET THEN EXISTS_TAC `B:real^M->bool` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((x:real^M) IN k)` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(s:real^M) (t:real^1). (f:real^M->real^N)(s + drop t % basis i)`;
                 `\(s:real^M) (t:real^1). (f':real^M->real^M->real^N) (s + drop t % basis i) (basis i)`;
                 `--((R + &1) % vec 1):real^M`; `(R + &1) % vec 1:real^M`;
                 `lift(-- &1)`; `lift(&1)`; `vec 0:real^1`]
         HAS_VECTOR_DERIVATIVE_PARAMETRIC_INTEGRAL) THEN
  ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; ETA_AX] THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous_on (:real^M)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; differentiable];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      MP_TAC(ISPECL [`\t:real^1. (s:real^M) + drop t % basis i`;
                     `f:real^M->real^N`; `basis i:real^M`;
                     `(f':real^M->real^M->real^N) (s + drop t % basis i)`;
                     `t:real^1`] WAN_HVD_FRECHET_COMPOSE) THEN
      ASM_REWRITE_TAC[o_DEF; WAN_NT_LINE_VECTOR_DERIVATIVE];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^(M,1)finite_sum)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      SUBGOAL_THEN
       `(\z. (f':real^M->real^M->real^N)
               (fstcart z + drop (sndcart z) % basis i) (basis i)) =
        (\x. f' x (basis i)) o
        (\z:real^(M,1)finite_sum. fstcart z + drop (sndcart z) % basis i)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN REWRITE_TAC[LINEAR_FSTCART] THEN
        MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_SNDCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      REPEAT STRIP_TAC THEN EXPAND_TAC "B" THEN
      MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
      SUBGOAL_THEN `(\s. (f:real^M->real^N) (s + drop t % basis i)) =
                    f o (\s:real^M. s + drop t % basis i)` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `norm(basis i:real^M) <= &1` ASSUME_TAC THENL
   [ASM_CASES_TAC `1 <= i /\ i <= dimindex(:M)` THENL
     [ASM_SIMP_TAC[NORM_BASIS; REAL_LE_REFL];
      SUBGOAL_THEN `basis i:real^M = vec 0` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG]; REWRITE_TAC[NORM_0; REAL_POS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN interval[lift(-- &1),lift(&1)]
     ==> integral B (\s. (f:real^M->real^N)(s + drop t % basis i)) =
         integral (:real^M) f` ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
    REWRITE_TAC[INTEGRAL_TRANSLATION] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y - drop t % basis i:real^M` THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(drop t) * &1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral B (\s. (f':real^M->real^M->real^N) s (basis i)) = vec 0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC [`(\t:real^1. integral (:real^M) (f:real^M->real^N))`;
                          `lift(-- &1)`; `lift(&1)`; `vec 0:real^1`] THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; LIFT_DROP; IN_INTERVAL_1;
                DROP_VEC] THEN
    REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`(\t. integral B (\s. (f:real^M->real^N)(s + drop t % basis i)))`; `&1`] THEN
    ASM_SIMP_TAC[REAL_LT_01; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (f':real^M->real^M->real^N) x (basis i)) integrable_on B`
  MP_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN ASM_REWRITE_TAC[]);;

let WAN_NT_INTEGRAL_PARTIAL = prove
 (`!(f:real^M->real^N) f' s k i.
     open s /\ compact k /\ k SUBSET s /\
     (!x. x IN s ==> (f has_derivative f' x) (at x)) /\
     (\x. f' x (basis i)) continuous_on s /\
     (!x. x IN s /\ ~(x IN k) ==> f x = vec 0)
     ==> ((\x. f' x (basis i)) has_integral vec 0) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^M. x IN s /\ ~(x IN k) ==> f' x = (\h:real^M. vec 0:real^N)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_NT_DERIVATIVE_ZERO_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s DIFF k:real^M->bool`; `x:real^M`] THEN
    ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^M. ~(x IN k)
                ==> (if x IN s then (f:real^M->real^N) x else vec 0) = vec 0`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^M. if x IN s then (f:real^M->real^N) x else vec 0`;
                 `\x:real^M. if x IN s then (f':real^M->real^M->real^N) x
                             else (\h:real^M. vec 0:real^N)`;
                 `k:real^M->bool`; `i:num`] WAN_NT_INTEGRAL_PARTIAL_UNIV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN s` THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
        EXISTS_TAC `f:real^M->real^N` THEN
        FIRST_ASSUM(MP_TAC o SPEC `x:real^M` o
          GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
        ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `e:real` THEN REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
          SUBGOAL_THEN `(y:real^M) IN s` (fun th -> REWRITE_TAC[th]) THEN
          ASM_MESON_TAC[DIST_SYM];
          ASM_SIMP_TAC[]];
        SUBGOAL_THEN `~((x:real^M) IN k)` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `(:real^M) DIFF k` OPEN_CONTAINS_BALL) THEN
        ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
        ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; SUBSET; IN_BALL] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
        MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
        MAP_EVERY EXISTS_TAC [`(\y:real^M. vec 0:real^N)`; `e:real`] THEN
        ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN X_GEN_TAC `y:real^M` THEN
        DISCH_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN
        ASM_MESON_TAC[DIST_SYM]];
      REWRITE_TAC[COND_RATOR] THEN
      MATCH_MP_TAC WAN_NT_ZERO_EXTENSION_CONTINUOUS THEN
      EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[COND_RATOR; HAS_INTEGRAL_RESTRICT_UNIV]]);;

(* ========================================================================= *)
(* Sanity theorems: the                                                      *)
(* integral of a directional derivative of a compactly supported smooth map *)
(* vanishes; integration by parts against test functions; nontrivial        *)
(* members of W^{1,2} with their weak partials; constants solve the weak    *)
(* heat equation (non-vacuity) and U = t does not (teeth).                  *)
(* ========================================================================= *)

let WAN_INTEGRAL_DIRDERIV_ZERO = prove
 (`!(f:real^M->real^K) k v.
     compact k /\ smooth_map_on (:real^M) f /\ (!x. ~(x IN k) ==> f x = vec 0)
     ==> ((\x. frechet_derivative f (at x) v) has_integral vec 0) (:real^M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. ((\x. frechet_derivative (f:real^M->real^K) (at x) (basis i))
         has_integral vec 0) (:real^M)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_NT_INTEGRAL_PARTIAL_UNIV THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^K`; `k:real^M->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^M)`; `f:real^M->real^K`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. frechet_derivative (f:real^M->real^K) (at x) v) =
    (\x. vsum(1..dimindex(:M)) (\i. (v:real^M)$i % frechet_derivative f (at x) (basis i)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
    SUBGOAL_THEN `linear(frechet_derivative (f:real^M->real^K) (at x))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^M)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `vec 0:real^K = vsum(1..dimindex(:M)) (\i. (v:real^M)$i % vec 0)`
  SUBST1_TAC THENL [REWRITE_TAC[VECTOR_MUL_RZERO; VSUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
  ASM_REWRITE_TAC[]);;

let WAN_TEST_DERIV_ZERO = prove
 (`!(phi:real^N->real) k v x.
     smooth_map_on (:real^N) (\y. lift(phi y)) /\ compact k /\
     (!y. ~(y IN k) ==> phi y = &0) /\ ~(x IN k)
     ==> frechet_derivative (\y. lift(phi y)) (at x) v = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative (\y. lift((phi:real^N->real) y)) (at x) = (\h. vec 0)`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC WAN_NT_DERIVATIVE_ZERO_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`\y. lift((phi:real^N->real) y)`; `(:real^N) DIFF k`; `x:real^N`] THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; LIFT_NUM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let WAN_TEST_IBP_UNIV = prove
 (`!(phi:real^N->real) psi k v.
     smooth_map_on (:real^N) (\x. lift(phi x)) /\ compact k /\
     (!x. ~(x IN k) ==> phi x = &0) /\
     smooth_map_on (:real^N) (\x. lift(psi x))
     ==> ((\x. lift(drop(frechet_derivative (\y. lift(phi y)) (at x) v) * psi x +
                    phi x * drop(frechet_derivative (\y. lift(psi y)) (at x) v)))
          has_integral vec 0) (:real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift((phi:real^N->real) x * psi x)`; `k:real^N->bool`; `v:real^N`]
                WAN_INTEGRAL_DIRDERIV_ZERO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_MUL_LZERO; LIFT_NUM] THEN
    MP_TAC(ISPECL [`(:real^N)`; `\x. lift((phi:real^N->real) x)`; `\x. lift((psi:real^N->real) x)`]
                  SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
  SUBGOAL_THEN
   `((\y. lift((phi:real^N->real) y)) has_derivative
     frechet_derivative (\y. lift(phi y)) (at x)) (at x) /\
    ((\y. lift((psi:real^N->real) y)) has_derivative
     frechet_derivative (\y. lift(psi y)) (at x)) (at x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
                    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^N->real`;
                 `\h. drop(frechet_derivative (\y. lift((phi:real^N->real) y)) (at x) h)`;
                 `\y. lift((psi:real^N->real) y)`;
                 `frechet_derivative (\y. lift((psi:real^N->real) y)) (at x)`;
                 `x:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT
                         (REWRITE_RULE[GSYM LIFT_CMUL] (BETA_RULE th)))]) THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let WAN_TEST_IBP = prove
 (`!(s:real^N->bool) phi psi v.
     open s /\ wan_test s phi /\ smooth_map_on (:real^N) (\x. lift(psi x))
     ==> (\x. lift(drop(frechet_derivative (\y. lift(phi y)) (at x) v) * psi x))
           integrable_on s /\
         (\x. lift(phi x * drop(frechet_derivative (\y. lift(psi y)) (at x) v)))
           integrable_on s /\
         integral s (\x. lift(drop(frechet_derivative (\y. lift(phi y)) (at x) v) * psi x)) =
         --(integral s (\x. lift(phi x * drop(frechet_derivative (\y. lift(psi y)) (at x) v))))`,
  REWRITE_TAC[wan_test] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^N->real`; `psi:real^N->real`; `k:real^N->bool`; `v:real^N`]
                WAN_TEST_IBP_UNIV) THEN
  ASM_REWRITE_TAC[LIFT_ADD] THEN DISCH_TAC THEN
  ABBREV_TAC `a = \x:real^N. lift(drop(frechet_derivative (\y. lift(phi y)) (at x) v) * psi x)` THEN
  ABBREV_TAC `b = \x:real^N. lift(phi x * drop(frechet_derivative (\y. lift(psi y)) (at x) v))` THEN
  SUBGOAL_THEN `((\x. (a:real^N->real^1) x + (b:real^N->real^1) x) has_integral vec 0) (:real^N)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. ~(x IN k) ==> (a:real^N->real^1) x = vec 0 /\ (b:real^N->real^1) x = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXPAND_TAC "a" THEN EXPAND_TAC "b" THEN
    MP_TAC(ISPECL [`phi:real^N->real`; `k:real^N->bool`; `v:real^N`; `x:real^N`]
                  WAN_TEST_DERIV_ZERO) THEN
    ASM_SIMP_TAC[DROP_VEC; REAL_MUL_LZERO; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N->real^1) continuous_on (:real^N) /\ (b:real^N->real^1) continuous_on (:real^N)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN EXPAND_TAC "b" THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THENL
     [MP_TAC(ISPECL [`(:real^N)`;
                     `\x. frechet_derivative (\y. lift((phi:real^N->real) y)) (at x) v`;
                     `\x. lift((psi:real^N->real) x)`] SMOOTH_MAP_ON_LIFT_MUL);
      MP_TAC(ISPECL [`(:real^N)`; `\x. lift((phi:real^N->real) x)`;
                     `\x. frechet_derivative (\y. lift((psi:real^N->real) y)) (at x) v`]
                    SMOOTH_MAP_ON_LIFT_MUL)] THEN
    ASM_SIMP_TAC[OPEN_UNIV; LIFT_DROP; SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N->real^1) integrable_on (:real^N) /\ (b:real^N->real^1) integrable_on (:real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_NT_INTEGRABLE_COMPACT_SUPPORT THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. if x IN s then (a:real^N->real^1) x else vec 0) = a /\
                (\x. if x IN s then (b:real^N->real^1) x else vec 0) = b`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N->real^1) integrable_on s /\ (b:real^N->real^1) integrable_on s /\
                integral s a = integral (:real^N) a /\ integral s b = integral (:real^N) b`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV; GSYM INTEGRAL_RESTRICT_UNIV] THEN
    ASM_REWRITE_TAC[IN_UNIV; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INTEGRAL_UNIQUE o
    check (fun th -> is_comb(concl th) && can (find_term ((=) `(:real^N)`)) (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "has_integral")) (concl th))) THEN
  ASM_SIMP_TAC[INTEGRAL_ADD] THEN VECTOR_ARITH_TAC);;

let WAN_CONTINUOUS_LLOC = prove
 (`!(s:real^N->bool) (f:real^N->real^K).
     f continuous_on (:real^N) ==> wan_lloc s f`,
  REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `interval[a:real^N,b]` THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let WAN_WPD_TEST_VEC = prove
 (`!(s:real^N->bool) psi (c:real^K) i.
     open s /\ wan_test s psi
     ==> wan_wpd s i (\x. psi x % c) (\x. wan_dpart i psi x % c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_wpd] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. lift((psi:real^N->real) x))` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_test]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN
    SUBGOAL_THEN `(\x. (psi:real^N->real) x % (c:real^K)) = (\y. drop y % c) o (\x. lift(psi x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC];
    MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN
    SUBGOAL_THEN `(\x. wan_dpart i (psi:real^N->real) x % (c:real^K)) =
                  (\y. drop y % c) o (\x. frechet_derivative (\y. lift(psi y)) (at x) (basis i))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_dpart]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC]];
    X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `psi:real^N->real`; `basis i:real^N`]
                  WAN_TEST_IBP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `linear (\y:real^1. drop y % (c:real^K))` ASSUME_TAC THENL
     [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. lift(drop(frechet_derivative (\y. lift((phi:real^N->real) y)) (at x) (basis i)) * psi x)`;
                   `s:real^N->bool`; `\y:real^1. drop y % (c:real^K)`] INTEGRAL_LINEAR) THEN
    MP_TAC(ISPECL [`\x. lift((phi:real^N->real) x * drop(frechet_derivative (\y. lift(psi y)) (at x) (basis i)))`;
                   `s:real^N->bool`; `\y:real^1. drop y % (c:real^K)`] INTEGRAL_LINEAR) THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC[wan_dpart; VECTOR_MUL_ASSOC; DROP_NEG; VECTOR_MUL_LNEG] THEN
    REWRITE_TAC[REAL_MUL_SYM]]);;

let WAN_LSPACE2_CONT_SUPPORT = prove
 (`!(s:real^N->bool) (f:real^N->real^K) k.
     open s /\ compact k /\ k SUBSET s /\ f continuous_on (:real^N) /\
     (!x. ~(x IN k) ==> f x = vec 0)
     ==> f IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    MATCH_MP_TAC WAN_NT_INTEGRABLE_COMPACT_SUPPORT THEN
    EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[NORM_0; LIFT_NUM; REAL_POW_ZERO; ARITH_EQ] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
    SUBGOAL_THEN `(\x. lift(norm((f:real^N->real^K) x))) = (lift o norm) o f`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]]);;

let WAN_W12_TEST_VEC = prove
 (`!(s:real^N->bool) psi (c:real^K).
     open s /\ wan_test s psi ==> wan_w12 s (\x. psi x % c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_test]) THEN
  SUBGOAL_THEN `linear (\y:real^1. drop y % (c:real^K))` ASSUME_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[wan_w12] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO] THEN
    SUBGOAL_THEN `(\x. (psi:real^N->real) x % (c:real^K)) = (\y. drop y % c) o (\x. lift(psi x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LINEAR_CONTINUOUS_ON];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    EXISTS_TAC `\x. wan_dpart i (psi:real^N->real) x % (c:real^K)` THEN
    ASM_SIMP_TAC[WAN_WPD_TEST_VEC] THEN
    MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. wan_dpart i (psi:real^N->real) x % (c:real^K)) =
                    (\y. drop y % c) o (\x. frechet_derivative (\y. lift(psi y)) (at x) (basis i))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_dpart]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`psi:real^N->real`; `k:real^N->bool`; `basis i:real^N`; `x:real^N`]
                    WAN_TEST_DERIV_ZERO) THEN
      ASM_SIMP_TAC[wan_dpart; DROP_VEC; VECTOR_MUL_LZERO]]]);;


let WAN_PWEAK_CONST = prove
 (`!om:real^(N,1)finite_sum->bool.
     open om
     ==> wan_pweak om (\z. &1) (\z. mat 1) (\z. vec 0) (\z. &0) (\z. &0) (\z. &1) (\j z. &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_pweak] THEN X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN
  DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0; VEC_COMPONENT; REAL_ADD_RID;
              REAL_SUB_RZERO; REAL_MUL_LID; LIFT_NUM; INTEGRAL_0] THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `phi:real^(N,1)finite_sum->real`;
                 `\z:real^(N,1)finite_sum. &1`;
                 `pastecart (vec 0:real^N) (lift(&1))`] WAN_TEST_IBP) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; LIFT_NUM] THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; DROP_VEC; REAL_MUL_RZERO; REAL_MUL_RID;
              LIFT_NUM; INTEGRAL_0; VECTOR_NEG_0; LIFT_DROP] THEN
  REWRITE_TAC[wan_tder; LIFT_NUM; LIFT_DROP] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2 th)]));;

(* Teeth: U = t (the time coordinate) is not a weak solution of the heat   *)
(* equation on space-time, so the weak form constrains its solutions.      *)

let WAN_PWEAK_TEETH = prove
 (`~(wan_pweak (:real^(N,1)finite_sum) (\z. &1) (\z. mat 1) (\z. vec 0) (\z. &0) (\z. &0)
               (\z. drop(sndcart z)) (\j z. &0))`,
  REWRITE_TAC[wan_pweak] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0; VEC_COMPONENT; REAL_ADD_RID;
              REAL_SUB_RZERO; REAL_MUL_LID; LIFT_NUM; INTEGRAL_0] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?phi. wan_test (interval(vec 0:real^(N,1)finite_sum,vec 1)) phi /\
          phi (inv(&2) % vec 1) = &1 /\ (!x. &0 <= phi x /\ phi x <= &1)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_TEST_BUMP THEN
    REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(N,1)finite_sum) (\x. lift(phi x)) /\
    ?k. compact k /\ k SUBSET interval(vec 0:real^(N,1)finite_sum,vec 1) /\
        !x. ~(x IN k) ==> phi x = &0`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[wan_test]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_test (:real^(N,1)finite_sum) phi` ASSUME_TAC THENL
   [REWRITE_TAC[wan_test] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^(N,1)finite_sum) (\z. lift(drop(sndcart z) * wan_tder phi z)) = vec 0`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[wan_tder] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^(N,1)finite_sum) (\x. lift(drop(sndcart x)))` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `\x:real^(N,1)finite_sum. x`;
                   `sndcart:real^(N,1)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
    REWRITE_TAC[OPEN_UNIV; LINEAR_SNDCART; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^(N,1)finite_sum.
      frechet_derivative (\y. lift(drop(sndcart y))) (at x) = sndcart`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `phi:real^(N,1)finite_sum->real`;
                 `\z:real^(N,1)finite_sum. drop(sndcart z)`;
                 `pastecart (vec 0:real^N) (lift(&1))`] WAN_TEST_IBP) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP; ETA_AX]) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SNDCART_PASTECART; LIFT_DROP; REAL_MUL_RID; ETA_AX] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[VECTOR_NEG_EQ_0] o SYM) THEN
  SUBGOAL_THEN `integral (interval[vec 0:real^(N,1)finite_sum,vec 1]) (\x. lift(phi x)) =
                integral (:real^(N,1)finite_sum) (\x. lift(phi x))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; IN_UNIV] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((x:real^(N,1)finite_sum) IN k)` (fun th -> ASM_SIMP_TAC[th; LIFT_NUM]) THEN
    MP_TAC(ISPECL [`vec 0:real^(N,1)finite_sum`; `vec 1:real^(N,1)finite_sum`]
                  INTERVAL_OPEN_SUBSET_CLOSED) THEN
    UNDISCH_TAC `(k:real^(N,1)finite_sum->bool) SUBSET interval(vec 0,vec 1)` THEN
    UNDISCH_TAC `~((x:real^(N,1)finite_sum) IN interval[vec 0,vec 1])` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^(N,1)finite_sum. x IN interval[vec 0,vec 1] ==> phi x = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NSPU_INTEGRAL_EQ_0_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^(N,1)finite_sum` THEN REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF] THEN
    MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `\x:real^(N,1)finite_sum. lift(phi x)`]
                  SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(inv(&2) % vec 1:real^(N,1)finite_sum) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[REAL_ARITH `~(&1 = &0)`]);;

